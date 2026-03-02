import requests
import hashlib
import json
import time
from datetime import datetime, timedelta
from datetime import date as date_cls
import os
import psutil
import socket
import glob
import platform
import sys
import re
import math
import subprocess
from zoneinfo import ZoneInfo
from collections import deque
from collections import defaultdict
import statistics
from pytz import timezone
from pathlib import Path
from typing import Any, Dict, Tuple, Optional, List
import traceback
import signal
import shutil
import subprocess
from urllib.parse import urlparse, parse_qs

# NEW: threading / futures
import threading
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

# =========================
# ENV / CONFIG
# =========================
BOT_TOKEN = os.environ['MY_BOT_TOKEN']
CHAT_ID = os.environ['MY_CHAT_ID']
WEATHER_API = os.environ['MY_WEATHER_API']
LOCATION_LAT = os.environ['MY_LOCATION_LAT']
LOCATION_LON = os.environ['MY_LOCATION_LON']
APP_ID = os.environ['MY_APP_ID']
APP_SECRET = os.environ['MY_APP_SECRET']
EMAIL = os.environ['MY_EMAIL']
PASSWORD = os.environ['MY_PASSWORD']
DEVICE_SN = os.environ['MY_DEVICE_SN']
QUOTE_LIMIT = int(os.getenv('MY_QUOTE_LIMIT', '200000'))
QUOTE_FILE = os.environ['MY_QUOTE_FILE']
STATE_FILE = os.environ['MY_STATE_FILE']
SOLARMAN_FILE = os.environ['MY_SOLARMAN_FILE']
WALLET_ADDRESS = os.environ['WALLET_ADDRESS']
HISTORY_DIR = os.getenv('MY_HISTORY_DIR', 'solarman_json')

print(platform.machine())
print(platform.system())

# =========================
# GLOBALS
# =========================
is_rpi = None
last_update_id: Optional[int] = None
prev_state: Optional[str] = None
state: Optional[str] = None
uptime: Optional[datetime] = None
used_quote: int = 0
last_quote_reset_date: Optional[date_cls] = None
budapest_tz = ZoneInfo("Europe/Budapest")

oled = None
image = None
draw = None
font = None

# HTTP session (shared; protect with lock in threads)
session = requests.Session()
session.headers.update({'Connection': 'close'})
TELEGRAM_BASE = f'https://api.telegram.org/bot{BOT_TOKEN}'

# Locks for thread safety
session_lock = threading.Lock()
gpio_lock = threading.Lock()
snapshot_lock = threading.Lock()

# Shared snapshot for Telegram thread
_shared_snapshot = {
    "battery": 0, "power": 0, "state": "init", "current_condition": "unknown",
    "sunrise": datetime.now(tz=budapest_tz), "sunset": datetime.now(tz=budapest_tz),
    "clouds": 0, "garage_temp": 0, "garage_hum": 0,
    "historical_hints": {
        "month_quality": "neutral",
        "early_start_soc": 55,
        "min_stop_soc": 20,
        "late_day_reserve_soc": 80,
        "should_preserve_battery": False,
        "headroom_good": False,
    },
}

# 6 months @ 5-minute cycle hard cap ≈ 51,840 points
MAX_HISTORY_POINTS = int(os.getenv("MY_HISTORY_MAX_POINTS", "51840"))
telemetry_history: deque = deque(maxlen=MAX_HISTORY_POINTS)


def _resolve_telemetry_file() -> Path:
    raw = os.getenv("MY_TELEMETRY_FILE", "telemetry_history.json")
    p = Path(raw)
    if p.is_absolute():
        return p
    # Keep default file near script to avoid cwd-dependent path issues.
    return (Path(__file__).resolve().parent / p).resolve()


TELEMETRY_FILE = _resolve_telemetry_file()
print(f"[Telemetry] Using telemetry store: {TELEMETRY_FILE}")


# Historical profile cache (derived from solarman_json/*.json)
historical_profile: Optional[Dict[str, Any]] = None

# Detect Raspberry Pi
if platform.system() == "Linux" and any(arch in platform.machine() for arch in ['arm', 'aarch64', 'armv7l']):
    is_rpi = True
else:
    is_rpi = False

# Hardware feature flags (soft-optional)
OLED_AVAILABLE = False
GPIO_AVAILABLE = False
DHT_AVAILABLE = False

# Attempt Raspberry Pi-specific imports without ever exiting the app
if is_rpi:
    try:
        import board
        import busio
        import digitalio
        from PIL import Image, ImageDraw, ImageFont
        import adafruit_ssd1306
        import RPi.GPIO as GPIO
        import adafruit_dht
        import atexit

        dht_sensor = adafruit_dht.DHT11(board.D26)
        atexit.register(dht_sensor.exit)
        OLED_AVAILABLE = True
        GPIO_AVAILABLE = True
        DHT_AVAILABLE = True
        print("Raspberry Pi OLED/DHT/GPIO dependencies loaded.")
    except Exception as e:
        # Fall back gracefully – keep the app running
        print(f"[Warning] Raspberry Pi-specific modules not fully available: {e}")
        try:
            # Try partial availability
            import RPi.GPIO as GPIO  # noqa: F401
            GPIO_AVAILABLE = True
        except Exception:
            pass
        dht_sensor = None
else:
    print("Not running on Raspberry Pi. Skipping OLED/DHT/GPIO setup.")
    dht_sensor = None


# =========================
# SMALL, FAST HELPERS
# =========================
def _safe_float(v: Any, default: float = 0.0) -> float:
    try:
        return float(v)
    except (TypeError, ValueError):
        return default

def _find_value(data_list: List[Dict[str, Any]], key: str, default: float = 0.0) -> float:
    for e in data_list:
        if e.get("key") == key:
            return _safe_float(e.get("value"), default)
    return default

def _extract_phase_powers(data: Dict[str, Any]) -> Dict[str, Any]:
    """
    Extract per-phase inverter output power. Always present in saved JSON under 'phasePowers'.
    """
    dl = data.get("dataList", []) if isinstance(data, dict) else []
    l1 = int(_find_value(dl, "INV_O_P_L1", 0.0))
    l2 = int(_find_value(dl, "INV_O_P_L2", 0.0))
    l3 = int(_find_value(dl, "INV_O_P_L3", 0.0))
    lt = int(_find_value(dl, "INV_O_P_T", 0.0))
    return {"L1": l1, "L2": l2, "L3": l3, "LT": lt, "unit": "W"}


def _parse_history_ts(value: str) -> Optional[datetime]:
    try:
        return datetime.strptime(value.strip(), "%Y/%m/%d %H:%M").replace(tzinfo=budapest_tz)
    except Exception:
        return None


def _history_float(value: Any, default: float = 0.0) -> float:
    if value in (None, ""):
        return default
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def build_historical_profile(history_dir: str = "solarman_json") -> Dict[str, Any]:
    """
    Build month-level and hour-level production profile from downloaded Solarman JSON exports.
    Robust behaviors:
    - tolerates malformed files/rows,
    - deduplicates overlaps on exact timestamp (same minute),
    - avoids overweighting duplicate download windows,
    - clamps obviously broken values.
    """
    files = sorted(glob.glob(os.path.join(history_dir, "*.json")))
    if not files:
        print(f"[History] No history files found in {history_dir}. Using static defaults.")
        return {}

    # timestamp -> list of observed values coming from possibly overlapping files
    sample_by_ts: Dict[datetime, Dict[str, List[float]]] = defaultdict(lambda: {"prod": [], "soc": []})
    invalid_rows = 0
    parsed_rows = 0

    for fp in files:
        try:
            with open(fp, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
        except Exception as err:
            print(f"[History] Failed loading {fp}: {err}")
            continue

        if not isinstance(payload, list):
            print(f"[History] Ignoring non-list JSON payload in {fp}")
            continue

        for row in payload:
            if not isinstance(row, dict):
                invalid_rows += 1
                continue

            ts = _parse_history_ts(str(row.get("Updated Time", "")).strip())
            if ts is None:
                invalid_rows += 1
                continue

            prod = max(0.0, min(_history_float(row.get("Production Power(W)"), 0.0), 25000.0))
            soc = max(0.0, min(_history_float(row.get("SoC(%)"), 0.0), 100.0))

            sample_by_ts[ts]["prod"].append(prod)
            sample_by_ts[ts]["soc"].append(soc)
            parsed_rows += 1

    if not sample_by_ts:
        print("[History] All rows were invalid or empty. Using static defaults.")
        return {}

    # Canonicalize each timestamp to a single robust sample to prevent overlap bias.
    canonical: List[Dict[str, Any]] = []
    duplicate_timestamps = 0
    for ts in sorted(sample_by_ts.keys()):
        prod_values = sample_by_ts[ts]["prod"]
        soc_values = sample_by_ts[ts]["soc"]
        if len(prod_values) > 1:
            duplicate_timestamps += 1

        # median is robust to occasional outliers in duplicate windows
        prod = statistics.median(prod_values) if prod_values else 0.0
        soc = statistics.median(soc_values) if soc_values else 0.0

        canonical.append({"ts": ts, "prod": prod, "soc": soc})

    month_hour_prod: Dict[int, Dict[int, List[float]]] = defaultdict(lambda: defaultdict(list))
    month_hour_soc: Dict[int, Dict[int, List[float]]] = defaultdict(lambda: defaultdict(list))
    month_daily_peaks: Dict[int, Dict[str, float]] = defaultdict(dict)

    for item in canonical:
        ts = item["ts"]
        month = ts.month
        hour = ts.hour
        day_key = ts.strftime("%Y-%m-%d")
        prod = item["prod"]
        soc = item["soc"]

        month_hour_prod[month][hour].append(prod)
        month_hour_soc[month][hour].append(soc)

        if day_key not in month_daily_peaks[month] or prod > month_daily_peaks[month][day_key]:
            month_daily_peaks[month][day_key] = prod

    profile: Dict[str, Any] = {
        "months": {},
        "files": len(files),
        "parsed_rows": parsed_rows,
        "invalid_rows": invalid_rows,
        "unique_timestamps": len(canonical),
        "duplicate_timestamps": duplicate_timestamps,
    }

    for month in range(1, 13):
        hourly_prod = month_hour_prod.get(month, {})
        if not hourly_prod:
            continue

        daily_peaks = list(month_daily_peaks.get(month, {}).values())
        monthly_peak_p75 = (
            statistics.quantiles(daily_peaks, n=4)[2]
            if len(daily_peaks) >= 4
            else (max(daily_peaks) if daily_peaks else 0.0)
        )

        daylight_hours = [h for h, vals in hourly_prod.items() if vals and statistics.mean(vals) >= 350]
        solar_start_hour = min(daylight_hours) if daylight_hours else 8
        solar_end_hour = max(daylight_hours) if daylight_hours else 15

        midday_hours = [h for h in range(10, 15) if h in hourly_prod and hourly_prod[h]]
        if midday_hours:
            midday_avg = statistics.mean([statistics.mean(hourly_prod[h]) for h in midday_hours])
        else:
            midday_avg = statistics.mean([statistics.mean(v) for v in hourly_prod.values() if v])

        evening_hours = [h for h in range(16, 24) if h in month_hour_soc.get(month, {})]
        evening_soc_values: List[float] = []
        for h in evening_hours:
            evening_soc_values.extend(month_hour_soc[month][h])

        evening_soc_p40 = (
            statistics.quantiles(evening_soc_values, n=5)[1]
            if len(evening_soc_values) >= 5
            else (statistics.mean(evening_soc_values) if evening_soc_values else 45.0)
        )

        profile["months"][month] = {
            "solar_start_hour": int(solar_start_hour),
            "solar_end_hour": int(solar_end_hour),
            "daylight_span": int(max(0, solar_end_hour - solar_start_hour + 1)),
            "midday_avg": float(midday_avg),
            "daily_peak_p75": float(monthly_peak_p75),
            "evening_soc_p40": float(evening_soc_p40),
        }

    print(
        f"[History] Profile ready from {profile['files']} files | parsed={profile['parsed_rows']} "
        f"invalid={profile['invalid_rows']} unique_ts={profile['unique_timestamps']} "
        f"dup_ts={profile['duplicate_timestamps']} months={sorted(profile['months'].keys())}"
    )
    return profile


def _interpolate_month_config(target_month: int, months_cfg: Dict[int, Dict[str, Any]]) -> Dict[str, Any]:
    """Interpolate missing month values from nearest available months (circular calendar distance)."""
    if target_month in months_cfg:
        return dict(months_cfg[target_month])
    if not months_cfg:
        return {}

    keys = [
        "solar_start_hour", "solar_end_hour", "daylight_span",
        "midday_avg", "daily_peak_p75", "evening_soc_p40"
    ]

    weighted: Dict[str, float] = defaultdict(float)
    weights: Dict[str, float] = defaultdict(float)

    for m, cfg in months_cfg.items():
        dist = min((target_month - m) % 12, (m - target_month) % 12)
        if dist == 0:
            dist = 0.5
        w = 1.0 / dist
        for k in keys:
            if k in cfg:
                weighted[k] += w * float(cfg[k])
                weights[k] += w

    out: Dict[str, Any] = {}
    for k in keys:
        if weights[k] > 0:
            out[k] = weighted[k] / weights[k]
    return out


def _history_recommendation(now: datetime, battery_charge: float, current_power: float,
                            sunrise_dt: datetime, sunset_dt: datetime) -> Dict[str, Any]:
    """
    Creates dynamic decision hints from historical production behavior for current month.
    """
    global historical_profile
    months = (historical_profile or {}).get("months", {})
    month_cfg = _interpolate_month_config(now.month, months)

    if not month_cfg:
        return {
            "month_quality": "neutral",
            "early_start_soc": 55,
            "min_stop_soc": 20,
            "late_day_reserve_soc": 80,
            "should_preserve_battery": now.hour >= 15 and battery_charge < 80,
            "headroom_good": current_power >= 2500,
        }

    daylight_span = int(month_cfg.get("daylight_span", 8))
    midday_avg = float(month_cfg.get("midday_avg", 2000))
    daily_peak_p75 = float(month_cfg.get("daily_peak_p75", 3500))
    solar_start_hour = int(month_cfg.get("solar_start_hour", sunrise_dt.hour))
    evening_soc_p40 = float(month_cfg.get("evening_soc_p40", 45.0))

    strong_month = daylight_span >= 9 and midday_avg >= 2400
    weak_month = daylight_span <= 7 or midday_avg <= 1700

    early_start_soc = 32 if strong_month else (58 if weak_month else 45)
    min_stop_soc = 26 if weak_month else 20
    late_day_reserve_soc = max(72, int(evening_soc_p40 + (8 if weak_month else 4)))

    headroom_good = (
        current_power >= max(1800.0, 0.55 * daily_peak_p75)
        and now.hour <= max(solar_start_hour + 5, sunrise_dt.hour + 4)
    )

    # Preserve battery in weaker months or later afternoon.
    should_preserve_battery = (
        now.hour >= (14 if weak_month else 16)
        and battery_charge < late_day_reserve_soc
        and current_power < max(1400.0, 0.4 * daily_peak_p75)
    )

    return {
        "month_quality": "strong" if strong_month else ("weak" if weak_month else "neutral"),
        "early_start_soc": early_start_soc,
        "min_stop_soc": min_stop_soc,
        "late_day_reserve_soc": late_day_reserve_soc,
        "should_preserve_battery": should_preserve_battery,
        "headroom_good": headroom_good,
    }

def _runtime_info() -> str:
    try:
        ip = get_ip_address()
    except Exception:
        ip = "N/A"
    return (
        f"Host: {platform.node()} \nOS: {platform.system()} {platform.release()} ({platform.machine()})\n"
        f"Python: {platform.python_version()} | PID: {os.getpid()}\n"
        f"IP: {ip}"
    )

def _extract_error_fields(err: Exception) -> Tuple[str, Optional[int], Optional[str]]:
    """
    Returns (error_type, http_status, http_reason) if available.
    For requests exceptions, try to surface status code & reason.
    """
    etype = type(err).__name__
    status = None
    reason = None
    try:
        # requests HTTPError may carry response
        resp = getattr(err, "response", None)
        if resp is not None:
            status = getattr(resp, "status_code", None)
            reason = getattr(resp, "reason", None)
    except Exception:
        pass
    return etype, status, reason

def _format_exception_for_tg(err: Exception, max_lines: int = 6) -> str:
    etype, status, reason = _extract_error_fields(err)
    lines = [f"Type: {etype}"]
    if status is not None:
        lines.append(f"HTTP status: {status}{' ' + str(reason) if reason else ''}")
    try:
        tb_iter = traceback.TracebackException.from_exception(err).format()
        head = "".join(tb_iter).strip().splitlines()[:max_lines]
        if head:
            lines.append("Traceback:")
            lines.extend(head)
    except Exception:
        lines.append("Traceback: <unavailable>")
    return "\n".join(lines)


def notify_startup():
    ts = datetime.now(tz=budapest_tz).strftime("%Y-%m-%d %H:%M:%S")
    msg = (
        f"🚀 Program started\n"
        f"Time (Europe/Budapest): {ts}\n"
        f"{_runtime_info()}"
    )
    send_telegram_message(msg, keyboard=True)

def notify_shutdown(reason: str = "normal", err: Exception = None):
    ts = datetime.now(tz=budapest_tz).strftime("%Y-%m-%d %H:%M:%S")
    header = f"🛑 Program stopped"
    body = [f"Reason: {reason}", f"\nTime (Europe/Budapest): {ts}\n", _runtime_info()]
    if err is not None:
        body.append("\nError details:\n" + _format_exception_for_tg(err))
    send_telegram_message(f"{header}\n" + "\n".join(body), keyboard=True)

# graceful signal handlers
def _signal_handler(sig, frame):
    name = signal.Signals(sig).name if isinstance(sig, int) else str(sig)
    try:
        notify_shutdown(reason=f"signal {name}", err=None)
    finally:
        # Immediate exit after notifying
        os._exit(0)

# =========================
# ORIGINAL FUNCTION NAMES
# =========================
def init_display():
    """Initialize OLED on Raspberry Pi."""
    if not (is_rpi and OLED_AVAILABLE):
        return
    global oled, image, draw, font
    try:
        i2c = busio.I2C(board.SCL, board.SDA)
        oled = adafruit_ssd1306.SSD1306_I2C(128, 32, i2c)
        image = Image.new("1", (oled.width, oled.height))
        draw = ImageDraw.Draw(image)
        font = ImageFont.load_default()
        oled.fill(0)
        oled.show()
        print("OLED initialized")
    except Exception as e:
        print(f"[Warning] OLED init failed: {e}")


def flush_display():
    if oled:
        oled.fill(0)
        oled.show()

def get_ip_address():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
    except Exception:
        ip = "No IP"
    return ip

def get_ram_usage():
    return f"{psutil.virtual_memory().percent}%"

def get_cpu_usage():
    return f"{psutil.cpu_percent(interval=1)}%"

import shutil
import subprocess

def get_temperatures():
    """
    Returns a dict of temperatures from available sensors.
    Prefer 'vcgencmd' when available (RPi), otherwise thermal zones.
    Never let missing tools print shell errors or raise.
    """
    temps = {}

    try:
        if shutil.which("vcgencmd"):
            res = subprocess.run(
                ["vcgencmd", "measure_temp"],
                capture_output=True, text=True, timeout=2
            )
            line = (res.stdout or "").strip()
            if line.startswith("temp="):
                temps["CPU"] = line.replace("temp=", "")
                return temps
        # If vcgencmd missing or not usable, fall through to thermal zones
    except Exception:
        pass

    try:
        for path in glob.glob('/sys/class/thermal/thermal_zone*/temp'):
            try:
                with open(path, 'r') as f:
                    milli = int(f.read().strip())
                c = milli / 1000
                type_path = path.replace('temp', 'type')
                try:
                    with open(type_path, 'r') as tf:
                        name = tf.read().strip()
                except Exception:
                    name = f"zone_{Path(path).parent.name}"
                temps[name] = f"{c:.1f}C"
            except Exception:
                continue
    except Exception:
        pass

    return temps


def read_dht11(prev_temperature, prev_humidity):
    # If not Pi or DHT not available, keep previous values (no-op)
    if not (is_rpi and DHT_AVAILABLE and dht_sensor):
        return {'temperature': prev_temperature, 'humidity': prev_humidity}
    try:
        temperature = dht_sensor.temperature
        humidity = dht_sensor.humidity
        if humidity is not None and temperature is not None:
            return {'temperature': temperature, 'humidity': humidity}
        return {'temperature': prev_temperature, 'humidity': prev_humidity}
    except Exception:
        return {'temperature': prev_temperature, 'humidity': prev_humidity}


def clean_value(value):
    return int(float(re.sub(r'[^\d.]+', '', str(value))))

def write_to_display(state_text, soc, solar_power, temperature, humidity):
    if not oled:
        return
    flush_display()
    draw.rectangle((0, 0, oled.width, oled.height), outline=0, fill=0)

    temperature = clean_value(temperature)
    humidity = clean_value(humidity)
    soc = clean_value(soc)
    solar_power = clean_value(solar_power)

    line1 = f"SOC: {soc}% PWR: {solar_power}W"
    line2 = f"{state_text}"
    line3 = f"{temperature}C {humidity}%"

    draw.text((0, 0), line1, font=font, fill=25)
    draw.text((0, 8), line2, font=font, fill=25)
    draw.text((0, 16), line3, font=font, fill=25)

    oled.image(image)
    oled.show()

def sleep_until_next_5min(offset_seconds=60):
    now = datetime.now(tz=budapest_tz)
    seconds_since_hour = now.minute * 60 + now.second
    next_5_min = ((seconds_since_hour // 300) + 1) * 300
    target_seconds = next_5_min + offset_seconds
    sleep_seconds = target_seconds - seconds_since_hour
    if sleep_seconds < 0:
        sleep_seconds += 3600
    print(f"Sleeping for {sleep_seconds} seconds...")
    time.sleep(sleep_seconds)

def send_telegram_message(message, max_retries=15, keyboard=True):
    url = f'{TELEGRAM_BASE}/sendMessage'
    payload = {'chat_id': CHAT_ID, 'text': message}
    if keyboard:
        payload['reply_markup'] = json.dumps({
            "keyboard": [
                ["/now", "/phase"],
                ["/start", "/stop"],
                ["/force_stop"]
            ],
            "resize_keyboard": True,
            "one_time_keyboard": False
        }, ensure_ascii=False)
    backoff = 2
    for attempt in range(1, max_retries + 1):
        try:
            with session_lock:
                r = session.post(url, data=payload, timeout=12)
            r.raise_for_status()
            print("Telegram message sent successfully.")
            return
        except requests.exceptions.RequestException as e:
            print(f"[Attempt {attempt}] Telegram send failed: {e}")
            if attempt < max_retries:
                time.sleep(backoff)
                backoff = min(backoff * 2, 60)
            else:
                print("All retry attempts failed.")

def handle_telegram_messages(battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum, historical_hints=None):
    """
    Poll Telegram updates and process commands.
    Long polling reduces request count and improves responsiveness.
    Thread-safe: uses session_lock for HTTP.
    """
    global last_update_id
    try:
        params = {}
        if last_update_id:
            params['offset'] = last_update_id + 1
        params['timeout'] = 25  # long poll
        with session_lock:
            r = session.get(f'{TELEGRAM_BASE}/getUpdates', params=params, timeout=35)
        r.raise_for_status()
        data = r.json()
        for update in data.get('result', []):
            last_update_id = update['update_id']
            msg = update.get('message', {})
            text = msg.get('text')
            if text:
                process_message(text, battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum, historical_hints)
    except requests.exceptions.RequestException as e:
        print(f"Error while handling Telegram messages: {e}")

def process_message(message_text, battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum, historical_hints=None):
    global used_quote
    if message_text == "/now":
        ip = get_ip_address()
        ram = get_ram_usage()
        cpu = get_cpu_usage()
        temps = get_temperatures()
        percentage = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0

        # read last saved phase powers
        l1 = l2 = l3 = lt = None
        unit = "W"
        try:
            if os.path.exists(SOLARMAN_FILE):
                with open(SOLARMAN_FILE, 'r', encoding='utf-8') as f:
                    saved = json.load(f)
                phase = saved.get("phasePowers", {})
                l1 = phase.get("L1")
                l2 = phase.get("L2")
                l3 = phase.get("L3")
                lt = phase.get("LT")
                unit = phase.get("unit", "W")
        except Exception as e:
            print(f"/now phase read error: {e}")

        l1_str = f"{l1} {unit}" if isinstance(l1, (int, float)) else "N/A"
        l2_str = f"{l2} {unit}" if isinstance(l2, (int, float)) else "N/A"
        l3_str = f"{l3} {unit}" if isinstance(l3, (int, float)) else "N/A"
        lt_str = f"{lt} {unit}" if isinstance(lt, (int, float)) else "N/A"

        now_dt = datetime.now(tz=budapest_tz)
        hints = historical_hints if isinstance(historical_hints, dict) and historical_hints else _history_recommendation(
            now_dt,
            _safe_float(battery, 0.0),
            _safe_float(power, 0.0),
            sunrise if isinstance(sunrise, datetime) else now_dt,
            sunset if isinstance(sunset, datetime) else now_dt,
        )

        month_quality = str(hints.get("month_quality", "neutral"))
        month_quality_label = {"strong": "Strong", "weak": "Weak", "neutral": "Neutral"}.get(month_quality, month_quality)
        preserve_battery_label = "Yes" if hints.get("should_preserve_battery", False) else "No"
        headroom_good_label = "Yes" if hints.get("headroom_good", False) else "No"

        message = (
            f"⚡️ Solar Mining — NOW\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"🔋 Energy\n"
            f"• Battery: {battery}%\n"
            f"• Power: {power}W\n"
            f"• State: {state}\n"
            f"• Weather: {current_condition}\n"
            f"• Clouds: {clouds}%\n"
            f"• Sunrise: {sunrise.strftime('%H:%M')}\n"
            f"• Sunset: {sunset.strftime('%H:%M')}\n\n"
            f"🏠 Environment\n"
            f"• Garage temperature: {garage_temp}C\n"
            f"• Garage humidity: {garage_hum}%\n\n"
            f"⚡ Inverter phases\n"
            f"• L1: {l1_str}\n"
            f"• L2: {l2_str}\n"
            f"• L3: {l3_str}\n"
            f"• Total: {lt_str}\n\n"
            f"🧠 Historical decision hints\n"
            f"• Month quality: {month_quality_label}\n"
            f"• Early start SOC: {hints.get('early_start_soc', 'N/A')}%\n"
            f"• Minimum stop SOC: {hints.get('min_stop_soc', 'N/A')}%\n"
            f"• Late-day reserve SOC: {hints.get('late_day_reserve_soc', 'N/A')}%\n"
            f"• Preserve battery: {preserve_battery_label}\n"
            f"• Headroom good: {headroom_good_label}\n\n"
            f"🖥️ System\n"
            f"• IP: {ip}\n"
            f"• RAM usage: {ram}\n"
            f"• CPU usage: {cpu}\n"
            f"• CPU temp: {temps.get('cpu-thermal') or temps.get('CPU') or 'N/A'}\n"
            f"• Quote usage: {used_quote} / {QUOTE_LIMIT} ({percentage:.2f}%)"
        )
        send_telegram_message(message)

    if message_text == "/phase":
        try:
            if os.path.exists(SOLARMAN_FILE):
                with open(SOLARMAN_FILE, 'r', encoding='utf-8') as f:
                    saved = json.load(f)
                phase = saved.get("phasePowers")
                ts = None
                try:
                    for e in saved.get("dataList", []):
                        if e.get("key") == "SYSTIM1":
                            ts = e.get("value")
                            break
                except Exception:
                    pass
                if phase:
                    msg = (
                        f"Per-phase inverter output power\n"
                        f"L1: {phase.get('L1', 0)} {phase.get('unit', 'W')}\n"
                        f"L2: {phase.get('L2', 0)} {phase.get('unit', 'W')}\n"
                        f"L3: {phase.get('L3', 0)} {phase.get('unit', 'W')}\n"
                        f"Total: {phase.get('LT', 0)} {phase.get('unit', 'W')}"
                    )
                    send_telegram_message(msg)
                else:
                    send_telegram_message("No phase data available yet.")
            else:
                send_telegram_message("No saved device data found.")
        except Exception as e:
            print(f"/phase handling error: {e}")
            send_telegram_message("Failed to read phase data.")

    if message_text == "/start":
        if is_rpi and GPIO_AVAILABLE:
            press_power_button(16, 0.55)
            send_telegram_message("Crypto production started! Pressed power button.")
        else:
            send_telegram_message("Crypto production start requested, but GPIO is not available on this host.")
    if message_text == "/stop":
        if is_rpi and GPIO_AVAILABLE:
            press_power_button(16, 0.55)
            send_telegram_message("Crypto production stopped! Pressed power button.")
        else:
            send_telegram_message("Crypto production stop requested, but GPIO is not available on this host.")
    if message_text == "/force_stop":
        if is_rpi and GPIO_AVAILABLE:
            press_power_button(16, 10)
            send_telegram_message("Crypto production force stopped! Pressed power button for 10 seconds.")
        else:
            send_telegram_message("Force stop requested, but GPIO is not available on this host.")


def load_quote_usage():
    if os.path.exists(QUOTE_FILE):
        try:
            with open(QUOTE_FILE, 'r') as f:
                return json.load(f).get('used_quote', 0)
        except Exception:
            return 0
    return 0

def save_quote_usage(used_quote_val: int):
    try:
        with open(QUOTE_FILE, 'w') as f:
            json.dump({'used_quote': used_quote_val}, f, indent=4)
    except Exception as e:
        print(f"Failed to persist quote usage: {e}")

def sha256_hash(password):
    hashed = hashlib.sha256(password.encode('utf-8')).hexdigest()
    print(f"Hashed password: {hashed}")
    return hashed

def get_access_token():
    print("Getting access token...")
    url = f'https://globalapi.solarmanpv.com/account/v1.0/token?appId={APP_ID}&language=en'
    headers = {'Content-Type': 'application/json'}
    payload = {
        'appSecret': APP_SECRET,
        'email': EMAIL,
        'password': sha256_hash(PASSWORD)
    }
    try:
        r = requests.post(url, headers=headers, json=payload, timeout=12)
        r.raise_for_status()
        data = r.json()
        token = data.get('access_token')
        if not token:
            print("[Warning] Access token missing in response.")
            return None
        print("Access token received!")
        return token
    except (requests.RequestException, ValueError) as e:
        print(f"[Warning] Failed to get access token: {e}")
        return None

def fetch_current_data(access_token):
    print("Fetching current device data...")
    url = f'https://globalapi.solarmanpv.com/device/v1.0/currentData?appId={APP_ID}&language=en'
    headers = {
        'Authorization': f'Bearer {access_token}',
        'Content-Type': 'application/json'
    }
    payload = {'deviceSn': DEVICE_SN}
    try:
        r = requests.post(url, headers=headers, json=payload, timeout=12)
        r.raise_for_status()
        print("Current data fetched successfully.")
        return r.json()
    except (requests.RequestException, ValueError) as e:
        et, sc, rsn = _extract_error_fields(e)
        print(f"[Warning] Failed to fetch current device data: {et}"
            f"{f' | HTTP {sc} {rsn}' if sc else ''} | {e}")
        return {}

def store_data(data, filename=SOLARMAN_FILE):
    """
    Save raw JSON and attach per-phase inverter powers into 'phasePowers'.
    No CSV logging (as requested).
    """
    try:
        out = dict(data) if isinstance(data, dict) else {"raw": data}
        out["phasePowers"] = _extract_phase_powers(out)
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(out, f, indent=4, ensure_ascii=False)
        print(f"Data stored to {filename}")
    except Exception as e:
        print(f"[Warning] Failed to store data: {e}")

def load_data(filename=SOLARMAN_FILE):
    if os.path.exists(filename):
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            print(f"[Warning] Failed to load {filename}: {e}")
            return {}
    print(f"File {filename} not found. Returning empty data.")
    return {}

def load_prev_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, 'r') as f:
                d = json.load(f)
        except Exception:
            return None, None
        prev_state_val = d.get('prev_state', None)
        uptime_str = d.get('uptime', None)
        if uptime_str:
            try:
                up = datetime.fromisoformat(uptime_str)
                if up.tzinfo is None:
                    up = up.replace(tzinfo=budapest_tz)
            except Exception:
                up = None
        else:
            up = None
        return prev_state_val, up
    return None, None

def save_prev_state(state_val, uptime_val):
    try:
        uptime_str = uptime_val.isoformat() if isinstance(uptime_val, datetime) else uptime_val
        with open(STATE_FILE, 'w') as f:
            json.dump({'prev_state': state_val, 'uptime': uptime_str}, f, indent=4)
    except Exception as e:
        print(f"[Warning] Failed to save prev state: {e}")

def get_current_weather(api_key, location_lat, location_lon):
    try:
        # Current
        url = "https://api.openweathermap.org/data/2.5/weather"
        params = {"lat": location_lat, "lon": location_lon, "appid": api_key, "units": "metric"}
        r = requests.get(url, params=params, timeout=12)
        r.raise_for_status()
        d = r.json()

        current_condition = d['weather'][0]['description'].lower()
        clouds = d['clouds']['all']
        sunrise_ts = d['sys']['sunrise']
        sunset_ts = d['sys']['sunset']

        sunrise_dt = datetime.fromtimestamp(sunrise_ts, tz=budapest_tz) - timedelta(minutes=10)
        sunset_dt = datetime.fromtimestamp(sunset_ts, tz=budapest_tz) - timedelta(minutes=90)

        # Forecast
        url = "https://api.openweathermap.org/data/2.5/forecast"
        params = {"lat": location_lat, "lon": location_lon, "appid": api_key, "units": "metric"}
        r = requests.get(url, params=params, timeout=12)
        r.raise_for_status()
        fd = r.json()

        def _pick(i: int):
            ent = fd['list'][i]
            return ent['clouds']['all'], ent['weather'][0]['description'].lower(), ent['dt_txt']

        f1_clouds, f1_cond, f1_ts = _pick(0)
        f3_clouds, f3_cond, f3_ts = _pick(1)

    except (requests.RequestException, KeyError, IndexError, ValueError) as e:
        print(f"[Warning] Weather request failed: {e}")
        current_condition = "unknown"
        clouds = 0
        now = datetime.now(tz=budapest_tz)
        sunrise_dt = now.replace(hour=6, minute=0, second=0)
        sunset_dt = now.replace(hour=18, minute=0, second=0)
        f1_cond = "unknown"; f1_clouds = 0; f1_ts = now.strftime("%Y-%m-%d %H:%M:%S")
        f3_cond = "unknown"; f3_clouds = 0; f3_ts = (now + timedelta(hours=3)).strftime("%Y-%m-%d %H:%M:%S")

    return (
        current_condition, sunrise_dt, sunset_dt, clouds,
        f1_cond, f1_clouds, f1_ts,
        f3_cond, f3_clouds, f3_ts
    )

def press_power_button(gpio_pin, press_time):
    if not (is_rpi and GPIO_AVAILABLE):
        print(f"[Info] GPIO not available. Skipping power button press ({gpio_pin}, {press_time}s).")
        return
    print(f"Pressing power button on GPIO pin {gpio_pin} for {press_time} seconds...")
    try:
        with gpio_lock:
            GPIO.setmode(GPIO.BCM)
            GPIO.setup(gpio_pin, GPIO.OUT, initial=GPIO.LOW)
            GPIO.output(gpio_pin, GPIO.HIGH)
            time.sleep(press_time)
            GPIO.output(gpio_pin, GPIO.LOW)
            GPIO.cleanup()
        print("Power button press completed.")
    except Exception as e:
        print(f"[Warning] GPIO press failed: {e}")


def check_uptime(now, prev_state_val):
    global uptime
    miner_ip = "192.168.0.200"
    if uptime is None:
        uptime = now
    difference = now - uptime
    hours, remainder = divmod(difference.seconds, 3600)
    minutes, _ = divmod(remainder, 60)

    print(f"Pinging {miner_ip} to check uptime...")
    try:
        result = subprocess.run(["ping", "-c", "1", "-W", "2", miner_ip], stdout=subprocess.DEVNULL)
        if result.returncode != 0:
            print("No reply!")
            if prev_state_val == "production":
                print(f"No reply from {miner_ip}. Attempting restart sequence...")
                press_power_button(16, 10)
                time.sleep(15)
                press_power_button(16, 0.55)
                print("Restart sequence completed.")
                uptime = now
                save_prev_state(prev_state_val, uptime)
        else:
            print("Reply!")
            if prev_state_val == "stop":
                print(f"Reply from {miner_ip}. Attempting force shutdown sequence...")
                press_power_button(16, 10)
                time.sleep(5)
                print("Force shutdown completed.")
                uptime = now
                save_prev_state(prev_state_val, uptime)

        total_hours = difference.days * 24 + hours
        if prev_state_val == "production":
            print(f"{miner_ip} is online for {total_hours} hours and {minutes} minutes")
        elif prev_state_val == "stop":
            print(f"{miner_ip} is offline for {total_hours} hours and {minutes} minutes")
    except Exception as e:
        print(f"Error during uptime check: {e}")

def check_crypto_production_conditions(data, weather_api_key, location_lat, location_lon):
    global prev_state, state, used_quote, sunrise, sunset, uptime
    prev_state, uptime = load_prev_state()

    try:
        (current_condition, sunrise, sunset, clouds,
         f1_cond, f1_clouds, f1_ts,
         f3_cond, f3_clouds, f3_ts) = get_current_weather(weather_api_key, location_lat, location_lon)

        print(f"\nCurrent weather: {current_condition}, | Clouds: {clouds}%")
        print(f"1H forecast: {f1_cond}, | Clouds: {f1_clouds}% | Time:{f1_ts}")
        print(f"3H forecast: {f3_cond}, | Clouds: {f3_clouds}% | Time:{f3_ts}")

        garage_data = read_dht11(0, 0)
        temperature = garage_data['temperature']
        humidity = garage_data['humidity']

        dl = data.get("dataList", [])

        # core values
        battery_charge = _find_value(dl, "BMS_SOC", 0)
        current_power = _find_value(dl, "S_P_T", 0)
        internal_power = _find_value(dl, "GS_T", 0)

        # per-phase inverter outputs (W)
        inv_l1 = _find_value(dl, "INV_O_P_L1", 0.0)
        inv_l2 = _find_value(dl, "INV_O_P_L2", 0.0)
        inv_l3 = _find_value(dl, "INV_O_P_L3", 0.0)
        inv_lt = _find_value(dl, "INV_O_P_T", 0.0)

        print(f"Battery charge: {battery_charge}%")
        print(f"Current production (PV total): {current_power}W")
        print(f"Inverter output per phase: L1={int(inv_l1)}W, L2={int(inv_l2)}W, L3={int(inv_l3)}W, Total={int(inv_lt)}W")
        print(f"Internal Power: {internal_power}W")

        now = datetime.now(tz=budapest_tz)
        hist = _history_recommendation(now, battery_charge, current_power, sunrise, sunset)
        print(
            "[History tuning] "
            f"month={hist['month_quality']} early_start_soc={hist['early_start_soc']}% "
            f"min_stop_soc={hist['min_stop_soc']}% late_reserve={hist['late_day_reserve_soc']}% "
            f"headroom_good={hist['headroom_good']} preserve={hist['should_preserve_battery']}"
        )

        solar_keywords = [
            'sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds',
            'partly cloudy', 'mostly sunny', 'sunshine', 'sunrise', 'sunset'
        ]
        non_solar_keywords = [
            'rain', 'storm', 'thunder', 'snow', 'fog', 'haze',
            'sleet', 'blizzard', 'dust', 'sand', 'ash', 'drizzle', 'shower', 'mist', 'smoke',
            'tornado', 'hurricane', 'squall', 'lightning', 'moderate rain', 'heavy intensity rain', 'overcast'
        ]

        # Optional ping supervision
        if is_rpi and uptime and (now - uptime) > timedelta(minutes=3):
            check_uptime(now, prev_state)

        # IMMEDIATE POWER-BASED STOP RULE MINER IS ON L2 and L3
        if (inv_l2 > 2000) or (inv_l3 > 2000) or (inv_lt > 5000):
            print("Power safety threshold exceeded → Crypto production over (STOP).")
            state = "stop"
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
            if state != prev_state:
                prev_state = state
                save_prev_state(prev_state, now)
                send_telegram_message(
                    f""" Production stopped (power threshold).
________________________________
________________________________
 Battery: {battery_charge}%
 Current power: {current_power}W
 L1: {int(inv_l1)}W | L2: {int(inv_l2)}W | L3: {int(inv_l3)}W | Total: {int(inv_lt)}W
________________________________
 Weather: {current_condition}
 Temperature: {temperature}
 Humidity: {humidity}%
"""
                )
            return (battery_charge, current_power, state, current_condition, sunrise, sunset, clouds,
                    f1_cond, f1_clouds, f1_ts,
                    f3_cond, f3_clouds, f3_ts, hist)

        # ===== existing logic continues below =====
        if ((prev_state == "production" and battery_charge < hist["min_stop_soc"]) or
            (prev_state == "production" and now.hour > 14 and battery_charge < hist["late_day_reserve_soc"]) or
            (prev_state == "production" and hist["should_preserve_battery"])):
            print("Battery emergency shutdown.")
            state = "stop"
            if prev_state == "production":
                print("Trying to press power button.")
                if state != prev_state:
                    prev_state = state
                    uptime = now
                    save_prev_state(prev_state, uptime)
                if is_rpi:
                    press_power_button(16, 0.55)
        elif (
            (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and current_power > 0 and battery_charge >= hist["early_start_soc"] and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 65 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 55 and now.hour < 12)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 45 and now.hour < 11)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and current_power > 0 and battery_charge >= hist["early_start_soc"] and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 65 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 55 and now.hour < 12)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 45 and now.hour < 11)
            or (hist["headroom_good"] and battery_charge >= hist["early_start_soc"] and now.hour < 14)
            or (battery_charge >= 60 and current_power >= 2500 and now.hour < 11)
            or (battery_charge >= 70 and current_power >= 2250 and now.hour < 12)
            or (battery_charge >= 80 and current_power >= 2000 and now.hour < 13)
            or (battery_charge >= 50 and current_power >= 3000 and now.hour < 14)
            or (battery_charge > 90 and current_power > 50)
        ):
            print("Crypto production ready!")
            state = "production"
            if prev_state == "stop":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
        elif (
            (battery_charge <= max(90, hist["late_day_reserve_soc"]))
            or (current_power <= 150)
            or (any(k in current_condition for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
            or (any(k in f1_cond for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
            or (any(k in f3_cond for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
            or (hist["should_preserve_battery"] and now.hour >= 14)
        ):
            print("Crypto production over.")
            state = "stop"
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
        else:
            print("No change!")

        if state == "production" and prev_state != "production":
            send_telegram_message(
                f""" Production started!
________________________________
 Battery: {battery_charge}%
 Current power: {current_power}W
 L1: {int(inv_l1)}W | L2: {int(inv_l2)}W | L3: {int(inv_l3)}W | Total: {int(inv_lt)}W
________________________________
 Weather: {current_condition}
 Temperature: {temperature}
 Humidity: {humidity}%"""
            )
        elif state == "stop" and prev_state != "stop":
            send_telegram_message(
                f""" Production stopped.
________________________________
 Battery: {battery_charge}%
 Current power: {current_power}W
 L1: {int(inv_l1)}W | L2: {int(inv_l2)}W | L3: {int(inv_l3)}W | Total: {int(inv_lt)}W
________________________________
 Weather: {current_condition}
 Temperature: {temperature}
 Humidity: {humidity}%"""
            )

        if state != prev_state:
            prev_state = state
            save_prev_state(prev_state, now)

        return (battery_charge, current_power, state, current_condition, sunrise, sunset, clouds,
                f1_cond, f1_clouds, f1_ts,
                f3_cond, f3_clouds, f3_ts, hist)

    except Exception as e:
        print(f"Error while checking production conditions: {e}")
        return None, None, state, sunrise, sunset


def _load_telemetry_from_file() -> int:
    """Load persisted telemetry points into in-memory deque at startup."""
    candidates = [TELEMETRY_FILE]

    # Backward compatibility: previous versions may have written to cwd/telemetry_history.json
    legacy_cwd_file = (Path.cwd() / "telemetry_history.json").resolve()
    if legacy_cwd_file not in candidates:
        candidates.append(legacy_cwd_file)

    loaded_total = 0
    seen_ts = set()

    try:
        telemetry_history.clear()

        for fp in candidates:
            if not fp.exists():
                continue
            try:
                with fp.open("r", encoding="utf-8") as fh:
                    payload = json.load(fh)
            except Exception as err:
                print(f"[Telemetry] Failed reading {fp}: {err}")
                continue

            if not isinstance(payload, list):
                print(f"[Telemetry] Ignoring non-list telemetry payload in {fp}.")
                continue

            for item in payload[-MAX_HISTORY_POINTS:]:
                if not isinstance(item, dict):
                    continue
                ts = str(item.get("ts", "")).strip()
                if not ts or ts in seen_ts:
                    continue
                telemetry_history.append(item)
                seen_ts.add(ts)
                loaded_total += 1

        sorted_hist = sorted(list(telemetry_history), key=lambda x: str(x.get("ts", "")))
        telemetry_history.clear()
        telemetry_history.extend(sorted_hist[-MAX_HISTORY_POINTS:])

        print(f"[Telemetry] Loaded {len(telemetry_history)} points (raw read: {loaded_total}) from: {', '.join(str(x) for x in candidates)}")
        return len(telemetry_history)
    except Exception as err:
        print(f"[Telemetry] Failed loading telemetry history: {err}")
        return 0


def _record_telemetry(now: datetime, data: Dict[str, Any], battery: float, power: float,
                      state_val: str, current_condition: str, clouds: float,
                      garage_temp: Optional[float], garage_hum: Optional[float],
                      historical_hints: Optional[Dict[str, Any]] = None,
                      sunrise_dt: Optional[datetime] = None, sunset_dt: Optional[datetime] = None):
    if not _is_active_window(now, sunrise_dt, sunset_dt):
        print("[Telemetry] Skipping idle-period telemetry persist (outside active sunrise/sunset window).")
        return

    dl = data.get("dataList", []) if isinstance(data, dict) else []
    record = {
        "ts": now.isoformat(),
        "battery": float(battery or 0),
        "power": float(power or 0),
        "state": state_val or "unknown",
        "condition": current_condition or "unknown",
        "clouds": float(clouds or 0),
        "garage_temp": float(garage_temp or 0),
        "garage_hum": float(garage_hum or 0),
        "inv_l1": float(_find_value(dl, "INV_O_P_L1", 0.0)),
        "inv_l2": float(_find_value(dl, "INV_O_P_L2", 0.0)),
        "inv_l3": float(_find_value(dl, "INV_O_P_L3", 0.0)),
        "inv_lt": float(_find_value(dl, "INV_O_P_T", 0.0)),
        "internal_power": float(_find_value(dl, "GS_T", 0.0)),
        "month_quality": str((historical_hints or {}).get("month_quality", "neutral")),
        "early_start_soc": float((historical_hints or {}).get("early_start_soc", 55)),
        "min_stop_soc": float((historical_hints or {}).get("min_stop_soc", 20)),
        "late_day_reserve_soc": float((historical_hints or {}).get("late_day_reserve_soc", 80)),
        "should_preserve_battery": bool((historical_hints or {}).get("should_preserve_battery", False)),
        "headroom_good": bool((historical_hints or {}).get("headroom_good", False)),
    }
    telemetry_history.append(record)
    _append_telemetry_to_file(record)


def _is_active_window(now: datetime, sunrise_dt: Optional[datetime], sunset_dt: Optional[datetime]) -> bool:
    """Return True when current time is within the sunrise/sunset window."""
    if not isinstance(now, datetime):
        return False
    if not isinstance(sunrise_dt, datetime) or not isinstance(sunset_dt, datetime):
        return False

    if now.tzinfo is None:
        now = now.replace(tzinfo=budapest_tz)
    if sunrise_dt.tzinfo is None:
        sunrise_dt = sunrise_dt.replace(tzinfo=budapest_tz)
    if sunset_dt.tzinfo is None:
        sunset_dt = sunset_dt.replace(tzinfo=budapest_tz)

    return (sunrise_dt.hour, sunrise_dt.minute) <= (now.hour, now.minute) <= (sunset_dt.hour, sunset_dt.minute)


def _append_telemetry_to_file(record: Dict[str, Any]) -> None:
    try:
        TELEMETRY_FILE.parent.mkdir(parents=True, exist_ok=True)

        existing: List[Dict[str, Any]] = []
        if TELEMETRY_FILE.exists():
            try:
                with TELEMETRY_FILE.open("r", encoding="utf-8") as fh:
                    payload = json.load(fh)
                if isinstance(payload, list):
                    existing = payload
            except Exception as err:
                print(f"[Telemetry] Could not read telemetry file, recreating: {err}")

        existing.append(record)
        if len(existing) > MAX_HISTORY_POINTS:
            existing = existing[-MAX_HISTORY_POINTS:]

        tmp_file = TELEMETRY_FILE.with_suffix(TELEMETRY_FILE.suffix + ".tmp")
        with tmp_file.open("w", encoding="utf-8") as fh:
            json.dump(existing, fh, ensure_ascii=False)
        tmp_file.replace(TELEMETRY_FILE)
    except Exception as err:
        print(f"[Telemetry] Failed to persist record: {err}")


def _miner_action(action: str) -> Dict[str, Any]:
    now = datetime.now(tz=budapest_tz).isoformat()
    duration = 0.55
    if action == "force_stop":
        duration = 10
    if action not in {"start", "stop", "force_stop"}:
        return {"ok": False, "message": "invalid action", "ts": now}

    if not is_rpi:
        return {"ok": False, "message": "GPIO unavailable (not Raspberry Pi runtime)", "ts": now}

    try:
        with gpio_lock:
            press_power_button(16, duration)
        return {"ok": True, "message": f"{action} signal sent ({duration}s)", "ts": now}
    except Exception as err:
        return {"ok": False, "message": str(err), "ts": now}


def _weather_icon(condition: str) -> str:
    c = (condition or "").lower()
    if any(k in c for k in ["rain", "drizzle", "storm", "thunder"]):
        return "fa-cloud-rain"
    if any(k in c for k in ["snow", "sleet", "blizzard"]):
        return "fa-snowflake"
    if any(k in c for k in ["fog", "mist", "haze", "smoke"]):
        return "fa-smog"
    if any(k in c for k in ["cloud", "overcast"]):
        return "fa-cloud"
    return "fa-sun"


DASHBOARD_HTML = """
<!doctype html>
<html lang="en"><head>
<meta charset="utf-8" /><meta name="viewport" content="width=device-width,initial-scale=1" />
<title>Solar Mining Control</title>
<link rel="icon" type="image/png" href="/solarmining_logo.png" />
<link rel="apple-touch-icon" href="/solarmining_logo.png" />
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.5.2/css/all.min.css" />
<script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
<style>
:root{--bg:#0b1220;--bg2:#182845;--card:rgba(20,31,56,.72);--txt:#e9eefc;--muted:#9fb0d0;--ok:#47d16c;--warn:#f2b84b;--danger:#ff6b6b;--input:#1f2c48;--border:rgba(255,255,255,.2)}
[data-theme="light"]{--bg:#eef3ff;--bg2:#d9e8ff;--card:rgba(255,255,255,.85);--txt:#111827;--muted:#4b5563;--input:#ffffff;--border:rgba(17,24,39,.15)}
*{box-sizing:border-box}
body{margin:0;background:linear-gradient(145deg,var(--bg),var(--bg2));color:var(--txt);font-family:Inter,system-ui,sans-serif;min-height:100vh;overflow-x:hidden}
.wrap{padding:10px 18px 16px;max-width:1500px;margin:0 auto;display:flex;flex-direction:column;gap:10px}
.logo-wrap{display:flex;justify-content:center;padding-top:0;margin:-8px 0 -14px;line-height:0}
.logo{display:block;max-width:min(300px,72vw);height:auto;filter:drop-shadow(0 8px 18px rgba(0,0,0,.28));}
.top{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
.title{display:flex;align-items:center;gap:10px;margin:0;font-size:clamp(1.35rem,2.3vw,2rem)}
.panel{background:var(--card);backdrop-filter:blur(10px);border:1px solid var(--border);border-radius:16px;padding:14px}
.grid{display:grid;gap:12px}
.metrics-grid{grid-template-columns:repeat(8,minmax(120px,1fr));gap:10px}
@media(max-width:1280px){.metrics-grid{grid-template-columns:repeat(4,minmax(150px,1fr));gap:10px}}
@media(max-width:760px){.metrics-grid{grid-template-columns:repeat(2,minmax(150px,1fr));gap:10px}}
.card{background:rgba(255,255,255,.03);border:1px solid var(--border);border-radius:14px;padding:14px;min-width:0}
.metrics-grid .card{display:flex;flex-direction:column;justify-content:space-between;min-height:102px}.k{color:var(--muted);font-size:.88rem;margin-bottom:8px;display:flex;align-items:center;gap:8px}.v{font-size:clamp(1.08rem,1.25vw,1.35rem);font-weight:700;line-height:1.25;white-space:normal;overflow-wrap:anywhere;word-break:break-word;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;min-height:2.5em}
.k i{opacity:.95}
.chart-head{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:10px;padding-bottom:8px;border-bottom:1px solid var(--border)}
.chart-title{font-size:1rem;font-weight:700;display:flex;align-items:center;gap:8px}
.chart-sub{font-size:.78rem;color:var(--muted)}
.toolbar{display:grid;grid-template-columns:2fr 1fr;gap:12px;align-items:end}
.filters{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:10px}
.field{display:flex;flex-direction:column;gap:6px}
.field label{font-size:.82rem;color:var(--muted)}
.field input,.btn{border-radius:10px;border:1px solid var(--border);padding:10px 12px;font-size:.95rem}
.field input{background:var(--input);color:var(--txt)}
input[type="date"]{appearance:none;-webkit-appearance:none;background:linear-gradient(180deg,rgba(255,255,255,.12),rgba(255,255,255,.04));border:1px solid rgba(148,163,184,.45);box-shadow:inset 0 1px 0 rgba(255,255,255,.18),0 8px 18px rgba(2,6,23,.22);font-weight:700;letter-spacing:.02em;color:var(--txt);min-height:42px;color-scheme:dark}
[data-theme="light"] input[type="date"]{background:linear-gradient(180deg,#ffffff,#eef4ff);border-color:rgba(71,85,105,.28);box-shadow:inset 0 1px 0 rgba(255,255,255,.8),0 6px 14px rgba(15,23,42,.08);color-scheme:light}
input[type="date"]:hover{border-color:rgba(96,165,250,.75)}
input[type="date"]:focus{outline:none;border-color:#60a5fa;box-shadow:0 0 0 3px rgba(96,165,250,.25),0 10px 22px rgba(59,130,246,.2)}
input[type="date"]::-webkit-calendar-picker-indicator{filter:invert(86%) sepia(8%) saturate(321%) hue-rotate(178deg) brightness(102%) contrast(96%);cursor:pointer;opacity:.95}
[data-theme="light"] input[type="date"]::-webkit-calendar-picker-indicator{filter:invert(25%) sepia(8%) saturate(1510%) hue-rotate(178deg) brightness(94%) contrast(85%)}
.actions{display:flex;gap:8px;flex-wrap:wrap}
.btn{color:#fff;cursor:pointer;background:transparent}
.btn.ok{background:var(--ok)}.btn.warn{background:var(--warn)}.btn.danger{background:var(--danger)}.btn.ghost{background:transparent;color:var(--txt)}
.charts{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.chart-card{height:360px;display:flex;flex-direction:column;overflow:hidden}
.chart-card canvas{width:100% !important;flex:1 1 auto;min-height:0}
.hints-panel{padding:16px}
.hints-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px}
.hint-card{background:linear-gradient(165deg,rgba(99,102,241,.18),rgba(14,165,233,.12));border:1px solid var(--border);border-radius:16px;padding:14px;box-shadow:0 12px 26px rgba(2,6,23,.2);min-height:112px}
.hint-title{font-size:.8rem;color:var(--muted);margin-bottom:8px;display:flex;align-items:center;gap:8px}
.hint-value{font-size:1.15rem;font-weight:800;line-height:1.2}
.hint-sub{margin-top:6px;color:var(--muted);font-size:.8rem}
@media(max-width:1100px){.charts{grid-template-columns:1fr}.hints-grid{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media(max-width:840px){.toolbar{grid-template-columns:1fr}.chart-card{height:320px}.hints-grid{grid-template-columns:1fr}}
</style></head>
<body data-theme="dark"><div class="wrap">
<div class="logo-wrap"><img class="logo" src="/solarmining_logo.png" alt="Solar Mining logo" /></div>
<div class="top"><h2 id="dashTitle" class="title"><i class="fa-solid fa-solar-panel"></i> Solar Mining Dashboard</h2>
<div class="actions"><button id="lang" class="btn ghost"><i class="fa-solid fa-earth-europe"></i> HU</button><button id="theme" class="btn warn"><i class="fa-solid fa-circle-half-stroke"></i> Theme</button><button id="downloadTelemetry" class="btn ghost"><i class="fa-solid fa-download"></i> Telemetry JSON</button></div></div>
<div class="grid metrics-grid" id="metrics"></div>
<div class="panel toolbar"><div class="filters">
<div class="field"><label id="lblFrom" for="fromDate">From</label><input id="fromDate" type="date" /></div>
<div class="field"><label id="lblTo" for="toDate">To</label><input id="toDate" type="date" /></div>
<div class="actions"><button class="btn ghost" id="resetRange"><i class="fa-solid fa-rotate-left"></i> Last 30 days</button><button class="btn ok" id="applyRange"><i class="fa-solid fa-filter"></i> Apply range</button></div>
</div><div class="actions">
<button id="btnStart" class="btn ok" onclick="act('start')"><i class="fa-solid fa-play"></i> Start miner</button>
<button id="btnStop" class="btn warn" onclick="act('stop')"><i class="fa-solid fa-stop"></i> Stop miner</button>
<button id="btnForce" class="btn danger" onclick="act('force_stop')"><i class="fa-solid fa-power-off"></i> Force stop</button>
</div></div>
<div id="actionResult" class="k"></div>
<div class="panel hints-panel"><div class="hints-grid" id="historyHints"></div></div>
<div class="charts"><div class="card chart-card"><div class="chart-head"><div id="chPower" class="chart-title"><i class="fa-solid fa-solar-panel"></i> PV Production</div><div id="chPowerSub" class="chart-sub">Watt trend</div></div><canvas id="powerChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chPhase" class="chart-title"><i class="fa-solid fa-bolt"></i> Phase Power</div><div id="chPhaseSub" class="chart-sub">L1 / L2 / L3</div></div><canvas id="phaseChart"></canvas></div>
<div class="card chart-card"><div class="chart-head"><div id="chBattery" class="chart-title"><i class="fa-solid fa-battery-three-quarters"></i> Battery & Mining Rig</div><div id="chBatterySub" class="chart-sub">Charge level and status</div></div><canvas id="batteryChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chEnv" class="chart-title"><i class="fa-solid fa-temperature-half"></i> Garage Environment</div><div id="chEnvSub" class="chart-sub">Temperature / Humidity</div></div><canvas id="envChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chHistSoc" class="chart-title"><i class="fa-solid fa-layer-group"></i> Historical SOC Thresholds</div><div id="chHistSocSub" class="chart-sub">Dynamic SOC logic over time</div></div><canvas id="histSocChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chHistFlags" class="chart-title"><i class="fa-solid fa-chart-line"></i> Historical Decision Flags</div><div id="chHistFlagsSub" class="chart-sub">Battery preserve / headroom / month quality</div></div><canvas id="histFlagsChart"></canvas></div></div></div>
<script>
let powerChart,phaseChart,batteryChart,envChart,histSocChart,histFlagsChart;
const defaultLastDays=30;
let currentRange={from:null,to:null};
let currentLang='en';
const I18N={
  en:{title:'Solar Mining Dashboard',theme:'Theme',downloadTelemetry:'Telemetry JSON',from:'From',to:'To',last30:'Last 30 days',apply:'Apply range',start:'Start miner',stop:'Stop miner',force:'Force stop',
      state:'State',battery:'Battery',pv:'PV Power',weather:'Weather',sunrise:'Sunrise',sunset:'Sunset',clouds:'Clouds',history:'History Points',
      chPower:'PV Production',chPowerSub:'Watt trend',chPhase:'Phase Power',chPhaseSub:'L1 / L2 / L3',chBattery:'Battery & Mining Rig',chBatterySub:'Charge level and status',chEnv:'Garage Environment',chEnvSub:'Temperature / Humidity',chHistSoc:'Historical SOC Thresholds',chHistSocSub:'Dynamic SOC logic over time',chHistFlags:'Historical Decision Flags',chHistFlagsSub:'Battery preserve / headroom / month quality',monthQuality:'Month quality',earlyStart:'Early start SOC',minStop:'Min stop SOC',lateReserve:'Late day reserve SOC',preserveBattery:'Preserve battery',headroomGood:'Headroom good',yes:'Yes',no:'No',strong:'Strong',weak:'Weak',neutral:'Neutral',langBtn:'HU',dsPv:'PV power (W)',dsL1:'L1',dsL2:'L2',dsL3:'L3',dsBatt:'Charge %',dsMiner:'Mining Rig ON',dsTemp:'Temp °C',dsHum:'Humidity %',dsHistEarly:'Early start SOC %',dsHistMinStop:'Min stop SOC %',dsHistLate:'Late reserve SOC %',dsFlagPreserve:'Preserve battery',dsFlagHeadroom:'Headroom good',dsFlagMonth:'Month quality score',stProduction:'production',stStop:'stop',stUnknown:'unknown'},
  hu:{title:'Solar Bányászat Dashboard',theme:'Téma',downloadTelemetry:'Telemetry JSON letöltése',from:'Ettől',to:'Eddig',last30:'Utolsó 30 nap',apply:'Szűrés alkalmazása',start:'Bányászgép indítása',stop:'Bányászgép leállítása',force:'Kényszerleállítás',
      state:'Állapot',battery:'Töltöttség',pv:'PV teljesítmény',weather:'Időjárás',sunrise:'Napkelte',sunset:'Napnyugta',clouds:'Felhőzet',history:'Előzményadatok',
      chPower:'PV termelés',chPowerSub:'Teljesítménytrend (W)',chPhase:'Fázisteljesítmény',chPhaseSub:'L1 / L2 / L3',chBattery:'Akkumulátor és bányászgép',chBatterySub:'Töltöttségi szint és állapot',chEnv:'Garázskörnyezet',chEnvSub:'Hőmérséklet / páratartalom',chHistSoc:'Történeti SOC-küszöbök',chHistSocSub:'Dinamikus SOC-logika időben',chHistFlags:'Történeti döntési jelzők',chHistFlagsSub:'Akkumulátorkímélés / tartalék / havi minőség',monthQuality:'Havi minőség',earlyStart:'Korai indítás SOC',minStop:'Minimum leállítási SOC',lateReserve:'Késői tartalék SOC',preserveBattery:'Akkumulátorkímélés',headroomGood:'Megfelelő teljesítménytartalék',yes:'Igen',no:'Nem',strong:'Erős',weak:'Gyenge',neutral:'Semleges',langBtn:'EN',dsPv:'PV teljesítmény (W)',dsL1:'L1',dsL2:'L2',dsL3:'L3',dsBatt:'Töltöttség %',dsMiner:'Bányászgép bekapcsolva',dsTemp:'Hőmérséklet °C',dsHum:'Páratartalom %',dsHistEarly:'Korai indítás SOC %',dsHistMinStop:'Minimum leállítási SOC %',dsHistLate:'Késői tartalék SOC %',dsFlagPreserve:'Akkumulátorkímélés',dsFlagHeadroom:'Megfelelő tartalék',dsFlagMonth:'Havi minőség pontszám',stProduction:'termelés',stStop:'leállítva',stUnknown:'ismeretlen'}
};
const t=(k)=>I18N[currentLang][k]||k;
function mapState(v){if(v==='production')return t('stProduction'); if(v==='stop')return t('stStop'); return t('stUnknown');}
function localizeWeather(cond){
  const raw=String(cond||'').trim();
  if(currentLang!=='hu') return raw;
  const c=raw.toLowerCase();
  const m=[
    ['clear sky','tiszta ég'],['few clouds','gyengén felhős'],['scattered clouds','szórványfelhős'],
    ['broken clouds','erősen felhős'],['overcast clouds','borult'],['shower rain','zápor'],['light rain','enyhe eső'],
    ['moderate rain','mérsékelt eső'],['heavy intensity rain','erős eső'],['rain','eső'],['thunderstorm','zivatar'],
    ['snow','havazás'],['mist','pára'],['fog','köd'],['haze','párás']
  ];
  for(const [en,hu] of m){ if(c.includes(en)) return hu; }
  return raw;
}
function applyChartI18n(){
  if(!powerChart||!phaseChart||!batteryChart||!envChart)return;
  powerChart.data.datasets[0].label=t('dsPv');
  phaseChart.data.datasets[0].label=t('dsL1'); phaseChart.data.datasets[1].label=t('dsL2'); phaseChart.data.datasets[2].label=t('dsL3');
  batteryChart.data.datasets[0].label=t('dsBatt'); batteryChart.data.datasets[1].label=t('dsMiner');
  envChart.data.datasets[0].label=t('dsTemp'); envChart.data.datasets[1].label=t('dsHum');
  histSocChart.data.datasets[0].label=t('dsHistEarly'); histSocChart.data.datasets[1].label=t('dsHistMinStop'); histSocChart.data.datasets[2].label=t('dsHistLate');
  histFlagsChart.data.datasets[0].label=t('dsFlagPreserve'); histFlagsChart.data.datasets[1].label=t('dsFlagHeadroom'); histFlagsChart.data.datasets[2].label=t('dsFlagMonth');
  powerChart.update('none'); phaseChart.update('none'); batteryChart.update('none'); envChart.update('none'); histSocChart.update('none'); histFlagsChart.update('none');
}
function applyI18n(){
  document.getElementById('dashTitle').innerHTML=`<i class="fa-solid fa-solar-panel"></i> ${t('title')}`;
  document.getElementById('theme').innerHTML=`<i class="fa-solid fa-circle-half-stroke"></i> ${t('theme')}`;
  document.getElementById('lang').innerHTML=`<i class="fa-solid fa-earth-europe"></i> ${t('langBtn')}`;
  document.getElementById('downloadTelemetry').innerHTML=`<i class="fa-solid fa-download"></i> ${t('downloadTelemetry')}`;
  document.getElementById('lblFrom').textContent=t('from');
  document.getElementById('lblTo').textContent=t('to');
  document.getElementById('resetRange').innerHTML=`<i class="fa-solid fa-rotate-left"></i> ${t('last30')}`;
  document.getElementById('applyRange').innerHTML=`<i class="fa-solid fa-filter"></i> ${t('apply')}`;
  document.getElementById('btnStart').innerHTML=`<i class="fa-solid fa-play"></i> ${t('start')}`;
  document.getElementById('btnStop').innerHTML=`<i class="fa-solid fa-stop"></i> ${t('stop')}`;
  document.getElementById('btnForce').innerHTML=`<i class="fa-solid fa-power-off"></i> ${t('force')}`;
  document.getElementById('chPower').innerHTML=`<i class="fa-solid fa-solar-panel"></i> ${t('chPower')}`;
  document.getElementById('chPowerSub').textContent=t('chPowerSub');
  document.getElementById('chPhase').innerHTML=`<i class="fa-solid fa-bolt"></i> ${t('chPhase')}`;
  document.getElementById('chPhaseSub').textContent=t('chPhaseSub');
  document.getElementById('chBattery').innerHTML=`<i class="fa-solid fa-battery-three-quarters"></i> ${t('chBattery')}`;
  document.getElementById('chBatterySub').textContent=t('chBatterySub');
  document.getElementById('chEnv').innerHTML=`<i class="fa-solid fa-temperature-half"></i> ${t('chEnv')}`;
  document.getElementById('chEnvSub').textContent=t('chEnvSub');
  document.getElementById('chHistSoc').innerHTML=`<i class="fa-solid fa-layer-group"></i> ${t('chHistSoc')}`;
  document.getElementById('chHistSocSub').textContent=t('chHistSocSub');
  document.getElementById('chHistFlags').innerHTML=`<i class="fa-solid fa-chart-line"></i> ${t('chHistFlags')}`;
  document.getElementById('chHistFlagsSub').textContent=t('chHistFlagsSub');
  applyChartI18n();
}
const chartOpts={responsive:true,maintainAspectRatio:false,animation:false,interaction:{mode:'nearest',intersect:false,axis:'x'},plugins:{tooltip:{enabled:true,displayColors:false,backgroundColor:'rgba(14,23,41,.92)',titleColor:'#e9eefc',bodyColor:'#e9eefc',padding:12,cornerRadius:12,caretPadding:8,borderColor:'rgba(255,255,255,.2)',borderWidth:1,callbacks:{label:(ctx)=>`${ctx.dataset.label}: ${Number(ctx.parsed.y).toFixed(2)}`}}},scales:{x:{ticks:{maxRotation:0}},y:{beginAtZero:false}}};
const styledSet=(label,color,tension=.2)=>({label,borderColor:color,backgroundColor:color,data:[],pointRadius:0,pointHoverRadius:5,pointHoverBorderWidth:2,pointHoverBackgroundColor:'#ffffff',pointHoverBorderColor:color,pointHitRadius:14,borderWidth:2,tension});
const mk=(id,label,color)=>new Chart(document.getElementById(id),{type:'line',data:{labels:[],datasets:[styledSet(label,color,.25)]},options:chartOpts});
const mkMulti=(id,sets)=>new Chart(document.getElementById(id),{type:'line',data:{labels:[],datasets:sets.map(s=>styledSet(s.label,s.color,s.tension??.2))},options:chartOpts});
function init(){powerChart=mk('powerChart','PV power (W)','#4ade80');phaseChart=mkMulti('phaseChart',[{label:'L1',color:'#60a5fa'},{label:'L2',color:'#f59e0b'},{label:'L3',color:'#f43f5e'}]);batteryChart=mkMulti('batteryChart',[{label:'Charge %',color:'#a78bfa'},{label:'Mining Rig ON',color:'#22c55e'}]);envChart=mkMulti('envChart',[{label:'Temp °C',color:'#ef4444'},{label:'Humidity %',color:'#38bdf8'}]);histSocChart=mkMulti('histSocChart',[{label:t('dsHistEarly'),color:'#22d3ee'},{label:t('dsHistMinStop'),color:'#f59e0b'},{label:t('dsHistLate'),color:'#a78bfa'}]);histFlagsChart=mkMulti('histFlagsChart',[{label:t('dsFlagPreserve'),color:'#ef4444'},{label:t('dsFlagHeadroom'),color:'#22c55e'},{label:t('dsFlagMonth'),color:'#60a5fa'}]);setDefaultRange();}
function shortTs(s){return new Date(s).toLocaleString([], {month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit'});} 
function formatDate(d){return d.toISOString().slice(0,10)}
function setDefaultRange(){const to=new Date();const from=new Date();from.setDate(to.getDate()-defaultLastDays);document.getElementById('fromDate').value=formatDate(from);document.getElementById('toDate').value=formatDate(to);currentRange={from:document.getElementById('fromDate').value,to:document.getElementById('toDate').value};}
async function pull(){const qs=new URLSearchParams(currentRange).toString();const r=await fetch(`/api/snapshot?${qs}`);const d=await r.json();const icon=d.weather_icon||'fa-sun';
const sunrise=(d.sunrise||'').slice(11,16); const sunset=(d.sunset||'').slice(11,16);
document.getElementById('metrics').innerHTML=`<div class='card'><div class='k'><i class='fa-solid fa-toggle-on'></i> ${t('state')}</div><div class='v'>${mapState(d.state)}</div></div><div class='card'><div class='k'><i class='fa-solid fa-battery-half'></i> ${t('battery')}</div><div class='v'>${d.battery}%</div></div><div class='card'><div class='k'><i class='fa-solid fa-solar-panel'></i> ${t('pv')}</div><div class='v'>${Math.round(d.power)} W</div></div><div class='card'><div class='k'><i class='fa-solid fa-cloud-sun'></i> ${t('weather')}</div><div class='v'><i class='fa-solid ${icon}'></i> ${localizeWeather(d.current_condition)}</div></div><div class='card'><div class='k'><i class='fa-solid fa-sun'></i> ${t('sunrise')}</div><div class='v'>${sunrise||'--:--'}</div></div><div class='card'><div class='k'><i class='fa-solid fa-moon'></i> ${t('sunset')}</div><div class='v'>${sunset||'--:--'}</div></div><div class='card'><div class='k'><i class='fa-solid fa-cloud'></i> ${t('clouds')}</div><div class='v'>${d.clouds}%</div></div><div class='card'><div class='k'><i class='fa-solid fa-clock-rotate-left'></i> ${t('history')}</div><div class='v'>${d.history_count}</div></div>`;
const h=d.history||[]; const labels=h.map(x=>shortTs(x.ts));
const hints=d.historical_hints||{};
const monthQ=String(hints.month_quality||'neutral');
const qText=t(monthQ==='strong'?'strong':(monthQ==='weak'?'weak':'neutral'));
const boolTxt=(v)=>v?t('yes'):t('no');
document.getElementById('historyHints').innerHTML=`<div class='hint-card'><div class='hint-title'><i class='fa-solid fa-calendar-days'></i> ${t('monthQuality')}</div><div class='hint-value'>${qText}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-bolt'></i> ${t('earlyStart')}</div><div class='hint-value'>${Number(hints.early_start_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-circle-stop'></i> ${t('minStop')}</div><div class='hint-value'>${Number(hints.min_stop_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-hourglass-end'></i> ${t('lateReserve')}</div><div class='hint-value'>${Number(hints.late_day_reserve_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-shield-heart'></i> ${t('preserveBattery')}</div><div class='hint-value'>${boolTxt(!!hints.should_preserve_battery)}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-gauge-high'></i> ${t('headroomGood')}</div><div class='hint-value'>${boolTxt(!!hints.headroom_good)}</div></div>`;
powerChart.data.labels=labels; powerChart.data.datasets[0].data=h.map(x=>x.power); powerChart.update();
phaseChart.data.labels=labels; phaseChart.data.datasets[0].data=h.map(x=>x.inv_l1); phaseChart.data.datasets[1].data=h.map(x=>x.inv_l2); phaseChart.data.datasets[2].data=h.map(x=>x.inv_l3); phaseChart.update();
batteryChart.data.labels=labels; batteryChart.data.datasets[0].data=h.map(x=>x.battery); batteryChart.data.datasets[1].data=h.map(x=>x.state==='production'?100:0); batteryChart.update();
envChart.data.labels=labels; envChart.data.datasets[0].data=h.map(x=>x.garage_temp); envChart.data.datasets[1].data=h.map(x=>x.garage_hum); envChart.update();
histSocChart.data.labels=labels; histSocChart.data.datasets[0].data=h.map(x=>Number(x.early_start_soc||0)); histSocChart.data.datasets[1].data=h.map(x=>Number(x.min_stop_soc||0)); histSocChart.data.datasets[2].data=h.map(x=>Number(x.late_day_reserve_soc||0)); histSocChart.update();
const mq=(m)=>m==='strong'?100:(m==='weak'?0:50);
histFlagsChart.data.labels=labels; histFlagsChart.data.datasets[0].data=h.map(x=>x.should_preserve_battery?100:0); histFlagsChart.data.datasets[1].data=h.map(x=>x.headroom_good?100:0); histFlagsChart.data.datasets[2].data=h.map(x=>mq(String(x.month_quality||'neutral'))); histFlagsChart.update();}
async function act(a){const r=await fetch('/api/action',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:a})});const d=await r.json();document.getElementById('actionResult').textContent=d.message + ' @ ' + d.ts;}
document.getElementById('applyRange').onclick=()=>{currentRange={from:document.getElementById('fromDate').value,to:document.getElementById('toDate').value};pull();};
document.getElementById('resetRange').onclick=()=>{setDefaultRange();pull();};
document.getElementById('downloadTelemetry').onclick=()=>{window.location.href='/api/telemetry/download';};
init();applyI18n();pull();setInterval(pull,10000);document.getElementById('theme').onclick=()=>{document.body.dataset.theme=document.body.dataset.theme==='dark'?'light':'dark';};document.getElementById('lang').onclick=()=>{currentLang=currentLang==='en'?'hu':'en';applyI18n();pull();};
</script></body></html>
"""


def _build_snapshot_payload(from_date: Optional[str] = None, to_date: Optional[str] = None) -> Dict[str, Any]:
    with snapshot_lock:
        snap = dict(_shared_snapshot)
        hist = list(telemetry_history)

    now = datetime.now(tz=budapest_tz)
    start_ts = None
    end_ts = None
    try:
        if from_date:
            start_ts = datetime.strptime(from_date, "%Y-%m-%d").replace(tzinfo=budapest_tz)
    except ValueError:
        start_ts = None
    try:
        if to_date:
            end_ts = datetime.strptime(to_date, "%Y-%m-%d").replace(tzinfo=budapest_tz) + timedelta(days=1)
    except ValueError:
        end_ts = None

    if start_ts is None or end_ts is None:
        end_ts = now + timedelta(seconds=1)
        start_ts = now - timedelta(days=30)

    filtered_hist = []
    for item in hist:
        try:
            ts = datetime.fromisoformat(str(item.get("ts", "")))
        except Exception:
            continue
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=budapest_tz)
        if start_ts <= ts < end_ts:
            filtered_hist.append(item)

    filtered_hist.sort(key=lambda x: str(x.get("ts", "")))

    return {
        "battery": snap.get("battery", 0),
        "power": snap.get("power", 0),
        "state": snap.get("state", "unknown"),
        "current_condition": snap.get("current_condition", "unknown"),
        "weather_icon": _weather_icon(snap.get("current_condition", "")),
        "clouds": snap.get("clouds", 0),
        "sunrise": snap.get("sunrise").isoformat() if snap.get("sunrise") else "",
        "sunset": snap.get("sunset").isoformat() if snap.get("sunset") else "",
        "history_count": len(filtered_hist),
        "history": filtered_hist,
        "historical_hints": snap.get("historical_hints", {}),
    }


class WebHandler(BaseHTTPRequestHandler):
    def _write(self, code: int, body: bytes, ctype: str):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)

        if parsed.path in ["/", "/index.html"]:
            self._write(200, DASHBOARD_HTML.encode("utf-8"), "text/html; charset=utf-8")
            return
        if parsed.path == "/solarmining_logo.png":
            logo_path = Path("solarmining_logo.png")
            if not logo_path.exists():
                self._write(404, b'{"error":"logo not found"}', "application/json")
                return
            self._write(200, logo_path.read_bytes(), "image/png")
            return

        # Dedicated favicon pack support (GitHub-uploaded /favicon/* assets)
        if parsed.path in {"/favicon.ico", "/site.webmanifest"} or parsed.path.startswith("/favicon/"):
            rel = parsed.path.lstrip("/")
            # allow root aliases when browsers request these
            if parsed.path == "/favicon.ico":
                rel = "favicon/favicon.ico"
            if parsed.path == "/site.webmanifest":
                rel = "favicon/site.webmanifest"

            static_path = Path(rel)
            if not static_path.exists() or not static_path.is_file():
                self._write(404, b'{"error":"favicon asset not found"}', "application/json")
                return

            suffix = static_path.suffix.lower()
            ctype = "application/octet-stream"
            if suffix == ".png":
                ctype = "image/png"
            elif suffix == ".svg":
                ctype = "image/svg+xml"
            elif suffix == ".ico":
                ctype = "image/x-icon"
            elif suffix == ".webmanifest":
                ctype = "application/manifest+json"

            self._write(200, static_path.read_bytes(), ctype)
            return
        if parsed.path == "/api/snapshot":
            qs = parse_qs(parsed.query)
            payload = json.dumps(
                _build_snapshot_payload(
                    qs.get("from", [None])[0],
                    qs.get("to", [None])[0],
                )
            ).encode("utf-8")
            self._write(200, payload, "application/json")
            return
        if parsed.path == "/api/telemetry/download":
            try:
                with snapshot_lock:
                    payload_data = list(telemetry_history)
                body = json.dumps(payload_data, ensure_ascii=False).encode("utf-8")
                filename = f"telemetry_history_{datetime.now(tz=budapest_tz).strftime('%Y%m%d_%H%M%S')}.json"
                self.send_response(200)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except Exception as err:
                self._write(500, json.dumps({"error": f"telemetry export failed: {err}"}).encode("utf-8"), "application/json")
            return
        self._write(404, b'{"error":"not found"}', "application/json")

    def do_POST(self):
        if self.path != "/api/action":
            self._write(404, b'{"error":"not found"}', "application/json")
            return
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b"{}"
        try:
            payload = json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            payload = {}
        action = str(payload.get("action", "")).strip().lower()
        out = _miner_action(action)
        code = 200 if out.get("ok") else 400
        self._write(code, json.dumps(out).encode("utf-8"), "application/json")

    def log_message(self, fmt, *args):
        return


def _start_web_server():
    host = os.getenv("MY_WEB_HOST", "0.0.0.0")
    port = int(os.getenv("MY_WEB_PORT", "9000"))
    print(f"[Web] Starting GUI on http://{host}:{port}")
    try:
        server = ThreadingHTTPServer((host, port), WebHandler)
        server.serve_forever()
    except Exception as err:
        print(f"[Web] Server crashed: {err}")


# ---------- THREAD RUNNER FOR TELEGRAM ----------
def _telegram_loop():
    """
    Background long-poll loop for Telegram updates.
    Periodically reads the latest shared snapshot and passes it to handle_telegram_messages.
    """
    while True:
        try:
            with snapshot_lock:
                snap = dict(_shared_snapshot)
            handle_telegram_messages(
                snap["battery"], snap["power"], snap["state"],
                snap["current_condition"], snap["sunrise"], snap["sunset"],
                snap["clouds"], snap["garage_temp"], snap["garage_hum"],
                snap.get("historical_hints", {})
            )
            # handle_telegram_messages long-polls (25s). No extra sleep needed.
        except Exception as e:
            print(f"[telegram loop] error: {e}")
            time.sleep(2)  # brief backoff on errors


def main_loop():
    global prev_state, state, used_quote, sunrise, sunset, uptime, last_quote_reset_date, historical_profile

    if historical_profile is None:
        historical_profile = build_historical_profile(HISTORY_DIR)

    _load_telemetry_from_file()

    used_quote = load_quote_usage()
    (current_condition, sunrise, sunset, clouds,
     f1_cond, f1_clouds, f1_ts,
     f3_cond, f3_clouds, f3_ts) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

    # START TELEGRAM THREAD ONCE
    t_thread = threading.Thread(target=_telegram_loop, name="telegram-poller", daemon=True)
    t_thread.start()

    web_thread = threading.Thread(target=_start_web_server, name="web-gui", daemon=True)
    web_thread.start()

    garage_temp_history = deque(maxlen=12)
    garage_hum_history = deque(maxlen=12)
    prev_garage_temp = None
    prev_garage_hum = None

    temp_alert_active = False
    hum_alert_active = False

    # ThreadPool for concurrent I/O (token, weather, DHT)
    executor = ThreadPoolExecutor(max_workers=4)

    while True:
        now = datetime.now(tz=budapest_tz)

        # Concurrently read DHT and prefetch next weather + token
        fut_dht = executor.submit(read_dht11, prev_garage_temp, prev_garage_hum)
        fut_weather = executor.submit(get_current_weather, WEATHER_API, LOCATION_LAT, LOCATION_LON)
        fut_token = executor.submit(get_access_token)

        # Use DHT reading immediately for local decisions
        try:
            garage_data = fut_dht.result(timeout=5)
        except Exception:
            garage_data = {'temperature': prev_garage_temp, 'humidity': prev_garage_hum}

        garage_temp = garage_data['temperature']
        garage_hum = garage_data['humidity']

        garage_temp_history.append(garage_temp)
        garage_hum_history.append(garage_hum)

        if len(garage_temp_history) == garage_temp_history.maxlen:
            mean_temp = statistics.mean(garage_temp_history)
            mean_hum = statistics.mean(garage_hum_history)

            if mean_temp > 40 and not temp_alert_active:
                send_telegram_message(f"Warning! The average garage temperature is too high: {mean_temp:.1f}C")
                temp_alert_active = True
            elif mean_temp <= 40:
                temp_alert_active = False

            if mean_hum > 80 and not hum_alert_active:
                send_telegram_message(f"Warning! The average garage humidity is too high: {mean_hum:.1f}%")
                hum_alert_active = True
            elif mean_hum <= 80:
                hum_alert_active = False

            if abs(garage_temp - mean_temp) > 5:
                direction = "risen" if garage_temp > mean_temp else "fallen"
                send_telegram_message(
                    f"Garage temperature has {direction} to: {garage_temp}C (mean was {mean_temp:.1f}C)"
                )

        prev_garage_temp = garage_temp
        prev_garage_hum = garage_hum

        today = now.date()

        if (
            today != last_quote_reset_date
            and now.month == 1
            and now.day == 1
            and used_quote != 0
        ):
            print("January 1st detected – resetting quote usage to 0.")
            send_telegram_message("January 1st detected – resetting quote usage to 0.")
            used_quote = 0
            save_quote_usage(used_quote)
            last_quote_reset_date = today

        print(f"Sunrise start: {sunrise}:00 | Sunset stop: {sunset}:00")
        within_active = (sunrise.hour, sunrise.minute) <= (now.hour, now.minute) <= (sunset.hour, sunset.minute)

        if within_active:
            try:
                used_quote += 1
                save_quote_usage(used_quote)

                print("\n\nStarting new cycle...")
                print(f"Time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n")

                # Join the prefetches
                try:
                    token = fut_token.result(timeout=10)
                except Exception:
                    token = None
                try:
                    (current_condition, sunrise, sunset, clouds,
                     f1_cond, f1_clouds, f1_ts,
                     f3_cond, f3_clouds, f3_ts) = fut_weather.result(timeout=10)
                except Exception:
                    (current_condition, sunrise, sunset, clouds,
                     f1_cond, f1_clouds, f1_ts,
                     f3_cond, f3_clouds, f3_ts) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

                # Fetch device data (depends on token)
                data = fetch_current_data(token) if token else {}
                store_data(data)  # attaches phasePowers

                (battery, power, state, current_condition, sunrise, sunset, clouds,
                f1_cond, f1_clouds, f1_ts, f3_cond, f3_clouds, f3_ts, hist_hints) = check_crypto_production_conditions(
                    data, WEATHER_API, LOCATION_LAT, LOCATION_LON
                )

                has_usable_solarman_data = bool((data or {}).get("dataList"))
                if not has_usable_solarman_data:
                    print("[Telemetry] Solarman dataList is empty for this cycle; saving fallback telemetry row.")
                _record_telemetry(now, data or {}, battery or 0, power or 0, state or "unknown",
                                  current_condition or "unknown", clouds or 0, garage_temp, garage_hum, hist_hints, sunrise, sunset)

                # update shared snapshot for telegram thread
                with snapshot_lock:
                    _shared_snapshot.update({
                        "battery": battery or 0,
                        "power": power or 0,
                        "state": state or "unknown",
                        "current_condition": current_condition or "unknown",
                        "sunrise": sunrise, "sunset": sunset, "clouds": clouds or 0,
                        "garage_temp": garage_temp or 0, "garage_hum": garage_hum or 0,
                        "historical_hints": hist_hints or {}
                    })

                if is_rpi:
                    write_to_display(
                        state_text=state,
                        soc=battery,
                        solar_power=power,
                        temperature=garage_temp,
                        humidity=garage_hum
                    )
                print("Cycle complete. Waiting for next interval.")
            except requests.HTTPError as http_err:
                print(f"HTTP error occurred: {http_err}")
            except Exception as err:
                print(f"An unexpected error occurred: {err}")

            pct = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0
            print(f"Quote usage: {used_quote} / {QUOTE_LIMIT} ({pct:.2f}%)")
            print(f"Garage temperature: {garage_temp}C")
            print(f"Garage humidity: {garage_hum}%")

            # Telegram polling is already running in its own thread.
            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")
        else:
            print(f"Outside of active hours. Sleeping... (Sunrise: {sunrise.strftime('%H:%M')} | Sunset: {sunset.strftime('%H:%M')})")
            print(f"Time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n")

            (current_condition, sunrise, sunset, clouds,
             f1_cond, f1_clouds, f1_ts,
             f3_cond, f3_clouds, f3_ts) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

            state = "stop"
            if prev_state == "production":
                print("Miner did not shut down correctly, shutting down...")
                send_telegram_message("Miner did not shut down correctly, shutting down...")
                print("Trying to press power button.")
                if is_rpi:
                    press_power_button(16, 0.55)
                if state != prev_state:
                    prev_state = state
                    uptime = now
                    save_prev_state(prev_state, uptime)
            if is_rpi:
                write_to_display(
                    state_text="sleep",
                    soc=0,
                    solar_power=0,
                    temperature=garage_temp,
                    humidity=garage_hum
                )

            # update snapshot for telegram thread even during idle
            with snapshot_lock:
                _shared_snapshot.update({
                    "battery": 0, "power": 0, "state": state or "stop",
                    "current_condition": current_condition or "unknown",
                    "sunrise": sunrise, "sunset": sunset, "clouds": clouds or 0,
                    "garage_temp": garage_temp or 0, "garage_hum": garage_hum or 0,
                    "historical_hints": _history_recommendation(now, 0, 0, sunrise, sunset)
                })

            pct = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0
            print(f"Garage temperature: {garage_temp}C")
            print(f"Garage humidity: {garage_hum}%")
            print(f"Quote usage: {used_quote} / {QUOTE_LIMIT} ({pct:.2f}%)")

            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")

if __name__ == '__main__':
    # Send startup notification first
    try:
        notify_startup()
    except Exception as _e:
        # Startup message shouldn't kill the app
        print(f"[startup notify] {type(_e).__name__}: {_e}")

    # Register graceful shutdown notifications
    try:
        signal.signal(signal.SIGINT, _signal_handler)
        signal.signal(signal.SIGTERM, _signal_handler)
    except Exception as _e:
        print(f"[signal register] {type(_e).__name__}: {_e}")

    # Also try atexit as a last resort (won't catch SIGKILL)
    import atexit
    atexit.register(lambda: notify_shutdown(reason="atexit", err=None))

    try:
        if is_rpi and OLED_AVAILABLE:
            init_display()
        main_loop()
    except KeyboardInterrupt as e:
        # This is usually handled by SIGINT, but keep as fallback
        notify_shutdown(reason="KeyboardInterrupt", err=e)
        sys.exit(130)  # 128+SIGINT
    except SystemExit as e:
        # sys.exit(...) – include code if present
        code = getattr(e, 'code', None)
        notify_shutdown(reason=f"SystemExit code={code}", err=None)
        raise
    except Exception as e:
        # Any unhandled exception – crash report with error details
        try:
            notify_shutdown(reason="crash", err=e)
        finally:
            # Non-zero exit for supervisors (systemd, etc.)
            sys.exit(1)
