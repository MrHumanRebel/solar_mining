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
import ipaddress

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
BATTERY_CAPACITY_AH = float(os.getenv("MY_BATTERY_CAPACITY_AH", "200"))
BATTERY_NOMINAL_V = float(os.getenv("MY_BATTERY_NOMINAL_V", "55.2"))
MINER_POWER_W = float(os.getenv("MY_MINER_POWER_W", "1050"))
BATTERY_FLOOR_SOC = float(os.getenv("MY_BATTERY_FLOOR_SOC", "20"))
HIGH_SOC_STOP_SOC = float(os.getenv("MY_HIGH_SOC_STOP_SOC", "90"))
HIGH_SOC_STOP_MAX_PV_W = float(os.getenv("MY_HIGH_SOC_STOP_MAX_PV_W", "400"))
BATTERY_PROTECT_SOC = float(os.getenv("MY_BATTERY_PROTECT_SOC", "90"))
HARD_AFTERNOON_STOP_SOC = float(os.getenv("MY_HARD_AFTERNOON_STOP_SOC", "90"))
HARD_AFTERNOON_STOP_HOUR = int(os.getenv("MY_HARD_AFTERNOON_STOP_HOUR", "14"))
PV_COVERAGE_RATIO_STOP = float(os.getenv("MY_PV_COVERAGE_RATIO_STOP", "0.9"))
PV_COVERAGE_RATIO_START = float(os.getenv("MY_PV_COVERAGE_RATIO_START", "0.75"))
MIN_RUN_MINUTES = int(os.getenv("MY_MIN_RUN_MINUTES", "18"))
MIN_RESTART_DELAY_MINUTES = int(os.getenv("MY_MIN_RESTART_DELAY_MINUTES", "10"))
MINER_IPS = [
    ip.strip()
    for ip in os.getenv("MY_MINER_IPS", "192.168.0.200,192.168.0.201").split(",")
    if ip.strip()
]
MINER_PING_RETRIES_PER_IP = max(1, int(os.getenv("MY_MINER_PING_RETRIES_PER_IP", "2")))
MINER_PING_FAIL_STREAK_FOR_RESTART = max(1, int(os.getenv("MY_MINER_PING_FAIL_STREAK_FOR_RESTART", "2")))
MINER_STOP_FORCE_CONSECUTIVE = max(1, int(os.getenv("MY_MINER_STOP_FORCE_CONSECUTIVE", "2")))
MINER_STOP_FORCE_COOLDOWN_MINUTES = max(1, int(os.getenv("MY_MINER_STOP_FORCE_COOLDOWN_MINUTES", "20")))
HASHRATE_CHECK_DELAY_MINUTES = max(1, int(os.getenv("MY_HASHRATE_CHECK_DELAY_MINUTES", "10")))
HASHRATE_MIN_HS = max(0.0, float(os.getenv("MY_HASHRATE_MIN_HS", "1")))
HASHRATE_RESTART_COOLDOWN_MINUTES = max(5, int(os.getenv("MY_HASHRATE_RESTART_COOLDOWN_MINUTES", "30")))

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
    "inv_l1": 0, "inv_l2": 0, "inv_l3": 0, "inv_lt": 0,
    "historical_hints": {
        "month_quality": "neutral",
        "early_start_soc": 55,
        "min_stop_soc": 20,
        "late_day_reserve_soc": 80,
        "should_preserve_battery": False,
        "headroom_good": False,
        "start_guard_allow": False,
        "start_guard_reason": "unknown",
        "start_guard_bridge_minutes": 0,
        "start_guard_eta_minutes": 0,
        "start_guard_capacity_wh": 0,
        "start_guard_battery_ah": 0,
        "start_guard_battery_voltage": 0,
        "start_guard_usable_wh": 0,
        "start_guard_bms_floor_soc": 20,
        "start_guard_bms_window_wh": 0,
        "start_guard_needed_bridge_minutes": 0,
        "start_guard_needed_bridge_wh": 0,
        "decision_state": "unknown",
        "decision_start_rules": [],
        "decision_stop_rules": [],
        "decision_summary": "unknown",
    },
}


def _idle_historical_hints() -> Dict[str, Any]:
    """Reset hint payload during sleep/idle so /now does not show stale decisions."""
    return {
        "month_quality": "neutral",
        "early_start_soc": 0,
        "min_stop_soc": 0,
        "late_day_reserve_soc": 0,
        "should_preserve_battery": False,
        "headroom_good": False,
        "start_guard_allow": False,
        "start_guard_reason": "idle",
        "start_guard_bridge_minutes": 0,
        "start_guard_eta_minutes": 0,
        "start_guard_capacity_wh": 0,
        "start_guard_battery_ah": 0,
        "start_guard_battery_voltage": 0,
        "start_guard_usable_wh": 0,
        "start_guard_bms_floor_soc": 0,
        "start_guard_bms_window_wh": 0,
        "start_guard_needed_bridge_minutes": 0,
        "start_guard_needed_bridge_wh": 0,
        "decision_state": "sleep",
        "decision_start_rules": [],
        "decision_stop_rules": ["Idle window"],
        "decision_summary": "SLEEP: outside active hours",
        "weather_risk_5d": "unknown",
        "weather_sunny_ratio_5d": 0.0,
        "weather_bad_ratio_5d": 0.0,
    }


def _classify_weather_condition(condition: str) -> str:
    c = str(condition or "").lower()
    if any(k in c for k in ["snow", "sleet", "blizzard", "freezing"]):
        return "snow"
    if any(k in c for k in ["rain", "drizzle", "storm", "thunder", "shower"]):
        return "rain"
    if any(k in c for k in ["overcast", "cloud", "fog", "mist", "haze", "smoke", "dust"]):
        return "cloud"
    if any(k in c for k in ["clear", "sun", "fair"]):
        return "sun"
    return "mixed"


def _summarize_free_weather_outlook(forecast_payload: Dict[str, Any], now: Optional[datetime] = None) -> Dict[str, Any]:
    """
    Build a 5-day risk outlook from FREE OpenWeather 2.5 forecast data.
    No long-range extrapolation: use only the directly available 5-day/3h entries.
    """
    if now is None:
        now = datetime.now(tz=budapest_tz)

    entries = forecast_payload.get("list", []) if isinstance(forecast_payload, dict) else []
    if not entries:
        return {
            "source": "owm_free_2.5_forecast_5d",
            "confidence": 0.0,
            "summary_5d": "unknown",
            "sunny_ratio_5d": 0.0,
            "bad_ratio_5d": 0.0,
            "score_5d": 0.0,
        }

    counts = {"sun": 0, "cloud": 0, "rain": 0, "snow": 0, "mixed": 0}
    for ent in entries:
        cond = ((ent.get("weather") or [{}])[0] or {}).get("description", "")
        kind = _classify_weather_condition(cond)
        counts[kind] = counts.get(kind, 0) + 1

    total = float(max(1, sum(counts.values())))
    ratios = {k: counts.get(k, 0) / total for k in counts}
    bad_ratio = ratios.get("rain", 0.0) + ratios.get("snow", 0.0) + 0.5 * ratios.get("cloud", 0.0)
    sunny_ratio = ratios.get("sun", 0.0)

    score_5d = (
        sunny_ratio * 1.0
        - ratios.get("cloud", 0.0) * 0.35
        - ratios.get("rain", 0.0) * 0.85
        - ratios.get("snow", 0.0) * 1.0
    )

    month_season_boost = 0.08 if now.month in (5, 6, 7, 8) else (-0.08 if now.month in (11, 12, 1, 2) else 0.0)
    score_5d = score_5d + month_season_boost

    def _risk_label(score: float) -> str:
        if score >= 0.18:
            return "solar_friendly"
        if score <= -0.18:
            return "solar_weak"
        return "mixed"

    return {
        "source": "owm_free_2.5_forecast_5d",
        "confidence": min(1.0, total / 40.0),
        "summary_5d": _risk_label(score_5d),
        "sunny_ratio_5d": round(sunny_ratio, 3),
        "bad_ratio_5d": round(bad_ratio, 3),
        "score_5d": round(score_5d, 3),
        "samples_5d": int(total),
    }

# Unbounded in-memory telemetry history (no MAX_HISTORY_POINTS cap).
telemetry_history: deque = deque()
_pending_transition_state: Optional[str] = None
_pending_transition_since: Optional[datetime] = None
_pending_transition_hits: int = 0
_miner_ping_full_failure_streak: int = 0
_last_miner_ping_check_at: Optional[datetime] = None
_miner_stop_reply_streak: int = 0
_last_force_shutdown_at: Optional[datetime] = None
_last_production_start_at: Optional[datetime] = None
_hashrate_low_streak: int = 0
_last_hashrate_restart_at: Optional[datetime] = None
web_notifications: deque = deque(maxlen=160)


def _parse_timestamp(value: Any) -> Optional[datetime]:
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(str(value))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=budapest_tz)
        return dt
    except Exception:
        return None


def _parse_wallet_address(value: str) -> Optional[str]:
    raw = str(value or "").strip()
    if not raw:
        return None
    if raw.startswith("http://") or raw.startswith("https://"):
        m = re.search(r"/wallet/([A-Za-z0-9]+)", raw)
        if m:
            raw = m.group(1)
    raw = raw.strip()
    if not re.fullmatch(r"[A-Za-z0-9]{24,64}", raw):
        return None
    return raw


def _effective_wallet_address() -> str:
    global WALLET_ADDRESS
    parsed = _parse_wallet_address(WALLET_ADDRESS)
    return parsed or str(WALLET_ADDRESS).strip()


def _hashrate_to_hs(value: float, unit: str) -> float:
    factor = {
        "h/s": 1.0,
        "kh/s": 1e3,
        "mh/s": 1e6,
        "gh/s": 1e9,
        "th/s": 1e12,
    }.get(str(unit or "").strip().lower(), 1.0)
    return max(0.0, value) * factor


def _wallet_hashrate_hs(wallet: str) -> Optional[float]:
    wallet = _parse_wallet_address(wallet or "") or ""
    if not wallet:
        return None
    api_url = f"https://www.ravenminer.com/api/v1/wallet/{wallet}"
    try:
        r = requests.get(api_url, timeout=10)
        if r.status_code == 200:
            payload = r.json()
            if isinstance(payload, dict):
                for key in ("hashrate", "currentHashrate", "current_hashrate", "hash"):
                    if key in payload:
                        try:
                            return max(0.0, float(payload.get(key) or 0.0))
                        except Exception:
                            pass
                data = payload.get("data", {}) if isinstance(payload.get("data"), dict) else {}
                for key in ("hashrate", "currentHashrate", "current_hashrate", "hash"):
                    if key in data:
                        try:
                            return max(0.0, float(data.get(key) or 0.0))
                        except Exception:
                            pass
    except Exception:
        pass

    # Fallback: parse wallet page text for any H/s values, keep highest.
    try:
        page_url = f"https://www.ravenminer.com/ravencoin/wallet/{wallet}"
        resp = requests.get(page_url, timeout=12)
        text = resp.text if resp.status_code == 200 else ""
        matches = re.findall(r"([0-9]+(?:[.,][0-9]+)?)\s*([kmgth]?h/s)", text, flags=re.IGNORECASE)
        if not matches:
            return None
        vals = []
        for n, unit in matches:
            try:
                vals.append(_hashrate_to_hs(float(str(n).replace(",", ".")), unit))
            except Exception:
                continue
        return max(vals) if vals else None
    except Exception:
        return None


def _should_run_miner_ping_check(now: datetime, min_interval_minutes: int = 3) -> bool:
    """Throttle miner ping checks without coupling them to miner uptime timestamps."""
    global _last_miner_ping_check_at
    if not isinstance(now, datetime):
        return False
    if _last_miner_ping_check_at is None:
        _last_miner_ping_check_at = now
        return True
    elapsed = now - _last_miner_ping_check_at
    if elapsed >= timedelta(minutes=max(1, int(min_interval_minutes))):
        _last_miner_ping_check_at = now
        return True
    return False


def _last_state_change_ts() -> Optional[datetime]:
    """Find the last timestamp where persisted telemetry state changed."""
    items = list(telemetry_history)
    if len(items) < 2:
        return None
    for i in range(len(items) - 1, 0, -1):
        cur = items[i]
        prev = items[i - 1]
        s1 = str(cur.get("state", "")).strip().lower()
        s0 = str(prev.get("state", "")).strip().lower()
        if not s1 or not s0 or s1 == s0:
            continue
        try:
            ts = datetime.fromisoformat(str(cur.get("ts", "")))
            if ts.tzinfo is None:
                ts = ts.replace(tzinfo=budapest_tz)
            return ts
        except Exception:
            continue
    return None


def _apply_transition_guard(prev_state_val: str, desired_state: str, now: datetime,
                            confirmed: bool = True) -> Tuple[str, bool, str]:
    """
    Time-based transition guard to avoid fast ON/OFF thrashing from short PV/weather noise.
    Returns (effective_state, blocked, reason).
    """
    if desired_state == prev_state_val:
        return desired_state, False, "no_transition_needed"

    if not confirmed:
        return prev_state_val, True, "confirmation_pending"

    last_change_ts = _last_state_change_ts()
    if last_change_ts is None:
        return desired_state, False, "no_recent_change"

    minutes_since_change = (now - last_change_ts).total_seconds() / 60.0

    # Don't cut a fresh production run too quickly on temporary cloud dips.
    if prev_state_val == "production" and desired_state == "stop":
        if minutes_since_change < max(0, MIN_RUN_MINUTES):
            return prev_state_val, True, f"min_run_protection({minutes_since_change:.1f}<{MIN_RUN_MINUTES}min)"

    # After a stop, avoid immediate restart ping-pong.
    if prev_state_val == "stop" and desired_state == "production":
        if minutes_since_change < max(0, MIN_RESTART_DELAY_MINUTES):
            return prev_state_val, True, f"restart_delay({minutes_since_change:.1f}<{MIN_RESTART_DELAY_MINUTES}min)"

    return desired_state, False, "time_guard_passed"


def _resolve_telemetry_file() -> Path:
    raw = os.getenv("MY_TELEMETRY_FILE", "").strip()
    if not raw:
        # Use the state file directory by default, because it is usually a bind-mounted path.
        state_path = Path(STATE_FILE)
        default_dir = state_path.parent if str(state_path).strip() else Path(__file__).resolve().parent
        return (default_dir / "telemetry_history.json").resolve()

    p = Path(raw)
    if p.is_absolute():
        return p
    # Keep default file near script to avoid cwd-dependent path issues.
    return (Path(__file__).resolve().parent / p).resolve()


TELEMETRY_FILE = _resolve_telemetry_file()
TELEMETRY_BACKUP_FILE = (Path(STATE_FILE).resolve().parent / "telemetry_history_backup.json").resolve()
print(f"[Telemetry] Using telemetry store: {TELEMETRY_FILE}")
print(f"[Telemetry] Using telemetry backup store: {TELEMETRY_BACKUP_FILE}")


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


def _format_minutes_human(minutes: float) -> str:
    if minutes is None:
        return "--"
    try:
        total_minutes = float(minutes)
    except (TypeError, ValueError):
        return "--"
    if not math.isfinite(total_minutes) or total_minutes < 0:
        return "--"

    total_minutes = max(0.0, total_minutes)
    hours = int(total_minutes // 60)
    mins = int(round(total_minutes - (hours * 60)))
    if mins == 60:
        hours += 1
        mins = 0
    return f"{total_minutes:.1f} min ({hours}h {mins}m)"

def _find_value(data_list: List[Dict[str, Any]], key: str, default: float = 0.0) -> float:
    for e in data_list:
        if e.get("key") == key:
            return _safe_float(e.get("value"), default)
    return default



def _find_first_value(data_list: List[Dict[str, Any]], keys: List[str], default: float = 0.0) -> float:
    for k in keys:
        v = _find_value(data_list, k, None)
        if v is not None:
            try:
                return float(v)
            except (TypeError, ValueError):
                continue
    return float(default)


def _effective_battery_capacity_wh(battery_voltage: float, battery_ah: float) -> float:
    # System requirement: Wh is derived from Ah * V (no fixed Wh input).
    v = battery_voltage if battery_voltage > 1 else BATTERY_NOMINAL_V
    ah = battery_ah if battery_ah > 0 else BATTERY_CAPACITY_AH
    return max(100.0, ah * v)

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
            "hourly_prod_mean": {str(h): float(statistics.mean(vals)) for h, vals in hourly_prod.items() if vals},
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


def _interpolate_hourly_profile_for_month(target_month: int, months_cfg: Dict[int, Dict[str, Any]]) -> Dict[str, float]:
    """Builds an interpolated hourly PV profile for a month (0..23) from nearby months."""
    if target_month in months_cfg:
        direct = months_cfg[target_month].get("hourly_prod_mean", {})
        if isinstance(direct, dict) and direct:
            return {str(int(k)): float(v) for k, v in direct.items()}

    blended: Dict[int, float] = defaultdict(float)
    weights: Dict[int, float] = defaultdict(float)
    for m, cfg in months_cfg.items():
        hourly = cfg.get("hourly_prod_mean", {}) if isinstance(cfg, dict) else {}
        if not isinstance(hourly, dict) or not hourly:
            continue
        dist = min((target_month - m) % 12, (m - target_month) % 12)
        if dist == 0:
            dist = 0.5
        w = 1.0 / dist
        for h_raw, p_raw in hourly.items():
            try:
                h = max(0, min(23, int(h_raw)))
                p = max(0.0, float(p_raw))
            except (TypeError, ValueError):
                continue
            blended[h] += w * p
            weights[h] += w

    return {str(h): (blended[h] / weights[h]) for h in sorted(weights.keys()) if weights[h] > 0}


def _pv_estimate_at(dt: datetime, hourly_profile: Dict[str, Any]) -> float:
    """Linear interpolation between hourly means for smoother bridge estimation."""
    if not hourly_profile:
        return 0.0
    h0 = dt.hour
    h1 = min(23, h0 + 1)
    p0 = max(0.0, _safe_float(hourly_profile.get(str(h0), 0.0), 0.0))
    p1 = max(0.0, _safe_float(hourly_profile.get(str(h1), p0), p0))
    frac = dt.minute / 60.0
    return p0 + (p1 - p0) * frac


def _estimate_full_supply_and_energy(sunrise_dt: datetime, now: datetime,
                                     hourly_profile: Dict[str, Any]) -> Tuple[Optional[datetime], float]:
    """Returns expected full-supply timestamp and needed bridge energy from sunrise."""
    if not hourly_profile:
        return None, 0.0

    start = sunrise_dt.replace(second=0, microsecond=0)
    end = (start + timedelta(hours=12)).replace(second=0, microsecond=0)
    t = start
    step_min = 5
    needed_wh = 0.0
    full_supply_dt: Optional[datetime] = None

    while t < end:
        pv = _pv_estimate_at(t, hourly_profile)
        deficit = max(0.0, MINER_POWER_W - pv)
        # We need a future full-supply point for runtime start-guard decisions.
        if full_supply_dt is None and t >= now and deficit <= 1e-6:
            full_supply_dt = t
            break
        needed_wh += deficit * (step_min / 60.0)
        t += timedelta(minutes=step_min)

    if full_supply_dt is None:
        # if we never reach full feed in modeled window, use conservative future fallback
        base = max(now, sunrise_dt).replace(second=0, microsecond=0)
        full_supply_dt = base + timedelta(hours=3)
    return full_supply_dt, max(0.0, needed_wh)


def _estimate_minutes_for_energy_budget(sunrise_dt: datetime, hourly_profile: Dict[str, Any],
                                        energy_budget_wh: float) -> float:
    """Estimate bridge minutes from sunrise until a given energy budget is consumed."""
    if not hourly_profile or energy_budget_wh <= 0:
        return 0.0

    start = sunrise_dt.replace(second=0, microsecond=0)
    end = (start + timedelta(hours=12)).replace(second=0, microsecond=0)
    t = start
    step_min = 5
    spent_wh = 0.0

    while t < end:
        pv = _pv_estimate_at(t, hourly_profile)
        deficit = max(0.0, MINER_POWER_W - pv)
        step_wh = deficit * (step_min / 60.0)
        if spent_wh + step_wh >= energy_budget_wh:
            if step_wh <= 1e-9:
                break
            frac = (energy_budget_wh - spent_wh) / step_wh
            return max(0.0, (t - start).total_seconds() / 60.0 + frac * step_min)
        spent_wh += step_wh
        t += timedelta(minutes=step_min)

    return max(0.0, (end - start).total_seconds() / 60.0)


def _estimate_bridge_energy_between(start_dt: datetime, end_dt: datetime,
                                    hourly_profile: Dict[str, Any]) -> float:
    """Estimate required bridge energy (Wh) between two timestamps."""
    if not hourly_profile or not isinstance(start_dt, datetime) or not isinstance(end_dt, datetime):
        return 0.0

    start = start_dt.replace(second=0, microsecond=0)
    end = end_dt.replace(second=0, microsecond=0)
    if end <= start:
        return 0.0

    t = start
    step_min = 5
    needed_wh = 0.0

    while t < end:
        next_t = min(t + timedelta(minutes=step_min), end)
        pv = _pv_estimate_at(t, hourly_profile)
        deficit = max(0.0, MINER_POWER_W - pv)
        needed_wh += deficit * ((next_t - t).total_seconds() / 3600.0)
        t = next_t

    return max(0.0, needed_wh)


def _telemetry_context_for_history(now: datetime) -> Dict[str, Any]:
    """Recent telemetry context (fresh/runtime signal) to blend with long-range Solarman history."""
    items = list(telemetry_history)
    if not items:
        return {
            "samples": 0,
            "fresh_midday_pv": 0.0,
            "fresh_charge_rate_pct_per_hour": 0.0,
            "fresh_clouds": 100.0,
            "fresh_soc_floor": 0.0,
            "fresh_month_quality": "neutral",
            "confidence": 0.0,
        }

    points: List[Dict[str, Any]] = []
    for rec in items[-1200:]:  # cap scan cost
        try:
            ts = datetime.fromisoformat(str(rec.get("ts", "")))
        except Exception:
            continue
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=budapest_tz)

        # Prefer fresh data from the same month and within ~10 days.
        age_h = (now - ts).total_seconds() / 3600.0
        if age_h < 0 or age_h > 24 * 10:
            continue
        if ts.month != now.month:
            continue

        points.append({
            "ts": ts,
            "battery": _safe_float(rec.get("battery"), 0.0),
            "power": _safe_float(rec.get("power"), 0.0),
            "clouds": _safe_float(rec.get("clouds"), 100.0),
        })

    if len(points) < 8:
        return {
            "samples": len(points),
            "fresh_midday_pv": 0.0,
            "fresh_charge_rate_pct_per_hour": 0.0,
            "fresh_clouds": 100.0,
            "fresh_soc_floor": 0.0,
            "fresh_month_quality": "neutral",
            "confidence": 0.2 if points else 0.0,
        }

    points.sort(key=lambda x: x["ts"])
    midday = [x["power"] for x in points if 10 <= x["ts"].hour <= 14]
    fresh_midday_pv = statistics.median(midday) if midday else statistics.median([x["power"] for x in points])

    charge_rates: List[float] = []
    for i in range(1, len(points)):
        p0 = points[i - 1]
        p1 = points[i]
        dt_h = (p1["ts"] - p0["ts"]).total_seconds() / 3600.0
        if dt_h <= 0 or dt_h > 0.5:
            continue
        if max(p0["power"], p1["power"]) < 700:
            continue
        rate = (p1["battery"] - p0["battery"]) / dt_h
        if 0.05 <= rate <= 18:
            charge_rates.append(rate)

    fresh_charge_rate = statistics.median(charge_rates) if charge_rates else 0.0
    fresh_clouds = statistics.median([x["clouds"] for x in points])

    # Recent low-SOC behavior during active hours to shape reserve discipline.
    active_soc = [x["battery"] for x in points if 9 <= x["ts"].hour <= 18]
    fresh_soc_floor = statistics.quantiles(active_soc, n=5)[1] if len(active_soc) >= 5 else (min(active_soc) if active_soc else 0.0)

    if fresh_midday_pv >= 2300 and fresh_charge_rate >= 2.2 and fresh_clouds <= 70:
        fresh_month_quality = "strong"
    elif fresh_midday_pv <= 1500 or fresh_charge_rate <= 1.0 or fresh_clouds >= 85:
        fresh_month_quality = "weak"
    else:
        fresh_month_quality = "neutral"

    confidence = min(1.0, len(points) / 120.0)
    return {
        "samples": len(points),
        "fresh_midday_pv": float(fresh_midday_pv),
        "fresh_charge_rate_pct_per_hour": float(fresh_charge_rate),
        "fresh_clouds": float(fresh_clouds),
        "fresh_soc_floor": float(fresh_soc_floor),
        "fresh_month_quality": fresh_month_quality,
        "confidence": float(confidence),
    }


def _history_recommendation(now: datetime, battery_charge: float, current_power: float,
                            sunrise_dt: datetime, sunset_dt: datetime,
                            weather_outlook: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Creates dynamic decision hints from historical production behavior for current month.
    Blends long-range Solarman history with fresh runtime telemetry context.
    """
    global historical_profile
    months = (historical_profile or {}).get("months", {})
    month_cfg = _interpolate_month_config(now.month, months)
    interpolated_hourly = _interpolate_hourly_profile_for_month(now.month, months)
    telem_ctx = _telemetry_context_for_history(now)
    wx = weather_outlook or {}
    wx5 = str(wx.get("summary_5d", "unknown")).lower()

    if not month_cfg:
        return {
            "month_quality": telem_ctx.get("fresh_month_quality", "neutral"),
            "early_start_soc": 55,
            "min_stop_soc": 20,
            "late_day_reserve_soc": 80,
            "should_preserve_battery": now.hour >= 15 and battery_charge < 80,
            "headroom_good": current_power >= 2500,
            "hourly_prod_mean": {},
            "predicted_minutes_to_full": None,
            "predicted_full_charge_time": None,
            "can_refill_before_sunset": False,
            "telemetry_samples": int(telem_ctx.get("samples", 0)),
            "telemetry_confidence": float(telem_ctx.get("confidence", 0.0)),
            "telemetry_month_quality": str(telem_ctx.get("fresh_month_quality", "neutral")),
            "weather_risk_5d": wx5,
            "weather_sunny_ratio_5d": float(wx.get("sunny_ratio_5d", 0.0)),
            "weather_bad_ratio_5d": float(wx.get("bad_ratio_5d", 0.0)),
            "weather_confidence": float(wx.get("confidence", 0.0)),
        }

    daylight_span = int(month_cfg.get("daylight_span", 8))
    midday_avg = float(month_cfg.get("midday_avg", 2000))
    daily_peak_p75 = float(month_cfg.get("daily_peak_p75", 3500))
    solar_start_hour = int(month_cfg.get("solar_start_hour", sunrise_dt.hour))
    evening_soc_p40 = float(month_cfg.get("evening_soc_p40", 45.0))

    # Blend historical (slow) with telemetry (fresh) for stronger adaptivity.
    telem_weight = min(0.45, max(0.0, float(telem_ctx.get("confidence", 0.0)) * 0.45))
    blended_midday = (1.0 - telem_weight) * midday_avg + telem_weight * float(telem_ctx.get("fresh_midday_pv", midday_avg))

    strong_month = daylight_span >= 9 and blended_midday >= 2300
    weak_month = daylight_span <= 7 or blended_midday <= 1650

    telem_quality = str(telem_ctx.get("fresh_month_quality", "neutral"))
    if telem_quality == "strong" and not weak_month:
        strong_month = True
    if telem_quality == "weak":
        weak_month = True
        strong_month = False

    if wx5 == "solar_friendly":
        strong_month = True
        weak_month = False if telem_quality != "weak" else weak_month
    elif wx5 == "solar_weak":
        weak_month = True
        strong_month = False

    early_start_soc = 32 if strong_month else (58 if weak_month else 45)
    min_stop_soc = 26 if weak_month else 20
    late_day_reserve_soc = max(70, int(evening_soc_p40 + (8 if weak_month else 4)))

    fresh_floor = float(telem_ctx.get("fresh_soc_floor", 0.0))
    if fresh_floor > 0:
        late_day_reserve_soc = max(late_day_reserve_soc, int(min(88.0, fresh_floor + (8 if weak_month else 5))))

    # Keep reserve discipline realistic so the miner does not stop too early on good days.
    # In non-export systems an overfilled battery causes PV curtailment; reserve should not
    # be so high that we waste midday/afternoon production windows.
    reserve_cap = 88 if weak_month else (86 if strong_month else 87)
    late_day_reserve_soc = min(reserve_cap, late_day_reserve_soc)

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

    full_charge_pred = _predict_time_to_full_charge(now, battery_charge, current_power, sunrise_dt, sunset_dt, interpolated_hourly)

    refill_confident_morning = False
    full_charge_time_raw = full_charge_pred.get("full_charge_time")
    full_charge_dt: Optional[datetime] = None
    if isinstance(full_charge_time_raw, str) and full_charge_time_raw:
        try:
            full_charge_dt = datetime.fromisoformat(full_charge_time_raw)
            if full_charge_dt.tzinfo is None:
                full_charge_dt = full_charge_dt.replace(tzinfo=budapest_tz)
        except Exception:
            full_charge_dt = None

    # If history suggests the battery will refill before sunset, allow earlier starts.
    if wx5 == "solar_weak":
        early_start_soc = max(early_start_soc, min_stop_soc + 8)
        late_day_reserve_soc = min(90, max(late_day_reserve_soc, 82))
    elif wx5 == "solar_friendly":
        early_start_soc = max(min_stop_soc + 4, early_start_soc - 3)

    if full_charge_pred.get("can_refill_before_sunset", False) and full_charge_pred.get("minutes_to_full") is not None:
        margin_min = float(full_charge_pred.get("sunset_margin_minutes", 0.0))

        # Stronger relaxation when full recharge is predicted before late morning.
        if full_charge_dt is not None and full_charge_dt <= now.replace(hour=11, minute=30, second=0, microsecond=0):
            refill_confident_morning = True
            early_start_soc = max(min_stop_soc + 4, early_start_soc - 14)
        elif margin_min >= 120:
            early_start_soc = max(min_stop_soc + 5, early_start_soc - 10)
        elif margin_min >= 45:
            early_start_soc = max(min_stop_soc + 6, early_start_soc - 8)
        elif margin_min >= 15:
            early_start_soc = max(min_stop_soc + 8, early_start_soc - 4)

    return {
        "month_quality": "strong" if strong_month else ("weak" if weak_month else "neutral"),
        "early_start_soc": early_start_soc,
        "min_stop_soc": min_stop_soc,
        "late_day_reserve_soc": late_day_reserve_soc,
        "should_preserve_battery": should_preserve_battery,
        "headroom_good": headroom_good,
        "hourly_prod_mean": month_cfg.get("hourly_prod_mean", {}) or interpolated_hourly,
        "predicted_minutes_to_full": full_charge_pred.get("minutes_to_full"),
        "predicted_full_charge_time": full_charge_pred.get("full_charge_time"),
        "can_refill_before_sunset": bool(full_charge_pred.get("can_refill_before_sunset", False)),
        "sunset_margin_minutes": float(full_charge_pred.get("sunset_margin_minutes", 0.0)),
        "predicted_charge_rate_pct_per_hour": float(full_charge_pred.get("rate_pct_per_hour", 0.0)),
        "refill_confident_morning": bool(refill_confident_morning),
        "telemetry_samples": int(telem_ctx.get("samples", 0)),
        "telemetry_confidence": float(telem_ctx.get("confidence", 0.0)),
        "telemetry_month_quality": telem_quality,
        "blended_midday_pv": float(blended_midday),
        "weather_risk_5d": wx5,
        "weather_sunny_ratio_5d": float(wx.get("sunny_ratio_5d", 0.0)),
        "weather_bad_ratio_5d": float(wx.get("bad_ratio_5d", 0.0)),
        "weather_confidence": float(wx.get("confidence", 0.0)),
        "weather_source": str(wx.get("source", "none")),
    }


def _predict_time_to_full_charge(now: datetime, battery_charge: float, current_power: float,
                                 sunrise_dt: datetime, sunset_dt: datetime,
                                 hourly_prod_mean: Dict[str, Any]) -> Dict[str, Any]:
    """
    Estimate minutes to 100% SOC based on recent telemetry trend and historical month profile.
    This is intentionally conservative: it only allows early-start relaxation when refill
    is likely before sunset.
    """
    if battery_charge >= 99.5:
        return {
            "minutes_to_full": 0.0,
            "full_charge_time": now.isoformat(),
            "can_refill_before_sunset": True,
            "sunset_margin_minutes": max(0.0, (sunset_dt - now).total_seconds() / 60.0),
            "rate_pct_per_hour": 0.0,
        }

    # 1) Learn charge-rate from telemetry deltas (same month, daytime, positive charging periods).
    rates: List[float] = []
    hist_items = list(telemetry_history)
    for i in range(1, len(hist_items)):
        prev = hist_items[i - 1]
        cur = hist_items[i]
        try:
            t0 = datetime.fromisoformat(str(prev.get("ts", "")))
            t1 = datetime.fromisoformat(str(cur.get("ts", "")))
        except Exception:
            continue

        if t0.tzinfo is None:
            t0 = t0.replace(tzinfo=budapest_tz)
        if t1.tzinfo is None:
            t1 = t1.replace(tzinfo=budapest_tz)

        if t1 <= t0 or t1.month != now.month:
            continue

        dt_h = (t1 - t0).total_seconds() / 3600.0
        if dt_h <= 0 or dt_h > 0.5:
            continue

        b0 = _safe_float(prev.get("battery"), -1)
        b1 = _safe_float(cur.get("battery"), -1)
        if not (0 <= b0 <= 100 and 0 <= b1 <= 100):
            continue

        p0 = _safe_float(prev.get("power"), 0)
        p1 = _safe_float(cur.get("power"), 0)
        c0 = _safe_float(prev.get("clouds"), 100)
        c1 = _safe_float(cur.get("clouds"), 100)

        # Prefer segments where PV is meaningful and weather is not heavily overcast.
        if max(p0, p1) < 700 or max(c0, c1) > 90:
            continue

        rate = (b1 - b0) / dt_h
        if 0.05 <= rate <= 18.0:
            rates.append(rate)

    rate_pct_per_hour = statistics.median(rates) if rates else 0.0

    # 2) Blend with profile confidence from expected hourly PV around "now".
    expected_now_pv = _pv_estimate_at(now, hourly_prod_mean) if hourly_prod_mean else 0.0
    if rate_pct_per_hour <= 0.0 and expected_now_pv > MINER_POWER_W * 0.8:
        # fallback conservative synthetic rate when telemetry is sparse
        rate_pct_per_hour = 2.8 if now.month in (4, 5, 6, 7, 8) else 1.8

    if rate_pct_per_hour <= 0.0:
        return {
            "minutes_to_full": None,
            "full_charge_time": None,
            "can_refill_before_sunset": False,
            "sunset_margin_minutes": 0.0,
            "rate_pct_per_hour": 0.0,
        }

    missing_pct = max(0.0, 100.0 - battery_charge)
    minutes_to_full = (missing_pct / rate_pct_per_hour) * 60.0
    full_dt = now + timedelta(minutes=minutes_to_full)
    margin_min = (sunset_dt - full_dt).total_seconds() / 60.0

    return {
        "minutes_to_full": round(max(0.0, minutes_to_full), 2),
        "full_charge_time": full_dt.isoformat(),
        "can_refill_before_sunset": margin_min >= 0,
        "sunset_margin_minutes": round(margin_min, 2),
        "rate_pct_per_hour": round(rate_pct_per_hour, 3),
    }


def _has_solarman_payload(data: Optional[Dict[str, Any]]) -> bool:
    return bool(isinstance(data, dict) and isinstance(data.get("dataList"), list) and len(data.get("dataList")) > 0)


def _with_daytime_data_fallback(data: Dict[str, Any], now: datetime,
                                sunrise_dt: datetime, sunset_dt: datetime) -> Tuple[Dict[str, Any], bool]:
    """During active daylight window, keep the previous non-empty payload if API returns empty dataList."""
    if _has_solarman_payload(data):
        return data, False

    if not _is_active_window(now, sunrise_dt, sunset_dt):
        return data, False

    previous = load_data()
    if _has_solarman_payload(previous):
        print("[Fallback] Empty Solarman dataList in daytime -> using previous stored payload to avoid false stop/start toggles.")
        return previous, True

    return data, False


def _compute_start_bridge_guard(now: datetime, battery_charge: float, current_power: float,
                                sunrise_dt: datetime, sunset_dt: datetime,
                                hist: Dict[str, Any], battery_voltage: float, battery_ah: float) -> Dict[str, Any]:
    """
    Prevent rapid ON/OFF cycles near minimum SOC by requiring enough battery energy
    to bridge the period until typical PV can continuously feed the miner load.
    """
    min_stop_soc = float(hist.get("min_stop_soc", BATTERY_FLOOR_SOC))
    hourly_prod_mean = hist.get("hourly_prod_mean", {}) if isinstance(hist, dict) else {}
    if not isinstance(hourly_prod_mean, dict):
        hourly_prod_mean = {}

    capacity_wh = _effective_battery_capacity_wh(battery_voltage, battery_ah)

    # Usable bridge energy for start permission is intentionally measured only above min_stop_soc reserve.
    # Example: at 100% SOC and 26% min-stop reserve, usable window is 74% of capacity.
    soc_window_pct = max(0.0, battery_charge - min_stop_soc)
    usable_wh = max(0.0, soc_window_pct / 100.0 * capacity_wh)
    # Operational bridge runtime should reflect the actual BMS floor window (20-100%).
    bms_floor_soc = 20.0
    bridge_soc_window_pct = max(0.0, battery_charge - bms_floor_soc)
    bridge_usable_wh = max(0.0, bridge_soc_window_pct / 100.0 * capacity_wh)
    deficit_w = max(0.0, MINER_POWER_W - max(0.0, current_power))
    guard_bridge_minutes = 999.0 if deficit_w <= 0 else (usable_wh / deficit_w) * 60.0
    current_bridge_minutes = 0.0 if deficit_w <= 0 else (bridge_usable_wh / deficit_w) * 60.0

    estimated_full_supply_dt, daily_needed_bridge_wh = _estimate_full_supply_and_energy(
        sunrise_dt, now, hourly_prod_mean
    )
    daily_needed_bridge_minutes = (
        _estimate_minutes_for_energy_budget(sunrise_dt, hourly_prod_mean, daily_needed_bridge_wh)
        if daily_needed_bridge_wh > 0 else 0.0
    )

    eta_minutes = 999.0
    needed_bridge_minutes = daily_needed_bridge_minutes
    needed_bridge_wh = daily_needed_bridge_wh

    if estimated_full_supply_dt is not None:
        # Remaining time from now until expected full PV supply.
        eta_minutes = max(0.0, (estimated_full_supply_dt - now).total_seconds() / 60.0)

        # Remaining requirement from now to full-supply moment for runtime safety checks.
        remaining_bridge_wh = (
            _estimate_bridge_energy_between(now, estimated_full_supply_dt, hourly_prod_mean)
            if eta_minutes > 0.0 else 0.0
        )
    else:
        remaining_bridge_wh = 0.0
        if deficit_w <= 0:
            eta_minutes = 0.0

    # Avoid zero ETA when real-time PV is still below miner demand.
    if deficit_w > 0.0 and eta_minutes <= 0.0:
        eta_minutes = 5.0
        remaining_bridge_wh = max(remaining_bridge_wh, deficit_w * (eta_minutes / 60.0))

    # BMS floor applies system-wide: battery operational bridge window is 20-100% SOC.
    bms_window_pct = max(0.0, 100.0 - bms_floor_soc)
    bms_window_wh = (bms_window_pct / 100.0) * capacity_wh
    if needed_bridge_wh > bms_window_wh:
        needed_bridge_wh = bms_window_wh
        needed_bridge_minutes = min(
            needed_bridge_minutes,
            _estimate_minutes_for_energy_budget(sunrise_dt, hourly_prod_mean, needed_bridge_wh)
        )
    remaining_bridge_wh = min(remaining_bridge_wh, bms_window_wh)

    # Morning-only relevance: after full supply, current bridge/LTA is obsolete,
    # but daily needed bridge stats remain useful as day-level requirements.
    if now >= sunrise_dt and eta_minutes <= 0.0:
        current_bridge_minutes = 0.0
        eta_minutes = 0.0

    energy_cover_ok = remaining_bridge_wh > 0 and usable_wh >= remaining_bridge_wh
    allow_start = battery_charge > min_stop_soc and (guard_bridge_minutes >= eta_minutes or energy_cover_ok)

    # If historical profile predicts refill before sunset, relax morning start conservatively
    # to avoid missing production windows in non-export systems.
    refill_confident_morning = bool(hist.get("refill_confident_morning", False))
    refill_pv_threshold = max(120.0, MINER_POWER_W * 0.12) if refill_confident_morning else max(300.0, MINER_POWER_W * 0.30)
    refill_soc_buffer = 6 if refill_confident_morning else 10
    refill_morning_window_ok = now.hour < (11 if refill_confident_morning else 13)

    refill_relax = (
        bool(hist.get("can_refill_before_sunset", False))
        and refill_morning_window_ok
        and battery_charge >= (min_stop_soc + refill_soc_buffer)
        and current_power >= refill_pv_threshold
    )
    if (not allow_start) and refill_relax:
        allow_start = True

    refill_feasibility_block = (
        not bool(hist.get("can_refill_before_sunset", True))
        and now.hour >= 10
        and battery_charge < max(min_stop_soc + 18, 48.0)
        and current_power < max(320.0, MINER_POWER_W * 0.30)
    )
    if allow_start and refill_feasibility_block:
        allow_start = False

    refill_reason = "refill_confident_morning_relaxation" if refill_confident_morning else "refill_confident_relaxation"
    if refill_feasibility_block:
        reason = "cannot_refill_before_sunset_guard"
    elif allow_start and not refill_relax:
        reason = "ok"
    elif allow_start and refill_relax:
        reason = refill_reason
    else:
        reason = "soc_below_min_stop" if battery_charge <= min_stop_soc else "insufficient_bridge_energy"

    return {
        "allow_start": allow_start,
        "energy_cover_ok": bool(energy_cover_ok),
        "usable_wh": round(usable_wh, 2),
        "deficit_w": round(deficit_w, 2),
        "bridge_minutes": round(current_bridge_minutes, 2),
        "eta_minutes": round(eta_minutes, 2),
        "needed_bridge_minutes": round(needed_bridge_minutes, 2),
        "needed_bridge_wh": round(needed_bridge_wh, 2),
        "remaining_bridge_wh": round(remaining_bridge_wh, 2),
        "reason": reason,
        "capacity_wh": round(capacity_wh, 2),
        "battery_voltage": round(max(0.0, battery_voltage), 2),
        "battery_ah": round(max(0.0, battery_ah), 2),
        "soc_window_pct": round(soc_window_pct, 2),
        "min_stop_soc": round(min_stop_soc, 2),
        "bms_floor_soc": round(bms_floor_soc, 2),
        "bms_window_wh": round(bms_window_wh, 2),
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


def _push_web_notification(message: str, level: str = "info") -> None:
    msg = str(message or "").strip()
    if not msg:
        return
    cleaned = re.sub(r"\s+", " ", msg).strip()
    short = cleaned[:240] + "…" if len(cleaned) > 240 else cleaned
    web_notifications.appendleft({
        "ts": datetime.now(tz=budapest_tz).isoformat(),
        "level": level if level in {"info", "success", "warn", "error"} else "info",
        "message": short,
    })


def _guess_notification_level(message: str) -> str:
    m = str(message or "").lower()
    if any(k in m for k in ["error", "failed", "hiba", "exception", "❌"]):
        return "error"
    if any(k in m for k in ["warning", "warn", "⚠️", "ping hiba"]):
        return "warn"
    if any(k in m for k in ["started", "stopped", "elküldve", "✅", "ready"]):
        return "success"
    return "info"


def send_telegram_message(message, max_retries=15, keyboard=True, mirror_web=True):
    if mirror_web:
        _push_web_notification(message, level=_guess_notification_level(message))
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


def send_telegram_message_async(message, max_retries=4, keyboard=True, mirror_web=False):
    threading.Thread(
        target=send_telegram_message,
        kwargs={
            "message": message,
            "max_retries": max_retries,
            "keyboard": keyboard,
            "mirror_web": mirror_web,
        },
        daemon=True,
        name="telegram-send-async",
    ).start()

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
    global used_quote, WALLET_ADDRESS
    message_text = str(message_text or "").strip()
    if message_text == "/now":
        ip = get_ip_address()
        ram = get_ram_usage()
        cpu = get_cpu_usage()
        temps = get_temperatures()
        percentage = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0

        # read inverter phase powers from live snapshot first; fall back to saved file.
        l1 = l2 = l3 = lt = 0 if (_safe_float(power, 0.0) == 0 and str(state).lower() in {"stop", "sleep"}) else None
        unit = "W"
        with snapshot_lock:
            snap = dict(_shared_snapshot)
        if l1 is None:
            l1 = snap.get("inv_l1")
            l2 = snap.get("inv_l2")
            l3 = snap.get("inv_l3")
            lt = snap.get("inv_lt")
        try:
            if (l1 is None or l2 is None or l3 is None or lt is None) and os.path.exists(SOLARMAN_FILE):
                with open(SOLARMAN_FILE, 'r', encoding='utf-8') as f:
                    saved = json.load(f)
                phase = saved.get("phasePowers", {})
                l1 = phase.get("L1") if l1 is None else l1
                l2 = phase.get("L2") if l2 is None else l2
                l3 = phase.get("L3") if l3 is None else l3
                lt = phase.get("LT") if lt is None else lt
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

        start_guard_allow = "Yes" if hints.get("start_guard_allow", False) else "No"
        start_guard_reason_raw = str(hints.get("start_guard_reason", "unknown"))
        start_guard_reason_en = {
            "ok": "OK",
            "soc_below_min_stop": "SOC below minimum stop",
            "insufficient_bridge_energy": "Insufficient bridge energy",
            "cannot_refill_before_sunset_guard": "Likely cannot refill battery before sunset",
            "refill_confident_relaxation": "Confident refill relaxation",
            "refill_confident_morning_relaxation": "Confident morning refill relaxation",
            "bridge_energy_confident_sunny_day_relaxation": "Bridge-energy confident sunny-day relaxation",
            "aggressive_morning_refill_start": "Aggressive morning refill start",
        }.get(start_guard_reason_raw, start_guard_reason_raw)
        start_guard_bridge = _safe_float(hints.get("start_guard_bridge_minutes", 0.0), 0.0)
        start_guard_eta = _safe_float(hints.get("start_guard_eta_minutes", 0.0), 0.0)
        start_guard_capacity = _safe_float(hints.get("start_guard_capacity_wh", 0.0), 0.0)
        start_guard_usable = _safe_float(hints.get("start_guard_usable_wh", 0.0), 0.0)
        start_guard_needed_time = _safe_float(hints.get("start_guard_needed_bridge_minutes", 0.0), 0.0)
        start_guard_needed_capacity = _safe_float(hints.get("start_guard_needed_bridge_wh", 0.0), 0.0)
        start_guard_ah = _safe_float(hints.get("start_guard_battery_ah", 0.0), 0.0)
        start_guard_voltage = _safe_float(hints.get("start_guard_battery_voltage", 0.0), 0.0)
        start_guard_soc_window = _safe_float(hints.get("start_guard_soc_window_pct", 0.0), 0.0)
        start_guard_min_stop_soc = _safe_float(hints.get("start_guard_min_stop_soc", 0.0), 0.0)
        start_guard_bms_floor = _safe_float(hints.get("start_guard_bms_floor_soc", 20.0), 20.0)
        start_guard_bms_window = _safe_float(hints.get("start_guard_bms_window_wh", 0.0), 0.0)
        predicted_minutes_to_full = hints.get("predicted_minutes_to_full")
        predicted_minutes_to_full = _safe_float(predicted_minutes_to_full, -1.0) if predicted_minutes_to_full is not None else -1.0
        predicted_eta_full = _format_minutes_human(predicted_minutes_to_full)
        decision_state = str(hints.get("decision_state", "unknown"))
        decision_summary = str(hints.get("decision_summary", "No matched rules"))
        decision_start_rules = hints.get("decision_start_rules", []) if isinstance(hints.get("decision_start_rules", []), list) else []
        decision_stop_rules = hints.get("decision_stop_rules", []) if isinstance(hints.get("decision_stop_rules", []), list) else []
        decision_start_text = "; ".join(str(x) for x in decision_start_rules) if decision_start_rules else "No matched rules"
        decision_stop_text = "; ".join(str(x) for x in decision_stop_rules) if decision_stop_rules else "No matched rules"
        telem_samples = int(_safe_float(hints.get("telemetry_samples", 0), 0.0))
        telem_confidence = _safe_float(hints.get("telemetry_confidence", 0.0), 0.0)
        telem_quality = str(hints.get("telemetry_month_quality", "neutral"))
        blended_midday = _safe_float(hints.get("blended_midday_pv", 0.0), 0.0)
        weather_risk_5d = str(hints.get("weather_risk_5d", "unknown"))
        weather_sunny_ratio_5d = 100.0 * _safe_float(hints.get("weather_sunny_ratio_5d", 0.0), 0.0)
        weather_bad_ratio_5d = 100.0 * _safe_float(hints.get("weather_bad_ratio_5d", 0.0), 0.0)
        battery_pct = _safe_float(battery, 0.0)

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
            f"🛡️ Start guard\n"
            f"• Start allowed: {start_guard_allow}\n"
            f"• Reason: {start_guard_reason_en}\n"
            f"• Bridge: {start_guard_bridge:.1f} min\n"
            f"• ETA: {start_guard_eta:.1f} min\n"
            f"• Capacity: {start_guard_capacity:.1f}Wh ({start_guard_ah:.1f}Ah @ {start_guard_voltage:.2f}V)\n"
            f"• Usable: {start_guard_usable:.1f}Wh\n"
            f"• Needed time: {start_guard_needed_time:.1f} min\n"
            f"• Needed capacity: {start_guard_needed_capacity:.1f}Wh\n"
            f"• ETA to 100% battery charge: {predicted_eta_full}\n"
            f"• Usable formula: {start_guard_soc_window:.0f}% = {battery_pct:.0f}% - {start_guard_min_stop_soc:.0f}%\n"
            f"• BMS range: {start_guard_bms_floor:.0f}-100% ({start_guard_bms_window:.1f}Wh)\n\n"
            f"📋 Decision trace\n"
            f"• Decision state: {decision_state}\n"
            f"• Decision summary: {decision_summary}\n"
            f"• Matched start rules: {decision_start_text}\n"
            f"• Matched stop rules: {decision_stop_text}\n\n"
            f"📈 Telemetry blend\n"
            f"• Samples: {telem_samples}\n"
            f"• Confidence: {telem_confidence:.2f}\n"
            f"• Fresh month quality: {telem_quality}\n"
            f"• Blended midday PV: {blended_midday:.0f}W\n"
            f"• 5-day risk: {weather_risk_5d} (sunny: {weather_sunny_ratio_5d:.0f}%, bad: {weather_bad_ratio_5d:.0f}%)\n\n"
            f"🖥️ System\n"
            f"• IP: {ip}\n"
            f"• RAM usage: {ram}\n"
            f"• CPU usage: {cpu}\n"
            f"• CPU temp: {temps.get('cpu-thermal') or temps.get('CPU') or 'N/A'}\n"
            f"• Quote usage: {used_quote} / {QUOTE_LIMIT} ({percentage:.2f}%)"
        )
        # /now is a high-frequency status query; keep Telegram reply but do not mirror it into GUI notifications.
        send_telegram_message(message, mirror_web=False)

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

    if message_text == "/wallet":
        send_telegram_message(f"Current wallet: {_effective_wallet_address()}")

    if message_text.startswith("/wallet "):
        raw = message_text.split(" ", 1)[1].strip()
        parsed = _parse_wallet_address(raw)
        if not parsed:
            send_telegram_message("Invalid wallet. Use Ravencoin wallet address or full RavenMiner wallet URL.")
        else:
            WALLET_ADDRESS = parsed
            save_prev_state(prev_state, uptime)
            send_telegram_message(f"✅ Wallet updated: {WALLET_ADDRESS}")


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
    global WALLET_ADDRESS, _last_production_start_at, _last_hashrate_restart_at, _last_force_shutdown_at
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, 'r') as f:
                d = json.load(f)
        except Exception:
            return None, None
        wallet = _parse_wallet_address(d.get("wallet_address", WALLET_ADDRESS))
        if wallet:
            WALLET_ADDRESS = wallet
        _last_production_start_at = _parse_timestamp(d.get("last_production_start_at"))
        _last_hashrate_restart_at = _parse_timestamp(d.get("last_hashrate_restart_at"))
        _last_force_shutdown_at = _parse_timestamp(d.get("last_force_shutdown_at"))
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
        if prev_state_val == "production" and _last_production_start_at is None and isinstance(up, datetime):
            _last_production_start_at = up
        return prev_state_val, up
    return None, None

def save_prev_state(state_val, uptime_val):
    global WALLET_ADDRESS, _last_production_start_at, _last_hashrate_restart_at, _last_force_shutdown_at
    try:
        existing = {}
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE, 'r') as f:
                    existing = json.load(f) or {}
            except Exception:
                existing = {}
        uptime_str = uptime_val.isoformat() if isinstance(uptime_val, datetime) else uptime_val
        existing.update({
            'prev_state': state_val,
            'uptime': uptime_str,
            'wallet_address': _effective_wallet_address(),
            'last_production_start_at': _last_production_start_at.isoformat() if isinstance(_last_production_start_at, datetime) else None,
            'last_hashrate_restart_at': _last_hashrate_restart_at.isoformat() if isinstance(_last_hashrate_restart_at, datetime) else None,
            'last_force_shutdown_at': _last_force_shutdown_at.isoformat() if isinstance(_last_force_shutdown_at, datetime) else None,
        })
        with open(STATE_FILE, 'w') as f:
            json.dump(existing, f, indent=4)
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
        outlook = _summarize_free_weather_outlook(fd)

    except (requests.RequestException, KeyError, IndexError, ValueError) as e:
        print(f"[Warning] Weather request failed: {e}")
        current_condition = "unknown"
        clouds = 0
        now = datetime.now(tz=budapest_tz)
        sunrise_dt = now.replace(hour=6, minute=0, second=0)
        sunset_dt = now.replace(hour=18, minute=0, second=0)
        f1_cond = "unknown"; f1_clouds = 0; f1_ts = now.strftime("%Y-%m-%d %H:%M:%S")
        f3_cond = "unknown"; f3_clouds = 0; f3_ts = (now + timedelta(hours=3)).strftime("%Y-%m-%d %H:%M:%S")
        outlook = _summarize_free_weather_outlook({"list": []}, now)

    return (
        current_condition, sunrise_dt, sunset_dt, clouds,
        f1_cond, f1_clouds, f1_ts,
        f3_cond, f3_clouds, f3_ts,
        outlook,
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
    global uptime, _miner_ping_full_failure_streak, _miner_stop_reply_streak, _last_force_shutdown_at
    # OR semantics by design:
    # - production: if ANY configured miner IP replies, miner is considered online
    # - stop: if ANY configured miner IP replies, force shutdown is triggered
    miner_ips_raw = MINER_IPS or ["192.168.0.200", "192.168.0.201"]
    miner_ips = []
    for candidate in miner_ips_raw:
        try:
            miner_ips.append(str(ipaddress.ip_address(str(candidate).strip())))
        except Exception:
            print(f"[Warning] Invalid miner IP skipped: {candidate!r}")
    if not miner_ips:
        print("[Warning] No valid miner IP configured, skipping uptime check.")
        return
    if uptime is None:
        uptime = now
    difference = now - uptime
    hours, remainder = divmod(difference.seconds, 3600)
    minutes, _ = divmod(remainder, 60)

    print(
        f"Pinging miner IPs: {', '.join(miner_ips)} "
        f"(retries per IP: {MINER_PING_RETRIES_PER_IP}) to check uptime..."
    )
    try:
        reachable_ips = []
        for miner_ip in miner_ips:
            ip_reachable = False
            for _ in range(MINER_PING_RETRIES_PER_IP):
                # Avoid stuck ping subprocesses in edge network states.
                # NOTE: keep command list-form for safe argument handling.
                result = subprocess.run(
                    ["ping", "-c", "1", "-W", "2", miner_ip],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=4,
                    check=False,
                )
                if result.returncode == 0:
                    ip_reachable = True
                    break
            if ip_reachable:
                reachable_ips.append(miner_ip)

        if not reachable_ips:
            _miner_stop_reply_streak = 0
            print("No reply!")
            if prev_state_val == "production":
                _miner_ping_full_failure_streak += 1
                print(
                    f"No reply from any configured IP ({', '.join(miner_ips)}). "
                    f"Failure streak: {_miner_ping_full_failure_streak}/{MINER_PING_FAIL_STREAK_FOR_RESTART}."
                )
                if _miner_ping_full_failure_streak >= MINER_PING_FAIL_STREAK_FOR_RESTART:
                    print("Failure streak threshold reached. Attempting restart sequence...")
                    send_telegram_message(
                        f"⚠️ Miner ping failed in production mode ({', '.join(miner_ips)}) "
                        f"for {_miner_ping_full_failure_streak} consecutive checks. Restart sequence started."
                    )
                    press_power_button(16, 10)
                    time.sleep(15)
                    press_power_button(16, 0.55)
                    print("Restart sequence completed.")
                    send_telegram_message("✅ Miner restart sequence completed (after consecutive ping failures).")
                    uptime = now
                    save_prev_state(prev_state_val, uptime)
                    _miner_ping_full_failure_streak = 0
        else:
            _miner_ping_full_failure_streak = 0
            reachable_text = ", ".join(reachable_ips)
            print(f"Reply from: {reachable_text}!")
            if prev_state_val == "stop":
                _miner_stop_reply_streak += 1
                cooldown_ok = (
                    _last_force_shutdown_at is None
                    or (now - _last_force_shutdown_at) >= timedelta(minutes=MINER_STOP_FORCE_COOLDOWN_MINUTES)
                )
                if _miner_stop_reply_streak < MINER_STOP_FORCE_CONSECUTIVE:
                    print(
                        f"STOP response streak {_miner_stop_reply_streak}/{MINER_STOP_FORCE_CONSECUTIVE}. "
                        "Waiting for confirmation before force shutdown."
                    )
                elif not cooldown_ok:
                    wait_left = max(
                        0.0,
                        MINER_STOP_FORCE_COOLDOWN_MINUTES - (now - _last_force_shutdown_at).total_seconds() / 60.0
                    )
                    print(f"Force shutdown cooldown active ({wait_left:.1f} min remaining).")
                else:
                    print(f"Reply from {reachable_text}. Attempting force shutdown sequence...")
                    send_telegram_message(
                        f"⚠️ Miner is responding ({reachable_text}) while state is STOP. Force shutdown started."
                    )
                    press_power_button(16, 10)
                    time.sleep(5)
                    print("Force shutdown completed.")
                    send_telegram_message("✅ STOP safety force shutdown completed.")
                    _last_force_shutdown_at = now
                    _miner_stop_reply_streak = 0
                    uptime = now
                    save_prev_state(prev_state_val, uptime)

        total_hours = difference.days * 24 + hours
        status_target = ", ".join(reachable_ips) if reachable_ips else f"any configured IP ({', '.join(miner_ips)})"
        if prev_state_val == "production":
            print(f"{status_target} is online for {total_hours} hours and {minutes} minutes")
        elif prev_state_val == "stop":
            if reachable_ips:
                print(f"{status_target} is unexpectedly online while STOP was expected ({total_hours}h {minutes}m since last state change).")
            else:
                print(f"{status_target} is offline as expected for {total_hours} hours and {minutes} minutes")
    except Exception as e:
        print(f"Error during uptime check: {e}")


def check_hashrate_guard(now: datetime, effective_state: str) -> None:
    global _hashrate_low_streak, _last_hashrate_restart_at
    if str(effective_state).lower() != "production":
        _hashrate_low_streak = 0
        return
    if _last_production_start_at is None:
        return
    if (now - _last_production_start_at) < timedelta(minutes=HASHRATE_CHECK_DELAY_MINUTES):
        return

    wallet = _effective_wallet_address()
    hashrate_hs = _wallet_hashrate_hs(wallet)
    if hashrate_hs is None:
        _hashrate_low_streak += 1
        print(f"[Hashrate guard] Unable to fetch hashrate for wallet {wallet}. streak={_hashrate_low_streak}")
        return

    if hashrate_hs >= HASHRATE_MIN_HS:
        _hashrate_low_streak = 0
        return

    _hashrate_low_streak += 1
    cooldown_ok = (
        _last_hashrate_restart_at is None
        or (now - _last_hashrate_restart_at) >= timedelta(minutes=HASHRATE_RESTART_COOLDOWN_MINUTES)
    )
    if not cooldown_ok:
        print("[Hashrate guard] Low hashrate detected but restart cooldown is still active.")
        return

    msg = (
        f"⚠️ Hashrate is too low after startup window ({HASHRATE_CHECK_DELAY_MINUTES} min). "
        f"Wallet={wallet}, measured={hashrate_hs:.1f} H/s. Restarting miner."
    )
    print(msg)
    send_telegram_message(msg)
    if is_rpi and GPIO_AVAILABLE:
        press_power_button(16, 10)
        time.sleep(15)
        press_power_button(16, 0.55)
        _last_hashrate_restart_at = now
        _hashrate_low_streak = 0
        save_prev_state(prev_state, now)
        send_telegram_message("✅ Hashrate guard restart sequence completed.")

def check_crypto_production_conditions(data, weather_api_key, location_lat, location_lon):
    global prev_state, state, used_quote, sunrise, sunset, uptime, _last_production_start_at
    global _pending_transition_state, _pending_transition_since, _pending_transition_hits
    prev_state, uptime = load_prev_state()

    try:
        (current_condition, sunrise, sunset, clouds,
         f1_cond, f1_clouds, f1_ts,
         f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(weather_api_key, location_lat, location_lon)

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
        battery_voltage = _find_first_value(
            dl,
            ["BMS_B_V1", "B_V1", "BMS_V", "BMS_U", "BAT_V", "BAT_U", "BMS Voltage", "Battery Voltage"],
            BATTERY_NOMINAL_V,
        )
        battery_ah = _find_first_value(
            dl,
            ["BRC", "Battery Rated Capacity", "BMS_B_AH", "B_AH"],
            BATTERY_CAPACITY_AH,
        )

        # per-phase inverter outputs (W)
        inv_l1 = _find_value(dl, "INV_O_P_L1", 0.0)
        inv_l2 = _find_value(dl, "INV_O_P_L2", 0.0)
        inv_l3 = _find_value(dl, "INV_O_P_L3", 0.0)
        inv_lt = _find_value(dl, "INV_O_P_T", 0.0)

        print(f"Battery charge: {battery_charge}%")
        print(f"Current production (PV total): {current_power}W")
        print(f"Inverter output per phase: L1={int(inv_l1)}W, L2={int(inv_l2)}W, L3={int(inv_l3)}W, Total={int(inv_lt)}W")
        print(f"Internal Power: {internal_power}W")
        print(f"Battery voltage: {battery_voltage:.2f}V")
        print(f"Battery capacity: {battery_ah:.2f}Ah")

        now = datetime.now(tz=budapest_tz)
        hist = _history_recommendation(now, battery_charge, current_power, sunrise, sunset, weather_outlook)
        print(
            "[History tuning] "
            f"month={hist['month_quality']} early_start_soc={hist['early_start_soc']}% "
            f"min_stop_soc={hist['min_stop_soc']}% late_reserve={hist['late_day_reserve_soc']}% "
            f"headroom_good={hist['headroom_good']} preserve={hist['should_preserve_battery']} "
            f"telem_q={hist.get('telemetry_month_quality', 'neutral')} samples={hist.get('telemetry_samples', 0)} "
            f"conf={float(hist.get('telemetry_confidence', 0.0)):.2f} blended_midday={float(hist.get('blended_midday_pv', 0.0)):.0f}W "
            f"full_eta_min={hist.get('predicted_minutes_to_full')} "
            f"wx5={hist.get('weather_risk_5d', 'unknown')} "
            f"wx_conf={float(hist.get('weather_confidence', 0.0)):.2f}"
        )
        start_guard = _compute_start_bridge_guard(now, battery_charge, current_power, sunrise, sunset, hist, battery_voltage, battery_ah)
        print(
            "[Start guard] "
            f"allow={start_guard['allow_start']} reason={start_guard['reason']} "
            f"capacity={start_guard['capacity_wh']}Wh ({start_guard['battery_ah']}Ah @ {start_guard['battery_voltage']}V) "
            f"usable_wh={start_guard['usable_wh']}Wh deficit={start_guard['deficit_w']}W bridge={start_guard['bridge_minutes']}min eta={start_guard['eta_minutes']}min"
        )
        hist.update({
            "start_guard_allow": bool(start_guard.get("allow_start", False)),
            "start_guard_reason": str(start_guard.get("reason", "unknown")),
            "start_guard_bridge_minutes": float(start_guard.get("bridge_minutes", 0.0)),
            "start_guard_eta_minutes": float(start_guard.get("eta_minutes", 0.0)),
            "start_guard_capacity_wh": float(start_guard.get("capacity_wh", 0.0)),
            "start_guard_battery_ah": float(start_guard.get("battery_ah", 0.0)),
            "start_guard_battery_voltage": float(start_guard.get("battery_voltage", 0.0)),
            "start_guard_usable_wh": float(start_guard.get("usable_wh", 0.0)),
            "start_guard_soc_window_pct": float(start_guard.get("soc_window_pct", 0.0)),
            "start_guard_min_stop_soc": float(start_guard.get("min_stop_soc", 0.0)),
            "start_guard_bms_floor_soc": float(start_guard.get("bms_floor_soc", 20.0)),
            "start_guard_bms_window_wh": float(start_guard.get("bms_window_wh", 0.0)),
            "start_guard_needed_bridge_minutes": float(start_guard.get("needed_bridge_minutes", 0.0)),
            "start_guard_needed_bridge_wh": float(start_guard.get("needed_bridge_wh", 0.0)),
        })

        solar_keywords = [
            'sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds',
            'partly cloudy', 'mostly sunny', 'sunshine', 'sunrise', 'sunset'
        ]
        non_solar_keywords = [
            'rain', 'storm', 'thunder', 'snow', 'fog', 'haze',
            'sleet', 'blizzard', 'dust', 'sand', 'ash', 'drizzle', 'shower', 'mist', 'smoke',
            'tornado', 'hurricane', 'squall', 'lightning', 'moderate rain', 'heavy intensity rain', 'overcast'
        ]

        cond_now = str(current_condition).lower()
        cond_f1 = str(f1_cond).lower()
        cond_f3 = str(f3_cond).lower()
        solar_now = any(k in cond_now for k in solar_keywords)
        solar_f1 = any(k in cond_f1 for k in solar_keywords)
        solar_f3 = any(k in cond_f3 for k in solar_keywords)
        non_solar_now = any(k in cond_now for k in non_solar_keywords)
        non_solar_f1 = any(k in cond_f1 for k in non_solar_keywords)
        non_solar_f3 = any(k in cond_f3 for k in non_solar_keywords)

        confident_sunny_bridge_start = (
            bool(hist.get("refill_confident_morning", False))
            and bool(hist.get("can_refill_before_sunset", False))
            and bool(start_guard.get("energy_cover_ok", False))
            and battery_charge >= (hist["min_stop_soc"] + 4)
            and solar_now and solar_f1 and solar_f3
            and not non_solar_now and not non_solar_f1 and not non_solar_f3
            and now.hour < 11
        )
        if confident_sunny_bridge_start and not start_guard.get("allow_start", False):
            start_guard["allow_start"] = True
            start_guard["reason"] = "bridge_energy_confident_sunny_day_relaxation"

        summer_clear_day = (
            now.month in (5, 6, 7, 8)
            and solar_now and solar_f1 and solar_f3
            and not non_solar_now and not non_solar_f1 and not non_solar_f3
        )
        summer_fast_start = (
            summer_clear_day
            and battery_charge > hist["min_stop_soc"]
            and bool(start_guard.get("energy_cover_ok", False))
        )

        aggressive_morning_refill_start = (
            now.hour < 10
            and battery_charge >= max(hist["min_stop_soc"] + 10, 42)
            and bool(hist.get("can_refill_before_sunset", False))
            and _safe_float(hist.get("predicted_minutes_to_full"), 9999) <= 240
            and solar_now and solar_f1 and solar_f3
            and not non_solar_now and not non_solar_f1 and not non_solar_f3
            and str(hist.get("weather_risk_5d", "unknown")).lower() != "solar_weak"
            and current_power >= max(150.0, MINER_POWER_W * 0.15)
        )
        if aggressive_morning_refill_start and not start_guard.get("allow_start", False):
            start_guard["allow_start"] = True
            start_guard["reason"] = "aggressive_morning_refill_start"

        # Intelligent real-time start: require meaningful PV headroom and seasonal SOC discipline.
        # This prevents autumn/winter starts from eating into battery recharge.
        month_quality = str(hist.get("month_quality", "neutral")).lower()
        weather_risk_5d = str(hist.get("weather_risk_5d", "unknown")).lower()
        season_margin_w = 50 if month_quality == "strong" else (180 if month_quality == "neutral" else 350)
        if weather_risk_5d == "solar_weak":
            season_margin_w += 140
        elif weather_risk_5d == "solar_friendly":
            season_margin_w = max(30, season_margin_w - 40)
        season_soc_floor = (
            max(hist["min_stop_soc"] + 4, hist["early_start_soc"] - 6)
            if month_quality == "strong"
            else (max(hist["early_start_soc"] - 2, 52) if month_quality == "neutral" else max(hist["early_start_soc"], 68))
        )
        if weather_risk_5d == "solar_weak":
            season_soc_floor = max(season_soc_floor, hist["min_stop_soc"] + 12)
        season_time_ok = now.hour < (15 if month_quality == "strong" else (14 if month_quality == "neutral" else 12))
        if weather_risk_5d == "solar_weak":
            season_time_ok = season_time_ok and now.hour < 12
        smart_bridge_pv_start = (
            bool(start_guard.get("allow_start", False))
            and current_power >= (MINER_POWER_W + season_margin_w)
            and battery_charge >= season_soc_floor
            and season_time_ok
            and not hist.get("should_preserve_battery", False)
        )
        predictive_early_start = (
            bool(start_guard.get("allow_start", False))
            and bool(hist.get("can_refill_before_sunset", False))
            and weather_risk_5d in {"solar_friendly", "mixed"}
            and now.hour < 12
            and battery_charge >= (hist["min_stop_soc"] + 6)
            and current_power >= max(120.0, MINER_POWER_W * 0.10)
        )

        start_rule_hits: List[str] = []
        stop_rule_hits: List[str] = []
        pv_start_threshold = max(150.0, MINER_POWER_W * PV_COVERAGE_RATIO_START)
        pv_stop_threshold = max(150.0, MINER_POWER_W * PV_COVERAGE_RATIO_STOP)
        pv_covers_miner = current_power >= pv_stop_threshold

        start_rules = [
            ("Summer clear-day fast start: usable bridge energy covers needed bridge energy", summer_fast_start),
            ("Confident sunny-day bridge start: PV can be 0W if bridge energy is enough (before 11h)", confident_sunny_bridge_start),
            ("Aggressive morning refill start: battery can still refill before sunset", aggressive_morning_refill_start),
            (
                "Bridge guard OK + PV headroom + seasonal SOC/time gate",
                smart_bridge_pv_start,
            ),
            ("Predictive early start: refill before sunset is likely", predictive_early_start),
            ("Sunny+1H forecast, PV>0, SOC>=early_start, before 13h", solar_now and solar_f1 and current_power > 0 and battery_charge >= hist["early_start_soc"] and now.hour < 13),
            (f"Sunny+1H forecast, PV>={pv_start_threshold:.0f}W, SOC>=65, before 13h", solar_now and solar_f1 and current_power >= pv_start_threshold and battery_charge >= 65 and now.hour < 13),
            (f"Sunny+1H forecast, PV>={pv_start_threshold:.0f}W, SOC>=55, before 12h", solar_now and solar_f1 and current_power >= pv_start_threshold and battery_charge >= 55 and now.hour < 12),
            (f"Sunny+1H forecast, PV>={pv_start_threshold:.0f}W, SOC>=35, before 11h", solar_now and solar_f1 and current_power >= pv_start_threshold and battery_charge >= 35 and now.hour < 11),
            ("Bridge-friendly morning start: SOC>=min_stop+12 and PV>=450W before 11h", battery_charge >= (hist["min_stop_soc"] + 12) and current_power >= 450 and now.hour < 11),
            ("Sunny+3H forecast, PV>0, SOC>=early_start, before 13h", solar_now and solar_f3 and current_power > 0 and battery_charge >= hist["early_start_soc"] and now.hour < 13),
            (f"Sunny+3H forecast, PV>={pv_start_threshold:.0f}W, SOC>=65, before 13h", solar_now and solar_f3 and current_power >= pv_start_threshold and battery_charge >= 65 and now.hour < 13),
            (f"Sunny+3H forecast, PV>={pv_start_threshold:.0f}W, SOC>=55, before 12h", solar_now and solar_f3 and current_power >= pv_start_threshold and battery_charge >= 55 and now.hour < 12),
            (f"Sunny+3H forecast, PV>={pv_start_threshold:.0f}W, SOC>=35, before 11h", solar_now and solar_f3 and current_power >= pv_start_threshold and battery_charge >= 35 and now.hour < 11),
            ("Historical headroom good + SOC>=early_start, before 14h", hist["headroom_good"] and battery_charge >= hist["early_start_soc"] and now.hour < 14),
            ("SOC>=60 and PV>=2500W, before 11h", battery_charge >= 60 and current_power >= 2500 and now.hour < 11),
            ("SOC>=70 and PV>=2250W, before 12h", battery_charge >= 70 and current_power >= 2250 and now.hour < 12),
            ("SOC>=80 and PV>=2000W, before 13h", battery_charge >= 80 and current_power >= 2000 and now.hour < 13),
            ("SOC>=40 and PV>=3000W, before 14h", battery_charge >= 40 and current_power >= 3000 and now.hour < 14),
            (f"SOC>{BATTERY_PROTECT_SOC:.0f}% and PV>={pv_start_threshold:.0f}W", battery_charge > BATTERY_PROTECT_SOC and current_power >= pv_start_threshold),
        ]
        for label, ok in start_rules:
            if ok:
                start_rule_hits.append(label)

        stop_battery_rules = [
            ("Battery below minimum stop SOC while running", prev_state == "production" and battery_charge < hist["min_stop_soc"]),
            ("Late-day reserve protection (after 14h)", prev_state == "production" and now.hour > 14 and battery_charge < hist["late_day_reserve_soc"]),
            ("Historical preserve-battery flag while running", prev_state == "production" and hist["should_preserve_battery"]),
        ]
        for label, ok in stop_battery_rules:
            if ok:
                stop_rule_hits.append(label)

        curtailment_prevent_window = (
            prev_state == "production"
            and now.hour < 17
            and battery_charge >= 96
            and current_power >= max(350.0, MINER_POWER_W * 0.35)
        )
        minutes_to_sunset = _safe_float((sunset - now).total_seconds() / 60.0, -1.0) if isinstance(sunset, datetime) else -1.0
        eta_to_full_min = _safe_float(hist.get("predicted_minutes_to_full"), -1.0)
        eta_exceeds_daylight_low_soc_while_running = (
            prev_state == "production"
            and eta_to_full_min >= 0.0
            and minutes_to_sunset >= 0.0
            and eta_to_full_min > minutes_to_sunset
            and battery_charge < 90.0
        )
        cannot_refill_before_sunset_while_running = (
            prev_state == "production"
            and eta_to_full_min >= 0.0
            and not bool(hist.get("can_refill_before_sunset", False))
            and _safe_float(hist.get("sunset_margin_minutes"), 0.0) < -5.0
            and not curtailment_prevent_window
        )

        stop_runtime_rules = [
            (
                "ETA to 100% exceeds remaining daylight while SOC<90% (force stop protection)",
                eta_exceeds_daylight_low_soc_while_running,
            ),
            (
                f"Battery<{BATTERY_PROTECT_SOC:.0f}% and PV<{pv_stop_threshold:.0f}W (insufficient solar cover) while running",
                prev_state == "production" and battery_charge < BATTERY_PROTECT_SOC and not pv_covers_miner and not curtailment_prevent_window,
            ),
            (
                "Predicted full charge is after sunset while running (sunset refill protection)",
                cannot_refill_before_sunset_while_running,
            ),
            ("Late-day reserve reached (after 14h, while running)", prev_state == "production" and now.hour >= 14 and battery_charge <= hist["late_day_reserve_soc"] and not curtailment_prevent_window),
            (
                f"High-SOC bridge drained (SOC<{HIGH_SOC_STOP_SOC:.0f}% and PV<={HIGH_SOC_STOP_MAX_PV_W:.0f}W while running)",
                prev_state == "production" and battery_charge < HIGH_SOC_STOP_SOC and current_power <= HIGH_SOC_STOP_MAX_PV_W and not curtailment_prevent_window,
            ),
            ("PV <= 150W", current_power <= 150 and not curtailment_prevent_window),
            ("Current weather non-solar + battery<=95 + PV<=1000W", non_solar_now and battery_charge <= 95 and current_power <= 1000 and not curtailment_prevent_window),
            ("1H forecast non-solar + battery<=95 + PV<=1000W", non_solar_f1 and battery_charge <= 95 and current_power <= 1000 and not curtailment_prevent_window),
            ("3H forecast non-solar + battery<=95 + PV<=1000W", non_solar_f3 and battery_charge <= 95 and current_power <= 1000 and not curtailment_prevent_window),
            ("Historical preserve-battery after 14h", hist["should_preserve_battery"] and now.hour >= 14 and not curtailment_prevent_window),
            ("5-day weather risk is solar_weak + PV<70% miner", weather_risk_5d == "solar_weak" and current_power < (MINER_POWER_W * 0.7) and not curtailment_prevent_window),
        ]

        decision_summary = "No state change"
        decision_state = state or "unknown"

        # Optional ping supervision
        if is_rpi and _should_run_miner_ping_check(now, min_interval_minutes=3):
            check_uptime(now, prev_state)

        # HARD RULE: after configured afternoon hour, SOC under threshold must stop immediately.
        # This is intentionally unconditional and bypasses forecast/curtailment relaxations.
        if now.hour >= HARD_AFTERNOON_STOP_HOUR and battery_charge < HARD_AFTERNOON_STOP_SOC:
            stop_rule_hits = [f"Hard afternoon cutoff: SOC<{HARD_AFTERNOON_STOP_SOC:.0f}% after {HARD_AFTERNOON_STOP_HOUR}:00"]
            decision_summary = "STOP: hard afternoon SOC cutoff"
            print("Hard afternoon SOC cutoff triggered → forcing STOP.")
            state = "stop"
            decision_state = state
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
            hist.update({
                "decision_state": decision_state,
                "decision_start_rules": start_rule_hits,
                "decision_stop_rules": stop_rule_hits,
                "decision_summary": decision_summary,
            })
            if state != prev_state:
                prev_state = state
                save_prev_state(prev_state, now)
                send_telegram_message(
                    f""" Production stopped (hard afternoon SOC cutoff).
________________________________
________________________________
 Battery: {battery_charge}%
 Current power: {current_power}W
 Rule: SOC<{HARD_AFTERNOON_STOP_SOC:.0f}% after {HARD_AFTERNOON_STOP_HOUR}:00
________________________________
 Weather: {current_condition}
 Temperature: {temperature}
 Humidity: {humidity}%
"""
                )
            return (battery_charge, current_power, state, current_condition, sunrise, sunset, clouds,
                    f1_cond, f1_clouds, f1_ts,
                    f3_cond, f3_clouds, f3_ts, hist)

        # IMMEDIATE POWER-BASED STOP RULE MINER IS ON L2 and L3
        if (inv_l2 > 2500) or (inv_l3 > 2500) or (inv_lt > 5000):
            stop_rule_hits = ["Power safety threshold exceeded (L2/L3/Total inverter output)"]
            decision_summary = "STOP: power safety"
            print("Power safety threshold exceeded → Crypto production over (STOP).")
            state = "stop"
            decision_state = state
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
            hist.update({
                "decision_state": decision_state,
                "decision_start_rules": start_rule_hits,
                "decision_stop_rules": stop_rule_hits,
                "decision_summary": decision_summary,
            })
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
        matched_runtime_stops = [label for label, ok in stop_runtime_rules if ok]

        if stop_rule_hits:
            print("Battery emergency shutdown.")
            decision_summary = "STOP: battery protection"
            state = "stop"
            decision_state = state
            if prev_state == "production":
                print("Trying to press power button.")
                if state != prev_state:
                    prev_state = state
                    uptime = now
                    save_prev_state(prev_state, uptime)
                if is_rpi:
                    press_power_button(16, 0.55)
        elif matched_runtime_stops:
            stop_rule_hits = matched_runtime_stops
            decision_summary = "STOP: runtime stop rules satisfied"
            print("Crypto production over.")
            state = "stop"
            decision_state = state
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
        elif start_guard["allow_start"] and start_rule_hits:
            print("Crypto production ready!")
            decision_summary = "START: start rules satisfied"
            state = "production"
            decision_state = state
            if prev_state == "stop":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.55)
        elif (not start_guard["allow_start"]) and prev_state != "production":
            print("Start trigger blocked by battery bridge guard.")
            decision_summary = "STOP: bridge guard blocked start"
            stop_rule_hits = [f"Start guard blocked start ({start_guard.get('reason', 'unknown')})"]
            state = "stop"
            decision_state = state
        else:
            print("No change!")

        # Debounce non-emergency transitions to avoid flip-flop on short weather/PV noise.
        emergency_stop = decision_summary in {"STOP: battery protection", "STOP: power safety"}
        desired_state = state or prev_state or "stop"
        stable_prev_state = prev_state or "stop"
        if not emergency_stop:
            confirmation_needed = 2 if desired_state == "production" else 3
            min_hold_minutes = 10 if desired_state == "production" else 12

            if desired_state == stable_prev_state:
                _pending_transition_state = None
                _pending_transition_since = None
                _pending_transition_hits = 0
                transition_confirmed = True
            else:
                if _pending_transition_state != desired_state:
                    _pending_transition_state = desired_state
                    _pending_transition_since = now
                    _pending_transition_hits = 1
                else:
                    _pending_transition_hits += 1
                pending_age_min = (
                    (now - _pending_transition_since).total_seconds() / 60.0
                    if isinstance(_pending_transition_since, datetime) else 0.0
                )
                transition_confirmed = (
                    _pending_transition_hits >= confirmation_needed
                    and pending_age_min >= min_hold_minutes
                )

            effective_state, blocked, gate_reason = _apply_transition_guard(
                stable_prev_state, desired_state, now, confirmed=transition_confirmed
            )
            if blocked and effective_state != desired_state:
                state = effective_state
                decision_state = state
                decision_summary = f"HOLD: transition guard blocked ({gate_reason})"
                if desired_state == "production":
                    stop_rule_hits = stop_rule_hits or [f"Start delayed by transition guard ({gate_reason})"]
                else:
                    start_rule_hits = start_rule_hits or [f"Stop delayed by transition guard ({gate_reason})"]
            else:
                state = effective_state
                decision_state = state
                if state == desired_state:
                    _pending_transition_state = None
                    _pending_transition_since = None
                    _pending_transition_hits = 0

        hist.update({
            "decision_state": decision_state,
            "decision_start_rules": start_rule_hits,
            "decision_stop_rules": stop_rule_hits,
            "decision_summary": decision_summary,
        })

        if state == "production" and prev_state != "production":
            _last_production_start_at = now
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
            _last_production_start_at = None
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
        # Keep tuple arity stable for caller unpacking.
        now_fallback = datetime.now(tz=budapest_tz)
        safe_sunrise = sunrise if isinstance(sunrise, datetime) else now_fallback
        safe_sunset = sunset if isinstance(sunset, datetime) else now_fallback
        return (
            None, None, state, "unknown", safe_sunrise, safe_sunset, 0,
            "unknown", 0, "",
            "unknown", 0, "", {}
        )


def _load_telemetry_from_file() -> int:
    """Load persisted telemetry points into in-memory deque at startup."""
    candidates = [TELEMETRY_FILE, TELEMETRY_BACKUP_FILE]

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

            for item in payload:
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
        telemetry_history.extend(sorted_hist)

        # Heal/seed both telemetry stores so restarts always have a consistent source.
        _write_full_telemetry_history(telemetry_history)

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
        "weather_risk_5d": str((historical_hints or {}).get("weather_risk_5d", "unknown")),
        "weather_sunny_ratio_5d": float((historical_hints or {}).get("weather_sunny_ratio_5d", 0.0)),
        "weather_bad_ratio_5d": float((historical_hints or {}).get("weather_bad_ratio_5d", 0.0)),
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
    _persist_telemetry_record_to_file(TELEMETRY_FILE, record)
    if TELEMETRY_BACKUP_FILE != TELEMETRY_FILE:
        _persist_telemetry_record_to_file(TELEMETRY_BACKUP_FILE, record)


def _persist_telemetry_record_to_file(target_file: Path, record: Dict[str, Any]) -> None:
    try:
        target_file.parent.mkdir(parents=True, exist_ok=True)

        existing: List[Dict[str, Any]] = []
        if target_file.exists():
            try:
                with target_file.open("r", encoding="utf-8") as fh:
                    payload = json.load(fh)
                if isinstance(payload, list):
                    existing = payload
            except Exception as err:
                print(f"[Telemetry] Could not read telemetry file {target_file}, recreating: {err}")

        existing.append(record)
        tmp_file = target_file.with_suffix(target_file.suffix + ".tmp")
        with tmp_file.open("w", encoding="utf-8") as fh:
            json.dump(existing, fh, ensure_ascii=False)
        tmp_file.replace(target_file)
    except Exception as err:
        print(f"[Telemetry] Failed to persist record into {target_file}: {err}")


def _write_full_telemetry_history(history: deque) -> None:
    payload = list(history)
    for target_file in {TELEMETRY_FILE, TELEMETRY_BACKUP_FILE}:
        try:
            target_file.parent.mkdir(parents=True, exist_ok=True)
            tmp_file = target_file.with_suffix(target_file.suffix + ".tmp")
            with tmp_file.open("w", encoding="utf-8") as fh:
                json.dump(payload, fh, ensure_ascii=False)
            tmp_file.replace(target_file)
        except Exception as err:
            print(f"[Telemetry] Failed to sync telemetry history into {target_file}: {err}")


def _miner_action(action: str) -> Dict[str, Any]:
    now = datetime.now(tz=budapest_tz).isoformat()
    duration = 0.55
    if action == "force_stop":
        duration = 10
    if action not in {"start", "stop", "force_stop"}:
        return {"ok": False, "message": "invalid action", "ts": now}

    if not is_rpi:
        msg = "GPIO unavailable (not Raspberry Pi runtime)"
        _push_web_notification(f"❌ {action}: {msg}", level="error")
        return {"ok": False, "message": msg, "ts": now}

    try:
        with gpio_lock:
            press_power_button(16, duration)
        msg = f"{action} signal sent ({duration}s)"
        _push_web_notification(f"✅ GUI action: {msg}", level="success")
        send_telegram_message_async(f"GUI action: {msg}", max_retries=4, keyboard=True, mirror_web=False)
        return {"ok": True, "message": msg, "ts": now}
    except Exception as err:
        err_msg = str(err)
        _push_web_notification(f"❌ {action}: {err_msg}", level="error")
        return {"ok": False, "message": err_msg, "ts": now}


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
input[type="date"]{appearance:none;-webkit-appearance:none;background:linear-gradient(180deg,rgba(255,255,255,.12),rgba(255,255,255,.04));border:1px solid rgba(148,163,184,.45);box-shadow:inset 0 1px 0 rgba(255,255,255,.18),0 8px 18px rgba(2,6,23,.22);font-weight:700;letter-spacing:.02em;color:var(--txt);min-height:42px;color-scheme:dark;padding-right:36px}
[data-theme="light"] input[type="date"]{background:linear-gradient(180deg,#ffffff,#eef4ff);border-color:rgba(71,85,105,.28);box-shadow:inset 0 1px 0 rgba(255,255,255,.8),0 6px 14px rgba(15,23,42,.08);color-scheme:light}
input[type="date"]:hover{border-color:rgba(96,165,250,.75)}
input[type="date"]:focus{outline:none;border-color:#60a5fa;box-shadow:0 0 0 3px rgba(96,165,250,.25),0 10px 22px rgba(59,130,246,.2)}
input[type="date"]::-webkit-calendar-picker-indicator{opacity:0;cursor:pointer}
.field-date{position:relative}
.field-date .calendar-icon{position:absolute;right:12px;bottom:12px;color:rgba(226,232,240,.95);font-size:.92rem;pointer-events:none;text-shadow:0 1px 2px rgba(2,6,23,.65)}
[data-theme="light"] .field-date .calendar-icon{color:#334155;text-shadow:none}
.actions{display:flex;gap:8px;flex-wrap:wrap}
.btn{color:#fff;cursor:pointer;background:transparent;padding:7px 11px;font-size:.84rem;min-height:34px;line-height:1.2;transition:transform .15s ease,box-shadow .15s ease,opacity .15s ease}
.btn:hover{transform:translateY(-1px);box-shadow:0 6px 16px rgba(2,6,23,.24)}
.btn:disabled{opacity:.6;cursor:not-allowed;transform:none;box-shadow:none}
.btn.ok{background:var(--ok)}.btn.warn{background:var(--warn)}.btn.danger{background:var(--danger)}.btn.ghost{background:transparent;color:var(--txt)}
.toolbar-actions{justify-content:flex-end;align-items:center}
.range-shortcuts{display:flex;gap:6px;flex-wrap:wrap}
.range-shortcuts .btn{font-size:.8rem;min-height:30px;padding:6px 10px}
#actionResult{margin-top:8px;min-height:22px;padding:6px 10px;border-radius:10px;border:1px solid transparent;display:none}
#actionResult.show{display:flex;align-items:center;gap:8px}
#actionResult.ok{background:rgba(34,197,94,.14);border-color:rgba(34,197,94,.42);color:#86efac}
#actionResult.warn{background:rgba(245,158,11,.14);border-color:rgba(245,158,11,.42);color:#facc15}
#actionResult.err{background:rgba(239,68,68,.14);border-color:rgba(239,68,68,.45);color:#fda4af}
[data-theme="light"] #actionResult.ok{color:#166534}
[data-theme="light"] #actionResult.warn{color:#92400e}
[data-theme="light"] #actionResult.err{color:#991b1b}
.notice-panel{margin-top:8px}
.notice-head{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px}
.notice-list{display:grid;gap:8px;max-height:200px;overflow:auto;padding-right:4px}
.notice-item{border:1px solid var(--border);border-radius:10px;padding:8px 10px;background:rgba(255,255,255,.03)}
.notice-item.warn{border-color:rgba(245,158,11,.5)}
.notice-item.error{border-color:rgba(239,68,68,.5)}
.notice-item.success{border-color:rgba(34,197,94,.48)}
.notice-meta{font-size:.74rem;color:var(--muted);margin-bottom:4px}
.notice-empty{font-size:.82rem;color:var(--muted);padding:10px;border:1px dashed var(--border);border-radius:10px}
.charts{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.chart-card{height:360px;display:flex;flex-direction:column;overflow:hidden}
.chart-card canvas{width:100% !important;flex:1 1 auto;min-height:0}
.hints-panel{padding:16px}
.hints-wrap{width:min(1280px,100%);margin:0 auto;display:grid;grid-template-columns:repeat(2,minmax(340px,1fr));gap:16px;align-items:start}
.hints-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.hint-section-title{margin:0 0 10px;font-size:.86rem;letter-spacing:.03em;text-transform:uppercase;color:var(--muted);font-weight:700;text-align:center}
.hint-card{background:linear-gradient(165deg,rgba(99,102,241,.18),rgba(14,165,233,.12));border:1px solid var(--border);border-radius:16px;padding:14px;box-shadow:0 12px 26px rgba(2,6,23,.2);min-height:112px;display:flex;flex-direction:column;justify-content:center}
.hint-title{font-size:.8rem;color:var(--muted);margin-bottom:8px;display:flex;align-items:center;gap:8px}
.hint-value{font-size:1.15rem;font-weight:800;line-height:1.2}
.hint-sub{margin-top:6px;color:var(--muted);font-size:.8rem}
.decision-card{margin-top:12px;grid-column:1 / -1;min-height:170px;align-items:flex-start}
.hint-list{margin:6px 0 8px 16px;padding:0;color:var(--txt);font-size:.84rem;line-height:1.35}
.hint-list li{margin:2px 0}
@media(max-width:1100px){.charts{grid-template-columns:1fr}.hints-wrap{grid-template-columns:1fr}}
@media(max-width:840px){.toolbar{grid-template-columns:1fr}.chart-card{height:320px}.hints-grid{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media(max-width:560px){.hints-grid{grid-template-columns:1fr}}
</style></head>
<body data-theme="dark"><div class="wrap">
<div class="logo-wrap"><img class="logo" src="/solarmining_logo.png" alt="Solar Mining logo" /></div>
<div class="top"><h2 id="dashTitle" class="title"><i class="fa-solid fa-solar-panel"></i> Solar Mining Dashboard</h2>
<div class="actions"><button id="lang" class="btn ghost"><i class="fa-solid fa-earth-europe"></i> HU</button><button id="theme" class="btn warn"><i class="fa-solid fa-circle-half-stroke"></i> Theme</button><button id="downloadTelemetry" class="btn ghost"><i class="fa-solid fa-download"></i> Telemetry JSON</button></div></div>
<div class="grid metrics-grid" id="metrics"></div>
<div class="panel hints-panel"><div class="hints-wrap" id="historyHints"></div></div>
<div class="panel toolbar"><div class="filters">
<div class="field field-date"><label id="lblFrom" for="fromDate">From</label><input id="fromDate" type="date" /><i class="fa-solid fa-calendar-days calendar-icon"></i></div>
<div class="field field-date"><label id="lblTo" for="toDate">To</label><input id="toDate" type="date" /><i class="fa-solid fa-calendar-days calendar-icon"></i></div>
<div class="actions"><div class="range-shortcuts"><button class="btn ghost" id="shortcutDay"><i class="fa-solid fa-clock"></i> Last Day</button><button class="btn ghost" id="shortcutWeek"><i class="fa-solid fa-calendar-week"></i> Last Week</button><button class="btn ghost" id="shortcutMonth"><i class="fa-solid fa-calendar-days"></i> Last Month</button></div><button class="btn ok" id="applyRange"><i class="fa-solid fa-filter"></i> Apply range</button></div>
</div><div class="actions toolbar-actions">
<button id="btnStart" class="btn ok" onclick="act('start')"><i class="fa-solid fa-play"></i> Start miner</button>
<button id="btnStop" class="btn warn" onclick="act('stop')"><i class="fa-solid fa-stop"></i> Stop miner</button>
<button id="btnForce" class="btn danger" onclick="act('force_stop')"><i class="fa-solid fa-power-off"></i> Force stop</button>
</div></div>
<div id="actionResult" class="k"></div>
<div class="panel notice-panel"><div class="notice-head"><div id="notifTitle" class="chart-title"><i class="fa-solid fa-bell"></i> Notifications</div></div><div id="notifList" class="notice-list"></div></div>
<div class="charts"><div class="card chart-card"><div class="chart-head"><div id="chPower" class="chart-title"><i class="fa-solid fa-solar-panel"></i> PV Production</div><div id="chPowerSub" class="chart-sub">Watt trend</div></div><canvas id="powerChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chPhase" class="chart-title"><i class="fa-solid fa-bolt"></i> Phase Power</div><div id="chPhaseSub" class="chart-sub">L1 / L2 / L3</div></div><canvas id="phaseChart"></canvas></div>
<div class="card chart-card"><div class="chart-head"><div id="chBattery" class="chart-title"><i class="fa-solid fa-battery-three-quarters"></i> Battery & Mining Rig</div><div id="chBatterySub" class="chart-sub">Charge level and status</div></div><canvas id="batteryChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chEnv" class="chart-title"><i class="fa-solid fa-temperature-half"></i> Garage Environment</div><div id="chEnvSub" class="chart-sub">Temperature / Humidity</div></div><canvas id="envChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chHistSoc" class="chart-title"><i class="fa-solid fa-layer-group"></i> Historical SOC Thresholds</div><div id="chHistSocSub" class="chart-sub">Dynamic SOC logic over time</div></div><canvas id="histSocChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="chHistFlags" class="chart-title"><i class="fa-solid fa-chart-line"></i> Historical Decision Flags</div><div id="chHistFlagsSub" class="chart-sub">Battery preserve / headroom / month quality</div></div><canvas id="histFlagsChart"></canvas></div></div></div>
<script>
let powerChart,phaseChart,batteryChart,envChart,histSocChart,histFlagsChart;
const defaultLastDays=30;
let currentRange={from:null,to:null};
let currentLang='en';
const I18N={
  en:{title:'Solar Mining Dashboard',theme:'Theme',downloadTelemetry:'Telemetry JSON',from:'From',to:'To',lastDay:'Last Day',lastWeek:'Last Week',lastMonth:'Last Month',apply:'Apply range',start:'Start miner',stop:'Stop miner',force:'Force stop',actionInProgress:'Sending command…',actionStartOk:'Miner start command sent successfully.',actionStopOk:'Miner stop command sent successfully.',actionForceOk:'Force stop command sent successfully.',actionError:'Command failed',notifTitle:'Notifications',notifEmpty:'No notifications yet.',
      state:'State',battery:'Battery',pv:'PV Power',weather:'Weather',sunrise:'Sunrise',sunset:'Sunset',clouds:'Clouds',history:'History Points',
      chPower:'PV Production',chPowerSub:'Watt trend',chPhase:'Phase Power',chPhaseSub:'L1 / L2 / L3',chBattery:'Battery & Mining Rig',chBatterySub:'Charge level and status',chEnv:'Garage Environment',chEnvSub:'Temperature / Humidity',chHistSoc:'Historical SOC Thresholds',chHistSocSub:'Dynamic SOC logic over time',chHistFlags:'Historical Decision Flags',chHistFlagsSub:'Battery preserve / headroom / month quality',monthQuality:'Month quality',earlyStart:'Early start SOC',minStop:'Min stop SOC',lateReserve:'Late day reserve SOC',preserveBattery:'Preserve battery',headroomGood:'Headroom good',yes:'Yes',no:'No',strong:'Strong',weak:'Weak',neutral:'Neutral',langBtn:'HU',dsPv:'PV power (W)',dsL1:'L1',dsL2:'L2',dsL3:'L3',dsBatt:'Charge %',dsMiner:'Mining Rig ON',dsTemp:'Temp °C',dsHum:'Humidity %',dsHistEarly:'Early start SOC %',dsHistMinStop:'Min stop SOC %',dsHistLate:'Late reserve SOC %',dsFlagPreserve:'Preserve battery',dsFlagHeadroom:'Headroom good',dsFlagMonth:'Month quality score',hintHistoryTitle:'Historical tuning',hintDecisionTitle:'Decision trace',decisionState:'State decision',decisionStartRules:'Matched start rules',decisionStopRules:'Matched stop rules',decisionSummary:'Decision summary',decisionNone:'No matched rules',hintStartGuardTitle:'Start guard',startGuardAllow:'Start allowed',startGuardReason:'Reason',startGuardBridge:'Current bridge time',startGuardEta:'LTA (time to full solar supply)',startGuardFullEta:'ETA to 100% battery charge',startGuardCapacity:'Battery capacity',startGuardUsable:'Usable bridge energy (above min stop SOC)',neededBridgeTime:'Needed bridge time (sunrise → full supply)',neededBridgeEnergy:'Needed bridge energy (sunrise → full supply)',usableFormula:'Formula',bmsRange:'BMS range',reasonOk:'OK',reasonSocBelowMinStop:'SOC below minimum stop',reasonInsufficientBridgeEnergy:'Insufficient bridge energy',reasonCannotRefillBeforeSunset:'Likely cannot refill battery before sunset',reasonRefillRelaxation:'Confident refill relaxation',reasonRefillMorningRelaxation:'Confident morning refill relaxation',reasonBridgeEnergySunnyRelaxation:'Bridge-energy confident sunny-day relaxation',reasonAggressiveMorningRefillStart:'Aggressive morning refill start',unitMin:'min',unitWh:'Wh',stProduction:'production',stStop:'stop',stUnknown:'unknown'},
  hu:{title:'Solar Bányászat Dashboard',theme:'Téma',downloadTelemetry:'Telemetry JSON letöltése',from:'Ettől',to:'Eddig',lastDay:'Elmúlt nap',lastWeek:'Elmúlt hét',lastMonth:'Elmúlt hónap',apply:'Szűrés alkalmazása',start:'Bányászgép indítása',stop:'Bányászgép leállítása',force:'Kényszerleállítás',actionInProgress:'Parancs küldése…',actionStartOk:'Indítási parancs elküldve.',actionStopOk:'Leállítási parancs elküldve.',actionForceOk:'Kényszerleállítási parancs elküldve.',actionError:'Parancs hiba',notifTitle:'Értesítések',notifEmpty:'Még nincs értesítés.',
      state:'Állapot',battery:'Töltöttség',pv:'PV teljesítmény',weather:'Időjárás',sunrise:'Napkelte',sunset:'Napnyugta',clouds:'Felhőzet',history:'Előzményadatok',
      chPower:'PV termelés',chPowerSub:'Teljesítménytrend (W)',chPhase:'Fázisteljesítmény',chPhaseSub:'L1 / L2 / L3',chBattery:'Akkumulátor és bányászgép',chBatterySub:'Töltöttségi szint és állapot',chEnv:'Garázskörnyezet',chEnvSub:'Hőmérséklet / páratartalom',chHistSoc:'Történeti SOC-küszöbök',chHistSocSub:'Dinamikus SOC-logika időben',chHistFlags:'Történeti döntési jelzők',chHistFlagsSub:'Akkumulátorkímélés / tartalék / havi minőség',monthQuality:'Havi minőség',earlyStart:'Korai indítás SOC',minStop:'Minimum leállítási SOC',lateReserve:'Késői tartalék SOC',preserveBattery:'Akkumulátorkímélés',headroomGood:'Megfelelő teljesítménytartalék',yes:'Igen',no:'Nem',strong:'Erős',weak:'Gyenge',neutral:'Semleges',langBtn:'EN',dsPv:'PV teljesítmény (W)',dsL1:'L1',dsL2:'L2',dsL3:'L3',dsBatt:'Töltöttség %',dsMiner:'Bányászgép bekapcsolva',dsTemp:'Hőmérséklet °C',dsHum:'Páratartalom %',dsHistEarly:'Korai indítás SOC %',dsHistMinStop:'Minimum leállítási SOC %',dsHistLate:'Késői tartalék SOC %',dsFlagPreserve:'Akkumulátorkímélés',dsFlagHeadroom:'Megfelelő tartalék',dsFlagMonth:'Havi minőség pontszám',hintHistoryTitle:'Történeti finomhangolás',hintDecisionTitle:'Döntési logika',decisionState:'Állapotdöntés',decisionStartRules:'Teljesült indítási szabályok',decisionStopRules:'Teljesült leállítási szabályok',decisionSummary:'Döntés összegzése',decisionNone:'Nincs teljesült szabály',hintStartGuardTitle:'Indítási védelem',startGuardAllow:'Indítás engedélyezve',startGuardReason:'Indok',startGuardBridge:'Aktuális áthidalási idő',startGuardEta:'LTA (idő a teljes napellátásig)',startGuardFullEta:'Várható idő 100% akku töltésig',startGuardCapacity:'Akkumulátor kapacitás',startGuardUsable:'Felhasználható áthidaló energia (min. SOC felett)',neededBridgeTime:'Szükséges áthidalási idő (napkelte → teljes ellátás)',neededBridgeEnergy:'Szükséges áthidalási energia (napkelte → teljes ellátás)',usableFormula:'Képlet',bmsRange:'BMS tartomány',reasonOk:'Rendben',reasonSocBelowMinStop:'SOC minimum alatt',reasonInsufficientBridgeEnergy:'Nincs elég áthidaló energia',reasonCannotRefillBeforeSunset:'Várhatóan nem tölt vissza napnyugtáig',reasonRefillRelaxation:'Magabiztos visszatöltési lazítás',reasonRefillMorningRelaxation:'Magabiztos reggeli visszatöltési lazítás',reasonBridgeEnergySunnyRelaxation:'Bridge energia + napsütés miatti lazítás',reasonAggressiveMorningRefillStart:'Agresszív reggeli indítás (visszatöltés biztos)',unitMin:'perc',unitWh:'Wh',stProduction:'termelés',stStop:'leállítva',stUnknown:'ismeretlen'}
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
  document.getElementById('shortcutDay').innerHTML=`<i class="fa-solid fa-clock"></i> ${t('lastDay')}`;
  document.getElementById('shortcutWeek').innerHTML=`<i class="fa-solid fa-calendar-week"></i> ${t('lastWeek')}`;
  document.getElementById('shortcutMonth').innerHTML=`<i class="fa-solid fa-calendar-days"></i> ${t('lastMonth')}`;
  document.getElementById('applyRange').innerHTML=`<i class="fa-solid fa-filter"></i> ${t('apply')}`;
  document.getElementById('btnStart').innerHTML=`<i class="fa-solid fa-play"></i> ${t('start')}`;
  document.getElementById('btnStop').innerHTML=`<i class="fa-solid fa-stop"></i> ${t('stop')}`;
  document.getElementById('btnForce').innerHTML=`<i class="fa-solid fa-power-off"></i> ${t('force')}`;
  document.getElementById('notifTitle').innerHTML=`<i class="fa-solid fa-bell"></i> ${t('notifTitle')}`;
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
function formatDurationMinutes(mins){
const m=Number(mins);
if(!Number.isFinite(m)||m<0)return '--';
const total=Math.max(0,m);
let h=Math.floor(total/60);
let mm=Math.round(total-(h*60));
if(mm===60){h+=1;mm=0;}
return `${total.toFixed(1)} ${t('unitMin')} (${h}h ${mm}m)`;
}
function formatDate(d){return d.toISOString().slice(0,10)}
function setRangeDays(days){const to=new Date();const from=new Date();from.setDate(to.getDate()-days);document.getElementById('fromDate').value=formatDate(from);document.getElementById('toDate').value=formatDate(to);currentRange={from:document.getElementById('fromDate').value,to:document.getElementById('toDate').value};}
function setDefaultRange(){const to=new Date();const from=new Date();from.setDate(to.getDate()-defaultLastDays);document.getElementById('fromDate').value=formatDate(from);document.getElementById('toDate').value=formatDate(to);currentRange={from:document.getElementById('fromDate').value,to:document.getElementById('toDate').value};}
function showActionResult(msg,type='warn',details=''){
  const el=document.getElementById('actionResult');
  const icon=type==='ok'?'fa-circle-check':(type==='err'?'fa-triangle-exclamation':'fa-circle-info');
  const extra=details?` <span class='chart-sub'>${details}</span>`:'';
  el.className=`k show ${type}`;
  el.innerHTML=`<i class='fa-solid ${icon}'></i> <span>${msg}</span>${extra}`;
}
function renderNotifications(items){
  const box=document.getElementById('notifList');
  const list=Array.isArray(items)?items:[];
  if(!list.length){
    box.innerHTML=`<div class='notice-empty'>${t('notifEmpty')}</div>`;
    return;
  }
  box.innerHTML=list.slice(0,5).map((n)=>{
    const lvl=String(n.level||'info');
    const ts=n.ts?new Date(n.ts).toLocaleString():'';
    const icon=lvl==='success'?'fa-circle-check':(lvl==='warn'?'fa-triangle-exclamation':(lvl==='error'?'fa-circle-xmark':'fa-circle-info'));
    return `<div class='notice-item ${lvl}'><div class='notice-meta'><i class='fa-solid ${icon}'></i> ${ts}</div><div>${String(n.message||'')}</div></div>`;
  }).join('');
}
async function pull(){const qs=new URLSearchParams(currentRange).toString();const r=await fetch(`/api/snapshot?${qs}`);const d=await r.json();const icon=d.weather_icon||'fa-sun';
renderNotifications(d.notifications||[]);
const sunrise=(d.sunrise||'').slice(11,16); const sunset=(d.sunset||'').slice(11,16);
document.getElementById('metrics').innerHTML=`<div class='card'><div class='k'><i class='fa-solid fa-toggle-on'></i> ${t('state')}</div><div class='v'>${mapState(d.state)}</div></div><div class='card'><div class='k'><i class='fa-solid fa-battery-half'></i> ${t('battery')}</div><div class='v'>${d.battery}%</div></div><div class='card'><div class='k'><i class='fa-solid fa-solar-panel'></i> ${t('pv')}</div><div class='v'>${Math.round(d.power)} W</div></div><div class='card'><div class='k'><i class='fa-solid fa-cloud-sun'></i> ${t('weather')}</div><div class='v'><i class='fa-solid ${icon}'></i> ${localizeWeather(d.current_condition)}</div></div><div class='card'><div class='k'><i class='fa-solid fa-sun'></i> ${t('sunrise')}</div><div class='v'>${sunrise||'--:--'}</div></div><div class='card'><div class='k'><i class='fa-solid fa-moon'></i> ${t('sunset')}</div><div class='v'>${sunset||'--:--'}</div></div><div class='card'><div class='k'><i class='fa-solid fa-cloud'></i> ${t('clouds')}</div><div class='v'>${d.clouds}%</div></div><div class='card'><div class='k'><i class='fa-solid fa-clock-rotate-left'></i> ${t('history')}</div><div class='v'>${d.history_count}</div></div>`;
const h=d.history||[]; const labels=h.map(x=>shortTs(x.ts));
const hints=d.historical_hints||{};
const monthQ=String(hints.month_quality||'neutral');
const qText=t(monthQ==='strong'?'strong':(monthQ==='weak'?'weak':'neutral'));
const boolTxt=(v)=>v?t('yes'):t('no');
const reasonRaw=String(hints.start_guard_reason||'unknown');
const reasonMap={ok:'reasonOk',soc_below_min_stop:'reasonSocBelowMinStop',insufficient_bridge_energy:'reasonInsufficientBridgeEnergy',cannot_refill_before_sunset_guard:'reasonCannotRefillBeforeSunset',refill_confident_relaxation:'reasonRefillRelaxation',refill_confident_morning_relaxation:'reasonRefillMorningRelaxation',bridge_energy_confident_sunny_day_relaxation:'reasonBridgeEnergySunnyRelaxation',aggressive_morning_refill_start:'reasonAggressiveMorningRefillStart'};
const reasonTxt=t(reasonMap[reasonRaw]||reasonRaw);
const startGuardAllow=boolTxt(!!hints.start_guard_allow);
const bridgeMinutes=Number(hints.start_guard_bridge_minutes||0);
const etaMinutes=Number(hints.start_guard_eta_minutes||0);
const startGuardBridge=`${bridgeMinutes.toFixed(1)} ${t('unitMin')}`;
const startGuardEta=`${etaMinutes.toFixed(1)} ${t('unitMin')}`;
const predictedMinutesToFull=Number(hints.predicted_minutes_to_full);
const startGuardFullEta=formatDurationMinutes(predictedMinutesToFull);
const startGuardCapacity=`${Number(hints.start_guard_capacity_wh||0).toFixed(1)} ${t('unitWh')} (${Number(hints.start_guard_battery_ah||0).toFixed(1)}Ah @ ${Number(hints.start_guard_battery_voltage||0).toFixed(2)}V)`;
const startGuardUsable=`${Number(hints.start_guard_usable_wh||0).toFixed(1)} ${t('unitWh')}`;
const startGuardUsableFormula=`${Number(hints.start_guard_soc_window_pct||0).toFixed(0)}% = ${Number(d.battery||0).toFixed(0)}% - ${Number(hints.start_guard_min_stop_soc||0).toFixed(0)}%`;
const neededBridgeTime=`${Number(hints.start_guard_needed_bridge_minutes||0).toFixed(1)} ${t('unitMin')}`;
const neededBridgeEnergy=`${Number(hints.start_guard_needed_bridge_wh||0).toFixed(1)} ${t('unitWh')}`;
const neededBridgeBmsRange=`20-100% (${Number(hints.start_guard_bms_window_wh||0).toFixed(1)} ${t('unitWh')})`;
const decisionState=mapState(String(hints.decision_state||d.state||'unknown'));
const decisionSummary=String(hints.decision_summary||'').trim()||t('decisionNone');
const startRules=Array.isArray(hints.decision_start_rules)?hints.decision_start_rules:[];
const stopRules=Array.isArray(hints.decision_stop_rules)?hints.decision_stop_rules:[];
const renderRuleList=(arr)=>arr.length?`<ul class='hint-list'>${arr.map(x=>`<li>${String(x)}</li>`).join('')}</ul>`:`<div class='hint-sub'>${t('decisionNone')}</div>`;
const startGuardBridgeView=startGuardBridge;
const startGuardEtaView=startGuardEta;
document.getElementById('historyHints').innerHTML=`<div class='hint-section'><div class='hint-section-title'>${t('hintHistoryTitle')}</div><div class='hints-grid'><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-calendar-days'></i> ${t('monthQuality')}</div><div class='hint-value'>${qText}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-bolt'></i> ${t('earlyStart')}</div><div class='hint-value'>${Number(hints.early_start_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-circle-stop'></i> ${t('minStop')}</div><div class='hint-value'>${Number(hints.min_stop_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-hourglass-end'></i> ${t('lateReserve')}</div><div class='hint-value'>${Number(hints.late_day_reserve_soc||0).toFixed(0)}%</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-shield-heart'></i> ${t('preserveBattery')}</div><div class='hint-value'>${boolTxt(!!hints.should_preserve_battery)}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-gauge-high'></i> ${t('headroomGood')}</div><div class='hint-value'>${boolTxt(!!hints.headroom_good)}</div></div></div><div class='hint-card decision-card'><div class='hint-title'><i class='fa-solid fa-list-check'></i> ${t('hintDecisionTitle')}</div><div class='hint-sub'><strong>${t('decisionState')}:</strong> ${decisionState}</div><div class='hint-sub'><strong>${t('decisionSummary')}:</strong> ${decisionSummary}</div><div class='hint-sub'><strong>${t('decisionStartRules')}:</strong></div>${renderRuleList(startRules)}<div class='hint-sub'><strong>${t('decisionStopRules')}:</strong></div>${renderRuleList(stopRules)}</div></div><div class='hint-section'><div class='hint-section-title'>${t('hintStartGuardTitle')}</div><div class='hints-grid'><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-play-circle'></i> ${t('startGuardAllow')}</div><div class='hint-value'>${startGuardAllow}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-circle-info'></i> ${t('startGuardReason')}</div><div class='hint-value'>${reasonTxt}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-hourglass-start'></i> ${t('startGuardBridge')}</div><div class='hint-value'>${startGuardBridgeView}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-hourglass-half'></i> ${t('startGuardEta')}</div><div class='hint-value'>${startGuardEtaView}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-battery-full'></i> ${t('startGuardFullEta')}</div><div class='hint-value'>${startGuardFullEta}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-car-battery'></i> ${t('startGuardCapacity')}</div><div class='hint-value'>${startGuardCapacity}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-battery-three-quarters'></i> ${t('startGuardUsable')}</div><div class='hint-value'>${startGuardUsable}</div><div class='hint-sub'><strong>${t('usableFormula')}:</strong> ${startGuardUsableFormula}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-business-time'></i> ${t('neededBridgeTime')}</div><div class='hint-value'>${neededBridgeTime}</div><div class='hint-sub'><strong>${t('bmsRange')}:</strong> ${neededBridgeBmsRange}</div></div><div class='hint-card'><div class='hint-title'><i class='fa-solid fa-bolt-lightning'></i> ${t('neededBridgeEnergy')}</div><div class='hint-value'>${neededBridgeEnergy}</div><div class='hint-sub'><strong>${t('bmsRange')}:</strong> ${neededBridgeBmsRange}</div></div></div></div>`;
powerChart.data.labels=labels; powerChart.data.datasets[0].data=h.map(x=>x.power); powerChart.update();
phaseChart.data.labels=labels; phaseChart.data.datasets[0].data=h.map(x=>x.inv_l1); phaseChart.data.datasets[1].data=h.map(x=>x.inv_l2); phaseChart.data.datasets[2].data=h.map(x=>x.inv_l3); phaseChart.update();
batteryChart.data.labels=labels; batteryChart.data.datasets[0].data=h.map(x=>x.battery); batteryChart.data.datasets[1].data=h.map(x=>x.state==='production'?100:0); batteryChart.update();
envChart.data.labels=labels; envChart.data.datasets[0].data=h.map(x=>x.garage_temp); envChart.data.datasets[1].data=h.map(x=>x.garage_hum); envChart.update();
histSocChart.data.labels=labels; histSocChart.data.datasets[0].data=h.map(x=>Number(x.early_start_soc||0)); histSocChart.data.datasets[1].data=h.map(x=>Number(x.min_stop_soc||0)); histSocChart.data.datasets[2].data=h.map(x=>Number(x.late_day_reserve_soc||0)); histSocChart.update();
const mq=(m)=>m==='strong'?100:(m==='weak'?0:50);
histFlagsChart.data.labels=labels; histFlagsChart.data.datasets[0].data=h.map(x=>x.should_preserve_battery?100:0); histFlagsChart.data.datasets[1].data=h.map(x=>x.headroom_good?100:0); histFlagsChart.data.datasets[2].data=h.map(x=>mq(String(x.month_quality||'neutral'))); histFlagsChart.update();}
async function act(a){
  const buttons=['btnStart','btnStop','btnForce'].map(id=>document.getElementById(id));
  buttons.forEach(b=>b.disabled=true);
  showActionResult(t('actionInProgress'),'warn');
  try{
    const r=await fetch('/api/action',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:a})});
    const d=await r.json();
    const msgKey=a==='start'?'actionStartOk':(a==='stop'?'actionStopOk':'actionForceOk');
    const stamp=d.ts?new Date(d.ts).toLocaleString():'';
    if(d.ok){
      showActionResult(t(msgKey),'ok',`${d.message}${stamp?` · ${stamp}`:''}`);
    }else{
      showActionResult(`${t('actionError')}: ${d.message}`,'err',stamp);
    }
  }catch(err){
    showActionResult(`${t('actionError')}: ${String(err)}`,'err');
  }finally{
    buttons.forEach(b=>b.disabled=false);
  }
}
document.getElementById('applyRange').onclick=()=>{currentRange={from:document.getElementById('fromDate').value,to:document.getElementById('toDate').value};pull();};
document.getElementById('shortcutDay').onclick=()=>{setRangeDays(1);pull();};
document.getElementById('shortcutWeek').onclick=()=>{setRangeDays(7);pull();};
document.getElementById('shortcutMonth').onclick=()=>{setRangeDays(30);pull();};
document.getElementById('downloadTelemetry').onclick=()=>{window.location.href='/api/telemetry/download';};
init();applyI18n();pull();setInterval(pull,10000);document.getElementById('theme').onclick=()=>{document.body.dataset.theme=document.body.dataset.theme==='dark'?'light':'dark';};document.getElementById('lang').onclick=()=>{currentLang=currentLang==='en'?'hu':'en';applyI18n();pull();};
</script></body></html>
"""


def _build_snapshot_payload(from_date: Optional[str] = None, to_date: Optional[str] = None) -> Dict[str, Any]:
    with snapshot_lock:
        snap = dict(_shared_snapshot)
        hist = list(telemetry_history)
    notices = list(web_notifications)[:5]

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
        "notifications": notices,
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
     f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

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
                     f3_cond, f3_clouds, f3_ts, weather_outlook) = fut_weather.result(timeout=10)
                except Exception:
                    (current_condition, sunrise, sunset, clouds,
                     f1_cond, f1_clouds, f1_ts,
                     f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

                # Fetch device data (depends on token)
                raw_data = fetch_current_data(token) if token else {}
                data, used_previous_payload = _with_daytime_data_fallback(raw_data or {}, now, sunrise, sunset)
                store_data(data)  # attaches phasePowers

                (battery, power, state, current_condition, sunrise, sunset, clouds,
                f1_cond, f1_clouds, f1_ts, f3_cond, f3_clouds, f3_ts, hist_hints) = check_crypto_production_conditions(
                    data, WEATHER_API, LOCATION_LAT, LOCATION_LON
                )
                check_hashrate_guard(now, state or "unknown")

                has_usable_solarman_data = _has_solarman_payload(data)
                if not has_usable_solarman_data:
                    print("[Telemetry] Solarman dataList is empty for this cycle; saving fallback telemetry row.")
                elif used_previous_payload:
                    print("[Telemetry] API payload empty during daytime; telemetry uses previous valid Solarman snapshot.")
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
                        "inv_l1": float(_find_value((data or {}).get("dataList", []), "INV_O_P_L1", 0.0)),
                        "inv_l2": float(_find_value((data or {}).get("dataList", []), "INV_O_P_L2", 0.0)),
                        "inv_l3": float(_find_value((data or {}).get("dataList", []), "INV_O_P_L3", 0.0)),
                        "inv_lt": float(_find_value((data or {}).get("dataList", []), "INV_O_P_T", 0.0)),
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
             f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

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

            # Safety ping supervision must also run during sleep/idle window.
            # If any configured IP replies while stop is expected, force shutdown is executed.
            if is_rpi and _should_run_miner_ping_check(now, min_interval_minutes=3):
                check_uptime(now, prev_state)

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
                    "inv_l1": 0, "inv_l2": 0, "inv_l3": 0, "inv_lt": 0,
                    "historical_hints": _idle_historical_hints()
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
