import requests
from status_messages import status as telegram_status, phases as telegram_phases
from power_measurement import PowerSample
from miner_ping_guard import MinerPingGuard, ping_host
from history_model import load_exports, build_weekly_profiles, curve_value, week_metrics, plan as plan_energy
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
DEFAULT_WALLET_ADDRESS = "0xaedac36dcfc956864fcc03ec2ef256facaefd991"
WALLET_ADDRESS = os.getenv('WALLET_ADDRESS') or DEFAULT_WALLET_ADDRESS
MINING_COIN = "USDT"
MINING_ALGORITHM = os.getenv("MY_MINING_ALGORITHM", "pearlpow").strip().lower()
MINING_WORKER = os.getenv("MY_MINING_WORKER", "solarminer").strip()
HISTORY_DIR = os.getenv('MY_HISTORY_DIR', 'solarman_json')
BATTERY_CAPACITY_AH = float(os.getenv("MY_BATTERY_CAPACITY_AH", "200"))
BATTERY_NOMINAL_V = float(os.getenv("MY_BATTERY_NOMINAL_V", "55.2"))
# OC GPUs report ~548 W DC; board/CPU/RAM/SSD/fans + PSU losses need headroom.
# 750 W is a conservative whole-rig AC estimate, not a wall-meter reading.
MINER_POWER_W = float(os.getenv("MY_MINER_POWER_W", "750"))
BATTERY_FLOOR_SOC = float(os.getenv("MY_BATTERY_FLOOR_SOC", "20"))
HIGH_SOC_STOP_SOC = float(os.getenv("MY_HIGH_SOC_STOP_SOC", "90"))
AFTERNOON_PV_STOP_W = float(os.getenv("MY_AFTERNOON_PV_STOP_W", "50"))
HIGH_SOC_STOP_MAX_PV_W = float(os.getenv("MY_HIGH_SOC_STOP_MAX_PV_W", "400"))
BATTERY_PROTECT_SOC = float(os.getenv("MY_BATTERY_PROTECT_SOC", "90"))
HARD_AFTERNOON_STOP_SOC = float(os.getenv("MY_HARD_AFTERNOON_STOP_SOC", "90"))
HARD_AFTERNOON_STOP_HOUR = int(os.getenv("MY_HARD_AFTERNOON_STOP_HOUR", "14"))
PV_COVERAGE_RATIO_STOP = float(os.getenv("MY_PV_COVERAGE_RATIO_STOP", "0.9"))
PV_COVERAGE_RATIO_START = float(os.getenv("MY_PV_COVERAGE_RATIO_START", "0.75"))
MIN_RUN_MINUTES = int(os.getenv("MY_MIN_RUN_MINUTES", "18"))
MIN_RESTART_DELAY_MINUTES = int(os.getenv("MY_MIN_RESTART_DELAY_MINUTES", "10"))
MINER_STOP_FORCE_COOLDOWN_MINUTES = max(1, int(os.getenv("MY_MINER_STOP_FORCE_COOLDOWN_MINUTES", "20")))
POWER_BUTTON_SHORT_PRESS_SECONDS = min(1.0,max(0.1,float(os.getenv("MY_POWER_BUTTON_SHORT_PRESS_SECONDS", "0.55"))))
POWER_BUTTON_LONG_PRESS_SECONDS = max(10.0,float(os.getenv("MY_POWER_BUTTON_LONG_PRESS_SECONDS", "10")))

PRE_SUNRISE_CONTROL_MINUTES = int(os.getenv("MY_PRE_SUNRISE_CONTROL_MINUTES", "120"))
DAWN_ZERO_PV_MAX_W = float(os.getenv("MY_DAWN_ZERO_PV_MAX_W", "80"))
BRIDGE_START_SAFETY_FACTOR = float(os.getenv("MY_BRIDGE_START_SAFETY_FACTOR", "1.25"))
STARTUP_ENERGY_PENALTY_WH = float(os.getenv("MY_STARTUP_ENERGY_PENALTY_WH", "120"))
DAWN_START_TARGET_SOC_MARGIN = float(os.getenv("MY_DAWN_START_TARGET_SOC_MARGIN", "3"))
WEAK_WEATHER_BRIDGE_SOC_BUFFER = float(os.getenv("MY_WEAK_WEATHER_BRIDGE_SOC_BUFFER", "12"))
ZERO_PV_REFILL_DEADLINE_HOUR = int(os.getenv("MY_ZERO_PV_REFILL_DEADLINE_HOUR", "13"))
MIN_DECISION_CONFIDENCE_START = float(os.getenv("MY_MIN_DECISION_CONFIDENCE_START", "0.62"))
MIN_DECISION_CONFIDENCE_STOP = float(os.getenv("MY_MIN_DECISION_CONFIDENCE_STOP", "0.68"))
DAWN_RAIN_FORECAST_BLOCK_BAD_RATIO = float(os.getenv("MY_DAWN_RAIN_FORECAST_BLOCK_BAD_RATIO", "0.45"))
DAWN_OVERCAST_BLOCK_CLOUDS = float(os.getenv("MY_DAWN_OVERCAST_BLOCK_CLOUDS", "98"))

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
gpio_lock = threading.RLock()
runtime_lock = threading.RLock()
_runtime_guard = MinerPingGuard(os.getenv('MY_MINER_IP','192.168.0.185'),os.getenv('MY_MINER_MAC','90:DE:80:BD:AD:BF'))
_latest_power_sample = None
_power_measurement_error = None
_last_power_notice_key = None
_live_power_points = deque(maxlen=288)  # Display only; rolling 24 h in RAM, never a JSON archive.
_weather_daylight = None
snapshot_lock = threading.Lock()

# Shared snapshot for Telegram thread
_shared_snapshot = {
    "battery": None, "power": None, "state": "init", "current_condition": "unknown",
    "sunrise": None, "sunset": None,
    "clouds": None, "garage_temp": None, "garage_hum": None,
    "hashrate_hs": None, "hashrate_mhs": None,
    "inv_l1": None, "inv_l2": None, "inv_l3": None, "inv_lt": None,
    "historical_hints": {
        "week_quality": "neutral",
        "early_start_soc": 55,
        "min_stop_soc": 20,
        "late_day_reserve_soc": None,
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
    week = datetime.now(tz=budapest_tz).isocalendar().week
    profile = ((historical_profile or {}).get("weeks") or {}).get(week, {})
    return {
        "history_source": "solarman_json",
        "history_days": profile.get("days", 0),
        "history_samples": profile.get("samples", 0),
        "history_coverage": min(1.0, profile.get("days", 0) / 14),
        "week_quality": "neutral",
        "early_start_soc": 0,
        "min_stop_soc": BATTERY_FLOOR_SOC,
        "late_day_reserve_soc": None,
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
        "dawn_start_allowed": False,
        "zero_pv_bridge_start": False,
        "decision_confidence": 0.0,
        "start_score": 0.0,
        "stop_score": 0.0,
        "available_bridge_wh": 0.0,
        "required_bridge_wh": 0.0,
        "bridge_safety_factor": BRIDGE_START_SAFETY_FACTOR,
        "startup_energy_penalty_wh": STARTUP_ENERGY_PENALTY_WH,
        "predicted_first_miner_cover_time": None,
        "predicted_full_charge_time": None,
        "predicted_refill_confidence": 0.0,
        "active_control_window": False,
        "control_window_reason": "idle",
    }


def _is_adverse_dawn_weather(condition: str) -> bool:
    c = str(condition or "").lower()
    return any(k in c for k in [
        "rain", "drizzle", "storm", "thunder", "shower",
        "snow", "sleet", "blizzard", "freezing", "hail",
    ])


def _dawn_weather_block_reason(current_condition, f1_cond, f1_clouds, f3_cond, f3_clouds, weather_outlook) -> str:
    """Return non-empty reason when dawn battery bridge start should be blocked by near-term weather."""
    bad_hits = []
    for label, cond in (("now", current_condition), ("1h", f1_cond), ("3h", f3_cond)):
        if _is_adverse_dawn_weather(cond):
            bad_hits.append(f"{label}:{cond}")
    if bad_hits:
        return "rain/storm forecast in dawn window (" + "; ".join(str(x) for x in bad_hits) + ")"

    wx = weather_outlook or {}
    bad_ratio = _safe_float(wx.get("bad_ratio_5d"), 0.0)
    summary = str(wx.get("summary_5d", "unknown")).lower()
    f1c = _safe_float(f1_clouds, 0.0)
    f3c = _safe_float(f3_clouds, 0.0)
    if summary == "solar_weak" and bad_ratio >= DAWN_RAIN_FORECAST_BLOCK_BAD_RATIO and min(f1c, f3c) >= DAWN_OVERCAST_BLOCK_CLOUDS:
        return f"very weak overcast dawn forecast (bad_ratio={bad_ratio:.2f}, clouds={f1c:.0f}/{f3c:.0f}%)"
    return ""


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
        "forecast": [
            {"ts": datetime.fromtimestamp(e['dt'],tz=budapest_tz).isoformat(),
             "condition": ((e.get('weather') or [{}])[0] or {}).get('description','unknown'),
             "clouds": (e.get('clouds') or {}).get('all')}
            for e in entries if isinstance(e,dict) and isinstance(e.get('dt'),(int,float))
        ],
    }

_last_force_shutdown_at: Optional[datetime] = None
_last_production_start_at: Optional[datetime] = None
_last_hashrate_restart_at: Optional[datetime] = None
_last_wallet_hashrate_hs: Optional[float] = None
_last_wallet_hashrate_at: Optional[datetime] = None
_last_wallet_hashrate_key: Optional[Tuple[str, str, str, str]] = None
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
    """Accept an EVM USDT address or an unMineable USDT address-page URL."""
    raw = str(value or "").strip()
    if raw.startswith(("http://", "https://")):
        parsed = urlparse(raw)
        if parsed.scheme != "https" or parsed.netloc.lower() not in {"unmineable.com", "www.unmineable.com"}:
            return None
        if parse_qs(parsed.query).get("coin", [MINING_COIN]) != [MINING_COIN]:
            return None
        match = re.fullmatch(r"/address/(0x[0-9a-fA-F]{40})/?", parsed.path)
        if not match:
            return None
        raw = match.group(1)
    if not re.fullmatch(r"0x[0-9a-fA-F]{40}", raw):
        return None
    return raw.lower()


def _effective_wallet_address() -> str:
    # Ignore legacy RVN values in the environment or persisted state.
    return _parse_wallet_address(WALLET_ADDRESS) or DEFAULT_WALLET_ADDRESS


def _format_hashrate(value: Optional[float]) -> str:
    if value is None or not math.isfinite(value) or value < 0:
        return "N/A"
    for factor, unit in ((1e15, "PH/s"), (1e12, "TH/s"), (1e9, "GH/s"), (1e6, "MH/s"), (1e3, "kH/s")):
        if value >= factor:
            return f"{value / factor:.2f} {unit}"
    return f"{value:.2f} H/s"


def _extract_hashrate_from_wallet_payload(payload: Dict[str, Any]) -> Optional[float]:
    """Read v5 account/workers reported rates (rhr in H/s) for this rig only.

    Calculated rates and chart history can lag behind a stopped miner, so they
    must not be used to confirm that the rig is still running.
    """
    if not isinstance(payload, dict) or payload.get("success") is not True:
        return None
    data = payload.get("data")
    group = data.get(MINING_ALGORITHM) if isinstance(data, dict) else None
    workers = group.get("workers") if isinstance(group, dict) else None
    if not isinstance(workers, list):
        return None
    total = 0.0
    for worker in workers:
        if not isinstance(worker, dict):
            return None
        if MINING_WORKER and worker.get("name") != MINING_WORKER:
            continue
        online = worker.get("online")
        if online is False or online == 0:
            continue
        if online is not True and online != 1:
            return None
        rate = worker.get("rhr")
        if isinstance(rate, bool):
            return None
        try:
            rate = float(rate)
        except (ValueError, TypeError):
            return None
        if not math.isfinite(rate) or rate < 0:
            return None
        total += rate
    return total if math.isfinite(total) else None


def _wallet_hashrate_hs(wallet: str) -> Optional[float]:
    wallet = _parse_wallet_address(wallet)
    if not wallet:
        return None
    base_url = "https://api.unmineable.com/v5"
    last_err = "unknown"
    for attempt in range(1, 4):
        try:
            response = requests.get(
                f"{base_url}/address/{wallet}", params={"coin": MINING_COIN},
                timeout=(5, 12), headers={"Accept": "application/json"},
            )
            response.raise_for_status()
            account = response.json()
            data = account.get("data") if isinstance(account, dict) else None
            uuid = data.get("uuid") if isinstance(data, dict) else None
            if account.get("success") is not True or not isinstance(uuid, str) or not re.fullmatch(r"[a-zA-Z0-9-]+", uuid):
                raise ValueError("missing account UUID")
            response = requests.get(
                f"{base_url}/account/{uuid}/workers", timeout=(5, 12),
                headers={"Accept": "application/json"},
            )
            response.raise_for_status()
            hs = _extract_hashrate_from_wallet_payload(response.json())
            if hs is not None:
                return hs
            last_err = "workers_schema_or_hashrate_unavailable"
        except (requests.RequestException, ValueError, TypeError, AttributeError) as err:
            last_err = type(err).__name__
        if attempt < 3:
            time.sleep(0.35 * attempt)
    print(f"[Hashrate guard] unMineable {MINING_COIN}/{MINING_ALGORITHM} unavailable: {last_err}")
    return None


def _wallet_hashrate_hs_cached(wallet: str, now: Optional[datetime] = None, max_age_seconds: int = 120) -> Optional[float]:
    global _last_wallet_hashrate_hs, _last_wallet_hashrate_at, _last_wallet_hashrate_key
    if now is None:
        now = datetime.now(tz=budapest_tz)
    key = (_parse_wallet_address(wallet) or "", MINING_COIN, MINING_ALGORITHM, MINING_WORKER)
    if (
        key == _last_wallet_hashrate_key
        and _last_wallet_hashrate_at is not None
        and 0 <= (now - _last_wallet_hashrate_at).total_seconds() <= max(1, int(max_age_seconds))
    ):
        return _last_wallet_hashrate_hs
    hs = _wallet_hashrate_hs(wallet)
    _last_wallet_hashrate_key = key
    _last_wallet_hashrate_hs = hs
    _last_wallet_hashrate_at = now
    return hs


def _last_state_change_ts() -> Optional[datetime]:
    # Minimal controller state, not a recorded measurement dataset.
    return uptime if isinstance(uptime, datetime) else None


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

def build_historical_profile(history_dir: str = "solarman_json", before=None, bundled_dir=None) -> Dict[str, Any]:
    bundled = Path(bundled_dir) if bundled_dir is not None else Path(__file__).resolve().parent / 'bundled_solarman_json'
    directories = [history_dir] + ([bundled] if bundled.is_dir() else [])
    dataset = load_exports(directories, before=before or datetime.now(tz=budapest_tz))
    dataset['directories'] = [str(Path(d).resolve()) for d in directories]
    dataset["weeks"] = build_weekly_profiles(dataset["rows"])
    print(f"[History] Read-only exports: {dataset['files']} files, {dataset['unique_timestamps']} measurements, {dataset['invalid_rows']} invalid rows")
    if dataset['rows']:
        first,last = dataset['rows'][0]['ts'][:10],dataset['rows'][-1]['ts'][:10]
        print(f"[History] Coverage: {first} to {last} | read-only directories: {len(directories)}")
    return dataset


def _history_recommendation(now, battery_charge, current_power, sunrise_dt, sunset_dt,
                            weather_outlook=None, current_load=0.0, running=False,
                            battery_voltage=BATTERY_NOMINAL_V, battery_ah=BATTERY_CAPACITY_AH,
                            current_condition="unknown", clouds=None):
    profile = ((historical_profile or {}).get("weeks") or {}).get(now.isocalendar().week,{})
    weather = (weather_outlook or {}).get("summary_5d","unknown")
    floor = BATTERY_FLOOR_SOC
    daylight = _weather_daylight
    if daylight and any(at.date()!=now.date() for at in daylight):
        daylight = None
    dawn, dusk = daylight or (sunrise_dt, sunset_dt)
    if dusk < sunset_dt:
        dusk = sunset_dt
    budget = plan_energy(profile,now,dusk,battery_charge,current_power,current_load,running,
                         _effective_battery_capacity_wh(battery_voltage,battery_ah),MINER_POWER_W,
                         floor,HARD_AFTERNOON_STOP_SOC,weather,STARTUP_ENERGY_PENALTY_WH,
                         forecast=(weather_outlook or {}).get('forecast',[]),
                         current_condition=current_condition,clouds=clouds,
                         production_stop=sunset_dt,next_sunrise=dawn+timedelta(days=1),
                         min_run_minutes=5 if running else MIN_RUN_MINUTES,bridge_safety_factor=BRIDGE_START_SAFETY_FACTOR,
                         reserve_floor_soc=BATTERY_FLOOR_SOC)
    hours = profile.get("hours",{})
    midday = statistics.mean([hours[h]['pv_p25'] for h in range(10,15) if h in hours]) if any(h in hours for h in range(10,15)) else 0
    quality = "strong" if midday>=2300 else ("weak" if midday<1650 else "neutral")
    return {
        "history_source":"solarman_json", "history_week":now.isocalendar().week,
        "weekly_metrics":week_metrics(profile,MINER_POWER_W,battery_charge,now.hour*60+now.minute),
        "history_years":profile.get("years",[]), "history_samples":profile.get('samples',0),
        "history_days":profile.get('days',0), "history_coverage":budget['coverage'],
        "history_interpolated":profile.get('interpolated',False), "energy_budget":budget,
        "week_quality":quality,"early_start_soc":floor,"min_stop_soc":BATTERY_FLOOR_SOC,
        "late_day_reserve_soc":budget.get("reserve_soc"),
        "should_preserve_battery":not budget['safe'],"headroom_good":budget['safe'],
        "hourly_prod_mean":{str(h):v.get('pv_p50',v['pv_p25']) for h,v in hours.items()},
        "weather_risk_5d":weather,"weather_sunny_ratio_5d":(weather_outlook or {}).get('sunny_ratio_5d',0),
        "weather_bad_ratio_5d":(weather_outlook or {}).get('bad_ratio_5d',0),
        "predicted_full_charge_time":budget.get('full_charge_time'),
        "can_refill_before_sunset":bool(budget.get('full_charge_time')),
    }


def _has_solarman_payload(data: Optional[Dict[str, Any]]) -> bool:
    return bool(isinstance(data, dict) and isinstance(data.get("dataList"), list) and len(data.get("dataList")) > 0)


def _control_window_details(now, sunrise_dt, sunset_dt, hist=None) -> Dict[str, Any]:
    if not isinstance(now, datetime) or not isinstance(sunrise_dt, datetime) or not isinstance(sunset_dt, datetime):
        return {"active": False, "reason": "missing_time"}
    if now.tzinfo is None:
        now = now.replace(tzinfo=budapest_tz)
    if sunrise_dt.tzinfo is None:
        sunrise_dt = sunrise_dt.replace(tzinfo=budapest_tz)
    if sunset_dt.tzinfo is None:
        sunset_dt = sunset_dt.replace(tzinfo=budapest_tz)
    if sunrise_dt <= now <= sunset_dt:
        return {"active": True, "reason": "daylight"}
    dawn_start = sunrise_dt - timedelta(minutes=max(0, PRE_SUNRISE_CONTROL_MINUTES))
    has_context = bool((historical_profile or {}).get("weeks")) or bool(hist)
    if has_context and dawn_start <= now < sunrise_dt:
        return {"active": True, "reason": "dawn_pre_sunrise"}
    return {"active": False, "reason": "outside_control_window"}


def _is_control_window(now, sunrise_dt, sunset_dt, hist=None) -> bool:
    return bool(_control_window_details(now, sunrise_dt, sunset_dt, hist).get("active", False))


def _is_phase_power_safe(inv_l1, inv_l2, inv_l3, inv_lt) -> bool:
    return not (_safe_float(inv_l2, 0.0) > 2500 or _safe_float(inv_l3, 0.0) > 2500 or _safe_float(inv_lt, 0.0) > 5000)


def _make_miner_decision(
    now,
    prev_state,
    battery_charge,
    current_power,
    inv_l1,
    inv_l2,
    inv_l3,
    inv_lt,
    current_condition,
    clouds,
    f1_cond,
    f1_clouds,
    f3_cond,
    f3_clouds,
    sunrise,
    sunset,
    hist,
    start_guard,
    battery_voltage,
    battery_ah,
    weather_outlook,
    current_load=None,
) -> Dict[str, Any]:
    with runtime_lock:
        physical=_runtime_guard.status(now)
        pending_stop=(_runtime_guard.shutdown_after is not None and _runtime_guard.runtime_state in
                      ('stop_pending','stop_failed','stop_unverified'))
    physically_running=physical['reachable'] is True
    budget_running=True if physically_running else False if physical['state']=='off' else prev_state=='production'
    hints = _history_recommendation(now,battery_charge,current_power,sunrise,sunset,weather_outlook,
                                    inv_lt if current_load is None else current_load,
                                    budget_running,battery_voltage,battery_ah,current_condition,clouds)
    budget = hints['energy_budget']
    control = _control_window_details(now,sunrise,sunset,hints)
    reasons = []
    hard = False
    if not control['active']:
        reasons.append('Outside production window')
        hard = True
    if battery_charge<=BATTERY_FLOOR_SOC:
        reasons.append('Battery protected floor')
        hard = True
    if not _is_phase_power_safe(inv_l1,inv_l2,inv_l3,inv_lt):
        reasons.append('Phase/total inverter limit')
        hard = True
    if (now.hour>=HARD_AFTERNOON_STOP_HOUR and math.isfinite(current_power)
            and current_power<=AFTERNOON_PV_STOP_W and battery_charge<HARD_AFTERNOON_STOP_SOC):
        reasons.append(f'Afternoon cutoff: PV ≤ {AFTERNOON_PV_STOP_W:.0f} W and battery < {HARD_AFTERNOON_STOP_SOC:.0f}%')
        hard = True
    if not budget['safe']:
        explanations = {
            'insufficient_history_or_live_data':'Missing valid live measurements',
            'missing_daytime_history':'Missing hourly daytime history',
            'missing_overnight_history':'Missing hourly household history for the night reserve',
            'invalid_overnight_time_window':'Missing or inconsistent sunset/next-sunrise times',
            'overnight_reserve_exceeds_battery_capacity':'Estimated household night demand exceeds usable battery capacity',
            'battery_floor_would_be_crossed':'Proposed mining run/refill would cross the protected SOC floor',
            'no_sustained_solar_cover_for_morning_start':'No sustained solar cover forecast before the proposed morning run ends',
            'insufficient_battery_bridge':'Available battery bridge is smaller than the forecast deficit plus safety margin',
            'household_only_refill_not_feasible':'At the current household load and forecast, even without mining the battery would not recover its evening reserve; re-evaluate at the next live sample',
            'night_household_reserve_not_recovered':'Even an early mining stop would not recover the household night reserve',
            'insufficient_time_for_minimum_run':'Not enough production time remains for a useful mining run',
        }
        reasons.append(explanations.get(budget['reason'],budget['reason']))
    if prev_state!='production' and (sunset-now).total_seconds()<MIN_RUN_MINUTES*60:
        reasons.append('Insufficient time for minimum run before stop window')
    rain = _dawn_weather_block_reason(current_condition,f1_cond,f1_clouds,f3_cond,f3_clouds,weather_outlook or {})
    if prev_state!='production' and now<sunrise and rain:
        reasons.append(rain)
    cooldown = isinstance(_last_force_shutdown_at,datetime) and (now-_last_force_shutdown_at).total_seconds()<MINER_STOP_FORCE_COOLDOWN_MINUTES*60
    if pending_stop:
        reasons.append('Shutdown not confirmed; automatic start withheld')
        hard = True
    if cooldown and prev_state!='production':
        reasons.append('Shutdown cooldown')
    desired = 'stop' if reasons else 'production'
    # A forecast reserve violation must not wait through additional STOP samples.
    hard = hard or (prev_state=='production' and not budget['safe'])
    metrics = {
        'available_bridge_wh':budget.get('available_bridge_wh'),
        'required_bridge_wh':budget.get('required_bridge_wh'),
        'bridge_safety_factor':BRIDGE_START_SAFETY_FACTOR,'startup_energy_penalty_wh':STARTUP_ENERGY_PENALTY_WH,
        'predicted_first_miner_cover_time':budget.get('cover_time'),
        'predicted_full_charge_time':budget.get('full_charge_time'),
        'predicted_refill_confidence':budget['coverage'],
        'active_control_window':control['active'],'control_window_reason':control['reason'],
        'dawn_weather_block':bool(rain),'dawn_weather_block_reason':rain,
    }
    return {'desired_state':desired,'decision_state':desired,
            'decision_summary':('STOP: '+'; '.join(reasons)) if reasons else (
                f"RUN: near-full battery buffer; bounded run protects {budget['surplus_reserve_soc']:.0f}% at mining stop, reassess next live sample"
                if budget['reason']=='bounded_solar_surplus_run' else
                'RUN: battery bridge, finite mining run and overnight household reserve covered'),
            'start_rule_hits':[] if reasons else [budget['reason']],
            'stop_rule_hits':reasons,'hard_stop':hard,'soft_stop':desired=='stop' and not hard,
            'confidence':budget['coverage'],'start_score':budget['coverage'] if desired=='production' else 0,
            'stop_score':1 if desired=='stop' else 0,'zero_pv_bridge_start':desired=='production' and current_power<=DAWN_ZERO_PV_MAX_W,
            'dawn_start_allowed':desired=='production' and now<sunrise,
            'metrics':metrics,'history_hints':hints}


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
    send_telegram_message_async(msg, keyboard=True, mirror_web=True)

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
    """Format optional sensor values without inventing zero or losing signs."""
    if value is None or isinstance(value, bool):
        return None
    try:
        if isinstance(value, str):
            match = re.fullmatch(r'\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+))\s*(?:°?C|W|%)?\s*', value, re.IGNORECASE)
            if not match:
                return None
            value = match.group(1)
        number = float(value)
        return int(number) if math.isfinite(number) else None
    except (ValueError, TypeError, OverflowError):
        return None

def write_to_display(state_text, soc, solar_power, temperature, humidity):
    if not oled:
        return False
    def display(value):
        result = clean_value(value)
        return "--" if result is None else str(result)
    try:
        draw.rectangle((0, 0, oled.width, oled.height), outline=0, fill=0)
        lines = [f"SOC: {display(soc)}% PWR: {display(solar_power)}W",
                 str(state_text), f"{display(temperature)}C {display(humidity)}%"]
        for y, line in zip((0, 8, 16), lines):
            draw.text((0, y), line, font=font, fill=25)
        oled.image(image)
        oled.show()
        return True
    except Exception as err:
        # OLED/DHT failures must never stop power supervision or the dashboard.
        print(f"[OLED] Update skipped: {type(err).__name__}: {err}")
        return False

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
        now_dt=datetime.now(tz=budapest_tz)
        _update_pool_hashrate(now_dt)
        snapshot=_build_snapshot_payload()
        if historical_hints:
            snapshot['historical_hints']=historical_hints
        send_telegram_message(telegram_status(snapshot,now_dt,used_quote,QUOTE_LIMIT),mirror_web=False)

    if message_text == "/phase":
        send_telegram_message(telegram_phases(_build_snapshot_payload()),mirror_web=False)

    if message_text in ('/start','/stop','/force_stop'):
        result=_ensure_miner_started(manual=True) if message_text=='/start' else _request_miner_stop()
        send_telegram_message(result['message'])

    if message_text == "/wallet":
        send_telegram_message(f"unMineable {MINING_COIN} ({MINING_ALGORITHM}, worker={MINING_WORKER or 'all'}): {_effective_wallet_address()}")

    if message_text.startswith("/wallet "):
        raw = message_text.split(" ", 1)[1].strip()
        parsed = _parse_wallet_address(raw)
        if not parsed:
            send_telegram_message("Invalid wallet. Use a USDT EVM address (0x + 40 hex digits) or an unMineable address URL with coin=USDT.")
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
    global _weather_daylight
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
        _weather_daylight = (datetime.fromtimestamp(sunrise_ts, tz=budapest_tz),
                             datetime.fromtimestamp(sunset_ts, tz=budapest_tz))

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
    global _last_force_shutdown_at
    if not (is_rpi and GPIO_AVAILABLE):
        print(f"[Info] GPIO not available. Skipping power button press ({gpio_pin}, {press_time}s).")
        return False
    print(f"Pressing power button on GPIO pin {gpio_pin} for {press_time} seconds...")
    try:
        with gpio_lock:
            GPIO.setmode(GPIO.BCM)
            try:
                GPIO.setup(gpio_pin, GPIO.OUT, initial=GPIO.LOW)
                GPIO.output(gpio_pin, GPIO.HIGH)
                time.sleep(press_time)
            finally:
                try:
                    GPIO.output(gpio_pin, GPIO.LOW)
                finally:
                    GPIO.cleanup()
        with runtime_lock:
            if press_time == POWER_BUTTON_SHORT_PRESS_SECONDS:
                _runtime_guard.command_start(datetime.now(tz=budapest_tz))
            else:
                completed=datetime.now(tz=budapest_tz)
                _runtime_guard.command_stop_finished(completed,success=True)
                _last_force_shutdown_at=completed
        print("Power button press completed.")
        return True
    except Exception as e:
        if press_time >= POWER_BUTTON_LONG_PRESS_SECONDS:
            with runtime_lock:
                _runtime_guard.command_stop_finished(datetime.now(tz=budapest_tz),success=False)
        print(f"[Warning] GPIO press failed: {e}")
        return False


def _parse_power_measurement(data, now):
    """Return a measurement and a specific rejection reason, without side effects."""
    if not isinstance(data, dict) or data.get("success") is False:
        return None, "Solarman returned no successful device measurement"
    time_key = next((k for k in ("collectionTime", "dataTime", "timestamp")
                     if data.get(k) is not None), None)
    if time_key is None:
        return None, "Missing device collection timestamp"
    raw_time = data[time_key]
    try:
        if isinstance(raw_time, (int, float)) or str(raw_time).replace(".", "", 1).isdigit():
            epoch = float(raw_time)
            at = datetime.fromtimestamp(epoch / 1000 if epoch > 1e11 else epoch, tz=budapest_tz)
        else:
            at = datetime.fromisoformat(str(raw_time))
            if at.tzinfo is None:
                at = at.replace(tzinfo=budapest_tz)
    except (ValueError, TypeError, OverflowError, OSError):
        return None, f"Invalid device timestamp ({time_key})"
    items = data.get("dataList")
    if not isinstance(items, list):
        return None, "Missing Solarman dataList"
    fields = {item.get("key"): item for item in items
              if isinstance(item, dict) and isinstance(item.get("key"), str)}

    def watts(keys):
        for key in keys:
            item = fields.get(key)
            if item is None:
                continue
            if key == "E_Puse_t1" and not item.get("unit"):
                raise ValueError("E_Puse_t1 requires explicit W or kW units")
            unit = str(item.get("unit") or "W").strip().lower()
            if unit not in {"w", "kw"}:
                raise ValueError(f"Non-power unit in {key}: expected W or kW")
            try:
                value = float(item["value"]) * (1000 if unit == "kw" else 1)
            except (TypeError, ValueError, KeyError):
                raise ValueError(f"Invalid numeric power in {key}")
            if not math.isfinite(value) or value < 0:
                raise ValueError(f"Negative or non-finite power in {key}")
            return value
        return None

    def check_sum(total, phases, label):
        if abs(total - sum(phases)) > max(100, total * .1):
            raise ValueError(f"{label} total/phase mismatch: total={total:.1f} W, phases={sum(phases):.1f} W")

    try:
        total = watts(["LOAD_P_T", "C_P_T", "P_LOAD", "E_Puse_t1"])
        # E_Puse_t1 is instantaneous power on the supplied Deye schema (W),
        # despite its name. Energy counters with kWh units remain invalid.
        if total is None and "INV_O_P_T" not in fields:
            for item in items:
                if (isinstance(item, dict) and str(item.get("name", "")).strip().lower()
                    in {"total consumption power", "consumption power", "total load power", "load power"}
                    and str(item.get("unit") or "W").strip().lower() in {"w", "kw"}):
                    total = watts([item.get("key")])
                    if total is not None:
                        break
        if total is not None:
            # LPP is whole-house phase consumption on this inverter. C_P_L*
            # measures a different load port; never combine the two families.
            families = [("LPP_A", "LPP_B", "LPP_C"),
                        ("LOAD_P_L1", "LOAD_P_L2", "LOAD_P_L3"),
                        ("C_P_L1", "C_P_L2", "C_P_L3"),
                        ("INV_O_P_L1", "INV_O_P_L2", "INV_O_P_L3")]
            family = next((keys for keys in families if any(k in fields for k in keys)), None)
            if family is None or not all(k in fields for k in family):
                raise ValueError("Incomplete consumption phases: one complete L1/L2/L3 family required")
            phases = [watts([key]) for key in family]
            check_sum(total, phases, "Consumption")
            source = "consumption:" + family[0].rsplit("_", 1)[0]
        else:
            total = watts(["INV_O_P_T"])
            phases = [watts([f"INV_O_P_L{i}"]) for i in (1,2,3)]
            if total is None or any(v is None for v in phases):
                raise ValueError("Incomplete inverter power: INV_O_P_T and L1/L2/L3 required")
            check_sum(total, phases, "Inverter")
            source = "inverter_output"
        return PowerSample(at, total, *phases, source=source), None
    except ValueError as err:
        return None, str(err)


def _extract_power_sample(data: Dict[str, Any], now: datetime) -> Optional[PowerSample]:
    return _parse_power_measurement(data, now)[0]


def _power_measurement_reason(data, sample, now):
    if sample is None:
        return _parse_power_measurement(data, now)[1] or "Missing power measurement"
    age = (now - sample.at).total_seconds()
    if age < 0:
        return f"Device timestamp is {-age:.0f} seconds in the future"
    if age > PowerSample.MAX_SAMPLE_AGE_SECONDS:
        return f"Device power measurement is {age:.1f} seconds old (maximum {PowerSample.MAX_SAMPLE_AGE_SECONDS} seconds)"
    return None


def record_live_power(now: datetime, expected_state: str, data: Dict[str, Any], poll_interval_seconds=300) -> None:
    """Solarman data for display/planning only; no ping or GPIO operations."""
    global _latest_power_sample, _power_measurement_error
    _latest_power_sample = _extract_power_sample(data, now)
    _power_measurement_error = _power_measurement_reason(data, _latest_power_sample, now)
    if PowerSample.fresh(_latest_power_sample,now):
        sample = _latest_power_sample
        with snapshot_lock:
            if _live_power_points and _live_power_points[-1]['source']!=sample.source:
                _live_power_points.clear()
            while _live_power_points and datetime.fromisoformat(_live_power_points[0]['ts'])<now-timedelta(hours=24):
                _live_power_points.popleft()
            if not _live_power_points or datetime.fromisoformat(_live_power_points[-1]['ts'])<sample.at:
                _live_power_points.append({'ts':sample.at.isoformat(),'l1':sample.l1,'l2':sample.l2,
                                           'l3':sample.l3,'sum':sample.total,'source':sample.source})


def _runtime_tick():
    """ICMP-only supervision, independent of Solarman polling and power values."""
    global _last_force_shutdown_at,_last_power_notice_key
    with gpio_lock:
        reachable=ping_host(_runtime_guard.address)
        now=datetime.now(tz=budapest_tz)
        with runtime_lock:
            shutdown=_runtime_guard.observe(reachable,now)
        if shutdown:
            sent=bool(is_rpi and GPIO_AVAILABLE and press_power_button(16,POWER_BUTTON_LONG_PRESS_SECONDS))
            with runtime_lock:
                if _runtime_guard.shutdown_reserved:
                    _runtime_guard.command_stop_finished(datetime.now(tz=budapest_tz),success=sent)
            if sent:
                _last_force_shutdown_at=datetime.now(tz=budapest_tz)
                save_prev_state('stop',_last_force_shutdown_at)
        with runtime_lock:
            physical=_runtime_guard.status(datetime.now(tz=budapest_tz))
    key=(physical['state'],physical['attempts'])
    changed=key!=_last_power_notice_key
    if changed:
        _last_power_notice_key=key
        text={'off':'✅ A miner IP-je két egymást követő pingellenőrzésben nem válaszolt.',
              'stop_pending':'⏳ STOP kérve / hosszú nyomás után pinges ellenőrzésre vár.',
              'stop_failed':'🚨 A miner továbbra is elérhető vagy a GPIO-kísérlet hibás; leállítás nincs igazolva.',
              'stop_unverified':'⚠ Pingellenőrzési hiba; leállítás nem igazolható.'}.get(physical['state'])
        if text:
            send_telegram_message_async(f"{text} IP: {physical['target_ip']} · kísérlet {physical['attempts']}/2. {physical['reason']}",mirror_web=True)
    if changed:
        print(f"[Ping guard] {physical['target_ip']} {physical['state']}: {physical['reason']}")
    return physical


def _ping_monitor_loop():
    while True:
        try:
            _runtime_tick()
        except Exception as err:
            print(f'[Ping guard] Check failed: {type(err).__name__}')
        time.sleep(15)


def _ensure_miner_started(manual=False):
    """Never send a start pulse into an already ping-online/unknown target."""
    with gpio_lock:
        with runtime_lock:
            if not _runtime_guard.set_desired('production',force=manual):
                return {'ok':False,'message':'Outstanding STOP verification; automatic start withheld'}
        first=ping_host(_runtime_guard.address)
        if first is True:
            with runtime_lock:
                _runtime_guard.set_desired('production')
                _runtime_guard.observe(True,datetime.now(tz=budapest_tz))
            return {'ok':True,'message':'Miner already replies to ping; no start pulse sent'}
        if first is None:
            return {'ok':False,'message':'Ping status uncertain; start pulse withheld'}
        if _runtime_guard.start_after and datetime.now(tz=budapest_tz)-_runtime_guard.start_after<timedelta(seconds=90):
            return {'ok':True,'message':'Start already sent; waiting for boot ping'}
        second=ping_host(_runtime_guard.address)
        if second is None:
            return {'ok':False,'message':'Ping status uncertain; start pulse withheld'}
        with runtime_lock:
            _runtime_guard.set_desired('production')
            _runtime_guard.observe(first,datetime.now(tz=budapest_tz))
            _runtime_guard.observe(second,datetime.now(tz=budapest_tz))
        if second is True:
            return {'ok':True,'message':'Miner already replies to ping; no start pulse sent'}
        sent=press_power_button(16,POWER_BUTTON_SHORT_PRESS_SECONDS)
        return {'ok':bool(sent),'message':'Start pulse sent; waiting for ping' if sent else 'Start GPIO failed'}


def _request_miner_stop():
    with runtime_lock:
        _runtime_guard.set_desired('stop')
    physical=_runtime_tick()
    return {'ok':physical['state'] in ('stop_pending','off'),
            'message':f"Long STOP / ping verification: {physical['state']} · {physical['reason']}"}


def _update_pool_hashrate(now: datetime) -> None:
    """Pool telemetry is display-only, including outside the control window."""
    hs = _wallet_hashrate_hs_cached(_effective_wallet_address(), now=now, max_age_seconds=120)
    with snapshot_lock:
        _shared_snapshot.update({"hashrate_hs": hs, "hashrate_mhs": hs / 1e6 if hs is not None else None})


def _solarman_poll_slot(now, sunrise_dt, sunset_dt):
    """One Solarman attempt per 5-minute daylight / 30-minute night slot.

    Use astronomical sunrise/sunset, independently of the earlier production
    stop and pre-dawn control offsets. If weather is unavailable, use the
    existing supplied bounds rather than guessing a daylight window.
    """
    dawn, dusk = _weather_daylight or (sunrise_dt, sunset_dt)
    daylight = isinstance(dawn, datetime) and isinstance(dusk, datetime) and dawn <= now < dusk
    interval = 300 if daylight else 1800
    return interval, int(now.timestamp()) // interval


def _solarman_poll_due(now, slot, last_slot, last_attempt):
    if slot == last_slot:
        return False
    # Nightfall or a half-hour wall-clock boundary must not cause two night
    # requests only five minutes apart. Count time since the last attempt.
    if slot[0] == 1800 and last_attempt is not None:
        return int(now.timestamp()) - int(last_attempt.timestamp()) >= 1800
    return True


def _idle_monitor_cycle(now: datetime, token_future, garage_temp, garage_hum, poll_interval_seconds=300):
    """Process one scheduled live read; never reuse cached data for GPIO."""
    global used_quote
    data = {}
    try:
        token = token_future.result(timeout=10)
        if token:
            used_quote += 1
            save_quote_usage(used_quote)
            data = fetch_current_data(token) or {}
    except Exception as err:
        print(f"[Safety monitoring] Solarman read unavailable: {type(err).__name__}")
    with runtime_lock:
        _runtime_guard.set_desired('stop')
    record_live_power(now, "stop", data, poll_interval_seconds=poll_interval_seconds)
    dl = data.get("dataList", []) if isinstance(data, dict) else []
    dl = [item for item in dl if isinstance(item, dict)] if isinstance(dl, list) else []
    readings = {
        "battery": _find_value(dl, "BMS_SOC", None),
        "power": _find_value(dl, "S_P_T", None),
        **{f"inv_l{i}": _find_value(dl, f"INV_O_P_L{i}", None) for i in (1,2,3)},
        "inv_lt": _find_value(dl, "INV_O_P_T", None),
    }
    readings = {key: value if value is not None and math.isfinite(value) else None
                for key, value in readings.items()}
    with snapshot_lock:
        _shared_snapshot.update(readings)
        _shared_snapshot.update({"state": "stop", "garage_temp": garage_temp,
                                 "garage_hum": garage_hum, "monitoring_mode": "idle_safety",
                                 "solarman_polled_at": now.isoformat(),
                                 "solarman_poll_interval_seconds": poll_interval_seconds})
    if is_rpi:
        write_to_display("monitor", readings["battery"], readings["power"], garage_temp, garage_hum)
    return data


def _merge_decision_into_hints(hist: Dict[str, Any], decision: Dict[str, Any], start_guard: Dict[str, Any]) -> Dict[str, Any]:
    metrics = decision.get("metrics", {}) if isinstance(decision, dict) else {}
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
        "decision_state": str(decision.get("decision_state", "unknown")),
        "decision_start_rules": list(decision.get("start_rule_hits", [])),
        "decision_stop_rules": list(decision.get("stop_rule_hits", [])),
        "decision_summary": str(decision.get("decision_summary", "unknown")),
        "dawn_start_allowed": bool(decision.get("dawn_start_allowed", False)),
        "zero_pv_bridge_start": bool(decision.get("zero_pv_bridge_start", False)),
        "decision_confidence": float(decision.get("confidence", 0.0)),
        "start_score": float(decision.get("start_score", 0.0)),
        "stop_score": float(decision.get("stop_score", 0.0)),
    })
    for key in (
        "available_bridge_wh", "required_bridge_wh", "bridge_safety_factor", "startup_energy_penalty_wh",
        "predicted_first_miner_cover_time", "predicted_full_charge_time", "predicted_refill_confidence",
        "active_control_window", "control_window_reason", "dawn_weather_block", "dawn_weather_block_reason",
    ):
        hist[key] = metrics.get(key)
    return hist


def check_crypto_production_conditions(data, weather_api_key, location_lat, location_lon):
    global prev_state, state, used_quote, sunrise, sunset, uptime, _last_production_start_at
    prev_state, uptime = load_prev_state()

    try:
        (current_condition, sunrise, sunset, clouds,
         f1_cond, f1_clouds, f1_ts,
         f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(weather_api_key, location_lat, location_lon)

        garage_data = read_dht11(0, 0)
        temperature = garage_data['temperature']
        humidity = garage_data['humidity']
        dl = data.get("dataList", []) if isinstance(data, dict) else []
        battery_charge = _find_value(dl, "BMS_SOC", float("nan"))
        current_power = _find_value(dl, "S_P_T", float("nan"))
        internal_power = _find_value(dl, "GS_T", 0)
        battery_voltage = _find_first_value(dl, ["BMS_B_V1", "B_V1", "BMS_V", "BMS_U", "BAT_V", "BAT_U", "BMS Voltage", "Battery Voltage"], BATTERY_NOMINAL_V)
        battery_ah = _find_first_value(dl, ["BRC", "Battery Rated Capacity", "BMS_B_AH", "B_AH"], BATTERY_CAPACITY_AH)
        inv_l1 = _find_value(dl, "INV_O_P_L1", 0.0)
        inv_l2 = _find_value(dl, "INV_O_P_L2", 0.0)
        inv_l3 = _find_value(dl, "INV_O_P_L3", 0.0)
        inv_lt = _find_value(dl, "INV_O_P_T", 0.0)
        now = datetime.now(tz=budapest_tz)

        live_sample = _extract_power_sample(data,now)
        decision = _make_miner_decision(now,prev_state or 'stop',battery_charge,current_power,
            inv_l1,inv_l2,inv_l3,inv_lt,current_condition,clouds,f1_cond,f1_clouds,f3_cond,f3_clouds,
            sunrise,sunset,{}, {},battery_voltage,battery_ah,weather_outlook,
            current_load=(live_sample.total if PowerSample.fresh(live_sample,now) else float("nan")))
        hist = decision['history_hints']
        hist = _merge_decision_into_hints(hist,decision,{
            'allow_start':decision['desired_state']=='production','reason':hist['energy_budget']['reason'],
            'capacity_wh':_effective_battery_capacity_wh(battery_voltage,battery_ah)})
        desired_state = decision['desired_state']
        if decision['hard_stop']:
            state = 'stop'
        else:
            state,_,_ = _apply_transition_guard(prev_state or 'stop',desired_state,now,confirmed=True)

        print(
            f"[Decision] desired={desired_state} effective={state} summary={hist.get('decision_summary')} "
            f"confidence={hist.get('decision_confidence')} start={hist.get('start_score')} stop={hist.get('stop_score')} "
            f"bridge_required={hist.get('required_bridge_wh')}Wh available={hist.get('available_bridge_wh')}Wh "
            f"startup={hist['energy_budget'].get('startup_energy_wh')}Wh cover={hist.get('predicted_first_miner_cover_time')}"
        )
        print(f"Battery charge: {battery_charge}% | PV: {current_power}W | Internal: {internal_power}W")
        print(f"Inverter output per phase: L1={int(inv_l1)}W, L2={int(inv_l2)}W, L3={int(inv_l3)}W, Total={int(inv_lt)}W")

        with runtime_lock:
            if not _runtime_guard.set_desired(state):
                state='stop'
                hist['decision_summary']='STOP: outstanding ping shutdown verification'
        start_result=None
        if state == "production" and is_rpi:
            start_result=_ensure_miner_started()
        if state == "production" and prev_state != "production":
            _last_production_start_at = now
            print("Crypto production ready!")
            live=_build_snapshot_payload()
            live.update(state=state,battery=battery_charge,power=current_power,historical_hints=hist,
                        inv_l1=inv_l1,inv_l2=inv_l2,inv_l3=inv_l3,inv_lt=inv_lt)
            send_telegram_message_async('▶ '+(start_result['message'] if start_result else 'RUN döntés; GPIO-jel nem lett küldve ezen a gépen.')+'\n'+telegram_status(live,now),mirror_web=True)
        elif state == "stop" and prev_state != "stop":
            _last_production_start_at = None
            live=_build_snapshot_payload()
            live.update(state=state,battery=battery_charge,power=current_power,historical_hints=hist)
            send_telegram_message_async('⏹ Leállítás kérve; pinggel elérhető minernél hosszú gombnyomás és pinges visszaellenőrzés következik. A gép még nincs leálltnak igazolva.\n'+telegram_status(live,now),mirror_web=True)

        if state != prev_state:
            prev_state = state
            uptime = now
            save_prev_state(prev_state, now)

        return (battery_charge, current_power, state, current_condition, sunrise, sunset, clouds,
                f1_cond, f1_clouds, f1_ts,
                f3_cond, f3_clouds, f3_ts, hist)

    except Exception as e:
        print(f"Error while checking production conditions: {e}")
        traceback.print_exc()
        now_fallback = datetime.now(tz=budapest_tz)
        safe_sunrise = sunrise if isinstance(sunrise, datetime) else now_fallback
        safe_sunset = sunset if isinstance(sunset, datetime) else now_fallback
        return (
            None, None, state, "unknown", safe_sunrise, safe_sunset, 0,
            "unknown", 0, "",
            "unknown", 0, "", {}
        )


def _miner_action(action: str) -> Dict[str, Any]:
    now = datetime.now(tz=budapest_tz).isoformat()
    if action not in {"start", "stop", "force_stop"}:
        return {"ok": False, "message": "invalid action", "ts": now}
    if not (is_rpi and GPIO_AVAILABLE):
        return {'ok':False,'message':'GPIO unavailable','ts':now}
    try:
        result=_ensure_miner_started(manual=True) if action=='start' else _request_miner_stop()
        _push_web_notification(result['message'],level='info' if result['ok'] else 'error')
        return {**result,'ts':now}

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


DASHBOARD_HTML = r"""

<!doctype html>
<html lang="hu"><head>
<meta charset="utf-8" /><meta name="viewport" content="width=device-width,initial-scale=1" />
<title>Solar Mining Control</title>
<link rel="icon" type="image/png" href="/solarmining_logo.png" />
<link rel="apple-touch-icon" href="/solarmining_logo.png" />
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fortawesome/fontawesome-free@7.3.1/css/all.min.css" />
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.5.1/dist/chart.umd.min.js"></script>
<style>
:root{--bg:#0b1220;--bg2:#182845;--card:rgba(20,31,56,.72);--txt:#e9eefc;--muted:#9fb0d0;--ok:#47d16c;--warn:#f2b84b;--danger:#ff6b6b;--input:#1f2c48;--border:rgba(255,255,255,.2)}
[data-theme="light"]{--bg:#eef3ff;--bg2:#d9e8ff;--card:rgba(255,255,255,.85);--txt:#111827;--muted:#4b5563;--input:#ffffff;--border:rgba(17,24,39,.15)}
*{box-sizing:border-box}
body{margin:0;background:linear-gradient(145deg,var(--bg),var(--bg2));color:var(--txt);font-family:Inter,system-ui,sans-serif;min-height:100vh;overflow-x:hidden}
.runtime-alarm .v{color:#f87171}
.wrap{padding:10px 18px 16px;max-width:1500px;margin:0 auto;display:flex;flex-direction:column;gap:10px}
.logo-wrap{display:flex;justify-content:center;padding-top:0;margin:-8px 0 -14px;line-height:0}
.logo{display:block;max-width:min(300px,72vw);height:auto;filter:drop-shadow(0 8px 18px rgba(0,0,0,.28));}
.top{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
.title{display:flex;align-items:center;gap:10px;margin:0;font-size:clamp(1.35rem,2.3vw,2rem)}
.panel{background:var(--card);backdrop-filter:blur(10px);border:1px solid var(--border);border-radius:16px;padding:14px}
.grid{display:grid;gap:12px}
.metrics-grid{grid-template-columns:repeat(5,minmax(140px,1fr));gap:10px}
.metrics-grid .card.metrics-history{grid-column:span 2}
@media(max-width:1280px){.metrics-grid{grid-template-columns:repeat(4,minmax(150px,1fr));gap:10px}.metrics-grid .card.metrics-history{grid-column:span 1}}
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
.field-date input{appearance:none;-webkit-appearance:none;background:linear-gradient(180deg,rgba(255,255,255,.12),rgba(255,255,255,.04));border:1px solid rgba(148,163,184,.45);box-shadow:inset 0 1px 0 rgba(255,255,255,.18),0 8px 18px rgba(2,6,23,.22);font-weight:700;letter-spacing:.02em;color:var(--txt);min-height:42px;color-scheme:dark;padding-right:36px}
[data-theme="light"] .field-date input{background:linear-gradient(180deg,#ffffff,#eef4ff);border-color:rgba(71,85,105,.28);box-shadow:inset 0 1px 0 rgba(255,255,255,.8),0 6px 14px rgba(15,23,42,.08);color-scheme:light}
.field-date input:hover{border-color:rgba(96,165,250,.75)}
.field-date input:focus{outline:none;border-color:#60a5fa;box-shadow:0 0 0 3px rgba(96,165,250,.25),0 10px 22px rgba(59,130,246,.2)}
.field-date input::-webkit-calendar-picker-indicator{opacity:0;cursor:pointer}
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
.pool-meta{display:flex;align-items:center;flex-wrap:wrap;gap:8px;margin-top:12px}
.pool-link,.pool-link:visited{display:inline-flex;align-items:center;gap:7px;color:var(--txt);text-decoration:none;border:1px solid var(--border,#46516b);border-radius:999px;padding:5px 10px;font-size:12px;font-weight:600;line-height:1.4}
.pool-link:hover,.pool-link:focus-visible{color:#e8b957;border-color:#e8b957;outline-offset:3px}
.pool-note{font-size:11px;opacity:.7}

.calendar-trigger{position:absolute;right:8px;bottom:5px;background:transparent;border:0;color:var(--txt);padding:8px;cursor:pointer;font-size:17px}.field-date input{padding-right:46px;cursor:pointer}.date-picker{color:var(--txt);background:var(--card);border:1px solid var(--border);border-radius:16px;padding:16px;width:min(380px,calc(100vw - 24px));max-height:90vh;overflow:auto;background-color:#182438}.date-picker::backdrop{background:rgba(0,0,0,.65)}[data-theme="light"] .date-picker{background:#fff}.calendar-nav{display:flex;gap:6px;align-items:center;flex-wrap:wrap;margin-bottom:14px}.calendar-nav button,.calendar-nav select,.calendar-day{background:var(--input);color:var(--txt);border:1px solid var(--border);border-radius:8px;padding:8px;cursor:pointer}.calendar-nav select{min-width:0;flex:1}.calendar-grid{display:grid;grid-template-columns:repeat(7,minmax(0,1fr));gap:4px;text-align:center}.calendar-day{min-height:38px}.calendar-day:hover,.calendar-day.selected{background:#398853;color:#fff}.calendar-week{color:var(--muted);font-size:12px;padding-bottom:8px}.history-coverage{color:var(--muted);font-size:13px;line-height:1.6}.history-coverage.empty{border-color:#d8a340;color:#efc779}
</style></head>
<body data-theme="dark"><div class="wrap">
<div class="logo-wrap"><img class="logo" src="/solarmining_logo.png" alt="Solar Mining logo" /></div>
<div class="top"><h2 id="dashTitle" class="title"><i class="fa-solid fa-solar-panel"></i> Solar Mining Dashboard</h2>
<div class="actions"><button id="lang" class="btn ghost"><i class="fa-solid fa-earth-europe"></i> HU</button><button id="theme" class="btn warn"><i class="fa-solid fa-circle-half-stroke"></i> Theme</button><button id="downloadHistory" class="btn ghost"><i class="fa-solid fa-download"></i> History JSON</button></div></div>
<div class="grid metrics-grid" id="metrics"></div>
<div class="panel hints-panel"><div class="hints-wrap" id="historyHints"></div></div>
<section class="panel"><h3 id="weeklyTitle"></h3><p id="weeklySummary" class="history-coverage"></p><div class="charts"><div class="card chart-card"><canvas id="weeklyPvChart"></canvas></div><div class="card chart-card"><canvas id="weeklySocChart"></canvas></div></div></section><section class="panel"><h3 id="livePowerTitle"></h3><p id="livePowerNote" class="history-coverage"></p><div class="charts"><div class="card chart-card"><div class="chart-head"><div id="liveL1ChartTitle" class="chart-title"></div></div><canvas id="liveL1Chart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="liveL2ChartTitle" class="chart-title"></div></div><canvas id="liveL2Chart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="liveL3ChartTitle" class="chart-title"></div></div><canvas id="liveL3Chart"></canvas></div><div class="card chart-card"><div class="chart-head"><div id="liveSumChartTitle" class="chart-title"></div></div><canvas id="liveSumChart"></canvas></div></div></section><div class="panel history-coverage">Dátumszűrhető nyers exportok · a fenti heti referenciáktól és élő fázisplotoktól független.</div>
<div class="panel toolbar"><div class="filters">
<div class="field field-date"><label id="lblFrom" for="fromDate">From</label><input id="fromDate" type="text" readonly placeholder="ÉÉÉÉ.HH.NN." aria-label="fromDate" /><button type="button" class="calendar-trigger" data-calendar="fromDate" aria-label="Naptár megnyitása"><i class="fa-solid fa-calendar-days" aria-hidden="true"></i></button></div>
<div class="field field-date"><label id="lblTo" for="toDate">To</label><input id="toDate" type="text" readonly placeholder="ÉÉÉÉ.HH.NN." aria-label="toDate" /><button type="button" class="calendar-trigger" data-calendar="toDate" aria-label="Naptár megnyitása"><i class="fa-solid fa-calendar-days" aria-hidden="true"></i></button></div>
<div class="actions"><div class="range-shortcuts"><button class="btn ghost" id="shortcutDay"><i class="fa-solid fa-clock"></i> Last Day</button><button class="btn ghost" id="shortcutWeek"><i class="fa-solid fa-calendar-week"></i> Last Week</button><button class="btn ghost" id="shortcutMonth"><i class="fa-solid fa-calendar-days"></i> Last Month</button></div><button class="btn ok" id="applyRange"><i class="fa-solid fa-filter"></i> Apply range</button></div>
</div><div class="actions toolbar-actions">
<button id="btnStart" class="btn ok" onclick="act('start')"><i class="fa-solid fa-play"></i> Start miner</button>
<button id="btnStop" class="btn warn" onclick="act('stop')"><i class="fa-solid fa-stop"></i> Stop miner</button>
<button id="btnForce" class="btn danger" onclick="act('force_stop')"><i class="fa-solid fa-power-off"></i> Force stop</button>
</div></div>
<div id="actionResult" class="k"></div>
<div class="panel notice-panel"><div class="notice-head"><div id="notifTitle" class="chart-title"><i class="fa-solid fa-bell"></i> Notifications</div></div><div id="notifList" class="notice-list"></div></div>
<div class="panel history-coverage" id="historyCoverage" role="status"></div>
<dialog id="datePicker" class="date-picker" aria-label="Dátum kiválasztása"><div class="calendar-nav"><button type="button" id="calendarPrevious" aria-label="Előző hónap">‹</button><select id="calendarYear" aria-label="Év"></select><select id="calendarMonth" aria-label="Hónap"></select><button type="button" id="calendarNext" aria-label="Következő hónap">›</button><button type="button" id="calendarClose" aria-label="Naptár bezárása">×</button></div><div class="calendar-grid calendar-week"><span>H</span><span>K</span><span>Sze</span><span>Cs</span><span>P</span><span>Szo</span><span>V</span></div><div id="calendarDays" class="calendar-grid"></div></dialog>
<div class="charts"><div class="card chart-card"><div class="chart-head"><div class="chart-title"><i class="fa-solid fa-solar-panel"></i> <span id="powerChartTitle"></span></div><div id="powerChartSub" class="chart-sub"></div></div><canvas id="powerChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div class="chart-title"><i class="fa-solid fa-bolt"></i> <span id="consumptionChartTitle"></span></div><div id="consumptionChartSub" class="chart-sub"></div></div><canvas id="consumptionChart"></canvas></div><div class="card chart-card"><div class="chart-head"><div class="chart-title"><i class="fa-solid fa-battery-three-quarters"></i> <span id="batteryChartTitle"></span></div><div id="batteryChartSub" class="chart-sub"></div></div><canvas id="batteryChart"></canvas></div></div></div><script>
let currentLang=localStorage.getItem('solar-lang')||'en',currentRange={},lastData,charts={},rangeInitialized=false;
const words={en:{title:'Solar Mining Dashboard',state:'State',battery:'Battery',pv:'PV Power',hash:'Hashrate',weather:'Weather',sunrise:'Sunrise',sunset:'Sunset',clouds:'Clouds',history:'History Points',plan:'Historical energy plan',guard:'Miner ping verification',decision:'Decision',minimum:'Minimum SOC during planned run/refill',end:'SOC at sunset after planned mining stop',pvwh:'Expected PV energy',loadwh:'Expected demand',coverage:'Week reference coverage',floor:'Protected SOC floor',reserve:'Household night reserve',planned:'Planned mining stop',cover:'Sustained solar cover',bridge:'PV deficit to cover / available battery (margin included)',startup:'Startup energy / total start budget',bridgeTime:'Time to sustained cover',houseOnly:'Sunset SOC without mining',houseLoad:'Household load assumed in forecast',noCover:'No sustained cover forecast; bridge unavailable',uncertainPV:'Not estimable from curtailed PV',bufferPV:'Delivered-PV scenario energy',bufferMinimum:'Worst-case SOC at stop (zero PV)',bufferBudget:'Bounded run budget / battery above reserve',bufferMode:'Near-full battery · bounded surplus run',bufferNote:'Zero export: measured PV may follow load when the battery is full. This short run is funded from battery energy above 90%, even assuming zero PV; the sunset SOC cannot be reliably inferred from curtailed PV. Reassess every 5 minutes.',source:'Provided solarman_json history · live phase plots use RAM only',load:'Consumption',measured:'Selected power measurement',collected:'Device collection time',inverter:'Inverter output',phase:'Live phase power',environment:'Garage',temp:'Temperature',hum:'Humidity',waiting:'No current energy plan',idle:'Outside production hours',last:'Last solar reading',lag:'Pool data · may lag',download:'History JSON',from:'From',to:'To',apply:'Apply range',day:'Last day',week:'Last week',month:'Last month',start:'Start miner',stop:'Stop miner',force:'Force stop',notices:'Notifications',empty:'No notifications yet',unknown:'Unavailable',shown:'Chart samples',samples:'measurements',days:'days',no:'No',yes:'Yes',allowed:'Start allowed'},hu:{title:'Solar Mining Dashboard',state:'Állapot',battery:'Töltöttség',pv:'PV teljesítmény',hash:'Hashrate',weather:'Időjárás',sunrise:'Napkelte',sunset:'Napnyugta',clouds:'Felhőzet',history:'Előzményadatok',plan:'Történeti energiaterv',guard:'Miner pinges ellenőrzés',decision:'Döntés',minimum:'Minimum SOC a tervezett futás/visszatöltés alatt',end:'Napnyugtai SOC a tervezett leállítás után',pvwh:'Várható PV energia',loadwh:'Várható fogyasztás',coverage:'Heti referencia lefedettsége',floor:'Védett SOC minimum',reserve:'Éjszakai háztartási tartalék',planned:'Tervezett bányászleállítás',cover:'Tartós napenergia-fedezet',bridge:'PV-hiány fedezetig / elérhető akku (ráhagyással)',startup:'Indítási energia / teljes indítási keret',bridgeTime:'Idő a tartós solar fedezetig',houseOnly:'Napnyugtai SOC bányászat nélkül',houseLoad:'Háztartási terhelés a becslésben',noCover:'Nincs előre jelzett tartós fedezet; bridge nem számítható',uncertainPV:'Visszafogott PV-ből nem becsülhető',bufferPV:'Leadott PV szerinti forgatókönyv',bufferMinimum:'Legrosszabb SOC leálláskor (PV nélkül)',bufferBudget:'Rövid futás kerete / tartalék feletti akku',bufferMode:'Közel tele akku · korlátozott többletfutás',bufferNote:'Nincs visszatáplálás: tele akkunál a mért PV követheti a terhelést. Ezt a rövid futást a 90% feletti akkukeret fedezi, akár nulla PV mellett; a napnyugtai SOC a visszafogott PV-ből nem becsülhető megbízhatóan. Újraszámítás 5 percenként.',source:'Megadott solarman_json előzmények · élő fázisgörbék csak RAM-ban',load:'Fogyasztás',measured:'Kiválasztott teljesítménymérés',collected:'Eszköz mérési ideje',inverter:'Inverterkimenet',phase:'Élő fázisteljesítmény',environment:'Garázs',temp:'Hőmérséklet',hum:'Páratartalom',waiting:'Nincs aktuális energiaterv',idle:'Termelési időn kívül',last:'Utolsó solar mérés',lag:'Pool-adat · késhet',download:'Előzmény JSON',from:'Ettől',to:'Eddig',apply:'Szűrés alkalmazása',day:'Elmúlt nap',week:'Elmúlt hét',month:'Elmúlt hónap',start:'Bányászgép indítása',stop:'Bányászgép leállítása',force:'Kényszerleállítás',notices:'Értesítések',empty:'Még nincs értesítés',unknown:'Nem elérhető',shown:'Grafikonminták',samples:'mérés',days:'nap',no:'Nem',yes:'Igen',allowed:'Indítás engedélyezve'}};
const t=k=>words[currentLang][k]||k;
const esc=v=>String(v??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const num=(v,u='',digits=0)=>v==null||!Number.isFinite(Number(v))?'—':Number(v).toFixed(digits)+u;
const icon=(name)=>`<i class="fa-solid ${name}" aria-hidden="true"></i>`;
const card=(label,value,i='fa-circle-info',kind='card')=>`<div class="${kind}"><div class="${kind==='card'?'k':'hint-title'}">${icon(i)} ${esc(label)}</div><div class="${kind==='card'?'v':'hint-value'}">${esc(value)}</div></div>`;
const huDate=iso=>iso?iso.slice(0,10).replaceAll('-','.')+'.':'—';
const dateText=v=>v?new Intl.DateTimeFormat('hu-HU',{timeZone:'Europe/Budapest',year:'numeric',month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit',second:'2-digit'}).format(new Date(v)):'—';
let calendarTarget,calendarYear,calendarMonth,activePull;
const monthsHU=['január','február','március','április','május','június','július','augusztus','szeptember','október','november','december'];
function setDateValue(id,iso){const el=document.getElementById(id);el.dataset.iso=iso||'';el.value=iso?huDate(iso):'';}
function openCalendar(id){
 calendarTarget=id;
 const iso=document.getElementById(id).dataset.iso||lastData?.history_available_to||new Date().toISOString().slice(0,10);
 calendarYear=Number(iso.slice(0,4));calendarMonth=Number(iso.slice(5,7))-1;
 renderCalendar();document.getElementById('datePicker').showModal();
}
function renderCalendar(){
 const selected=document.getElementById(calendarTarget).dataset.iso;
 const minYear=Math.min(Number((lastData?.history_available_from||'2025').slice(0,4)),calendarYear);
 const maxYear=Math.max(new Date().getFullYear(),Number((lastData?.history_available_to||'2026').slice(0,4)),calendarYear);
 document.getElementById('calendarYear').innerHTML=Array.from({length:maxYear-minYear+1},(_,i)=>`<option value="${minYear+i}" ${minYear+i===calendarYear?'selected':''}>${minYear+i}</option>`).join('');
 document.getElementById('calendarMonth').innerHTML=monthsHU.map((m,i)=>`<option value="${i}" ${i===calendarMonth?'selected':''}>${m}</option>`).join('');
 const offset=(new Date(Date.UTC(calendarYear,calendarMonth,1)).getUTCDay()+6)%7;
 const count=new Date(Date.UTC(calendarYear,calendarMonth+1,0)).getUTCDate();
 const cells=Array.from({length:offset},()=>'<span></span>');
 for(let day=1;day<=count;day++){
  const iso=`${calendarYear}-${String(calendarMonth+1).padStart(2,'0')}-${String(day).padStart(2,'0')}`;
  cells.push(`<button type="button" class="calendar-day ${selected===iso?'selected':''}" data-date="${iso}" aria-label="${huDate(iso)}" ${selected===iso?'aria-current="date"':''}>${day}</button>`);
 }
 document.getElementById('calendarDays').innerHTML=cells.join('');
 for(const button of document.querySelectorAll('.calendar-day'))button.onclick=()=>{setDateValue(calendarTarget,button.dataset.date);rangeInitialized=true;document.getElementById('datePicker').close();};
}
for(const id of ['fromDate','toDate']){
 const el=document.getElementById(id);el.onclick=()=>openCalendar(id);el.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();openCalendar(id);}};
 document.querySelector(`[data-calendar="${id}"]`).onclick=()=>openCalendar(id);
}
document.getElementById('calendarClose').onclick=()=>document.getElementById('datePicker').close();
document.getElementById('calendarMonth').onchange=e=>{calendarMonth=Number(e.target.value);renderCalendar();};
document.getElementById('calendarYear').onchange=e=>{calendarYear=Number(e.target.value);renderCalendar();};
function shiftMonth(delta){const d=new Date(Date.UTC(calendarYear,calendarMonth+delta,1));calendarYear=d.getUTCFullYear();calendarMonth=d.getUTCMonth();renderCalendar();}
document.getElementById('calendarPrevious').onclick=()=>shiftMonth(-1);document.getElementById('calendarNext').onclick=()=>shiftMonth(1);

function renderReferencePlots(d){
 const hu=currentLang==='hu',w=d.weekly_reference||{},m=w.metrics||{},curve=w.curve||[];
 const say=(en,hungarian)=>hu?hungarian:en;
 document.getElementById('weeklyTitle').textContent=say('Current calendar week · fixed historical PV and battery curves','Aktuális naptári hét · fix történeti PV- és akkugörbék');
 document.getElementById('weeklySummary').textContent=`${w.week}. ${say('week','hét')} · ${say('years','évek')}: ${(w.years||[]).join(', ')||'—'} · ${w.days||0} ${t('days')} · ${w.samples||0} ${t('samples')} · ${say('isolated outliers corrected','javított elszigetelt kiugrás')}: ${w.outlier_points||0}. `+
  `${say('PV starts','PV indul')}: ${m.production_start||'—'} · ${say('peak','maximum')}: ${m.peak_time||'—'} / ${num(m.peak_w,' W')} · ${say('miner-only 100% cover','100% minerfedezet, ház nélkül')}: ${m.miner_cover||'—'} · ${say('typical daily PV','tipikus napi PV')}: ${num(m.pv_energy_wh,' Wh')} (${num(m.pv_coverage_hours,' h',1)}). `+
  `SOC ${say('min/max','min/max')}: ${num(m.soc_min,'%')} / ${num(m.soc_max,'%')} · ${say('charging starts','töltés indul')}: ${m.charge_start||'—'} · ${say('discharge begins','merülés indul')}: ${m.discharge_start||'—'} · ${say('anchored SOC full estimate','aktuális SOC-hoz igazított feltöltési becslés')}: ${m.anchored_full_time||'—'}. `+
  say('Equal weight per day; shaded bands show the 25–75% range. These reference curves do not prove today’s battery trajectory.','Minden nap azonos súlyú; az árnyék a 25–75%-os sáv. Referenciagörbék, nem a mai akkumulátorút bizonyítékai.');
 function series(field){const values=curve.map(r=>({x:r.minute,y:r[field]}));if(values.length)values.push({x:1440,y:values[values.length-1].y});return values;}
 for(const [id,field,lower,upper,label,color] of [['weeklyPvChart','pv_w','pv_p25','pv_p75','PV (W)','#e8b957'],['weeklySocChart','soc_pct','soc_p25','soc_p75','SOC (%)','#a78bfa']]){
  if(!charts[id])charts[id]=new Chart(document.getElementById(id),{type:'line',data:{datasets:[]},options:{responsive:true,maintainAspectRatio:false,animation:false,plugins:{legend:{labels:{color:'#94a3b8',filter:item=>item.datasetIndex!==1}}},scales:{x:{type:'linear',min:0,max:1440,ticks:{stepSize:240,color:'#94a3b8',callback:v=>String(Math.floor(v/60)).padStart(2,'0')+':'+String(v%60).padStart(2,'0')}},y:{min:0,...(field==='soc_pct'?{max:100}:{}),ticks:{color:'#94a3b8'}}}}});
  charts[id].data.datasets=[{label:say('Weekly mean ','Heti átlag ')+label,data:series(field),borderColor:color,borderWidth:2,pointRadius:0},
   {label:'25%',data:series(lower),borderWidth:0,pointRadius:0,borderColor:color},
   {label:'25–75%',data:series(upper),borderWidth:0,pointRadius:0,fill:'-1',backgroundColor:field==='pv_w'?'rgba(232,185,87,.14)':'rgba(167,139,250,.14)'}];
  if(field==='pv_w')charts[id].data.datasets.push({label:'100% miner (W)',data:[{x:0,y:w.miner_power_w},{x:1440,y:w.miner_power_w}],borderColor:'#ef7777',borderDash:[6,5],borderWidth:1,pointRadius:0});
  charts[id].update();
 }
 document.getElementById('livePowerTitle').textContent=say('Measured L1 / L2 / L3 / SUM · last 24 h, RAM only','Mért L1 / L2 / L3 / SUM · utolsó 24 óra, csak RAM');
 document.getElementById('livePowerNote').textContent=say('The downloaded exports contain no historical phase columns. Real phase readings appear here after API polls; this bounded buffer is lost on restart and never saved to JSON.','A letöltött exportokban nincs történeti fázisoszlop. Az API valódi fázismérései itt jelennek meg; ez a korlátos puffer újraindításkor törlődik, JSON-ba nem mentjük.');
 const live=d.live_power||[],now=Date.now();
 for(const [id,field,color] of [['liveL1Chart','l1','#60a5fa'],['liveL2Chart','l2','#e8b957'],['liveL3Chart','l3','#f1788c'],['liveSumChart','sum','#68d9ab']]){
  const label=field==='sum'?'SUM':field.toUpperCase();
  document.getElementById(id+'Title').textContent=label+' (W)';
  if(!charts[id])charts[id]=new Chart(document.getElementById(id),{type:'line',data:{datasets:[]},options:{responsive:true,maintainAspectRatio:false,animation:false,scales:{x:{type:'linear',ticks:{maxTicksLimit:8,color:'#94a3b8',callback:v=>new Intl.DateTimeFormat('hu-HU',{timeZone:'Europe/Budapest',hour:'2-digit',minute:'2-digit'}).format(new Date(v))}},y:{min:0,ticks:{color:'#94a3b8'}}},plugins:{legend:{labels:{color:'#94a3b8'}}}}});
  charts[id].options.scales.x.min=now-24*3600000;charts[id].options.scales.x.max=now;
  const source=live.length&&String(live[0].source).startsWith('consumption')?t('load'):t('inverter');
  charts[id].data.datasets=[{label:source+' · '+label+' (W)',data:live.map(r=>({x:new Date(r.ts).getTime(),y:r[field]})),borderColor:color,borderWidth:2,pointRadius:live.length<3?3:0,spanGaps:false}];
  charts[id].update();
 }
}

function render(d){lastData=d;
 document.documentElement.lang='hu';
 if(!rangeInitialized){setDateValue('fromDate',d.history_selected_from);setDateValue('toDate',d.history_selected_to);rangeInitialized=true;}
 document.getElementById('dashTitle').innerHTML=icon('fa-solar-panel')+' '+t('title');
 document.getElementById('lang').innerHTML=icon('fa-earth-europe')+' '+(currentLang==='en'?'HU':'EN');
 const texts={downloadHistory:['download','fa-download'],applyRange:['apply','fa-filter'],shortcutDay:['day','fa-clock'],shortcutWeek:['week','fa-calendar-week'],shortcutMonth:['month','fa-calendar-days'],btnStart:['start','fa-play'],btnStop:['stop','fa-stop'],btnForce:['force','fa-power-off']};
 for(const [id,[key,i]] of Object.entries(texts))document.getElementById(id).innerHTML=icon(i)+' '+esc(t(key));
 document.getElementById('lblFrom').textContent=t('from');document.getElementById('lblTo').textContent=t('to');document.getElementById('notifTitle').innerHTML=icon('fa-bell')+' '+t('notices');
 const physical=d.runtime?.state||'unknown';
 const states={hu:{running:'ping elérhető',starting:'indítás ellenőrzésre vár',off:'ping nem elérhető',stop_pending:'leállítás ellenőrzésre vár',stop_failed:'LEÁLLÍTÁS NINCS IGAZOLVA',stop_unverified:'leállítás nem ellenőrizhető',unknown:'fizikai állapot ismeretlen'},en:{running:'ping reachable',starting:'start unconfirmed',off:'ping unreachable',stop_pending:'shutdown pending verification',stop_failed:'SHUTDOWN UNCONFIRMED',stop_unverified:'shutdown unverifiable',unknown:'physical state unknown'}};
 const state=(states[currentLang]||states.en)[physical]||t('unknown');
 let metrics=card(t('state'),state,'fa-toggle-on',['stop_failed','stop_unverified'].includes(physical)?'runtime-alarm':'')+card(t('battery'),num(d.battery,'%'),'fa-battery-half')+card(t('pv'),num(d.power,' W'),'fa-solar-panel');
 metrics+=`<div class="card"><div class="k">${icon('fa-gauge-high')} ${t('hash')}</div><div class="v">${esc(d.hashrate_text||'N/A')}</div><div class="pool-meta"><a class="pool-link" href="https://unmineable.com/address/${encodeURIComponent(d.wallet_address)}?coin=USDT" target="_blank" rel="noopener noreferrer">unMineable · USDT ${icon('fa-arrow-up-right-from-square')}</a><span class="pool-note">${t('lag')}</span></div></div>`;
 metrics+=card(t('weather'),d.current_condition||t('unknown'),'fa-cloud-sun')+card(t('sunrise'),(d.sunrise||'').slice(11,16)||'—','fa-sun')+card(t('sunset'),(d.sunset||'').slice(11,16)||'—','fa-moon')+card(t('clouds'),num(d.clouds,'%'),'fa-cloud')+card(t('history'),num(d.history_count),'fa-clock-rotate-left');
 document.getElementById('metrics').innerHTML=metrics;
 const hints=d.historical_hints||{},b=hints.energy_budget,meter=d.power_measurement;
 const buffered=b?.projection_mode==='surplus_buffer_run';
 const budget=b?card(t(buffered?'bufferMinimum':'minimum'),num(buffered?b.worst_case_stop_soc:b.minimum_soc,'%'),'fa-battery-quarter','hint-card')+card(t('end'),buffered?t('uncertainPV'):num(b.end_soc,'%'),'fa-battery-full','hint-card')+card(t(buffered?'bufferPV':'pvwh'),num(b.expected_pv_wh,' Wh'),'fa-solar-panel','hint-card')+card(t('loadwh'),num(b.expected_load_wh,' Wh'),'fa-bolt','hint-card')+card(t('floor'),num(hints.min_stop_soc,'%'),'fa-shield-heart','hint-card')+card(t('reserve'),num(hints.late_day_reserve_soc,'%'),'fa-moon','hint-card')+card(t('cover'),dateText(b.cover_time),'fa-sun','hint-card')+card(t('planned'),dateText(b.planned_stop),'fa-clock','hint-card')+card(t('bridge'),(b.required_bridge_wh==null?t('noCover'):num(b.required_bridge_wh,' Wh'))+' / '+num(b.available_bridge_wh,' Wh'),'fa-battery-half','hint-card')+card(t('startup'),num(b.startup_energy_wh,' Wh')+' / '+num(b.required_start_energy_wh,' Wh'),'fa-power-off','hint-card')+card(t('bridgeTime'),num(b.bridge_duration_minutes,' min',1),'fa-clock','hint-card')+card(t('houseOnly'),buffered?t('uncertainPV'):num(b.household_only_end_soc,'%'),'fa-house','hint-card')+card(t('houseLoad'),num(b.household_load_w,' W'),'fa-bolt','hint-card'):card(t('floor'),num(hints.min_stop_soc,'%'),'fa-shield-heart','hint-card')+card(t('reserve'),num(hints.late_day_reserve_soc,'%'),'fa-moon','hint-card')+`<div class="hint-card decision-card">${esc(d.monitoring_mode==='idle_safety'?t('idle'):t('waiting'))}</div>`;
 const bufferInfo=buffered?card(t('bufferBudget'),num(b.required_surplus_wh,' Wh')+' / '+num(b.available_surplus_wh,' Wh'),'fa-battery-half','hint-card')+`<p class="hint-sub">${esc(t('bufferNote'))}</p>`:'';
 const phase=[1,2,3].map(i=>card('INV L'+i,num(d['inv_l'+i],' W'),'fa-bolt','hint-card')).join('')+card(t('inverter'),num(d.inv_lt,' W'),'fa-gauge-high','hint-card')+card(t('temp'),num(d.garage_temp,' °C',1),'fa-temperature-half','hint-card')+card(t('hum'),num(d.garage_hum,'%'),'fa-droplet','hint-card');
 document.getElementById('historyHints').innerHTML=`<section class="hint-section"><h3 class="hint-section-title">${buffered?t('bufferMode'):t('plan')}${b&&!b.safe?(currentLang==='hu'?' · elutasított futás előrejelzése':' · rejected-run forecast'):''}</h3><div class="hints-grid">${budget}${bufferInfo}</div><div class="hint-card decision-card"><div class="hint-title">${icon('fa-list-check')} ${t('decision')}</div><div class="hint-sub">${esc(hints.decision_summary||t('waiting'))}</div><div class="hint-sub">${t('allowed')}: ${hints.start_guard_allow?t('yes'):t('no')}</div><div class="hint-sub">${t('coverage')}: ${num((hints.history_coverage||0)*100,'%')} · ${num(hints.history_days)} ${t('days')}</div><div class="hint-sub">${esc(t('source'))}</div></div></section><section class="hint-section"><h3 class="hint-section-title">${t('phase')} · ${t('environment')}</h3><div class="hints-grid">${phase}</div><div class="hint-card decision-card"><div class="hint-title">${icon('fa-shield-heart')} ${t('guard')}</div><div class="hint-sub">${esc(d.power_guard_reason||t('unknown'))}</div><div class="hint-sub">Ping: ${esc(d.runtime?.target_ip||'192.168.0.185')} · ${esc(dateText(d.runtime?.checked_at))}</div><div class="hint-sub">${currentLang==='hu'?'Kívánt állapot':'Requested state'}: ${esc(d.runtime?.desired_state&&d.runtime.desired_state!=='unknown'?d.runtime.desired_state:d.state||'unknown')} · ${currentLang==='hu'?'Hosszú STOP kísérletek':'Long STOP attempts'}: ${d.runtime?.attempts||0}/${d.runtime?.max_attempts||2}</div>${meter?`<div class="hint-sub">${t('measured')}: ${num(meter.total,' W')} · L1 ${num(meter.l1,' W')} / L2 ${num(meter.l2,' W')} / L3 ${num(meter.l3,' W')}</div><div class="hint-sub">${t('collected')}: ${esc(dateText(meter.at))}</div>`:''}<div class="hint-sub">${d.power_measurement_source==='inverter_output'?t('inverter'):String(d.power_measurement_source||'').startsWith('consumption')?t('load'):t('unknown')}</div><div class="hint-sub">${t('last')}: ${esc(dateText(d.solarman_polled_at))}</div></div></section>`;
 const notices=Array.isArray(d.notifications)?d.notifications:[];
 document.getElementById('notifList').innerHTML=notices.length?notices.slice(0,5).map(n=>`<div class="notice-item ${['info','warn','error','success'].includes(n.level)?n.level:'info'}"><div class="notice-meta">${esc(dateText(n.ts))}</div><div>${esc(String(n.message||'').replace(/(\d{4})-(\d{2})-(\d{2})(T| )?/g,(_,y,m,day,sep)=>`${y}.${m}.${day}.${sep?' ':''}`))}</div></div>`).join(''):`<div class="notice-empty">${t('empty')}</div>`;
 const coverage=document.getElementById('historyCoverage');coverage.className='panel history-coverage'+(d.history_count?'':' empty');coverage.textContent=(currentLang==='hu'?'Betöltött előzmények: ':'Loaded history: ')+huDate(d.history_available_from)+' – '+huDate(d.history_available_to)+' · '+d.history_files+' JSON · '+d.history_total_count+' '+t('samples')+(d.history_count?'':(currentLang==='hu'?' · A kiválasztott időszakhoz nincs betöltött mérés. Ellenőrizd az előzménykönyvtárat.':' · No loaded measurements in the selected period. Check the history directory.'));
 const h=d.history||[],step=Math.max(1,Math.ceil(h.length/2000)),rows=h.filter((_,i)=>i%step===0);
 for(const [id,key,title,color,unit] of [['powerChart','power',t('pv'),'#4ade80','W'],['consumptionChart','consumption',t('load'),'#60a5fa','W'],['batteryChart','battery',t('battery'),'#a78bfa','%']]){
  document.getElementById(id+'Title').textContent=title;document.getElementById(id+'Sub').textContent=`solarman_json · ${rows.length}/${h.length} ${t('samples')}`;
  if(!charts[id])charts[id]=new Chart(document.getElementById(id),{type:'line',data:{labels:[],datasets:[]},options:{responsive:true,maintainAspectRatio:false,animation:false,interaction:{mode:'nearest',intersect:false,axis:'x'},plugins:{legend:{labels:{color:'#94a3b8'}},tooltip:{backgroundColor:'rgba(14,23,41,.95)',padding:12,cornerRadius:12}},scales:{x:{ticks:{maxTicksLimit:8,color:'#94a3b8'}},y:{min:0,...(key==='battery'?{max:100}:{}),ticks:{color:'#94a3b8'}}}}});
  charts[id].data={labels:rows.map(r=>dateText(r.ts)),datasets:[{label:title+' ('+unit+')',data:rows.map(r=>r[key]),borderColor:color,backgroundColor:color,pointRadius:0,pointHoverRadius:5,borderWidth:2,tension:.2}]};charts[id].update();
 }
 renderReferencePlots(d);
}
async function pull(){if(activePull)activePull.abort();const controller=new AbortController();activePull=controller;try{const r=await fetch('/api/snapshot?'+new URLSearchParams(currentRange),{signal:controller.signal});const data=await r.json();if(!r.ok)throw Error(data.error||'HTTP '+r.status);if(!controller.signal.aborted)render(data);}catch(e){if(e.name!=='AbortError')showActionResult(String(e),'err');}}

function showActionResult(message,level='warn'){const el=document.getElementById('actionResult');el.className='k show '+level;el.textContent=message;}
async function act(action){const buttons=['btnStart','btnStop','btnForce'].map(id=>document.getElementById(id));buttons.forEach(b=>b.disabled=true);try{const r=await fetch('/api/action',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action})});const d=await r.json();showActionResult(d.message,d.ok?'ok':'err');}catch(e){showActionResult(String(e),'err');}finally{buttons.forEach(b=>b.disabled=false);}}
function setRangeDays(days){rangeInitialized=true;const latest=lastData?.history_available_to||new Date().toISOString().slice(0,10);const to=new Date(latest+'T12:00:00Z'),from=new Date(to);from.setUTCDate(to.getUTCDate()-days);setDateValue('fromDate',from.toISOString().slice(0,10));setDateValue('toDate',latest);applyRange();}
function applyRange(){currentRange={from:document.getElementById('fromDate').dataset.iso||'',to:document.getElementById('toDate').dataset.iso||''};pull();}
document.getElementById('applyRange').onclick=applyRange;for(const [id,days] of [['shortcutDay',1],['shortcutWeek',7],['shortcutMonth',30]])document.getElementById(id).onclick=()=>setRangeDays(days);
document.getElementById('downloadHistory').onclick=()=>{window.location.href='/api/history/download';};
document.body.dataset.theme=localStorage.getItem('solar-theme')||'dark';document.getElementById('theme').onclick=()=>{document.body.dataset.theme=document.body.dataset.theme==='dark'?'light':'dark';localStorage.setItem('solar-theme',document.body.dataset.theme);};document.getElementById('lang').onclick=()=>{currentLang=currentLang==='en'?'hu':'en';localStorage.setItem('solar-lang',currentLang);if(lastData)render(lastData);};
pull();setInterval(pull,10000);

</script></body></html>
"""


def _weekly_reference(now):
    week=now.isocalendar().week
    profile=((historical_profile or {}).get('weeks') or {}).get(week,{})
    with snapshot_lock:
        soc=_shared_snapshot.get('battery')
    return {**profile,'week':week,'reference_year':now.isocalendar().year,
            'metrics':week_metrics(profile,MINER_POWER_W,soc,now.hour*60+now.minute),
            'miner_power_w':MINER_POWER_W,'fixed_axis_minutes':[0,1440]}


def _build_snapshot_payload(from_date: Optional[str] = None, to_date: Optional[str] = None) -> Dict[str, Any]:
    with snapshot_lock:
        snap = dict(_shared_snapshot)
        hist = list((historical_profile or {}).get("rows",[]))
    for key in ('battery','power','inv_lt','inv_l1','inv_l2','inv_l3','garage_temp','garage_hum','clouds'):
        value = _safe_float(snap.get(key), None)
        snap[key] = value if value is not None and math.isfinite(value) else None
    with snapshot_lock:
        live_power=[dict(p) for p in _live_power_points if datetime.fromisoformat(p['ts'])>=datetime.now(tz=budapest_tz)-timedelta(hours=24)]
    notices = list(web_notifications)[:5]

    now = datetime.now(tz=budapest_tz)
    def parse_date(value):
        for pattern in ('%Y-%m-%d','%Y.%m.%d.','%Y.%m.%d'):
            try:
                return datetime.strptime(value,pattern).replace(tzinfo=budapest_tz)
            except ValueError:
                continue
        raise ValueError('Use YYYY-MM-DD or YYYY.MM.DD. dates')
    latest = datetime.fromisoformat(hist[-1]['ts']) if hist else now
    start_ts = parse_date(from_date) if from_date else latest.replace(hour=0,minute=0,second=0,microsecond=0)-timedelta(days=30)
    end_ts = parse_date(to_date)+timedelta(days=1) if to_date else latest+timedelta(seconds=1)
    if start_ts >= end_ts:
        raise ValueError('Start date must not be after end date')
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
    with runtime_lock:
        runtime=_runtime_guard.status(now)

    return {
        "battery": snap.get("battery", 0),
        "power": snap.get("power"),
        "inv_lt": snap.get("inv_lt"),
        "inv_l1": snap.get("inv_l1"),
        "inv_l2": snap.get("inv_l2"),
        "inv_l3": snap.get("inv_l3"),
        "garage_temp": snap.get("garage_temp"),
        "garage_hum": snap.get("garage_hum"),
        "state": snap.get("state", "unknown"),
        "runtime": runtime,
        "current_condition": snap.get("current_condition", "unknown"),
        "weather_icon": _weather_icon(snap.get("current_condition", "")),
        "clouds": snap.get("clouds", 0),
        "hashrate_hs": snap.get("hashrate_hs"),
        "hashrate_mhs": snap.get("hashrate_mhs"),
        "hashrate_text": _format_hashrate(snap.get("hashrate_hs")),
        "power_guard_reason": runtime['reason'],
        "power_measurement_error":_power_measurement_error,
        "power_measurement_source": _latest_power_sample.source if _latest_power_sample else None,
        "power_measurement": ({"total": _latest_power_sample.total,
                               "l1": _latest_power_sample.l1,
                               "l2": _latest_power_sample.l2,
                               "l3": _latest_power_sample.l3,
                               "at": _latest_power_sample.at.isoformat(),
                               "fresh": PowerSample.fresh(_latest_power_sample, now)}
                              if _latest_power_sample else None),
        "monitoring_mode": snap.get("monitoring_mode", "production_window"),
        "solarman_polled_at": snap.get("solarman_polled_at"),
        "solarman_poll_interval_seconds": snap.get("solarman_poll_interval_seconds"),
        "mining_pool": "unMineable",
        "mining_coin": MINING_COIN,
        "mining_algorithm": MINING_ALGORITHM,
        "mining_worker": MINING_WORKER,
        "wallet_address": _effective_wallet_address(),
        "sunrise": snap.get("sunrise").isoformat() if snap.get("sunrise") else "",
        "sunset": snap.get("sunset").isoformat() if snap.get("sunset") else "",
        "weekly_reference": _weekly_reference(now),
        "live_power": live_power,
        "live_power_window_hours":24,
        "miner_power_w":MINER_POWER_W,
        "afternoon_cutoff":{"hour":HARD_AFTERNOON_STOP_HOUR,"soc":HARD_AFTERNOON_STOP_SOC,"pv_w":AFTERNOON_PV_STOP_W},
        "history_source": "solarman_json",
        "history_selected_from": start_ts.date().isoformat(),
        "history_selected_to": (end_ts-timedelta(seconds=1)).date().isoformat(),
        "history_available_from": hist[0]['ts'][:10] if hist else None,
        "history_available_to": hist[-1]['ts'][:10] if hist else None,
        "history_total_count": len(hist),
        "history_files": (historical_profile or {}).get('files',0),
        "history_directories": (historical_profile or {}).get('directories',[]),
        "history_count": len(filtered_hist),
        "history": filtered_hist,
        "historical_hints": snap.get("historical_hints", {}),
        "notifications": notices,
    }


class WebHandler(BaseHTTPRequestHandler):
    def _write(self, code: int, body: bytes, ctype: str):
        try:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True


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
            try:
                payload = json.dumps(_build_snapshot_payload(
                    qs.get("from",[None])[0],qs.get("to",[None])[0])).encode("utf-8")
            except ValueError as error:
                self._write(400,json.dumps({'error':str(error)}).encode('utf-8'),'application/json')
                return
            self._write(200, payload, "application/json")
            return
        if parsed.path == "/api/history/download":
            rows = (historical_profile or {}).get('rows',[])
            self._write(200,json.dumps(rows,ensure_ascii=False).encode('utf-8'),'application/json; charset=utf-8')
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
    global _latest_power_sample

    if historical_profile is None:
        historical_profile = build_historical_profile(HISTORY_DIR)


    prev_state,uptime=load_prev_state()
    with runtime_lock:
        _runtime_guard.set_desired(prev_state)
    threading.Thread(target=_ping_monitor_loop,name='miner-ping-monitor',daemon=True).start()
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
    last_solar_slot = None
    last_solar_attempt = None

    while True:
        now = datetime.now(tz=budapest_tz)
        solar_slot = _solarman_poll_slot(now, sunrise, sunset)
        solar_due = _solarman_poll_due(now, solar_slot, last_solar_slot, last_solar_attempt)
        solar_interval = solar_slot[0]

        # Concurrently read DHT and prefetch next weather + token
        fut_dht = executor.submit(read_dht11, prev_garage_temp, prev_garage_hum)
        fut_weather = executor.submit(get_current_weather, WEATHER_API, LOCATION_LAT, LOCATION_LON)
        fut_token = None
        if solar_due:
            last_solar_slot = solar_slot
            last_solar_attempt = now
            fut_token = executor.submit(get_access_token)

        # Use DHT reading immediately for local decisions
        try:
            garage_data = fut_dht.result(timeout=5)
        except Exception:
            garage_data = {'temperature': prev_garage_temp, 'humidity': prev_garage_hum}

        garage_temp = _safe_float(garage_data.get('temperature'), None)
        garage_hum = _safe_float(garage_data.get('humidity'), None)
        garage_temp = garage_temp if garage_temp is not None and math.isfinite(garage_temp) else None
        garage_hum = garage_hum if garage_hum is not None and math.isfinite(garage_hum) else None
        valid_garage_sample = garage_temp is not None and garage_hum is not None
        if valid_garage_sample:
            garage_temp_history.append(garage_temp)
            garage_hum_history.append(garage_hum)

        if valid_garage_sample and len(garage_temp_history) == garage_temp_history.maxlen:
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
        control_details = _control_window_details(now, sunrise, sunset, historical_profile)
        within_active = bool(control_details.get("active", False))
        print(f"Control window: {within_active} ({control_details.get('reason')})")

        _update_pool_hashrate(now)
        with snapshot_lock:
            _shared_snapshot.update({"garage_temp": garage_temp, "garage_hum": garage_hum,
                                     "solarman_poll_interval_seconds": solar_interval})
        if within_active and not solar_due:
            print(f"[Solarman] Waiting for next {solar_interval // 60}-minute polling slot.")
            sleep_until_next_5min(offset_seconds=60)
            continue
        if within_active:
            try:
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
                raw_data = {}
                if token:
                    used_quote += 1
                    save_quote_usage(used_quote)
                    raw_data = fetch_current_data(token)
                data = raw_data or {}
                if not _has_solarman_payload(data):
                    record_live_power(now,state or 'unknown',{},poll_interval_seconds=solar_interval)
                    print('[History model] Live data unavailable; keeping controller state without new GPIO decisions.')
                    sleep_until_next_5min(offset_seconds=60)
                    continue

                _latest_power_sample = _extract_power_sample(raw_data or {}, now)
                (battery, power, state, current_condition, sunrise, sunset, clouds,
                f1_cond, f1_clouds, f1_ts, f3_cond, f3_clouds, f3_ts, hist_hints) = check_crypto_production_conditions(
                    data, WEATHER_API, LOCATION_LAT, LOCATION_LON
                )
                # Hardware supervision uses only this fresh API response.
                record_live_power(now, state or "unknown", raw_data or {}, poll_interval_seconds=solar_interval)

                # update shared snapshot for telegram thread
                with snapshot_lock:
                    _shared_snapshot.update({
                        "monitoring_mode": "production_window",
                        "solarman_polled_at": now.isoformat(),
                        "solarman_poll_interval_seconds": solar_interval,
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
            print("Garage temperature: " + (f"{garage_temp} °C" if garage_temp is not None else "unavailable"))
            print("Garage humidity: " + (f"{garage_hum}%" if garage_hum is not None else "unavailable"))

            # Telegram polling is already running in its own thread.
            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")
        else:
            print(f"[Safety monitoring] Outside production window: Solarman every {solar_interval // 60} minutes. (Sunset stop: {sunset.strftime('%H:%M') if isinstance(sunset,datetime) else 'N/A'})")
            print(f"Time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n")

            (current_condition, sunrise, sunset, clouds,
             f1_cond, f1_clouds, f1_ts,
             f3_cond, f3_clouds, f3_ts, weather_outlook) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

            state = "stop"
            with runtime_lock:
                _runtime_guard.set_desired('stop')
            if prev_state != "stop":
                prev_state = state
                uptime = now
                save_prev_state(prev_state, uptime)
            if solar_due:
                _idle_monitor_cycle(now, fut_token, garage_temp, garage_hum, poll_interval_seconds=solar_interval)

            # update snapshot for telegram thread even during idle
            with snapshot_lock:
                _shared_snapshot.update({
                    "state": state or "stop",
                    "current_condition": current_condition or "unknown",
                    "sunrise": sunrise, "sunset": sunset, "clouds": clouds or 0,
                    "garage_temp": garage_temp, "garage_hum": garage_hum,
                    "historical_hints": _idle_historical_hints()
                })

            pct = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0
            print("Garage temperature: " + (f"{garage_temp} °C" if garage_temp is not None else "unavailable"))
            print("Garage humidity: " + (f"{garage_hum}%" if garage_hum is not None else "unavailable"))
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
