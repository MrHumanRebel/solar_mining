import requests
import hashlib
import json
import time
from datetime import datetime, timedelta
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
import statistics
from pytz import timezone
from pathlib import Path
from typing import Any, Dict, Tuple, Optional, List

# NEW: threading / futures
import threading
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

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
    "clouds": 0, "garage_temp": 0, "garage_hum": 0
}

# Detect Raspberry Pi
if platform.system() == "Linux" and any(arch in platform.machine() for arch in ['arm', 'aarch64', 'armv7l']):
    is_rpi = True

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
        print("Raspberry Pi OLED dependencies loaded.")
    except ImportError as e:
        print(f"Failed to import Raspberry Pi-specific modules: {e}")
        sys.exit(1)
else:
    print("Not running on Raspberry Pi. Skipping OLED display setup.")

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

# =========================
# ORIGINAL FUNCTION NAMES (REFACTORED INSIDE)
# =========================
def init_display():
    """Initialize OLED on Raspberry Pi."""
    if not is_rpi:
        return
    global oled, image, draw, font
    i2c = busio.I2C(board.SCL, board.SDA)
    oled = adafruit_ssd1306.SSD1306_I2C(128, 32, i2c)
    image = Image.new("1", (oled.width, oled.height))
    draw = ImageDraw.Draw(image)
    font = ImageFont.load_default()
    oled.fill(0)
    oled.show()
    print("OLED initialized")

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

def get_temperatures():
    """
    Returns a dict of temperatures from available sensors.
    Prefer 'vcgencmd' when available (RPi), otherwise thermal zones.
    """
    temps = {}
    try:
        cpu_temp = os.popen("vcgencmd measure_temp").readline().strip()
        if cpu_temp.startswith("temp="):
            temps["CPU"] = cpu_temp.replace("temp=", "")
            return temps
    except Exception:
        pass

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
    return temps

def read_dht11(prev_temperature, prev_humidity):
    if not is_rpi:
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

def handle_telegram_messages(battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum):
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
                process_message(text, battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum)
    except requests.exceptions.RequestException as e:
        print(f"Error while handling Telegram messages: {e}")

def process_message(message_text, battery, power, state, current_condition, sunrise, sunset, clouds, garage_temp, garage_hum):
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

        message = (
            f"Battery: {battery}%\n"
            f"Power: {power}W\n"
            f"State: {state}\n"
            f"Condition: {current_condition}\n"
            f"Sunrise: {sunrise.strftime('%H:%M')}\n"
            f"Sunset: {sunset.strftime('%H:%M')}\n"
            f"Clouds: {clouds}%\n"
            f"Garage Temp: {garage_temp}C\n"
            f"Garage Humidity: {garage_hum}%"
            f"\nInverter Output (per phase):\n"
            f"  L1: {l1_str}\n"
            f"  L2: {l2_str}\n"
            f"  L3: {l3_str}\n"
            f"  Total: {lt_str}\n"
            f"IP: {ip}\n"
            f"RAM Usage: {ram}\n"
            f"CPU Usage: {cpu}\n"
            f"CPU Temp: {temps.get('cpu-thermal') or temps.get('CPU') or 'N/A'}\n"
            f"Quote usage: {used_quote} / {QUOTE_LIMIT} ({percentage:.2f}%)"
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
        press_power_button(16, 0.55)
        send_telegram_message("Crypto production started! Pressed power button.")
    if message_text == "/stop":
        press_power_button(16, 0.55)
        send_telegram_message("Crypto production stopped! Pressed power button.")
    if message_text == "/force_stop":
        press_power_button(16, 10)
        send_telegram_message("Crypto production force stopped! Pressed power button for 10 seconds.")

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
        print(f"[Warning] Failed to fetch current device data: {e}")
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
    print(f"Pressing power button on GPIO pin {gpio_pin} for {press_time} seconds...")
    with gpio_lock:
        GPIO.setmode(GPIO.BCM)
        GPIO.setup(gpio_pin, GPIO.OUT, initial=GPIO.LOW)
        GPIO.output(gpio_pin, GPIO.HIGH)
        time.sleep(press_time)
        GPIO.output(gpio_pin, GPIO.LOW)
        GPIO.cleanup()
    print("Power button press completed.")

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

        # IMMEDIATE POWER-BASED STOP RULE
        if (inv_l1 > 2000) or (inv_l2 > 2000) or (inv_l3 > 2000) or (inv_lt > 5000):
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
                    f3_cond, f3_clouds, f3_ts)

        # ===== existing logic continues below =====
        if ((prev_state == "production" and battery_charge < 20) or
            (prev_state == "production" and now.hour > 14 and battery_charge < 80)):
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
            (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and current_power > 0 and battery_charge >= 35 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 65 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 55 and now.hour < 12)
            or (any(k in current_condition for k in solar_keywords) and any(k in f1_cond for k in solar_keywords) and battery_charge >= 45 and now.hour < 11)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and current_power > 0 and battery_charge >= 35 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 65 and now.hour < 13)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 55 and now.hour < 12)
            or (any(k in current_condition for k in solar_keywords) and any(k in f3_cond for k in solar_keywords) and battery_charge >= 45 and now.hour < 11)
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
            (battery_charge <= 90)
            or (current_power <= 150)
            or (any(k in current_condition for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
            or (any(k in f1_cond for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
            or (any(k in f3_cond for k in non_solar_keywords) and battery_charge <= 95 and current_power <= 1000)
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
                f3_cond, f3_clouds, f3_ts)

    except Exception as e:
        print(f"Error while checking production conditions: {e}")
        return None, None, state, sunrise, sunset


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
                snap["clouds"], snap["garage_temp"], snap["garage_hum"]
            )
            # handle_telegram_messages long-polls (25s). No extra sleep needed.
        except Exception as e:
            print(f"[telegram loop] error: {e}")
            time.sleep(2)  # brief backoff on errors


def main_loop():
    global prev_state, state, used_quote, sunrise, sunset, uptime

    used_quote = load_quote_usage()
    (current_condition, sunrise, sunset, clouds,
     f1_cond, f1_clouds, f1_ts,
     f3_cond, f3_clouds, f3_ts) = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

    # START TELEGRAM THREAD ONCE
    t_thread = threading.Thread(target=_telegram_loop, name="telegram-poller", daemon=True)
    t_thread.start()

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

        if now.month == 1 and now.day == 1 and used_quote != 0:
            print("January 1st detected – resetting quote usage to 0.")
            send_telegram_message("January 1st detected – resetting quote usage to 0.")
            used_quote = 0
            save_quote_usage(used_quote)

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
                 f1_cond, f1_clouds, f1_ts,
                 f3_cond, f3_clouds, f3_ts) = check_crypto_production_conditions(
                    data, WEATHER_API, LOCATION_LON, LOCATION_LON  # NOTE: original signature uses (api, lat, lon); keep as is if needed
                )
                # ^ If your original order is (api, lat, lon), correct the above to LOCATION_LAT, LOCATION_LON

                # update shared snapshot for telegram thread
                with snapshot_lock:
                    _shared_snapshot.update({
                        "battery": battery or 0,
                        "power": power or 0,
                        "state": state or "unknown",
                        "current_condition": current_condition or "unknown",
                        "sunrise": sunrise, "sunset": sunset, "clouds": clouds or 0,
                        "garage_temp": garage_temp or 0, "garage_hum": garage_hum or 0
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
                    "garage_temp": garage_temp or 0, "garage_hum": garage_hum or 0
                })

            pct = (used_quote / QUOTE_LIMIT) * 100 if QUOTE_LIMIT else 0
            print(f"Garage temperature: {garage_temp}C")
            print(f"Garage humidity: {garage_hum}%")
            print(f"Quote usage: {used_quote} / {QUOTE_LIMIT} ({pct:.2f}%)")

            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")

if __name__ == '__main__':
    if is_rpi:
        init_display()
    main_loop()
