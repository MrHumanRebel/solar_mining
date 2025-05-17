import requests
import hashlib
import json
import time
from datetime import datetime
import os
import psutil
import socket
import platform
import sys
import re
import math
import subprocess
from datetime import datetime, timedelta


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


print(platform.machine())
print(platform.system())
is_rpi = None

# Telegram session
session = requests.Session()
session.headers.update({'Connection': 'close'})

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
        print("Raspberry Pi OLED dependencies loaded.")
    except ImportError as e:
        print(f"Failed to import Raspberry Pi-specific modules: {e}")
        sys.exit(1)
else:
    print("Not running on Raspberry Pi. Skipping OLED display setup.")

####################################################################

# Global variables
last_update_id = None
prev_state = None
state = None
uptime = None

oled = None
image = None
draw = None
font = None

def init_display():
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

def clean_value(value):
    # Ensure the value is a string before applying re.sub
    return int(float(re.sub(r'[^\d.]+', '', str(value))))

def write_to_display(state_text, soc, solar_power, weather_condition, temperature, humidity):
    flush_display()
    draw.rectangle((0, 0, oled.width, oled.height), outline=0, fill=0)

    ip = get_ip_address()
    ram = clean_value(get_ram_usage())
    cpu = clean_value(get_cpu_usage())
    temperature = clean_value(temperature)
    humidity = clean_value(humidity)
    soc = clean_value(soc)
    solar_power = clean_value(solar_power)

    line1 = f"SOC: {soc}% PWR: {solar_power}W"
    line2 = f"{state_text}"
    line3 = f"{weather_condition} {temperature}C {humidity}%"
    line4 = f""

    draw.text((0, 0), line1, font=font, fill=25)
    draw.text((0, 8), line2, font=font, fill=25)
    draw.text((0, 16), line3, font=font, fill=25)
    draw.text((0, 24), line4, font=font, fill=25)

    oled.image(image)
    oled.show()

def sleep_until_next_5min(offset_seconds=60):
    now = datetime.now()
    seconds_since_hour = now.minute * 60 + now.second
    next_5_min = ((seconds_since_hour // 300) + 1) * 300
    target_seconds = next_5_min + offset_seconds
    sleep_seconds = target_seconds - seconds_since_hour
    if sleep_seconds < 0:
        sleep_seconds += 3600
    print(f"Sleeping for {sleep_seconds} seconds...")
    time.sleep(sleep_seconds)

def send_telegram_message(message, max_retries=3):
    url = f'https://api.telegram.org/bot{BOT_TOKEN}/sendMessage'
    payload = {'chat_id': CHAT_ID, 'text': message}

    for attempt in range(1, max_retries + 1):
        try:
            response = session.post(url, data=payload, timeout=10)
            response.raise_for_status()
            print("Telegram message sent successfully.")
            return
        except requests.exceptions.RequestException as e:
            print(f"[Attempt {attempt}] Failed to send Telegram message:", e)
            if attempt < max_retries:
                time.sleep(2 ** attempt)  # Exponential backoff: 2s, 4s, 8s
            else:
                print("All retry attempts failed.")

def handle_telegram_messages():
    global last_update_id
    try:
        url = f'https://api.telegram.org/bot{BOT_TOKEN}/getUpdates'
        if last_update_id:
            url += f'?offset={last_update_id + 1}'
        
        response = session.get(url)
        response.raise_for_status()
        data = response.json()
        
        for update in data.get('result', []):
            last_update_id = update['update_id']  # Update the last processed update ID
            if 'message' in update and 'text' in update['message']:
                process_message(update['message']['text'], data)
    except requests.exceptions.RequestException as e:
        print("Error while handling Telegram messages:", e)

def process_message(message_text, data):
    if message_text == "/stats":
        if data:
            # Search for BMS_SOC in the dataList
            soc = next((item['value'] for item in data['dataList'] if item['name'] == 'BMS_SOC'), None)
            # If BMS_SOC is not found, handle the case gracefully
            if soc is None:
                soc = "N/A"  # or another fallback value
            # Extracting the solar power as an example
            solar_power = next((item['value'] for item in data['dataList'] if item['name'] == 'Total Solar Power'), None)
            if solar_power is None:
                solar_power = "N/A"  # or another fallback value
            message = f" Battery: {soc}%\n Solar: {solar_power}W"

def load_quote_usage():
    if os.path.exists(QUOTE_FILE):
        with open(QUOTE_FILE, 'r') as f:
            return json.load(f).get('used_quote', 0)
    return 0

def save_quote_usage(used_quote):
    with open(QUOTE_FILE, 'w') as f:
        json.dump({'used_quote': used_quote}, f, indent=4)

def sha256_hash(password):
    passwd = hashlib.sha256(password.encode('utf-8')).hexdigest()
    print(f"Hashed password: {passwd}")
    return passwd

def get_access_token():
    print("Getting access token...")
    url = f' https://globalapi.solarmanpv.com/account/v1.0/token?appId={APP_ID}&language=en'
    headers = {'Content-Type': 'application/json'}
    payload = {
        'appSecret': APP_SECRET,
        'email': EMAIL,
        'password': sha256_hash(PASSWORD)
    }
    response = requests.post(url, headers=headers, json=payload)
    response.raise_for_status()

    # Debug: Print the entire response to see its structure
    print("Response received!")

    # Ensure 'access_token' is extracted correctly
    access_token = response.json().get('access_token')
    if not access_token:
        raise ValueError("Access token not found in the response.")
    print("Access token received!")
    return access_token

def fetch_current_data(access_token):
    print("Fetching current device data...")
    url = f'https://globalapi.solarmanpv.com/device/v1.0/currentData?appId={APP_ID}&language=en'
    headers = {
        'Authorization': f'Bearer {access_token}',
        'Content-Type': 'application/json'
    }
    payload = {'deviceSn': DEVICE_SN}
    response = requests.post(url, headers=headers, json=payload)
    response.raise_for_status()
    print("Current data fetched successfully.")
    return response.json()

def store_data(data, filename=SOLARMAN_FILE):
    with open(filename, 'w') as f:
        json.dump(data, f, indent=4)
    print(f"Data stored to {filename}")

def load_data(filename=SOLARMAN_FILE):
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            return json.load(f)
    print(f"File {filename} not found. Returning empty data.")

def load_prev_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, 'r') as f:
            data = json.load(f)
            prev_state = data.get('prev_state', None)
            uptime_str = data.get('uptime', None)
            uptime = datetime.fromisoformat(uptime_str) if uptime_str else None
            return prev_state, uptime
    return None, None

def save_prev_state(state, uptime):
    # Convert uptime to string if it's a datetime object
    uptime_str = uptime.isoformat() if isinstance(uptime, datetime) else uptime
    with open(STATE_FILE, 'w') as f:
        json.dump({'prev_state': state, 'uptime': uptime_str}, f, indent=4)

def get_current_weather(api_key, location_lat, location_lon):
    ################################################
    # CURRENT WEATHER
    ################################################
    url = f"https://api.openweathermap.org/data/2.5/weather?lat={location_lat}&lon={location_lon}&appid={api_key}&units=metric"
    
    response = requests.get(url)
    response.raise_for_status()
    data = response.json()

    current_condition = data['weather'][0]['description'].lower()
    temperature = data['main']['temp']
    humidity = data['main']['humidity']
    clouds = data['clouds']['all'] 
    sunrise_ts = data['sys']['sunrise']
    sunset_ts = data['sys']['sunset']

    sunrise_dt = datetime.fromtimestamp(sunrise_ts)
    sunset_dt = datetime.fromtimestamp(sunset_ts)

    #sunrise_hour = math.floor(sunrise_dt.hour + sunrise_dt.minute / 60)
    #sunset_hour = math.ceil(sunset_dt.hour + sunset_dt.minute / 60)

    ################################################
    # FUTURE WEATHER
    ################################################
    url = f"https://api.openweathermap.org/data/2.5/forecast?lat={location_lat}&lon={location_lon}&appid={api_key}&units=metric"
    
    response = requests.get(url)
    response.raise_for_status()
    forecast_data = response.json()

    forecast_1h_data = forecast_data['list'][0]
    forecast_1h_temp = forecast_1h_data['main']['temp']
    forecast_1h_humidity = forecast_1h_data['main']['humidity']
    forecast_1h_clouds = forecast_1h_data['clouds']['all']
    forecast_1h_condition = forecast_1h_data['weather'][0]['description'].lower()
    forecast_1h_timestamp = forecast_1h_data['dt_txt']

    forecast_3h_data = forecast_data['list'][1]
    forecast_3h_temp = forecast_3h_data['main']['temp']
    forecast_3h_humidity = forecast_3h_data['main']['humidity']
    forecast_3h_clouds = forecast_3h_data['clouds']['all']
    forecast_3h_condition = forecast_3h_data['weather'][0]['description'].lower()
    forecast_3h_timestamp = forecast_3h_data['dt_txt']

    return (
        current_condition, temperature, humidity, sunrise_dt, sunset_dt, clouds,
        forecast_1h_condition, forecast_1h_temp, forecast_1h_humidity, forecast_1h_clouds, forecast_1h_timestamp,
        forecast_3h_condition, forecast_3h_temp, forecast_3h_humidity, forecast_3h_clouds, forecast_3h_timestamp
    )

def press_power_button(gpio_pin, press_time):
    print(f"Pressing power button on GPIO pin {gpio_pin} for {press_time} seconds...")
    GPIO.setmode(GPIO.BCM)
    GPIO.setup(gpio_pin, GPIO.OUT, initial=GPIO.LOW)
    GPIO.output(gpio_pin, GPIO.HIGH)
    time.sleep(press_time)
    GPIO.output(gpio_pin, GPIO.LOW)
    GPIO.cleanup()
    print("Power button press completed.")

def check_uptime(now, prev_state):
    global uptime
    miner_ip = "192.168.0.200"
    difference = now - uptime
    hours, remainder = divmod(difference.seconds, 3600)
    minutes, _ = divmod(remainder, 60)

    print(f"Pinging {miner_ip} to check uptime...")
    try:
        # Use ping command depending on the OS
        result = subprocess.run(["ping", "-c", "1", "-W", "2", miner_ip], stdout=subprocess.DEVNULL)
        if result.returncode != 0:
            print("No reply!")
            if prev_state == "production":
                print(f"No reply from {miner_ip}. Attempting restart sequence...")
                press_power_button(16, 10)
                time.sleep(15)
                press_power_button(16, 0.5)
                print("Restart sequence completed.")
                uptime = now
                save_prev_state(prev_state, uptime)
        if result.returncode == 0:
            print("Reply!")
            if prev_state == "stop":
                print(f"Reply from {miner_ip}. Attempting force shutdown sequence...")
                press_power_button(16, 10)
                time.sleep(5)
                print("Force shutdown completed.")
                uptime = now
                save_prev_state(prev_state, uptime)
        if prev_state == "production":
            print(f"{miner_ip} is online for {difference.days * 24 + hours} hours and {minutes} minutes")
        elif prev_state == "stop":
            print(f"{miner_ip} is offline for {difference.days * 24 + hours} hours and {minutes} minutes")
    except Exception as e:
        print(f"Error during uptime check: {e}")
    
def check_crypto_production_conditions(data, weather_api_key, location_lat, location_lon):
    global prev_state, state, used_quote, sunrise, sunset, uptime
    prev_state, uptime = load_prev_state()

    try:
        # Fetch current weather condition, temperature, and humidity
        current_condition, temperature, humidity, sunrise, sunset, clouds, forecast_1h_condition, forecast_1h_temp, forecast_1h_humidity, forecast_1h_clouds, forecast_1h_timestamp, forecast_3h_condition, forecast_3h_temp, forecast_3h_humidity, forecast_3h_clouds, forecast_3h_timestamp = get_current_weather(weather_api_key, location_lat, location_lon)
        print(f"")
        print(f"Current weather: {current_condition}, {temperature}C | Humidity: {humidity}% | Clouds: {clouds}%")
        print(f"1H forecast: {forecast_1h_condition}, {forecast_1h_temp}C | Humidity: {forecast_1h_humidity}% | Clouds: {forecast_1h_clouds}% | Time:{forecast_1h_timestamp}")
        print(f"3H forecast: {forecast_3h_condition}, {forecast_3h_temp}C | Humidity: {forecast_3h_humidity}% | Clouds: {forecast_3h_clouds}% | Time:{forecast_3h_timestamp}")

        data_list = data.get("dataList", [])

        # Helper to find a value by key
        def get_value_by_key(key, default=0):
            for entry in data_list:
                if entry.get("key") == key:
                    try:
                        return float(entry.get("value", default))
                    except ValueError:
                        return default
            return default

        # Fetch values
        battery_charge = get_value_by_key("BMS_SOC", 0) 
        current_power = get_value_by_key("S_P_T", 0)
        internal_power = get_value_by_key("GS_T", 0)

        print(f"Battery charge: {battery_charge}%")
        print(f"Current production: {current_power}W")
        print(f"Internal Power: {internal_power}W")

        now = datetime.now()
        
        # Ping the miner to check that it is turned on
        if is_rpi and (now - uptime) > timedelta(minutes=3):
            check_uptime(now, prev_state)

        # Emergency shutdown
        if ((prev_state == "production" and battery_charge < 20) or (prev_state == "production" and now.hour > 14 and battery_charge < 80)):
            print("Battery emergency shutdown.")
            state = "stop"
            if prev_state == "production":
                print("Trying to press power button.")
                if state != prev_state:
                    prev_state = state
                    uptime = now
                    save_prev_state(prev_state, uptime)
                if is_rpi:
                    press_power_button(16, 0.5)
        elif (
            # 1H Conditions
            (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_1h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and current_power > 0 
                and battery_charge >= 40
                and now.hour < 12
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_1h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 60
                and now.hour < 12
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_1h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 50
                and now.hour < 11
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_1h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 40
                and now.hour < 10
            ) or (  # 3H Conditions
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_3h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and current_power > 0 
                and battery_charge >= 40
                and now.hour < 12
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_3h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 60
                and now.hour < 12
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_3h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 50
                and now.hour < 11
            ) or (
                any(keyword in current_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and any(keyword in forecast_3h_condition for keyword in ['sunny', 'clear', 'clear sky', 'scattered clouds', 'few clouds', 'broken clouds'])
                and battery_charge >= 40
                and now.hour < 10
            ) or ( # Power Conditions
                battery_charge >= 60 
                and current_power >= 2500
            ) or (
                battery_charge >= 70 
                and current_power >= 2250
            ) or (
                battery_charge >= 80 
                and current_power >= 2000
            ) or (
                current_power >= 4000
                and now.hour < 12
            ) or (
                battery_charge > 90
                and current_power > 200
            )
        ):
            print("Crypto production ready!")
            state = "production"
            if prev_state == "stop":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.5)
        elif (
            battery_charge <= 90
            or current_power <= 450
            or (
                any(keyword in current_condition for keyword in [
                    'rain', 'storm', 'thunder', 'snow', 'fog', 'haze',
                    'sleet', 'blizzard', 'dust', 'sand', 'ash',
                    'tornado', 'hurricane', 'lightning'
                ])
                and battery_charge <= 95
                and current_power <= 1000
            )
            or (
                any(keyword in forecast_1h_condition for keyword in [
                    'rain', 'storm', 'thunder', 'snow', 'fog', 'haze',
                    'sleet', 'blizzard', 'dust', 'sand', 'ash',
                    'tornado', 'hurricane', 'lightning'
                ])
                and battery_charge <= 95
                and current_power <= 1000
            )
            or (
                any(keyword in forecast_3h_condition for keyword in [
                    'rain', 'storm', 'thunder', 'snow', 'fog', 'haze',
                    'sleet', 'blizzard', 'dust', 'sand', 'ash',
                    'tornado', 'hurricane', 'lightning'
                ])
                and battery_charge <= 95
                and current_power <= 1000
            )
        ):
            print("Crypto production over.")
            state = "stop"
            if prev_state == "production":
                print("Trying to press power button.")
                uptime = now
                if is_rpi:
                    press_power_button(16, 0.5)
        else:
            print("No change!")

        if state == "production" and prev_state != "production":
            send_telegram_message(f""" Production started!\n________________________________\n Battery: {battery_charge}%\n Current power: {current_power}W\n________________________________\n Weather: {current_condition}\n Temperature: {temperature}\n Humidity: {humidity}%""")
        elif state == "stop" and prev_state != "stop":
            send_telegram_message(f""" Production stopped.\n________________________________\n Battery: {battery_charge}%\n Current power: {current_power}W\n________________________________\n Weather: {current_condition}\n Temperature: {temperature}\n Humidity: {humidity}%""")
        if state != prev_state:
            prev_state = state
            save_prev_state(prev_state, now)

        return battery_charge, current_power, state, current_condition, temperature, humidity, sunrise, sunset, clouds, forecast_1h_condition, forecast_1h_temp, forecast_1h_humidity, forecast_1h_clouds, forecast_1h_timestamp, forecast_3h_condition, forecast_3h_temp, forecast_3h_humidity, forecast_3h_clouds, forecast_3h_timestamp
    except Exception as e:
        print(f"Error while checking production conditions: {e}")
        return None, None, state, sunrise, sunset

def main_loop():
    global prev_state, state, used_quote, sunrise, sunset, uptime
    used_quote = load_quote_usage()
    current_condition, temperature, humidity, sunrise, sunset, clouds, forecast_1h_condition, forecast_1h_temp, forecast_1h_humidity, forecast_1h_clouds, forecast_1h_timestamp, forecast_3h_condition, forecast_3h_temp, forecast_3h_humidity, forecast_3h_clouds, forecast_3h_timestamp = get_current_weather(WEATHER_API, LOCATION_LAT, LOCATION_LON)

    while True:
        now = datetime.now()       
        # Normalize sunrise/sunset
        if isinstance(sunrise, (int, float)):
            sunrise = datetime.fromtimestamp(sunrise)
        if isinstance(sunset, (int, float)):
            sunset = datetime.fromtimestamp(sunset)       

        if now.month == 1 and now.day == 1 and used_quote != 0:
            print("January 1st detected ? resetting quote usage to 0.")
            used_quote = 0
            save_quote_usage(used_quote)

        sunrise_ts = sunrise.timestamp()
        sunrise_ts = sunrise_ts - 1800 # 30 perc levonása másodpercben
        sunrise_start = datetime.fromtimestamp(sunrise_ts)
        print(f"Sunrise start: {sunrise_start}:00 | Sunset stop: {sunset}:00")
        if (sunrise_start.hour, sunrise_start.minute) <= (now.hour, now.minute) <= (sunset.hour, sunset.minute):
            try:
                used_quote += 1
                save_quote_usage(used_quote)

                print("\n\nStarting new cycle...")
                print(f"Time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n")
                token = get_access_token()
                data = fetch_current_data(token)
                store_data(data)
                battery, power, state, current_condition, temperature, humidity, sunrise, sunset, clouds, forecast_1h_condition, forecast_1h_temp, forecast_1h_humidity, forecast_1h_clouds, forecast_1h_timestamp, forecast_3h_condition, forecast_3h_temp, forecast_3h_humidity, forecast_3h_clouds, forecast_3h_timestamp = check_crypto_production_conditions(data, WEATHER_API, LOCATION_LAT, LOCATION_LON)
                if is_rpi:
                    write_to_display(
                        state_text=state,
                        soc=battery,
                        solar_power=power,
                        weather_condition=current_condition,
                        temperature=temperature,
                        humidity=humidity
                    )
                print("Cycle complete. Waiting for next interval.")
            except requests.HTTPError as http_err:
                print(f"HTTP error occurred: {http_err}")
            except Exception as err:
                print(f"An unexpected error occurred: {err}")
            used_quote = int(used_quote)
            percentage = (used_quote / QUOTE_LIMIT) * 100
            print(f"Quote usage: {used_quote} / {QUOTE_LIMIT} ({percentage:.2f}%)")
            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")
        else:
            print(f"Outside of active hours. Sleeping... (Sunrise: {sunrise.strftime('%H:%M')} | Sunset: {sunset.strftime('%H:%M')})")
            print(f"Time: {now.strftime('%Y-%m-%d %H:%M:%S')}\n")
            state = "stop"
            if prev_state == "production":
                print("Miner did not shut down correctly, shutting down...")
                print("Trying to press power button.")
                if is_rpi:
                    press_power_button(16, 0.5)
                if state != prev_state:
                    prev_state = state
                    uptime = now
                    save_prev_state(prev_state, uptime)
            if is_rpi:
                write_to_display(
                        state_text="sleep",
                        soc=0,
                        solar_power=0,
                        weather_condition = f"Sunrise: {sunrise.strftime('%H:%M')}",
                        temperature=0,
                        humidity=0
                )
            sleep_until_next_5min(offset_seconds=60)
            print("__________________________________________________________________________________________")

if __name__ == '__main__':    
    if is_rpi:
        init_display()
    main_loop()
