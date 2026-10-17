# Solar Mining

Raspberry Pi controller for a solar-powered mining rig, with a web dashboard,
OLED/DHT sensors, Telegram controls and unMineable USDT monitoring.

## Historical data and decisions

`solarman_json/*.json` is the **only historical measurement source**. Use the
provided downloaded Solarman exports. The application reads these files at
startup; it never updates them or creates a replacement measurement archive.
There is no `solarminer_json` recorder, telemetry backup, persisted live-data
cache, or learning from controller-generated recordings.

The model validates exported PV, total consumption and SOC, normalizes export
UTC offsets to Europe/Budapest, and combines duplicate timestamps by median.
Future records are excluded. Invalid records are counted and skipped.

The seasonal profile keeps hourly PV quartiles and household night-load
statistics for the current and neighboring months. Missing months may borrow
nearby seasons (up to two months away) with an extra forecast discount. At least
three historical days and hourly coverage of the planning horizon are required.
The source exports do not label miner state or individual appliances.

The planner evaluates three stages every live control cycle:

1. Bridge from the current PV output to sustained solar cover, allowing a start
   before PV fully covers the rig and household. Available battery energy above
   the protected SOC floor must cover the deficit, startup energy and a 25%
   bridge margin. A new morning start needs sustained solar cover before its
   planned stop; the available Wh determine whether the bridge is affordable. A running rig or an afternoon start can use a finite battery budget
   without waiting for another solar peak, provided the night reserve is safe.
2. Choose a finite mining run (at least the minimum run duration for a new
   start), ending no later than the existing production stop, 90 minutes before
   astronomical sunset. Search for an earlier stop when needed; do not assume
   the miner must run all day to be allowed to start.
3. Forecast household-only demand and battery refill after the planned stop,
   through actual sunset. Reserve enough energy for median historical household
   demand from sunset until the next sunrise, with charge/discharge losses,
   a 10% overnight allowance and the protected SOC floor. This is a calculated
   night reserve, not a blanket requirement to finish at 90% or 100% SOC.

Daytime demand comes from the current measured consumption and the configured
rig allowance, counted once. `MY_MINER_POWER_W` is the whole-rig power
allowance (default 1050 W), including GPUs, CPU and PSU losses. Historical daytime consumption may already include
the miner and is never added to it again. While running, subtracting the rig
allowance to estimate the household-only refill period is an explicit load
estimate, not evidence about historical appliance states.

The existing free three-hour weather forecast is retained with its timestamps
and applied to the matching part of the day. Clear, mixed and wet forecasts use
different seasonal PV quantiles. Current measured PV constrains the immediate
bridge; its influence fades over one hour instead of multiplying down the whole
day's forecast. No additional Solarman or weather requests are introduced.

The dashboard labels the minimum SOC and sunset SOC for the finite proposed
run/refill scenario, shows solar-cover time, planned mining stop, required versus
available bridge energy and calculated night reserve. If a start is rejected,
the projections are explicitly labelled as a rejected-run scenario; missing
inputs are unavailable rather than artificial zeros. A zero can still mean an
unsafe candidate would actually exhaust the battery. STOP reasons identify the
failed bridge, solar cover, missing coverage or night-reserve condition.

The energy model includes battery capacity from Ah × V, battery saturation,
startup cost and charge/discharge losses. It remains an estimate: future clouds
and household demand can differ. It is recalculated at each live sample, while
the separate power guard controls whether a physical shutdown is authorized.
Missing or stale API data never substitutes a saved JSON measurement.

## Hardware shutdown and API cadence

Pool hashrate is display-only. The separate power guard uses fresh total
consumption and L2/L3 readings, a stable off baseline, and a witnessed load rise
after the controller's own start command. It supports either mapping of three
RTX3070 GPUs on one phase and two GPUs plus CPU on the other.

When STOP is required, one matching fresh reading above 1000 W total may authorize
a long press. No three-reading STOP delay is required. A lost phase signature,
ambiguous load, missing baseline or restart prevents automatic long presses;
there is at most one automatic shutdown press per witnessed run. Aggregate
meters cannot uniquely distinguish every oven/hob combination from a miner.
The guard retains only bounded working samples in memory, never a JSON history.

On the supplied Deye schema, `E_Puse_t1` with explicit W/kW units is total
instantaneous consumption. Pair it with `LPP_A/B/C` (whole-house phases), not
`C_P_L1/L2/L3` (a different load port). The supplied example is 1241 W =
25 + 808 + 408 W; the C_P readings sum to only 50 W. Each phase family is
selected as a complete group and checked against its total, never mixed.

When no consumption register exists, the guard accepts `INV_O_P_T` with
`INV_O_P_L1/L2/L3`, labelled as inverter output. It does not establish
consumption of grid-side appliances. Changes in source or phase family discard
the learned identity. kWh/VA counters are rejected. The dashboard shows the
selected safety meter and device collection time separately from HTTP polling
time, with specific missing-field, timestamp, unit or total/phase errors.

Solarman authentication and device polling run every five minutes between
astronomical sunrise and sunset, and once every 30 minutes overnight. Failed
attempts also consume a polling slot. Dashboard refresh, sensors and pool
updates do not trigger extra Solarman polling.

## Dashboard

Live metrics, pool hashrate (also while idle), the decision and energy budget are
shown separately from the supplied historical charts. Historical PV, consumption
and SOC come solely from the exports; historical miner states and phases are
not invented. Dates always use Hungarian order (`YYYY.MM.DD.`) and
Europe/Budapest time, even under an English/US browser locale. Both the input
and calendar icon open the calendar dialog; the calendar uses Hungarian month
names and Monday-first weekdays. API range queries accept ISO `YYYY-MM-DD` or
Hungarian dates and reject malformed/inverted ranges instead of silently
replacing them. Empty selections show the actual loaded date coverage.

The image keeps its complete exports in `/app/bundled_solarman_json`, outside
the host mount at `/app/solarman_json`. The loader reads and deduplicates both,
so an older 11-file host directory cannot hide the newer bundled exports. The
bundled history is refreshed by updating the image; no data is downloaded or
recorded at runtime. `/api/history/download` returns the normalized supplied history
without saving it. The old telemetry download endpoint has been removed.

## Run on Raspberry Pi

Supply the existing `.env` credentials: `MY_BOT_TOKEN`, `MY_CHAT_ID`,
`MY_WEATHER_API`, `MY_LOCATION_LAT`, `MY_LOCATION_LON`, `MY_APP_ID`,
`MY_APP_SECRET`, `MY_EMAIL`, `MY_PASSWORD`, and `MY_DEVICE_SN`.
Optional `MY_QUOTE_LIMIT` controls the displayed API allowance.

The supplied Compose configuration uses the existing `pihole_backend` network
and DNS host `172.31.0.100`. Adjust these for your installation. Ensure
`state.json` and `quote_usage.json` exist as files for their bind mounts.

```sh
docker compose pull
docker compose up -d
```

The dashboard listens on port 9000. GPIO/I2C/DHT require the Pi devices and
privileges configured in Compose. The image is built natively for ARM64 in CI.
Build locally with `docker build -f dockerfile -t solar-mining .` if needed.

`MY_HISTORY_DIR` selects the export directory (default `solarman_json`). Compose
mounts it read-only. Minimal controller state and API quota files remain writable;
these contain bookkeeping, not historical measurements.

### Migration

Use the updated Compose file: remove legacy `MY_TELEMETRY_FILE` and
`MY_SOLARMAN_FILE` settings and the `solarminer_json` / raw measurement mounts.
They are no longer read or written. Existing recordings on your Pi are left
untouched and can be archived or deleted independently. The repository's old
generated telemetry sample and recorder-specific replay tool have been removed.
The supplied `solarman_json` exports remain unchanged.

## Development and offline validation

Use Python 3.11 and the dependencies in `requirements.txt`. GPIO integrations are
skipped off the Pi. The tests use simulation defaults and mock external services;
do not launch the live main loop with production credentials for a replay.

```sh
python -m unittest -q test_history_model test_solar_polling test_idle_monitoring test_miner_power_guard test_mining_pool test_solarman_power_fields test_bridge_planning test_web_disconnect
python simulate_decisions.py --history-dir solarman_json
python simulate_decisions.py --history-dir solarman_json --date 2026-10-16
```

The replay trains only on exports strictly before the selected local day and
walks that day's observations without API requests, GPIO or file writes. It uses
explicit unknown-weather and fixed 07:00–17:00 window assumptions and reports
these limitations. It does not infer historical miner state or phase behavior.
