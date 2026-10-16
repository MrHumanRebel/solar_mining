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

For the current month and neighboring months it builds hourly lower-quartile
PV and upper-quartile total-consumption profiles. Missing months can borrow
nearby seasons (up to two months away) with an additional PV discount; opposite
seasons cannot substitute. At least three historical days and coverage of each
forecast hour are required. Historical consumption includes the whole household;
the exports do not identify the miner, individual appliances or phase loads.

Every live control cycle evaluates a candidate mining run in five-minute energy
steps through the existing production-stop window (90 minutes before actual
sunset). Demand is the greater of historical aggregate demand and current total
consumption plus the rig allowance when starting. It does not add the miner to
historical aggregate load again. PV forecasts are reduced by uncertain weather
and weak current production, never boosted above the historical baseline.

The energy budget includes startup energy, charge/discharge losses, battery
capacity from measured/configured Ah × V, battery saturation, the protected SOC
floor and evening reserve. A start needs enough time for the minimum run and a
budget that protects both reserves. A running rig receives a STOP decision when
the budget fails. Missing history, invalid or stale live consumption prevents
new starts. No saved JSON substitutes for a failed API response.

The model is a conservative estimate, not a guarantee of future sunshine or
household demand. The simulator below exercises scenarios; it cannot reconstruct
counterfactual battery behavior or establish physical miner states.

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

If the inverter exposes no dedicated load register, the guard accepts
`INV_O_P_T` together with all three `INV_O_P_L1/L2/L3` readings when their sum
matches the total. The dashboard labels this source as inverter output, which
does not establish consumption of grid-side appliances. A change between meter
sources discards the learned identity. W and kW are normalized; energy counters
such as `E_Puse_t1` are never interpreted as instantaneous power.

Solarman authentication and device polling run every five minutes between
astronomical sunrise and sunset, and once every 30 minutes overnight. Failed
attempts also consume a polling slot. Dashboard refresh, sensors and pool
updates do not trigger extra Solarman polling.

## Dashboard

Live metrics, pool hashrate (also while idle), the decision and energy budget are
shown separately from the supplied historical charts. Historical PV, consumption
and SOC come solely from the exports; historical miner states and phases are
not invented. `/api/history/download` returns the normalized supplied history
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
python -m unittest -q test_history_model test_solar_polling test_idle_monitoring test_miner_power_guard test_mining_pool test_solarman_power_fields
python simulate_decisions.py --history-dir solarman_json
python simulate_decisions.py --history-dir solarman_json --date 2026-10-16
```

The replay trains only on exports strictly before the selected local day and
walks that day's observations without API requests, GPIO or file writes. It uses
explicit unknown-weather and fixed 07:00–17:00 window assumptions and reports
these limitations. It does not infer historical miner state or phase behavior.
