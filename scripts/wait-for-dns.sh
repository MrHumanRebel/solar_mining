#!/bin/sh

# Wait until both Solarman and OpenWeatherMap are reachable
while ! ping -c1 globalapi.solarmanpv.com >/dev/null 2>&1 || ! ping -c1 api.openweathermap.org >/dev/null 2>&1; do
  echo "Waiting for Solarman and OpenWeatherMap services to be reachable..."
  sleep 5
done

echo "External APIs are ready. Starting application..."
exec "$@"
