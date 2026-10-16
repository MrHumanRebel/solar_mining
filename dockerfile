FROM python:3.11-slim-bookworm

# Set environment variables
ENV PYTHONDONTWRITEBYTECODE=1
ENV PYTHONUNBUFFERED=1

# Set working directory
WORKDIR /app

# Build native GPIO extensions; retain the hardware libraries used at runtime.
# Pillow publishes ARM64 wheels, so image/BLAS/OpenGL development packages are
# unnecessary. Bookworm provides libgpiod2 for adafruit-circuitpython-dht.
RUN sed -i 's|http://deb.debian.org|https://deb.debian.org|g' /etc/apt/sources.list.d/debian.sources \
    && apt-get -o Acquire::Retries=3 update --error-on=any \
    && apt-get -o Acquire::Retries=3 install -y --no-install-recommends \
    build-essential \
    i2c-tools \
    iputils-ping \
    tzdata \
    libusb-1.0-0 \
    libgpiod2 \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt
   
# Copy the app code and bundled historical tuning data
COPY solar.py miner_power_guard.py ./
COPY solarmining_logo.png ./
COPY favicon ./favicon
COPY wait-for-dns.sh ./
COPY solarman_json ./solarman_json

EXPOSE 9000

# Entrypoint
CMD ["python", "solar.py"]
