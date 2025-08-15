FROM python:3.11-slim-bullseye

# Set environment variables
ENV PYTHONDONTWRITEBYTECODE=1
ENV PYTHONUNBUFFERED=1

# Set working directory
WORKDIR /app

# Install system dependencies for GPIO, OLED, and ping support
RUN apt-get update && apt-get install -y \
    build-essential \
    libjpeg-dev \
    zlib1g-dev \
    libfreetype6-dev \
    libtiff5-dev \
    libopenjp2-7 \
    libatlas-base-dev \
    i2c-tools \
    iputils-ping \
    tzdata \
    libgl1-mesa-dev \
    libffi-dev \
    libusb-1.0-0-dev \
    python3-dev \
    libc6-dev \
    libgpiod2 \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt ./
RUN pip install --no-cache-dir -r requirements.txt
   
# Copy the app code
COPY solar.py ./

# Entrypoint
CMD ["python", "solar.py"]
