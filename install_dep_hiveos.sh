#!/bin/bash

# Update and install system dependencies
sudo apt update && sudo apt upgrade -y

# Install Python 3 and pip
sudo apt install -y python3 python3-pip python3-venv python3-dev build-essential

# Upgrade pip
python3 -m pip install --upgrade pip

# Install Jupyter Notebook
pip install notebook

# Install Python libraries
pip install \
    pandas \
    numpy \
    scikit-learn \
    catboost \
    matplotlib \
    talib-binary \
    ephem \
    scipy \
    statsmodels

# Echo success
echo "All dependencies installed successfully."
