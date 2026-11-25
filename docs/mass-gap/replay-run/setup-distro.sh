#!/usr/bin/env bash
# Thread A, one-off: prepare a dedicated WSL distro for the replay (run as root inside it).
# Created on Windows with: wsl --install Ubuntu-24.04 --name ym-replay --location C:\wsl\ym-replay --no-launch
# Kept apart from the distro that hosts the CI runners, so the replay can neither disturb CI nor be disturbed by it.
set -euo pipefail
apt-get update -qq
DEBIAN_FRONTEND=noninteractive apt-get install -y -qq git curl ca-certificates build-essential python3 zstd unzip jq time golang-go >/dev/null
id -u ym >/dev/null 2>&1 || useradd -m -s /bin/bash ym
printf '[user]\ndefault=ym\n' > /etc/wsl.conf
su - ym -c 'command -v elan >/dev/null || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none'
echo "setup done: $(lsb_release -ds), $(nproc) threads, $(free -g | awk '/Mem/{print $2}') GB"
