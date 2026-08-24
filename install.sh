#!/usr/bin/env bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  if command -v sudo >/dev/null 2>&1; then
    exec sudo -- "$0" "$@"
  fi
  echo "[!] Run this installer as root."
  exit 1
fi

BASE_DIR="$(cd "$(dirname "$0")" && pwd)"

# Install immutable copies. Do not expose the checkout through a system-wide
# symlink and do not alter permissions on any parent/home directory.
install -m 0755 "$BASE_DIR/badomen.py" /usr/local/bin/badomen
install -m 0644 "$BASE_DIR/webrecon.py" /usr/local/bin/webrecon.py

# Retain the legacy command as a copied compatibility entry point.
install -m 0755 "$BASE_DIR/webrecon.py" /usr/local/bin/webrecon

echo "[+] Installed command: /usr/local/bin/badomen"
echo "[+] Compatibility command: /usr/local/bin/webrecon"
echo "[+] Reports are readable without root (directory 0755, files 0644) under ./outputs."
echo "[+] Runtime scans do not require root privileges."
