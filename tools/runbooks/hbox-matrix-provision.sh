#!/bin/sh
# Two clean native stores for the v0 matrix on hbox.  Run ON hbox:
#   sh hbox-matrix-provision.sh <image>   (e.g. /tank/fn/gates/freeze-dev-<rev>/build/fn-host)
set -eu
IMG=$1
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
BASE=$HOME/fn-native-matrix
for n in a b; do
  case $n in a) port=11190;; b) port=11191;; esac
  ss -ltn | grep -q ":$port " && { echo "port $port busy"; exit 1; }
done
rm -rf "$BASE"; mkdir -p "$BASE"
for n in a b; do
  case $n in a) port=11190;; b) port=11191;; esac
  root=$BASE/$n; mkdir -p "$root"
  "$IMG" --fn store "$root/store" init fn.letters >/dev/null
  printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' "$root/store" "$port" "$root/control.sock" > "$root/fn.toml"
done
echo "provisioned $BASE/a $BASE/b"
