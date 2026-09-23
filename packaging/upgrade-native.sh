#!/bin/sh
# Switch an already managed node to a staged native image. Linux only.
# Control hook: HOOK stop|start|check NODE; the service must use NODE/current/bin/fn.
set -eu
[ "$#" -eq 3 ] && [ -n "${FN_UPGRADE_CONTROL:-}" ] || {
  echo 'usage: FN_UPGRADE_CONTROL=/path/to/hook upgrade-native.sh NODE FROZEN_IMAGE REV' >&2; exit 2; }
node=$1 image=$2 rev=$3
case $node in /*) ;; *) echo 'upgrade-native: NODE must be absolute' >&2; exit 2;; esac
case $rev in ''|*[!A-Za-z0-9._-]*) echo 'upgrade-native: invalid revision' >&2; exit 2;; esac
[ -x "$FN_UPGRADE_CONTROL" ] && [ -x "$image/fn-host" ] || { echo 'upgrade-native: missing hook or image' >&2; exit 4; }
[ -L "$node/current" ] && [ -d "$node/store" ] && [ -s "$node/fn.toml" ] || {
  echo 'upgrade-native: existing managed node required' >&2; exit 4; }
for file in tls/cert.pem tls/key.pem credentials.txt; do
  [ -s "$node/$file" ] || { echo "upgrade-native: missing $file" >&2; exit 4; }
done
[ -d "$node/releases" ] || { echo 'upgrade-native: releases directory missing' >&2; exit 4; }
old=$(readlink "$node/current")
case $old in "$node"/releases/*) ;; *) echo 'upgrade-native: current target is outside releases' >&2; exit 4;; esac
[ -d "$old" ] || { echo 'upgrade-native: current target missing' >&2; exit 4; }
next=$node/releases/$rev
[ ! -e "$next" ] && [ ! -e "$node/releases/.$rev.pending" ] || {
  echo 'upgrade-native: revision already staged' >&2; exit 4; }
state_before=$(sha256sum "$node/fn.toml" "$node/tls/cert.pem" "$node/tls/key.pem" "$node/credentials.txt")
store_identity() { stat -c '%d:%i' "$1" 2>/dev/null || stat -f '%d:%i' "$1"; }
store_before=$(store_identity "$node/store")
replace_link() {
  if ! mv -Tf "$1" "$2" 2>/dev/null; then mv -fh "$1" "$2"; fi
}
pending=$node/releases/.$rev.pending
# The installer verifies the production profile and all frozen hashes before service stop.
PREFIX="$pending" FN_NATIVE_HOST="$image/fn-host" FN_NATIVE_CORE="$image/fn-host.core" \
  FN_NATIVE_SOURCE_REVISION="$rev" sh "$(dirname "$0")/install-native.sh"
rollback() {
  ln -s "$old" "$node/.current.rollback" || return 1
  replace_link "$node/.current.rollback" "$node/current" || return 1
  "$FN_UPGRADE_CONTROL" start "$node" || return 1
  "$FN_UPGRADE_CONTROL" check "$node" || return 1
}
"$FN_UPGRADE_CONTROL" stop "$node"
if ! mv "$pending" "$next" || ! ln -s "$next" "$node/.current.next" ||
   ! replace_link "$node/.current.next" "$node/current"; then
  echo 'upgrade-native: switch failed; restoring previous release' >&2
  rollback || { echo 'upgrade-native: rollback failed; operator action required' >&2; exit 6; }
  exit 5
fi
if ! "$FN_UPGRADE_CONTROL" start "$node" || ! "$FN_UPGRADE_CONTROL" check "$node"; then
  echo 'upgrade-native: new service failed; restoring previous release' >&2
  "$FN_UPGRADE_CONTROL" stop "$node" || true
  rollback || { echo 'upgrade-native: rollback failed; operator action required' >&2; exit 6; }
  exit 5
fi
state_after=$(sha256sum "$node/fn.toml" "$node/tls/cert.pem" "$node/tls/key.pem" "$node/credentials.txt")
store_after=$(store_identity "$node/store")
if [ "$state_before" != "$state_after" ] || [ "$store_before" != "$store_after" ]; then
  echo 'upgrade-native: persistent node identity changed; restoring previous release' >&2
  "$FN_UPGRADE_CONTROL" stop "$node" || true
  rollback || { echo 'upgrade-native: rollback failed; operator action required' >&2; exit 6; }
  exit 5
fi
echo "upgrade-native: active=$next previous=$old"
