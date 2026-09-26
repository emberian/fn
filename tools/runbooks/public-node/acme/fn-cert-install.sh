#!/bin/sh
# lego's run/renew hook (lane public-node, 2026-09-26). lego sets
# LEGO_CERT_PATH (the full chain: lego bundles the issuer by default) and
# LEGO_CERT_KEY_PATH. Installs them where fn.toml's [listener] tls_cert and
# tls_key point, atomically (same directory, then rename), and asks the
# running node to take them: `fn operator CONFIG tls reload` (lane tls-reload,
# PRF-212, HST-020; public-node's gap packet c). New connections get the new
# certificate, open sessions keep theirs, nothing restarts. A refusal (exit 1)
# names its reason (expired, not-yet-valid, names-dropped, ...) and the node
# keeps serving the old certificate: the hook exits 1 so lego and the timer's
# journal show it, and it does NOT restart (a restart would serve material
# the node just refused). Only when the owner cannot be asked (exit 2 or
# more: no socket, uncertain) does it fall back to the restart.
set -eu
TLS=/home/hbox/fn-public/node/tls
: "${LEGO_CERT_PATH:?}" "${LEGO_CERT_KEY_PATH:?}"
# Refuse a pair that does not match before touching the live files.
[ "$(openssl x509 -noout -pubkey -in "$LEGO_CERT_PATH" | openssl sha256)" = \
  "$(openssl pkey -pubout -in "$LEGO_CERT_KEY_PATH" | openssl sha256)" ] || { echo "key does not match certificate"; exit 1; }
umask 077
install -d -m 0700 "$TLS"
install -m 0644 "$LEGO_CERT_PATH" "$TLS/.cert.pem.new"
install -m 0600 "$LEGO_CERT_KEY_PATH" "$TLS/.key.pem.new"
mv "$TLS/.key.pem.new" "$TLS/key.pem"
mv "$TLS/.cert.pem.new" "$TLS/cert.pem"
# The same pair under the names deploy-fresh's --cert-dir reads.
LIVE=/home/hbox/fn-public/acme/live
install -d -m 0700 "$LIVE"
install -m 0644 "$TLS/cert.pem" "$LIVE/.fullchain.pem.new" && mv "$LIVE/.fullchain.pem.new" "$LIVE/fullchain.pem"
install -m 0600 "$TLS/key.pem" "$LIVE/.privkey.pem.new" && mv "$LIVE/.privkey.pem.new" "$LIVE/privkey.pem"
openssl x509 -noout -subject -issuer -enddate -in "$TLS/cert.pem"
CONFIG=/home/hbox/fn-public/node/fn.toml
# The release's launcher: FN_BIN, else `fn` on PATH, else the one release
# unpacked under /home/hbox/fn-public/release.
FN=${FN_BIN:-$(command -v fn || ls -d /home/hbox/fn-public/release/fn-*/bin/fn 2>/dev/null | tail -n 1)}
if systemctl --user is-active --quiet fn-node.service; then
  set +e
  "$FN" operator "$CONFIG" tls reload
  code=$?
  set -e
  case $code in
    0) ;;
    1) echo "tls reload refused; the node still serves the previous certificate" >&2
       exit 1 ;;
    *) echo "tls reload could not reach the owner (exit $code); restarting" >&2
       systemctl --user restart fn-node.service ;;
  esac
fi
