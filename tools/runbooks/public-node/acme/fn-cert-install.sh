#!/bin/sh
# lego's run/renew hook (lane public-node, 2026-09-26). lego sets
# LEGO_CERT_PATH (the full chain: lego bundles the issuer by default) and
# LEGO_CERT_KEY_PATH. Installs them where fn.toml's [listener] tls_cert and
# tls_key point, atomically (same directory, then rename), and restarts the
# node: fn reads the pair only at `run` (SIGHUP reopens the log, not the
# certificate: gap packet c), so a renewal is a restart every ~60 days. The
# feeds resume from their journals and readers reconnect.
set -eu
TLS=/srv/fn-public/node/tls
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
openssl x509 -noout -subject -issuer -enddate -in "$TLS/cert.pem"
if systemctl --user is-active --quiet fn-node.service; then
  systemctl --user restart fn-node.service
fi
