#!/bin/sh
# Stand up one native fn node on hbox from a frozen build tree.  Run ON hbox:
#   sh hbox-node-deploy.sh /tank/fn/gates/freeze-dev-<rev> <shortrev> <listen-ipv4> <frozen-image-dir>
# Idempotent only in the sense that it refuses to touch an existing node dir.
set -eu
[ "$#" -eq 4 ] || { echo "usage: $0 TREE SHORTREV LISTEN_IPV4 FROZEN_IMAGE_DIR" >&2; exit 2; }
TREE=$1; REV=$2; ADDR=$3; IMAGE=$4
NODE=/tank/fn/node
PREFIX=$NODE/fn-$REV
[ ! -e "$NODE/store" ] || { echo "refusing: $NODE/store exists"; exit 1; }
mkdir -p "$NODE/tls" "$NODE/log"
cd "$TREE"
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
# The image was built against OpenSSL 3.5 (ML-DSA-65); the host reads this
# variable at runtime (host/native/tls.lisp) and falls back to the system
# library without it, which on hbox is 3.3.1 and has no ML-DSA-65.
FN_OPENSSL_PREFIX=${FN_OPENSSL_PREFIX:-/tank/fn/toolchains/openssl-3.5.8}
export FN_OPENSSL_PREFIX
echo "== install the production image under $PREFIX"
FN_NATIVE_HOST="$IMAGE/fn-host" FN_NATIVE_CORE="$IMAGE/fn-host.core" \
  FN_NATIVE_SOURCE_REVISION="$REV" PREFIX="$PREFIX" sh packaging/install-native.sh
FN="$PREFIX/bin/fn"
echo "== TLS pair (self-signed, ten years)"
openssl req -x509 -newkey rsa:2048 -keyout "$NODE/tls/key.pem" -out "$NODE/tls/cert.pem" \
  -sha256 -days 3650 -nodes -subj "/CN=hbox.ember.software" \
  -addext "subjectAltName=DNS:hbox,DNS:hbox.ember.software,IP:$ADDR" 2>/dev/null
chmod 0600 "$NODE/tls/key.pem"
echo "== store"
"$PREFIX/libexec/fn/fn-host" --fn store "$NODE/store" init fn.test
cat > "$NODE/fn.toml" <<TOML
[store]
path = "$NODE/store"

[listener]
host = "$ADDR"
port = 1119
tls_cert = "$NODE/tls/cert.pem"
tls_key = "$NODE/tls/key.pem"

[auth]
required = true
protected_only = true
path = "$NODE/store/auth.toml"

[posting]
enabled = true

[log]
path = "$NODE/log/fn.log"

[control]
path = "$NODE/store/control.sock"
TOML
# [log] path: `run` opens it append-only before the store (absolute paths
# only; books/native-config.lisp fn-native-config-unsupported-key) and the
# owner writes one line per post and per accepted connection there instead of
# the journal.  fn never rotates it.
# [posting] agent is deliberately absent: the injecting agent is the node's
# <path-identity>, set below as the `path-identity` policy (one slot, read by
# Path, Injection-Info and loop suppression alike), and `run` refuses an
# `agent` key as `UNSUPPORTED-PROFILE agent`.  `fn@hbox.ember.software` would
# not be a <path-identity> anyway (RFC 5536 section 3.1.6 has no `@`).
echo "== configuration records: identity and groups"
"$FN" operator "$NODE/fn.toml" policy set path-identity hbox.ember.software
for g in fn.agents fn.humans fn.announce; do "$FN" operator "$NODE/fn.toml" group create "$g"; done
echo "== principals (passwords generated here, kept only in $NODE/credentials.txt, mode 0600)"
umask 077; : > "$NODE/credentials.txt"
for who in ember yue tulip; do
  pw=$(openssl rand -base64 18 | tr -d '=+/' | cut -c1-20)
  printf '%s\n%s\n' "$pw" "$pw" | "$FN" operator "$NODE/fn.toml" principal set-password "$who" --posting
  printf '%s %s\n' "$who" "$pw" >> "$NODE/credentials.txt"
done
umask 022
"$FN" operator "$NODE/fn.toml" principal list
"$FN" operator "$NODE/fn.toml" status
echo "== user service"
mkdir -p "$HOME/.config/systemd/user"
cat > "$HOME/.config/systemd/user/fn-node.service" <<UNIT
[Unit]
Description=fn native news node ($REV)
After=network-online.target
Wants=network-online.target
StartLimitIntervalSec=60
StartLimitBurst=5

[Service]
Type=simple
Environment=ACL2_CUSTOMIZATION=NONE
ExecStart=$FN operator $NODE/fn.toml run
Restart=on-failure
RestartSec=5
KillSignal=SIGTERM
TimeoutStopSec=120
NoNewPrivileges=yes
PrivateTmp=yes

[Install]
WantedBy=default.target
UNIT
systemctl --user daemon-reload
systemctl --user enable --now fn-node.service
sleep 3
systemctl --user --no-pager status fn-node.service | head -12
ss -ltn | grep ":1119 " || echo "NOT LISTENING"
echo "== done: credentials in $NODE/credentials.txt"
