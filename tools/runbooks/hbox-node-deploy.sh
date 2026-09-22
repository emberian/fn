#!/bin/sh
# Stand up one native fn node on hbox from a frozen build tree.  Run ON hbox:
#   sh hbox-node-deploy.sh /tank/fn/gates/freeze-dev-<rev> <shortrev> <listen-ipv4>
# Idempotent only in the sense that it refuses to touch an existing node dir.
set -eu
TREE=$1; REV=$2; ADDR=$3
NODE=/tank/fn/node
PREFIX=$NODE/fn-$REV
[ ! -e "$NODE/store" ] || { echo "refusing: $NODE/store exists"; exit 1; }
mkdir -p "$NODE/tls" "$NODE/log"
cd "$TREE"
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
echo "== install the production image under $PREFIX"
FN_NATIVE_HOST="$TREE/build/fn-host" FN_NATIVE_CORE="$TREE/build/fn-host.core" \
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
agent = "fn@hbox.ember.software"

[control]
path = "$NODE/store/control.sock"

[log]
path = "$NODE/log/fn.log"
TOML
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
