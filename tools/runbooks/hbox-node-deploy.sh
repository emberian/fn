#!/bin/sh
# Stand up one native fn node on hbox from a RELEASE TARBALL (D35: the
# release is the product; the developer checkout is never the deployment).
# Run ON hbox, as the hbox user (no root: the node runs under the user
# manager):
#   sh hbox-node-deploy.sh TARBALL SHA256 NODE_DIR PREFIX LISTEN_IPV4 PORT PATH_IDENTITY
# TARBALL is fn-REV12-linux-x86_64.tar.gz as packaging/release-tarball.sh
# made it, SHA256 its digest from the release's SHA256SUMS.  PREFIX and
# NODE_DIR must not exist (one installation directory; a redeploy is stop,
# export, remove, install, import, start: docs/install.md section 4).
# Refuses /tank/fn/node unless FN_DEPLOY_LIVE=yes names the intent.
set -eu
[ "$#" -eq 7 ] || { echo "usage: $0 TARBALL SHA256 NODE_DIR PREFIX LISTEN_IPV4 PORT PATH_IDENTITY" >&2; exit 2; }
TARBALL=$1; SUM=$2; NODE=$3; PREFIX=$4; ADDR=$5; PORT=$6; NAME=$7
case $NODE in /tank/fn/node*) [ "${FN_DEPLOY_LIVE:-}" = yes ] || { echo "refusing the live node without FN_DEPLOY_LIVE=yes" >&2; exit 2; };; esac
[ ! -e "$NODE/store" ] || { echo "refusing: $NODE/store exists" >&2; exit 1; }
echo "$SUM  $TARBALL" | sha256sum -c -
work=$(mktemp -d "${TMPDIR:-/tmp}/fn-deploy.XXXXXX")
tar -xzf "$TARBALL" -C "$work"
sh "$work/fn/install.sh" --prefix "$PREFIX" --node "$NODE" --no-service
rm -rf "$work"
FN="$PREFIX/bin/fn"; C="$NODE/fn.toml"
cd "$NODE"
"$FN" operator "$C" mission small-community --host "$ADDR" --port "$PORT"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 \
  -subj "/CN=$NAME" -addext "subjectAltName=DNS:$NAME,IP:$ADDR" \
  -keyout tls/key.pem -out tls/cert.pem 2>/dev/null
chmod 0600 tls/key.pem
"$FN" operator "$C" init
"$FN" operator "$C" policy set path-identity "$NAME"
echo "== principals (passwords generated here, kept only in $NODE/credentials.txt, mode 0600)"
umask 077; : > "$NODE/credentials.txt"
for who in ember yue tulip; do
  pw=$(openssl rand -base64 18 | tr -d '=+/' | cut -c1-20)
  printf '%s\n%s\n' "$pw" "$pw" | "$FN" operator "$C" principal set-password "$who" --posting
  printf '%s %s\n' "$who" "$pw" >> "$NODE/credentials.txt"
done
umask 022
"$FN" operator "$C" status
echo "== user service fn-node (the rendered unit is $NODE/fn.service; a user manager runs it)"
systemd-run --user --unit fn-node -p MemoryMax=24G -p WorkingDirectory="$NODE" "$FN" operator "$C" run
sleep 5
systemctl --user --no-pager status fn-node | head -8
ss -ltn | grep ":$PORT " || echo "NOT LISTENING"
echo "== done: $("$FN" --version); credentials in $NODE/credentials.txt"
