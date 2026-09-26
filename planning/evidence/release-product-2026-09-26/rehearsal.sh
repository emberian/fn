#!/bin/sh
# The release-product rehearsal, node side, run ON hbox (never /tank/fn/node):
#   sh rehearsal.sh install|start|stop|remove-reinstall|status  OUT_DIR TARBALL_NAME
# R=/tank/fn/scratch/release-product/rehearsal holds the stranger's download
# directory, the install prefix R/opt/fn and the node R/node.  Each phase logs
# to R/logs/PHASE.log.
set -eu
phase=$1 out=$2 name=$3
R=/tank/fn/scratch/release-product/rehearsal
ADDR=192.168.50.39 PORT=11995 ID=release-rehearsal.fn.invalid
mkdir -p "$R/logs" "$R/download"
exec > "$R/logs/$phase.log" 2>&1
set -x
case $phase in
  install)
    cp "$out/$name" "$out/SHA256SUMS" "$R/download/"
    cd "$R/download"
    sha256sum -c --ignore-missing SHA256SUMS
    tar -xzf "$name"
    sh fn/install.sh --prefix "$R/opt/fn" --node "$R/node" --no-service
    cd "$R/node"
    F=$R/opt/fn/bin/fn C=$R/node/fn.toml
    "$F" operator "$C" mission small-community --host "$ADDR" --port "$PORT"
    cat "$C"
    openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 \
      -subj "/CN=$ID" -addext "subjectAltName=DNS:$ID,IP:$ADDR" \
      -keyout tls/key.pem -out tls/cert.pem
    chmod 600 tls/key.pem
    "$F" operator "$C" init
    "$F" operator "$C" policy set path-identity "$ID"
    printf 'rehearsal-pw-7\nrehearsal-pw-7\n' | "$F" operator "$C" principal set-password rehearsal --posting
    "$F" operator "$C" status ;;
  start)
    systemd-run --user --unit fn-release-rehearsal -p MemoryMax=24G \
      -p WorkingDirectory="$R/node" "$R/opt/fn/bin/fn" operator "$R/node/fn.toml" run
    sleep 8
    systemctl --user --no-pager status fn-release-rehearsal | head -6
    ss -ltn | grep ":$PORT "
    "$R/opt/fn/bin/fn" --version ;;
  stop)
    systemctl --user stop fn-release-rehearsal
    systemctl --user --no-pager status fn-release-rehearsal | head -4 || true ;;
  remove-reinstall)
    rm -rf "$R/opt/fn"
    cd "$R/download"
    # the refusal first: installing over an existing prefix
    mkdir -p "$R/opt/fn" && touch "$R/opt/fn/keep"
    if sh fn/install.sh --prefix "$R/opt/fn" --node "$R/node" --no-service; then echo UNEXPECTED; exit 1; fi
    rm -rf "$R/opt/fn"
    sh fn/install.sh --prefix "$R/opt/fn" --node "$R/node" --no-service
    "$R/opt/fn/bin/fn" operator "$R/node/fn.toml" status ;;
esac
echo "PHASE $phase DONE"
