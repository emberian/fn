#!/bin/sh
# A scratch node with its web face on, for tests/web_face_drive.mjs (SCN-187):
#
#   sh tests/web_face_scratch.sh prepare IMAGE DIR PORT   # fn.toml, init, a posting login
#   sh tests/web_face_scratch.sh run IMAGE DIR            # the node, in the foreground
#   sh tests/web_face_scratch.sh seed IMAGE DIR           # welcome post, code, DIR/secrets.json
#
# Run from a source tree on the box that holds the developer IMAGE; `run'
# under `systemd-run --user' (it stays until stopped).  DIR is absolute and
# absent (never /tank/fn/node).  The node: [auth] required and
# protected_only, groups local.general and control.cancel, NNTP on
# 127.0.0.1:PORT, implicit TLS on PORT+1, the face on 127.0.0.1:PORT+2 with
# `tls = true' (the listener's self-made certificate, so the cookie is
# Secure).  The operator's welcome post goes in over TLS with
# tools/fn_client.py; the invitation code is the node's `account invite'.
# DIR/secrets.json (mode 0600) holds the code, a password for the friend to
# choose, and the welcome's subject and body: the browser's inputs.  Nothing
# here decides anything; the node does.
set -eu
[ "$#" -ge 3 ] || { echo 'usage: web_face_scratch.sh prepare|run|seed IMAGE DIR [PORT]' >&2; exit 2; }
verb=$1 image=$2 dir=$3
case $dir in /tank/fn/node*) echo 'web_face_scratch: never the live node' >&2; exit 2;; /*) ;; *) echo 'web_face_scratch: DIR must be absolute' >&2; exit 2;; esac
export ACL2_CUSTOMIZATION=NONE
unset ACL2_SYSTEM_BOOKS FN_HOST FN_NATIVE_POST_FAULT
op() { "$image" --fn operator "$dir/fn.toml" "$@"; }
case $verb in
  prepare)
    [ "$#" -eq 4 ] || { echo 'usage: web_face_scratch.sh prepare IMAGE DIR PORT' >&2; exit 2; }
    port=$4
    [ ! -e "$dir" ] || { echo "web_face_scratch: exists: $dir" >&2; exit 4; }
    mkdir -p "$dir"; chmod 0700 "$dir"
    openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 2 \
      -subj /CN=localhost -addext subjectAltName=IP:127.0.0.1,DNS:localhost \
      -keyout "$dir/key.pem" -out "$dir/cert.pem" 2>/dev/null
    chmod 0600 "$dir/key.pem"
    cat > "$dir/fn.toml" <<TOML
[store]
path = "$dir/store"

[listener]
host = "127.0.0.1"
port = $port
tls_port = $((port + 1))
tls_cert = "$dir/cert.pem"
tls_key = "$dir/key.pem"

[control]
path = "$dir/control.sock"

[auth]
required = true
protected_only = true

[web]
port = $((port + 2))
site = "Friends news"
domain = "friends.invalid"
tls = true
TOML
    op init local.general control.cancel
    secret=$(openssl rand -hex 12)
    printf '%s\n%s\n' "$secret" "$secret" | op principal set-password operator --posting
    printf 'operator %s\n' "$secret" > "$dir/operator.login"; chmod 0600 "$dir/operator.login"
    echo "web_face_scratch: prepared $dir (face on https://127.0.0.1:$((port + 2))/)" ;;
  run)
    exec "$image" --fn operator "$dir/fn.toml" run ;;
  seed)
    tls=$(sed -n 's/^tls_port = //p' "$dir/fn.toml")
    subject="Welcome to Friends news"
    body="Say hello here. The node checks every password and keeps every post."
    printf '%s\n' "$body" | python3 tools/fn_client.py post local.general \
      --node "127.0.0.1:$tls" --tls --cafile "$dir/cert.pem" \
      --credentials "$dir/operator.login" --from "operator <operator@friends.invalid>" \
      --subject "$subject"
    code=$(op account invite --expires 7200 | grep -E '^[0-9a-f]{32}$')
    password=$(openssl rand -hex 10)
    umask 077
    printf '{"code": "%s", "password": "%s", "welcome": "%s", "welcomeBody": "%s"}\n' \
      "$code" "$password" "$subject" "$body" > "$dir/secrets.json"
    echo "web_face_scratch: seeded; inputs in $dir/secrets.json" ;;
  *) echo "web_face_scratch: unknown verb $verb" >&2; exit 2 ;;
esac
