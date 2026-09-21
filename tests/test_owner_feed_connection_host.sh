#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
result=$(mktemp "${TMPDIR:-/tmp}/fn-owner-feed-host.XXXXXX")
trap 'rm -f "$result"' EXIT HUP INT TERM
ACL2_CUSTOMIZATION=NONE ACL2_SYSTEM_BOOKS= acl2 >"$result" 2>&1 <<'EOF'
(ld "host/owner-host.lisp" :ld-error-action :error)
(ld "tests/owner-feed-connection-host.lsp" :ld-error-action :error)
(cw "FN_OWNER_FEED_CONNECTION_HOST_OK~%")
(good-bye)
EOF
grep -q 'FN_OWNER_FEED_CONNECTION_HOST_OK' "$result"
printf '%s\n' 'owner feed connection host wrapper test passed'
