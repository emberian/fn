#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

# Use an explicit caller override when supplied.  The normal ACL2 command is
# discovered only as a local fallback, so CI/toolchain wrappers are preserved.
if [ -z "${FN_ACL2:-}" ]; then
  FN_ACL2=$(command -v acl2 || true)
  export FN_ACL2
fi
if [ -z "${FN_ACL2:-}" ]; then
  printf '%s\n' 'FN_ACL2 is unset and acl2 was not found on PATH' >&2
  exit 1
fi

python3 tests/owner_feed_connection_host_check.py
if python3 tests/owner_feed_connection_host_check.py tests/owner-feed-connection-host-bad.lsp; then
  printf '%s\n' 'host witness harness accepted deliberate failing load' >&2
  exit 1
fi
printf '%s\n' 'owner feed connection host wrapper test passed (including failing-load rejection)'
