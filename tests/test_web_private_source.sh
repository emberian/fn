#!/bin/sh
# Source admission/witnesses, not certification or a native browser result.
set -eu
cd "$(dirname "$0")/.."
session="web-private-source-$(date +%Y%m%dT%H%M%S)-$$"
trap 'python3 tools/proof_repl.py stop "$session" >/dev/null 2>&1' 0
python3 tools/proof_repl.py start "$session" books/web-session-keystones \
    --host "${FN_WEB_SOURCE_HOST:-laptop}" --ld-missing --limit 30 --load-limit 30
python3 tools/proof_repl.py send "$session" \
    '(include-book "../tests/acl2/must-fail-checked")' --limit 30
# These books' local includes are already loaded above. Sending their own
# forms preserves the exact source world without a certificate reinclusion.
python3 tools/proof_repl.py send-range "$session" tests/acl2/web-session-tests \
    --from wsst-octs --limit 30
python3 tools/proof_repl.py send-range "$session" tests/acl2/web-private-reply-tests \
    --from wprt-compare --limit 30
python3 tools/proof_repl.py send-range "$session" tests/acl2/web-private-begin-tests \
    --from wpbt-compare --limit 30
# Admit the actual host-reached streaming programs in this same coherent
# stobj world, then compare their windows against the existing page plans.
python3 tools/proof_repl.py send-range "$session" books/web-page-cursor --from fn-wpc-cursor --limit 30
python3 tools/proof_repl.py send-range "$session" books/web-list-stream --from fn-wgl-start --limit 30
python3 tools/proof_repl.py send-range "$session" books/web-article-stream --from fn-was-get --limit 30
python3 tools/proof_repl.py send-range "$session" books/web-reply-stream --from fn-wov-start --limit 30
python3 tools/proof_repl.py send-range "$session" host/web-host --from fn-web-host-private-reply-p --limit 30
python3 tools/proof_repl.py send-range "$session" tests/acl2/web-stream-consumer-source-tests \
    --from wwst-scan --limit 30
