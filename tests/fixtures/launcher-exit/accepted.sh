#!/bin/sh
# The same paths, each classified: exit "$status" only in a decision arm.
status=0
out=$(child) || status=$?
case $out in
    refused\ *) echo "fn: $out" >&2; exit "$status" ;;
esac
if [ "$status" -ne 0 ]; then
    echo "fn: fault child-did-not-run exit=$status" >&2   # not exit 1
    exit 4
fi
child || exit 4
rc=0
child2 || rc=$?
[ "$rc" -eq 0 ] || { echo "child2: fault exit=$rc" >&2; exit 4; }
exec child3 "$@"
