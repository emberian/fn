#!/bin/sh
# Each unclassified child-status path the launcher rule refuses.
status=0
out=$(child) || status=$?
[ "$status" -eq 0 ] || exit "$status"
child || exit 1
child || { echo "child failed" >&2; exit 1; }
child2
rc=$?
[ "$rc" -eq 0 ] || exit 1
case $out in
    *) exit "$status" ;;
esac
exit $?
