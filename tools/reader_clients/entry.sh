#!/bin/sh
# Put the scratch CA (/work/ca.pem) into the container's system trust store
# with the distribution's own tool, run the command, then hand /work back to
# the invoking user (FN_HOST_UID:FN_HOST_GID) so the phase can read and
# remove what the client wrote.
if [ -f /work/ca.pem ]; then
    cp /work/ca.pem /usr/local/share/ca-certificates/fn-scratch-ca.crt
    update-ca-certificates >/dev/null 2>&1 || exit 97
fi
"$@"
rc=$?
[ -n "${FN_HOST_UID:-}" ] && chown -R "$FN_HOST_UID:${FN_HOST_GID:-$FN_HOST_UID}" /work 2>/dev/null
exit $rc
