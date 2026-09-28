#!/bin/sh
# One wait primitive a lane can start with run_in_background and forget.
#
#   tools/wait_for.sh [--host HOST] [--deadline S] [--interval S] CONDITION
#
# The options may come before or after the CONDITION.
#
# CONDITION is one of
#   --log FILE REGEX         a line of FILE matches REGEX (grep -E); prints it
#   --file PATH              PATH exists and is non-empty
#   --pid PID                process PID (one you started) has exited
#   --unit UNIT              systemd --user UNIT is no longer active; prints
#                            its Result and ExecMainStatus
#   --farm RUN REMOTE_ROOT   the farm run's status file exists; exits with the
#                            run's own code (then `farm.py wait` fetches)
#
# With --host the check runs there over ssh (hbox, persvati); without it,
# here.  Exit: 0 the condition holds (--farm: the run's code); 124 the
# deadline passed first (uncertain: the thing may still happen); 4 the check
# could not observe (ssh failed five times running and for at least two
# minutes, FN_WAIT_FOR_UNOBSERVED_S; the message quotes ssh's last error);
# 2 usage.
#
# The polls share one ssh connection (ControlMaster, persisting 10 minutes):
# a fresh handshake every interval from many lanes meets sshd's MaxStartups
# (10:30:100 on hbox) under load and is dropped, which read as "could not
# observe" while an interactive ssh worked (feed-queue, 2026-09-27).
#
# Why (planning/review-2026-09-26-lane-friction.md section 8): 1,073 hand
# written wait loops, 214 foreground commands killed at 600 s, and 45 loops of
# `until ! pgrep -f "farm.py wait ..."` whose own argv matched the pattern, so
# they never ended.  Nothing here matches a process by pattern.
set -u

usage() {
    sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//' >&2
    exit 2
}

HOST=
DEADLINE=3300
INTERVAL=15
KIND=
while [ $# -gt 0 ]; do
    case $1 in
        --host) [ $# -ge 2 ] || usage; HOST=$2; shift 2 ;;
        --deadline) [ $# -ge 2 ] || usage; DEADLINE=$2; shift 2 ;;
        --interval) [ $# -ge 2 ] || usage; INTERVAL=$2; shift 2 ;;
        --log) [ $# -ge 3 ] && [ -z "$KIND" ] || usage; KIND=log; A=$2; B=$3; shift 3 ;;
        --file) [ $# -ge 2 ] && [ -z "$KIND" ] || usage; KIND=file; A=$2; B=; shift 2 ;;
        --pid) [ $# -ge 2 ] && [ -z "$KIND" ] || usage; KIND=pid; A=$2; B=; shift 2 ;;
        --unit) [ $# -ge 2 ] && [ -z "$KIND" ] || usage; KIND=unit; A=$2; B=; shift 2 ;;
        --farm) [ $# -ge 3 ] && [ -z "$KIND" ] || usage; KIND=farm; A=$2; B=$3; shift 3 ;;
        -h|--help) usage ;;
        *) echo "wait_for: unknown argument: $1" >&2; usage ;;
    esac
done
[ -n "$KIND" ] || usage
case $DEADLINE$INTERVAL in *[!0-9]*) echo "wait_for: --deadline and --interval are whole seconds" >&2; exit 2 ;; esac
if [ "$KIND" = pid ]; then
    case $A in ''|*[!0-9]*) echo "wait_for: --pid takes a number" >&2; exit 2 ;; esac
fi

# A single-quoted shell word for $1.
q() { printf "'%s'" "$(printf '%s' "$1" | sed "s/'/'\\\\''/g")"; }

# The check, as a snippet: exit 0 met, 1 not yet, anything else 1 too except
# that --farm exits 0 when the status file exists and prints its content.
case $KIND in
    log) SNIPPET="[ -f $(q "$A") ] || exit 1; grep -E -m1 -- $(q "$B") $(q "$A")" ;;
    file) SNIPPET="test -s $(q "$A")" ;;
    # A zombie has exited; only its parent has not reaped it yet.
    pid) SNIPPET="s=\$(ps -o stat= -p $A 2>/dev/null); case \$s in ''|Z*) echo \"pid $A exited\" ;; *) exit 1 ;; esac" ;;
    unit) SNIPPET="if systemctl --user is-active --quiet $(q "$A"); then exit 1; fi; systemctl --user show -p LoadState -p Result -p ExecMainStatus $(q "$A") 2>/dev/null | tr '\n' ' '; echo" ;;
    farm) SNIPPET="f=$(q "$B")/build/farm/$(q "$A").status; [ -s \"\$f\" ] || exit 1; cat \"\$f\"" ;;
esac

# ssh's stderr for the last poll, so an exit 4 can say why.
ERR=$(mktemp "${TMPDIR:-/tmp}/wait_for.XXXXXX") || exit 4
trap 'rm -f "$ERR"' EXIT
trap 'exit 130' INT TERM

check() {
    if [ -n "$HOST" ]; then
        ssh -n -o ConnectTimeout=30 -o BatchMode=yes -o ServerAliveInterval=30 \
            -o ControlMaster=auto -o ControlPersist=600 \
            -o "ControlPath=$HOME/.ssh/fn-wait-for-%r@%h:%p" "$HOST" "$SNIPPET"
    else
        sh -c "$SNIPPET"
    fi
}

start=$(date +%s)
unobserved=0
first_unobserved=
while :; do
    out=$(check 2>"$ERR")
    rc=$?
    if [ $rc -eq 0 ]; then
        [ -n "$out" ] && printf '%s\n' "$out"
        if [ "$KIND" = farm ]; then
            code=$(printf '%s' "$out" | tr -dc '0-9')
            echo "wait_for: farm run $A finished with exit code ${code:-unknown}" >&2
            [ -n "$code" ] && exit "$code"
            exit 1
        fi
        exit 0
    fi
    now=$(date +%s)
    if [ -n "$HOST" ] && [ $rc -eq 255 ]; then
        unobserved=$((unobserved + 1))
        [ -n "$first_unobserved" ] || first_unobserved=$now
        if [ $unobserved -ge 5 ] && [ $((now - first_unobserved)) -ge "${FN_WAIT_FOR_UNOBSERVED_S:-120}" ]; then
            echo "wait_for: ssh to $HOST failed $unobserved times running over $((now - first_unobserved))s; cannot observe $KIND $A" >&2
            echo "wait_for: ssh's last error: $(tail -n 3 "$ERR" | tr '\n' ' ')" >&2
            exit 4
        fi
    else
        unobserved=0
        first_unobserved=
    fi
    if [ $((now - start)) -ge "$DEADLINE" ]; then
        echo "wait_for: deadline ${DEADLINE}s passed; $KIND $A${B:+ $B} not yet${HOST:+ on $HOST}" >&2
        exit 124
    fi
    if [ $unobserved -gt 0 ] && [ "$INTERVAL" -gt 10 ]; then
        sleep 10
    else
        sleep "$INTERVAL"
    fi
done
