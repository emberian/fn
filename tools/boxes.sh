#!/bin/sh
# The build machines' load, memory and disk, one line each; or the box to use;
# and box reservations for measurements.
#
#   tools/boxes.sh            laptop, hbox, persvati: load1/cores, free memory, free disk,
#                             and a live reservation under its box; then each live
#                             TOKEN lease (e.g. `wide') with its holder and expiry
#   tools/boxes.sh --pick     print the build box (hbox or persvati) with the
#                             lowest load1 per core now among those not reserved by
#                             someone else, and both loads on stderr; when every box
#                             that answers is reserved, wait for the first lease to end
#   tools/boxes.sh reserve BOX --for MINUTES --why TEXT [--as NAME]
#   tools/boxes.sh release BOX [--as NAME] [--force]
#   tools/boxes.sh check BOX [--as NAME]      prints "free" or the holder and expiry;
#                             exit 0 free (or yours), 4 reserved
#   tools/boxes.sh wait BOX [--as NAME] [--max MINUTES]   until free (or yours)
#   BOX may also be a named TOKEN (a lower-case word that is not a box, e.g.
#   `wide'): a lease on a shared resource rather than a machine, kept on
#   $FN_BOX_TOKEN_HOST (hbox) as ~/.fn-box-reservation-token-NAME; the same
#   reserve/release/check/wait and the same --as holder rules
#   (closeout-common's wide-book rule: `reserve wide --for MIN --why TEXT').
#
# Free memory is MemAvailable plus, on hbox, the ZFS ARC, which shrinks on
# demand: `free` counts the ARC as used, and Claude misread an idle hbox as
# busy twice that way.  Disk is the free space of the box's scratch base
# (/tank/fn/scratch, ~/fn-gates).  A box that does not answer in 10 s reads
# "unreachable" and is never picked.
#
# A reservation is a lease on the box ($HOME/.fn-box-reservation: expiry
# epoch, holder, why; written under flock), so a measurement (a whole-tree
# timing, a scale curve, a matched before/after) runs on a quiet box.
# Measurements reserve; routine certification does not.  The lease expires
# by itself (--for is required; reserve again to extend it).  The holder is
# --as, else $FN_BOX_AS, else the basename of the git worktree (the lane).
# tools/hbox_native.sh, tools/remote_check.sh, tools/farm.py submit and
# tools/proof_repl.py start honour it: an explicit box waits for the lease
# (printing who holds it and until when; proof_repl refuses at once a lease
# longer than its --lease-wait), auto picks the other box.
# FN_BOX_RESERVATION=ignore skips the wait (the holder's own runs pass anyway).
#
# Exit: 0; 3 --pick found no box; 4 reserved by someone else (reserve,
# release, check, wait past --max); 2 usage.
#
# Why: the coordinator's rule (closeout-common, 2026-09-28) is to decide per
# run by load per core; hbox swung from load 74 to 12 in an hour.  Lanes
# tau-pass and batch AZ asked for reservations: matched-load before/after runs
# were impossible on a box anyone could start work on.
set -u

LEASE_SHOW='L=$HOME/.fn-box-reservation; if [ -f "$L" ]; then IFS=$(printf "\t") read -r u h w < "$L"; n=$(date +%s); if [ "${u:-0}" -gt "$n" ] 2>/dev/null; then echo "R $u $(( (u - n + 59) / 60 )) $(date -u -d @$u +%H:%MZ 2>/dev/null || echo ?) $h $w"; fi; fi
for T in "$HOME"/.fn-box-reservation-token-*; do case $T in *.lock|*.new|*"*") continue ;; esac; [ -f "$T" ] || continue; IFS=$(printf "\t") read -r u h w < "$T"; n=$(date +%s); if [ "${u:-0}" -gt "$n" ] 2>/dev/null; then echo "T ${T##*-token-} $u $(( (u - n + 59) / 60 )) $(date -u -d @$u +%H:%MZ 2>/dev/null || echo ?) $h $w"; fi; done'

PROBE='n=$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu); l=$(cut -d" " -f1 /proc/loadavg 2>/dev/null || sysctl -n vm.loadavg | tr -d "{}" | cut -d" " -f2)
if [ -r /proc/meminfo ]; then m=$(awk "/MemAvailable/{print int(\$2/1048576)}" /proc/meminfo); else m=$(vm_stat | awk "/free|inactive|speculative/{s+=\$NF} END{print int(s*16384/1073741824)}"); fi
a=0; [ -r /proc/spl/kstat/zfs/arcstats ] && a=$(awk "\$1==\"size\"{print int(\$3/1073741824)}" /proc/spl/kstat/zfs/arcstats)
d=$HOME; [ -d /tank/fn/scratch ] && d=/tank/fn/scratch; [ -d $HOME/fn-gates ] && d=$HOME/fn-gates
f=$(df -Pk "$d" | awk "NR==2{print int(\$4/1048576)}")
echo "$n $l $m $a $f $d"
'"$LEASE_SHOW"

SSH=${FN_BOXES_SSH:-ssh}

probe() {  # HOST ("" = here) -> "cores load memGiB arcGiB diskGiB dir" [+ an "R ..." lease line] or nothing
    if [ -z "$1" ]; then sh -c "$PROBE"
    else $SSH -o ConnectTimeout=10 -o BatchMode=yes "$1" "$PROBE" 2>/dev/null; fi
}

first() { printf '%s\n' "$1" | sed -n 1p; }
lease() { printf '%s\n' "$1" | sed -n 's/^R //p' | sed -n 1p; }  # "until minleft HH:MMZ holder why..."

me() { printf '%s' "${AS:-${FN_BOX_AS:-$(basename "$(git rev-parse --show-toplevel 2>/dev/null || pwd)")}}"; }

held_by_other() {  # LEASE -> 0 when a live lease names someone else
    [ -n "$1" ] || return 1
    set -- $1
    [ "$4" != "$(me)" ]
}

describe() {  # BOX LEASE
    b=$1; set -- $2
    u=$1; left=$2; at=$3; h=$4; shift 4
    echo "$b reserved by $h until $at ($left min left): $*"
}

line() {  # NAME "cores load mem arc disk dir"
    set -- "$1" $2
    if [ $# -lt 7 ]; then printf '%-9s unreachable\n' "$1"; return; fi
    awk -v n="$1" -v c="$2" -v l="$3" -v m="$4" -v a="$5" -v f="$6" -v d="$7" 'BEGIN{
        printf "%-9s load %6.2f on %3d cores (%.2f/core)  free mem %4d GiB%s  free disk %5d GiB (%s)\n",
            n, l, c, l/c, m+a, (a>0 ? sprintf(" (ARC %d GiB of it)", a) : ""), f, d}'
}

per_core() { set -- $1; [ $# -ge 2 ] && awk -v c="$1" -v l="$2" 'BEGIN{printf "%.3f", l/c}'; }

sq() { printf "'%s'" "$(printf '%s' "$1" | sed "s/'/'\\\\''/g")"; }

usage() { sed -n '2,43p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2; }

# The lease operations run on the box, under flock: OP HOLDER MINUTES WHY FORCE.
LEASE_OP='L=$HOME/.fn-box-reservation$6; op=$1; me=$2; min=$3; why=$4; force=$5
exec 9>"$L.lock"; flock -w 60 9 || { echo "boxes: cannot lock $L" >&2; exit 3; }
n=$(date +%s); u=0; h=; w=
[ -f "$L" ] && IFS=$(printf "\t") read -r u h w < "$L"
live=0; [ "${u:-0}" -gt "$n" ] 2>/dev/null && live=1
if [ $live = 1 ] && [ "$h" != "$me" ] && [ "$force" != 1 ]; then
    echo "R $u $(( (u - n + 59) / 60 )) $(date -u -d @$u +%H:%MZ) $h $w"; exit 4
fi
case $op in
    show) [ $live = 1 ] && echo "R $u $(( (u - n + 59) / 60 )) $(date -u -d @$u +%H:%MZ) $h $w" ;;
    reserve) u=$((n + min * 60)); printf "%s\t%s\t%s\n" "$u" "$me" "$why" > "$L.new" && mv "$L.new" "$L"
             echo "R $u $min $(date -u -d @$u +%H:%MZ) $me $why" ;;
    release) rm -f "$L" ;;
esac'

lease_op() {  # BOX-OR-TOKEN OP MINUTES WHY FORCE
    lhost=$1; suffix=
    case $1 in hbox|persvati) ;; *) lhost=${FN_BOX_TOKEN_HOST:-hbox}; suffix=-token-$1 ;; esac
    $SSH -o ConnectTimeout=10 -o BatchMode=yes "$lhost" \
        "sh -c $(sq "$LEASE_OP") lease $(sq "$2") $(sq "$(me)") $(sq "$3") $(sq "$4") $(sq "$5") $(sq "$suffix")"
}

cmd=${1:-}
[ $# -gt 0 ] && shift
AS=; FOR=; WHY=; FORCE=0; MAX=240; BOX=
case $cmd in reserve|release|check|wait)
    [ $# -ge 1 ] || usage; BOX=$1; shift
    case $BOX in hbox|persvati) ;; *[!a-z0-9-]*|''|-*) usage ;; esac
    while [ $# -gt 0 ]; do
        case $1 in
            --as) [ $# -ge 2 ] || usage; AS=$2; shift 2 ;;
            --for) [ $# -ge 2 ] || usage; FOR=$2; shift 2 ;;
            --why) [ $# -ge 2 ] || usage; WHY=$(printf '%s' "$2" | tr '\t\n' '  '); shift 2 ;;
            --max) [ $# -ge 2 ] || usage; MAX=$2; shift 2 ;;
            --force) FORCE=1; shift ;;
            *) usage ;;
        esac
    done ;;
esac

case $cmd in
    '')
        tokens=
        for box in laptop hbox persvati; do
            host=$box; [ $box = laptop ] && host=
            out=$(probe "$host")
            line "$box" "$(first "$out")"
            l=$(lease "$out"); [ -n "$l" ] && echo "          $(describe "$box" "$l")"
            if [ "$box" = "${FN_BOX_TOKEN_HOST:-hbox}" ]; then
                tokens=$(printf '%s\n' "$out" | sed -n 's/^T //p')
            fi
        done
        printf '%s\n' "$tokens" | while read -r name rest; do
            [ -n "$name" ] && echo "token     $(describe "$name" "$rest")"
        done ;;
    --pick)
        waited=0
        while :; do
            best=; bestload=; soonest=
            for box in hbox persvati; do
                out=$(probe "$box")
                load=$(per_core "$(first "$out")")
                echo "boxes: $box ${load:-unreachable} load per core" >&2
                [ -n "$load" ] || continue
                l=$(lease "$out")
                if held_by_other "$l"; then
                    echo "boxes: $(describe "$box" "$l"); not picked" >&2
                    set -- $l
                    if [ -z "$soonest" ] || [ "$2" -lt "$soonest" ]; then soonest=$2; fi
                    continue
                fi
                if [ -z "$best" ] || awk -v a="$load" -v b="$bestload" 'BEGIN{exit !(a<b)}'; then
                    best=$box; bestload=$load
                fi
            done
            if [ -n "$best" ]; then echo "boxes: picked $best" >&2; echo "$best"; exit 0; fi
            [ -n "$soonest" ] || { echo "boxes: neither hbox nor persvati answered" >&2; exit 3; }
            if [ "${FN_BOX_RESERVATION:-}" = ignore ] || [ $waited -ge $((MAX * 60)) ]; then
                echo "boxes: every box is reserved" >&2; exit 3
            fi
            echo "boxes: every box is reserved; waiting (the first lease ends in $soonest min)" >&2
            sleep 30; waited=$((waited + 30))
        done ;;
    reserve)
        [ -n "$FOR" ] && [ -n "$WHY" ] || { echo "boxes: reserve needs --for MINUTES and --why TEXT" >&2; exit 2; }
        case $FOR in *[!0-9]*|'') usage ;; esac
        out=$(lease_op "$BOX" reserve "$FOR" "$WHY" 0); rc=$?
        l=$(lease "$out")
        if [ $rc = 0 ] && [ -n "$l" ]; then echo "boxes: $(describe "$BOX" "$l")"; exit 0; fi
        if [ $rc = 4 ]; then echo "boxes: $(describe "$BOX" "$l")" >&2; exit 4; fi
        echo "boxes: reserve on $BOX failed ($rc): $out" >&2; exit 3 ;;
    release)
        out=$(lease_op "$BOX" release 0 "" "$FORCE"); rc=$?
        if [ $rc = 4 ]; then echo "boxes: $(describe "$BOX" "$(lease "$out")"); not released (--force)" >&2; exit 4; fi
        [ $rc = 0 ] || { echo "boxes: release on $BOX failed ($rc)" >&2; exit 3; }
        echo "boxes: $BOX released" ;;
    check|wait)
        waited=0
        while :; do
            case $BOX in
                hbox|persvati) l=$(lease "$(probe "$BOX")") ;;
                *) l=$(lease "$(lease_op "$BOX" show 0 "" 0 2>/dev/null)") ;;
            esac
            if ! held_by_other "$l" || [ "${FN_BOX_RESERVATION:-}" = ignore ]; then
                if [ $cmd = check ]; then
                    if [ -n "$l" ]; then echo "boxes: $(describe "$BOX" "$l")"
                    else echo "boxes: $BOX free"; fi
                fi
                exit 0
            fi
            if [ $cmd = check ] || [ $waited -ge $((MAX * 60)) ]; then
                echo "boxes: $(describe "$BOX" "$l")" >&2; exit 4
            fi
            [ $((waited % 300)) = 0 ] && echo "boxes: $(describe "$BOX" "$l"); waiting" >&2
            sleep 30; waited=$((waited + 30))
        done ;;
    *) usage ;;
esac
