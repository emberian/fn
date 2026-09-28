#!/bin/sh
# The build machines' load, memory and disk, one line each; or the box to use.
#
#   tools/boxes.sh            laptop, hbox, persvati: load1/cores, free memory, free disk
#   tools/boxes.sh --pick     print the build box (hbox or persvati) with the
#                             lowest load1 per core now, and both loads on stderr
#
# Free memory is MemAvailable plus, on hbox, the ZFS ARC, which shrinks on
# demand: `free` counts the ARC as used, and Claude misread an idle hbox as
# busy twice that way.  Disk is the free space of the box's scratch base
# (/tank/fn/scratch, ~/fn-gates).  A box that does not answer in 10 s reads
# "unreachable" and is never picked.  Exit: 0; 3 --pick found no box; 2 usage.
#
# Why: the coordinator's rule (closeout-common, 2026-09-28) is to decide per
# run by load per core; hbox swung from load 74 to 12 in an hour.
set -u

PROBE='n=$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu); l=$(cut -d" " -f1 /proc/loadavg 2>/dev/null || sysctl -n vm.loadavg | tr -d "{}" | cut -d" " -f2)
if [ -r /proc/meminfo ]; then m=$(awk "/MemAvailable/{print int(\$2/1048576)}" /proc/meminfo); else m=$(vm_stat | awk "/free|inactive|speculative/{s+=\$NF} END{print int(s*16384/1073741824)}"); fi
a=0; [ -r /proc/spl/kstat/zfs/arcstats ] && a=$(awk "\$1==\"size\"{print int(\$3/1073741824)}" /proc/spl/kstat/zfs/arcstats)
d=$HOME; [ -d /tank/fn/scratch ] && d=/tank/fn/scratch; [ -d $HOME/fn-gates ] && d=$HOME/fn-gates
f=$(df -Pk "$d" | awk "NR==2{print int(\$4/1048576)}")
echo "$n $l $m $a $f $d"'

probe() {  # HOST ("" = here) -> "cores load memGiB arcGiB diskGiB dir" or nothing
    if [ -z "$1" ]; then sh -c "$PROBE"
    else ssh -o ConnectTimeout=10 -o BatchMode=yes "$1" "$PROBE" 2>/dev/null; fi
}

line() {  # NAME "cores load mem arc disk dir"
    set -- "$1" $2
    if [ $# -lt 7 ]; then printf '%-9s unreachable\n' "$1"; return; fi
    awk -v n="$1" -v c="$2" -v l="$3" -v m="$4" -v a="$5" -v f="$6" -v d="$7" 'BEGIN{
        printf "%-9s load %6.2f on %3d cores (%.2f/core)  free mem %4d GiB%s  free disk %5d GiB (%s)\n",
            n, l, c, l/c, m+a, (a>0 ? sprintf(" (ARC %d GiB of it)", a) : ""), f, d}'
}

per_core() { set -- $1; [ $# -ge 2 ] && awk -v c="$1" -v l="$2" 'BEGIN{printf "%.3f", l/c}'; }

case ${1:-} in
    '')
        line laptop "$(probe '')"
        line hbox "$(probe hbox)"
        line persvati "$(probe persvati)" ;;
    --pick)
        best=; bestload=
        for box in hbox persvati; do
            load=$(per_core "$(probe "$box")")
            echo "boxes: $box ${load:-unreachable} load per core" >&2
            [ -n "$load" ] || continue
            if [ -z "$best" ] || awk -v a="$load" -v b="$bestload" 'BEGIN{exit !(a<b)}'; then
                best=$box; bestload=$load
            fi
        done
        [ -n "$best" ] || { echo "boxes: neither hbox nor persvati answered" >&2; exit 3; }
        echo "boxes: picked $best" >&2
        echo "$best" ;;
    *) sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
esac
