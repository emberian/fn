#!/bin/sh
# One build box's row for tools/hbox_native.sh (obstructions-7 item 67):
#
#   tools/native_box.sh BOX TREE [REMOTE_HOME]
#
# prints shell assignments for eval: BASE (the scratch base the runs live
# under), CACHE and WRAP (the certificate cache and the build wrapper, read
# from TREE/tools/farm.py HOSTS, the one table farm/remote_check use),
# IMAGES_BASE (where published image sets live; empty on a box that holds
# none) and OPENSSL (bundled: hbox's OpenSSL 3.5.8 test tool with its own
# libraries; system: the box's own openssl, 3.5 on persvati).  A leading ~
# in BASE or CACHE becomes REMOTE_HOME when given (the box's $HOME, so every
# path is absolute in the ssh commands and the box script); without it the ~
# stays, as a dry run prints it.  Exit 2 for an unknown box.
set -eu
BOX=${1:?BOX}
TREE=${2:?TREE}
HOMEDIR=${3:-}
case $BOX in
    hbox) BASE=/tank/fn/scratch IMAGES_BASE=/tank/fn/images OPENSSL=bundled ;;
    persvati) BASE='~/fn-gates' IMAGES_BASE= OPENSSL=system ;;
    *) echo "native_box: no row for box $BOX (hbox, persvati)" >&2; exit 2 ;;
esac
ROW=$(python3 - "$TREE" "$BOX" <<'PY'
import sys
sys.path.insert(0, sys.argv[1] + "/tools")
import farm
row = farm.HOSTS[sys.argv[2]]
print(row["cache"])
print(row.get("wrap", ""))
PY
) || { echo "native_box: tools/farm.py HOSTS has no row for $BOX" >&2; exit 2; }
CACHE=$(echo "$ROW" | sed -n 1p)
WRAP=$(echo "$ROW" | sed -n 2p)
if [ -n "$HOMEDIR" ]; then
    case $BASE in '~/'*) BASE=$HOMEDIR/${BASE#'~/'} ;; esac
    case $CACHE in '~/'*) CACHE=$HOMEDIR/${CACHE#'~/'} ;; esac
fi
for value in "$BASE" "$CACHE" "$WRAP" "$IMAGES_BASE"; do
    case $value in *[!A-Za-z0-9_./~-]*) echo "native_box: bad path in $BOX's row: $value" >&2; exit 2 ;; esac
done
printf "BASE='%s'\nCACHE='%s'\nWRAP='%s'\nIMAGES_BASE='%s'\nOPENSSL='%s'\n" \
    "$BASE" "$CACHE" "$WRAP" "$IMAGES_BASE" "$OPENSSL"
