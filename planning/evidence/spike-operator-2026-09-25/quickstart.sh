#!/bin/bash
# The quickstart, verbatim: nothing to a probed node.  Each numbered line is one operator command.
set -u
IMG=/tank/fn/scratch/bounds-join/tree/build/images/452d62cb31fc16ea3d5cf9c2e3b48404299509ec   # the release you downloaded
TREE=/tank/fn/scratch/spike-operator/tree                                                       # the fn source (packaging/)
export FN_NODE=/tank/fn/scratch/spike-operator/qs PATH=/tank/fn/scratch/spike-operator/qs/current/bin:$PATH
run() { echo; echo "\$ $*"; "$@"; echo "[exit $?]"; }
run $TREE/packaging/fn install $IMG 452d62cb                                        # 1
run fn init --mission small-community --host 127.0.0.1 --port 11932                   # 2
echo; echo "\$ printf \"%s\\n%s\\n\" \"\$PW\" \"\$PW\" | fn principal set-password alice --posting"
PW=$(openssl rand -hex 12); printf "%s\n%s\n" "$PW" "$PW" | fn principal set-password alice --posting; echo "[exit $?]"   # 3
run fn install-unit                                                                   # 4
run fn start                                                                          # 5
run fn doctor                                                                         # 6
echo; echo "\$ FN_PROBE_USER=alice FN_PROBE_PASSWORD=\$PW fn probe --post"
FN_PROBE_USER=alice FN_PROBE_PASSWORD=$PW fn probe --post; echo "[exit $?]"           # 7
run fn backup                                                                         # 8
echo; echo "\$ fn top   (one frame)"; TOP_ONCE=1 fn top; echo "[exit $?]"             # 9
run fn status                                                                         # 10
