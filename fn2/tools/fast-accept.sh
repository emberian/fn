#!/bin/sh
# Acceptance for a certify-time commit (fn2 fast-books).
#   fn2/tools/fast-accept.sh base   run at the parent commit: keeps its OWED export and driver logs
#   fn2/tools/fast-accept.sh <tag>  run at the change: certifies the closure with --export-owed,
#                                   runs the six A4 drivers, compares with the base run
# The closure is every book/test named in fn2/tools/fast-accept-closure.txt that exists.
# OWED.md is compared against the base run's export, not against the committed file
# (the committed one can lag the export). Results: build/fast-accept/<tag>/result.
# One certify at a time: certify.sh holds build/fn2-certify.lock. Run under nohup with a PID file.
set -u
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
cd "$root"
tag=${1:?tag}
out=build/fast-accept/$tag; mkdir -p "$out"; rm -f "$out/result"
base=build/fast-accept/base
export FN_ACL2_SLOT_DIR=${FN_ACL2_SLOT_DIR:-/tmp/fn2-a4-acl2-slots} FN_ACL2_SLOTS=${FN_ACL2_SLOTS:-6} TIME_CERT=1
closure=""
for f in $(cat fn2/tools/fast-accept-closure.txt); do [ -f "fn2/$f" ] && closure="$closure $f"; done
sh fn2/tools/certify.sh --export-owed -j "${FAST_ACCEPT_JOBS:-2}" $closure > "$out/certify.log" 2>&1
echo "certify $?" >> "$out/result"
cp fn2/docs/OWED.md "$out/OWED.export.md"
git checkout fn2/docs/OWED.md 2>/dev/null
if [ "$tag" != base ]; then
  if cmp -s "$out/OWED.export.md" "$base/OWED.export.md"; then echo "OWED identical" >> "$out/result"
  else echo "OWED DIFFERS" >> "$out/result"; fi
fi
for d in sim-layer-a-a4-driver core-allocation-driver executor-allocation-driver sim-allocation-driver sim-layer-a-a4-smoke sim-layer-a-smoke; do
  timeout 3600 tools/acl2 < fn2/tests/$d.lsp > "$out/$d.log" 2>&1
  echo "$d $?" >> "$out/result"
  if [ "$tag" != base ]; then
    # Summary lines only: strip timings and the source revision before comparing.
    norm() { grep -E '^(A4|S1|OWN|ECHO|WORK|L1|POOL|FAULT|RECOVERY|REPLAY|SCRIBE|DEVICE|TURN|BROAD|ABI|TRACE|:PASSED)' "$1" | sed -E 's/"HEAD=[^"]+"/<rev>/; s/(mean|max)-us=[0-9.]+/\1-us=<t>/g; s/[0-9.]+ (us|ms|seconds)/<t>/g'; }
    if [ "$(norm "$base/$d.log")" = "$(norm "$out/$d.log")" ]; then echo "$d summary identical" >> "$out/result"
    else echo "$d SUMMARY DIFFERS" >> "$out/result"; fi
  fi
done
echo done >> "$out/result"
