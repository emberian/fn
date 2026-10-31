#!/bin/sh
# H's nightly row on the Mac (WORKFLOW-20261031: everything slow is one unattended nightly nobody waits on).
# Fast-forwards the laptop worktree build/lanes/h-nightly to origin/dev, certifies the books the harness
# needs, runs the nntp family against fn2 under the simulator and on the socket at 1,000 x 50, and writes
# build/h8/nightly/<date>-<sha>/ {table.md, summary.txt, cert.log, sim/, native/} plus build/h8/nightly/LATEST.txt.
# Started by cron (crontab: 30 3 * * * sh <repo>/fn2/tests/harness/laptop_nightly.sh); stop a running one with
# kill -- -$(cat build/h8/nightly/running.pid) (the group leader). Refuses under 60 GiB free or with a run live.
set -eu
# cron's environment is bare: the interpreters tools/acl2 and certify.sh need.
export PATH=/Library/Frameworks/Python.framework/Versions/3.11/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin
repo=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
tree=$repo/build/lanes/h-nightly
base=$repo/build/h8/nightly
python=$repo/build/h-venv/bin/python
mkdir -p "$base"
if [ -z "${H_NIGHTLY_LEADER:-}" ]; then
  # Re-exec as a session leader so the PID file names the whole group.
  H_NIGHTLY_LEADER=1 exec /usr/bin/python3 -c 'import os,sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])' \
    sh "$0" "$@" >> "$base/cron.log" 2>&1 < /dev/null
fi
if [ -f "$base/running.pid" ] && kill -0 "$(cat "$base/running.pid")" 2>/dev/null; then
  echo "$(date) refused: a nightly is running (pid $(cat "$base/running.pid"))"; exit 2
fi
free=$(df -g "$repo" | awk 'NR==2 {print $4}')
if [ "$free" -lt 60 ]; then echo "$(date) refused: ${free} GiB free (< 60)"; exit 2; fi
echo $$ > "$base/running.pid"
trap 'rm -f "$base/running.pid"' EXIT
git -C "$repo" fetch -q origin dev
if [ ! -d "$tree" ]; then git -C "$repo" worktree add --detach "$tree" origin/dev; fi
if [ -n "$(git -C "$tree" status --porcelain --untracked-files=no)" ]; then
  echo "$(date) refused: $tree has local changes"; exit 2
fi
git -C "$tree" checkout -q --detach origin/dev
sha=$(git -C "$tree" rev-parse --short HEAD)
out=$base/$(date +%Y-%m-%d)-$sha
if [ -e "$out" ]; then out=$out-$(date +%H%M); fi
mkdir -p "$out"
echo "$(date) start $sha -> $out"
sh "$tree/fn2/tools/certify.sh" tests/conn-unit.lisp sim/echo.lisp sim/check-wire.lisp sim/check-envelope.lisp \
  > "$out/cert.log" 2>&1 || { echo "H nightly $(basename "$out") $sha: CERTIFY RED, see $out/cert.log" | tee "$out/summary.txt" > "$base/LATEST.txt"; exit 1; }
cd "$tree"
export PYTHONPATH="$tree" FN2_SIM_EXAMPLES="${H_NIGHTLY_EXAMPLES:-1000}" FN2_SIM_STEPS="${H_NIGHTLY_STEPS:-50}"
FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_sim_session:session \
  "$python" -m fn2.tests.surface.run_surface --target fn2 --family nntp --box laptop --out "$out/sim" \
  > "$out/sim.log" 2>&1 &
FN2_SURFACE_NATIVE_NNTP=fn2.tests.surface.fn2_native_session:session \
  "$python" -m fn2.tests.surface.run_surface --target fn2-native --family nntp --box laptop --out "$out/native" \
  > "$out/native.log" 2>&1 &
wait
"$python" -m fn2.tests.surface.nightly_nntp "$out" "$sha" > /dev/null
cp "$out/summary.txt" "$base/LATEST.txt"
echo "$(date) done $sha: $(cat "$out/summary.txt")"
