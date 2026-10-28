#!/bin/sh
# Build a native image on a build box and run named test modules against it.
#
# The box is --box BOX (hbox, persvati or auto; default $FN_HBOX, else auto).
# Each box's row: its scratch BASE (hbox
# /tank/fn/scratch, persvati ~/fn-gates), its certificate cache and build
# wrapper (tools/farm.py HOSTS: hbox /tank/fn/certcache under swarm-build,
# persvati ~/fn-certcache with none), its test OpenSSL (hbox the 3.5.8 test
# tool below, persvati the system openssl 3.5) and whether it holds the
# published image sets (hbox only, /tank/fn/images).  auto picks by load per
# core (tools/boxes.sh --pick), except that --image-set and --reuse-image
# take hbox, where the sets and the earlier runs live; name --box to
# override.  The record (build/hbox-native/LABEL.run here) names the box.
#
#   tools/hbox_native.sh [options] REV MODULE...
#
# REV is a commit (shipped with a gzip-compressed `git archive`, so the tree
# is exactly that revision) or `.` (this working tree, uncommitted edits
# included, rsynced with farm.py's excludes). MODULE is a unittest name:
# tests.test_native_owner or
# tests.test_native_owner.SomeTests.
#
# Static preflights reuse successful receipts under BASE/.native-preflight-cache
# only for identical source and Python inputs. To precheck a candidate on the
# box, run tools/native_preflight.py --cache BASE/.native-preflight-cache
# --gate world-check (also interfaces-check and host-books). --force rechecks.
# Receipts do not replace proof, host loading, image or runtime checks.
#
# On the box, under BASE/NAME/native-LABEL/ (NAME is the lane: the
# basename of this worktree, or --name), it
#   1. installs the default profile's closure from /tank/fn/certcache and
#      plans the rest, certifying under swarm-build only with --allow-certify;
#   2. acquires and validates the image's artifact set (tools/proof_artifacts.py;
#      the dtn profile too when a DTN image is asked);
#   3. builds the requested images under swarm-build
#      (--images from developer,production,dtn,dtn-developer,reference,
#      developer-stripped,prof; default
#      developer).  dtn and dtn-developer are host/native/build-dtn.lisp's
#      images (build/fn-host-dtn, build/fn-host-dtn-developer), built exactly
#      as tools/runbooks/hbox-image-build.sh builds them.  `prof` is the
#      PROFILING developer image (tools/profile/build_native_profile.sh,
#      build/fn-host-prof; sb-sprof when FN_PROF_OUT is set), a measurement
#      tool and never a release or test subject.  It needs this run's own
#      full certify and acquire (steps 1-2) for the profiling entry's world;
#   4. runs each MODULE (a MemoryMax of 40G or more waits on one box-wide flock,
#      /tank/fn/scratch/.hbox-native-bigmem.lock, so two such scopes never
#      overlap) under systemd-run --user --scope -p MemoryMax (the module's
#      NATIVE_MEMORY, else 24G; --mem overrides it; a served-read measurement through
#      tools/fundamentals/sr_measure.py or served_ab.sh needs 40G: at 24G the
#      owner refuses its connections, connections-exceed-memory), against
#      the box's shipped OpenSSL 3.5.8 (FN_OPENSSL_PREFIX, D64), with every
#      --env NAME=VALUE exported.  The same 3.5.8 binary is also the TEST TOOL
#      (ML-DSA-65 keys and signatures made independently of the node):
#      $FN_TEST_OPENSSL_BIN, a wrapper that gives that binary its own
#      libraries and nothing else.  When dtn-developer is built and dtn is
#      not, FN_NATIVE_BP_HOST defaults to the dtn-developer image (the BP
#      tests default to build/fn-host-dtn, which that run does not build).
#      Each module's process also gets every variable tools/native_env.py
#      finds it reading: the image variables for the images built
#      (FN_NATIVE_HOST is only ever the production image), the opt-in flags
#      FN_RUN_HYBRID_E2E and FN_RUN_CONSUMER_EXCHANGE, FN_TEST_OPENSSL.  A
#      module reading an image variable whose image is not built is refused
#      by name before anything ships (exit 2), and again on the box before
#      the first test when the image is not in the tree (--no-build).  Each
#      module runs through tools/test_budget.py --one, and its line in
#      run.log is OK (N ran, K skipped), FAILED, or SKIPPED (N of N) with
#      every skip's reason; a SKIPPED module makes the status 4;
#      When the tree holds the production image (or the one --env
#      FN_NATIVE_HOST names), tools/native_env.py identity exports its four
#      identity variables (launcher, core and runtime SHA-256, and the source:
#      the commit, or HEAD+dirty for `.`) for every module;
#   5. writes every log to logs/ and SHA256SUMS (images and logs), then
#      `status` holding the first failing step's exit code, 0 if none.
#      run.log carries the box's load (`uptime`) at the start and the end
#      and the load average before each module, so a timing taken on a
#      loaded box can be judged.
#
# It prints the scratch path and returns once the box run has started
# (detached by default, so it survives the launcher's death).
# The record build/hbox-native/LABEL.run names the box, the run directory,
# the detached pid and the log, and
#
#   tools/hbox_native.sh status LABEL   prints the record, whether the pid is
#                                        alive, the status file and the log's tail
#   tools/hbox_native.sh attach LABEL   re-attaches: waits for `status`
#                                        (tools/wait_for.sh, --deadline S),
#                                        prints the run log, exits with status
#   tools/hbox_native.sh adopt LABEL   complete a pending launch identity
# Pending launches refuse replacement; adopt must resolve them (no abandon).
#   tools/hbox_native.sh status LABEL --dir prints the recorded box:directory
#   tools/hbox_native.sh stop LABEL [--grace S] TERM the recorded process group only
#                                        through a pidfd after checking its
#                                        leader, start time and exact run.sh;
#                                        then stop its recorded module scopes
#
# from any later session.  --wait starts, then attaches
# at once.  --detach is accepted and is the
# default.  The box run survives a dropped ssh (nohup, its own setsid group).
# Records name pgid and the same pid for older readers; status/attach use pgid.
# Records name starttime (Linux /proc/PID/stat field 22). Stop refuses
# records lacking it and systems lacking pidfd group signals; no numeric kill
# fallback. Module scopes have run-specific names in RUN/scopes; stop names
# only those units, including their children in independent sessions.
# --allow-certify permits missing-book and certify-origin closure certification.
# Without it, either plan needing books finishes with status 16 (certify refused).
# Stop sends TERM, then pidfd group KILL after --grace S (default 90 seconds).
# Status 143 with RUN/stopped means TERM cancellation; without it, status 143
# is an ordinary step exit. TERM is the only cancellation signal. run.sh alone writes status:
# before finish is available it writes 143 directly; afterwards it writes
# 143 before collecting SHA256SUMS and gate_walls. Status/attach require RUN/stopped to
# display stopped (143). After cancellation the leader stays alive while
# any other process remains in its group, preserving the pidfd KILL anchor.
# Artifact helpers have 120-second timeouts with a 5-second KILL backstop.
# hbox_native does not coordinate with farm runs: farm locks are per mirror.
# Lanes should certify through python3 tools/farm.py submit BOX --affected-by ...
# first, publishing to the cache, then rerun native; coordinate any allowed certify.
# --mem SIZE explicitly overrides each module's NATIVE_MEMORY (default 24G).
# Modules with MemoryMax >=40G hold the box-wide native bigmem flock.
#
# Options: --box hbox|persvati|auto (above), --name NAME, --label LABEL, --images LIST, --mem SIZE,
# --image-acl2 PATH (the ACL2 wrapper the IMAGES are built with; certification
# keeps the toolchain's.  Default /tank/fn/toolchains/w28/acl2-literal-4g-tls64k,
# the w28 launcher at --tls-limit 65536; use the toolchain's own path for 16384),
# --jobs N|auto (modules run N at a time against the one image set, default 1;
# auto takes at most 8 and keeps the sum of their MemoryMax limits within 88G
# (a module with no NATIVE_MEMORY runs under 8x its measured peak, tests/native_peaks.json,
# at least 4G, else 24G):
# each is its own process, its own MemoryMax scope and its own ports; a
# group of 20 modules at 4 jobs on hbox takes about a quarter of the serial
# time), --certify-jobs N|auto (certify, default auto: tools/chain_schedule.py), --no-build (reuse the images already in that
# scratch tree -- the one --label names; refused before anything ships when
# it lacks one, naming the runs of NAME that hold them; re-shipping preserves .cert/.port/.fasl),
# --image-set SHA (no certify and no build: link the prebuilt images the batch
# published for dev commit SHA from hbox:/tank/fn/images/SHA, verified by its
# SHA256SUMS; layout and publishing in tools/image_set.py; --images names
# which of its production, developer, dtn, dtn-developer to link; the
# images' identity source is SHA, the tree is REV), --overlay (with
# --image-set SHA: REV's host and book changes since SHA applied form by form
# to the set's cores and saved as derived cores in the tree's build/, seconds
# instead of the image cycle; tools/native_overlay.py plans it here first and
# refuses, by name and before anything ships, a change a definition swap
# cannot carry -- layouts, macros, constants, build-time effects, the
# sealed dispatch table; a stripped image under an ACL2 change is refused and
# so is every module that reads it; docs/testing.md "Overlay"), --reuse-image RUN (no
# certify and no build: link the images an earlier run built, RUN =
# NAME/native-LABEL or a /tank/fn/scratch path, from RUN/tree/build; their
# identity source is the one RUN's log names; `tools/image_set.py link-run`),
# --keyed-images (the content-keyed image store, tools/image_key.py: after the
# static gates the run computes each image's key from its inputs -- host and raw
# files, the book sources of the world, build scripts, foreign-library sources,
# toolchain -- and, when the box's store /tank/fn/images/keyed holds a set for
# exactly those keys, links it and skips resolve, install, certify, acquire,
# validate, host-ld and the saves; a miss runs the full path and publishes the
# images it builds under the set's key),
# --env NAME=VALUE (repeatable; paths may use $T, the tree),
# --all (run every module even when the box's verdict store holds a verdict
# for exactly its inputs: without it, a module whose stored verdict -- keyed by
# the module and its tests/ helpers, the harness, the runner, the images'
# launcher/core/runtime digests or overlay record, and the FN_* it reads --
# is OK or SKIPPED is replayed from the store, naming the run it came from,
# and one whose stored verdict is red re-runs only its red cases, the rest
# carried; tools/native_verdicts.py, store $FN_VERDICT_STORE else
# BASE/.verdicts; a cached verdict satisfies no claim: a claim names a live
# run), --deadline S (default 5400), --dry-run (print the box script; the refusal
# and the per-module environment show there), --allow-skips (run a module
# whose opt-in gate -- FN_RUN_*_E2E, FN_INN_SRC ... -- is unset; without it
# such a module is refused at launch, naming the variable, not skipped after
# the build).  Options may come before or
# after REV and the modules.
#
# A box reserved for a measurement (tools/boxes.sh reserve) is waited for before
# anything ships (the holder's own worktree passes).
#
set -eu
# Run an immutable private launcher copy so worktree edits cannot change it.
if [ -z "${FN_HBOX_NATIVE_COPY:-}" ]; then
    FN_HBOX_NATIVE_HERE=$(cd "$(dirname "$0")/.." && pwd)
    FN_HBOX_NATIVE_COPY=$(mktemp -d "${TMPDIR:-/tmp}/hbox_native.XXXXXX") || exit 3
    cp "$FN_HBOX_NATIVE_HERE/tools/hbox_native.sh" "$FN_HBOX_NATIVE_HERE/tools/wait_for.sh" \
        "$FN_HBOX_NATIVE_HERE/tools/boxes.sh" "$FN_HBOX_NATIVE_HERE/tools/image_set.py" \
        "$FN_HBOX_NATIVE_HERE/tools/native_box.sh" "$FN_HBOX_NATIVE_HERE/tools/native_overlay.py" \
        "$FN_HBOX_NATIVE_HERE/tools/native_reuse.py" \
        "$FN_HBOX_NATIVE_HERE/tools/native_certify_plan.py" \
        "$FN_HBOX_NATIVE_COPY/" || exit 3
    export FN_HBOX_NATIVE_COPY FN_HBOX_NATIVE_HERE
    exec sh "$FN_HBOX_NATIVE_COPY/hbox_native.sh" "$@"
fi
trap 'rm -rf "$FN_HBOX_NATIVE_COPY"' EXIT
HERE=$FN_HBOX_NATIVE_HERE
ORIGINAL_ARGS=$(python3 -c 'import json,sys; print(json.dumps(sys.argv[1:]))' "$@")
BOX=${FN_HBOX:-auto}
NAME=$(basename "$HERE")
LABEL=${FN_NATIVE_LAUNCH_LABEL:-}
IMAGES=developer
MEM=
ALLOW_CERTIFY=
IMAGE_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k
JOBS=auto
MODULE_JOBS=1
BUILD=1
DETACH=1
DRY=0
ALLOW_SKIPS=
ALL=${FN_NATIVE_ALL:-0}
DEADLINE=5400
ENVS=
IMAGES_GIVEN=0
POSITIONAL=
BUILD_ONLY=
PUBLISH=
IMAGE_SET=
REUSE=
OVERLAY=
FROM_TRAIN=
KEYED=
usage() { sed -n '2,/^set -eu/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//' >&2; exit 2; }
# Shared by launch identity capture and stop, streamed from this private copy.
native_process_script() {
    cat <<'PROCESS'
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import select
import signal
import subprocess
import sys
import time


def process_stat(pid, proc_root=Path("/proc")):
    text = (proc_root / str(pid) / "stat").read_text()
    # comm is parenthesized and may contain spaces or closing parentheses.
    fields = text.rsplit(")", 1)[1].split()
    if int(text.split("(", 1)[0]) != pid:
        raise ValueError("stat names a different PID")
    return int(fields[2]), int(fields[19])  # fields 5 (pgrp), 22 (starttime)


def group_members(pgid, proc_root=Path("/proc"), helper_pid=None):
    """Read-only membership check; its output is never a signal target."""
    helper_pid = os.getpid() if helper_pid is None else helper_pid
    members = []
    for entry in proc_root.iterdir():
        if not entry.name.isdecimal():
            continue
        pid = int(entry.name)
        if pid in (pgid, helper_pid):
            continue
        try:
            pgrp, _ = process_stat(pid, proc_root)
        except (FileNotFoundError, ProcessLookupError):
            continue  # A process disappeared during the read-only snapshot.
        if pgrp == pgid:
            members.append(pid)
    return sorted(members)


def scope_prefix(run_dir, pid, starttime):
    digest = hashlib.sha256(os.fsencode(str(run_dir))).hexdigest()
    return f"fn-native-{digest}-{pid}-{starttime}"


def write_identity(pid, run_dir, launch_id):
    pgid, starttime = process_stat(pid)
    if pgid != pid or starttime <= 0:
        raise ValueError("launch process is not a live group leader")
    (run_dir / "scope-prefix").write_text(scope_prefix(run_dir, pid, starttime) + "\n")
    print(scope_prefix(run_dir, pid, starttime), flush=True)
    (run_dir / "run.starttime").write_text(str(starttime) + "\n")
    pending = run_dir / f"run.identity.{pid}.tmp"
    pending.write_text(f"{launch_id} {pid} {starttime} {scope_prefix(run_dir, pid, starttime)}\n")
    pending.replace(run_dir / "run.identity")


def publish_identity(record, launch_id, identity):
    fields = dict(line.split("=", 1) for line in record.read_text().splitlines())
    parts = identity.split()
    if fields.get("launch_id") != launch_id or len(parts) != 4 or parts[0] != launch_id:
        raise ValueError("launch identity mismatch; record not published")
    pid, starttime = map(int, parts[1:3])
    if pid <= 1 or starttime <= 0 or parts[3] != scope_prefix(Path(fields["dir"]), pid, starttime):
        raise ValueError("unsafe or mismatched leader identity; record not published")
    fields.update(pid=str(pid), pgid=str(pid), starttime=str(starttime))
    pending = record.with_name(record.name + ".tmp")
    pending.write_text("".join(f"{key}={value}\n" for key, value in fields.items()))
    pending.replace(record)


def leader_exited(fd, seconds=0):
    poller = select.poll()
    poller.register(fd, select.POLLIN)
    return bool(poller.poll(max(0, int(seconds * 1000))))


def recorded_generation(pid, starttime, run_dir):
    if (run_dir / "run.starttime").read_text().strip() != str(starttime):
        raise ValueError("run directory start time does not match the record")
    if (run_dir / "scope-prefix").read_text().strip() != scope_prefix(run_dir, pid, starttime):
        raise ValueError("run directory scope prefix does not match the recorded leader")


def scope_state(unit):
    done = subprocess.run(["systemctl", "--user", "show", "-p", "LoadState,ActiveState", "--", unit],
                          capture_output=True, text=True, timeout=60)
    if done.returncode:
        raise ValueError(f"state query failed (exit {done.returncode}): "
                         f"{done.stderr.strip() or done.stdout.strip()}")
    properties = dict(line.split("=", 1) for line in done.stdout.splitlines() if "=" in line)
    load, active = properties.get("LoadState"), properties.get("ActiveState")
    if not load or not active:
        raise ValueError("state query omitted LoadState or ActiveState")
    return load, active


def scope_already_stopped(unit):
    load, active = scope_state(unit)
    return load != "loaded" or active == "inactive"


def stop_scopes(pid, starttime, run_dir):
    recorded_generation(pid, starttime, run_dir)
    units = list(dict.fromkeys((run_dir / "scopes").read_text().splitlines()))
    pattern = re.compile(re.escape(scope_prefix(run_dir, pid, starttime)) + r"-[1-9][0-9]*\.scope")
    failed = False
    for unit in units:
        if not pattern.fullmatch(unit):
            print(f"hbox_native: refused scope name outside this run: {unit!r}", file=sys.stderr)
            failed = True
            continue
        try:
            if scope_already_stopped(unit):
                print(f"hbox_native: scope {unit}: already stopped", flush=True)
                continue
            done = subprocess.run(["systemctl", "--user", "stop", "--", unit],
                                  capture_output=True, text=True, timeout=60)
            if done.returncode:
                # The scope may disappear between show and stop as its group
                # exits. Recheck the exact unit before reporting a failure.
                if scope_already_stopped(unit):
                    print(f"hbox_native: scope {unit}: already stopped", flush=True)
                    continue
                print(f"hbox_native: scope {unit}: stop failed (exit {done.returncode}): "
                      f"{done.stderr.strip() or done.stdout.strip()}", file=sys.stderr)
                failed = True
            else:
                print(f"hbox_native: scope {unit}: stopped", flush=True)
        except (OSError, subprocess.TimeoutExpired, ValueError) as error:
            print(f"hbox_native: scope {unit}: cleanup failed: {error}", file=sys.stderr)
            failed = True
    if not units:
        print("hbox_native: no recorded module scopes")
    return 2 if failed else 0


def stop_run(pid, starttime, run_dir, proc_root=Path("/proc"), grace=90):
    fd = None
    generation_lock = None
    def cleanup_after_exit():
        rc = stop_scopes(pid, starttime, run_dir)
        if not (run_dir / "status").is_file():
            print(f"hbox_native: recovery failed: leader exited without final status; inspect {run_dir}", file=sys.stderr)
            return 2
        return rc
    try:
        if pid <= 1 or starttime <= 0 or grace < 0:
            raise ValueError("record lacks a safe PID/starttime or grace")
        try:
            fd = os.pidfd_open(pid)
        except OSError as error:
            if error.errno != errno.ESRCH:
                raise
            # Pin the directory generation while retrying scope cleanup. A new
            # launch cannot replace its identity or scopes during this retry.
            generation_lock = (run_dir / "run.lock").open("a")
            fcntl.flock(generation_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            recorded_generation(pid, starttime, run_dir)
            print(f"hbox_native: leader {pid} was already gone; retrying recorded scopes", flush=True)
            return cleanup_after_exit()
        pgid, observed_start = process_stat(pid, proc_root)
        if pgid != pid:
            raise ValueError("recorded process is not a group leader")
        if observed_start != starttime:
            raise ValueError("leader start time does not match the launch record")
        cmdline = (proc_root / str(pid) / "cmdline").read_bytes()
        script = os.fsencode(str(run_dir / "run.sh"))
        if cmdline not in (b"sh\0" + script + b"\0", b"/bin/sh\0" + script + b"\0"):
            raise ValueError("leader command line is not exactly this run's run.sh")
        recorded_generation(pid, starttime, run_dir)
        flags = getattr(signal, "PIDFD_SIGNAL_PROCESS_GROUP", 4)
        signal.pidfd_send_signal(fd, signal.SIGTERM, None, flags)
        print(f"hbox_native: sent TERM through pidfd to pgid {pid} ({run_dir}/run.sh)", flush=True)
        print("hbox_native: run.sh writes status 143 when it exits", flush=True)
        deadline = time.monotonic() + grace
        status_reported = False
        while not leader_exited(fd):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                signal.pidfd_send_signal(fd, signal.SIGKILL, None, flags)
                print(f"hbox_native: grace {grace}s expired; sent KILL through the same pidfd to pgid {pid}", flush=True)
                if not leader_exited(fd, 5):
                    raise ValueError("leader did not exit within 5s after pidfd KILL")
                break
            # Read status while polling the pinned leader; only run.sh writes it.
            if not status_reported and (run_dir / "status").exists():
                print("hbox_native: observed status " + (run_dir / "status").read_text().strip(), flush=True)
                status_reported = True
            leader_exited(fd, min(0.1, remaining))
        return cleanup_after_exit()
    except (AttributeError, OSError, ValueError, IndexError) as error:
        print(f"hbox_native: refused stop: {error}", file=sys.stderr)
        return 2
    finally:
        if fd is not None:
            os.close(fd)
        if generation_lock is not None:
            generation_lock.close()


if __name__ == "__main__":
    if sys.argv[1] == "identity":
        write_identity(int(sys.argv[2]), Path(sys.argv[3]), sys.argv[4])
    elif sys.argv[1] == "publish":
        try:
            publish_identity(Path(sys.argv[2]), sys.argv[3], sys.argv[4])
        except (OSError, ValueError, KeyError) as error:
            sys.exit(f"hbox_native: {error}")
    elif sys.argv[1] == "lock-launch":
        fd = os.open(sys.argv[2], os.O_RDWR | os.O_CREAT, 0o600)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            sys.exit("hbox_native: same-label launch already in progress: " + sys.argv[2])
        os.dup2(fd, 7, inheritable=True)
        os.environ["FN_NATIVE_LABEL_LOCK"] = sys.argv[2]
        os.environ["FN_NATIVE_LABEL_LOCK_OWNER"] = str(os.getpid())
        os.environ["FN_NATIVE_LAUNCH_LABEL"] = Path(sys.argv[2]).stem
        os.execvp("sh", ["sh", sys.argv[3], *json.loads(sys.argv[4])])
    elif sys.argv[1] == "group-members":
        print(" ".join(map(str, group_members(int(sys.argv[2])))))
    elif sys.argv[1] == "stop":
        sys.exit(stop_run(int(sys.argv[2]), int(sys.argv[3]), Path(sys.argv[4]), grace=int(sys.argv[5])))
    else:
        sys.exit("hbox_native: unknown process operation")
PROCESS
}
# Launch/adopt hold the local lock through publication; stop holds it through cleanup.
lock_label() {
    lock=$HERE/build/hbox-native/$LABEL.lock
    [ "${FN_NATIVE_LABEL_LOCK:-}" != "$lock" ] || [ "${FN_NATIVE_LABEL_LOCK_OWNER:-}" != "$$" ] || return 0
    mkdir -p "$HERE/build/hbox-native"
    native_process_script | python3 - lock-launch "$lock" "$0" "$ORIGINAL_ARGS"
    exit $?
}
# Shipping children cannot keep the local launcher lock alive.
ssh() { command ssh "$@" 7>&-; }
rsync() { command rsync "$@" 7>&-; }
readback_identity() {
    if IDENTITY=$(ssh -n "$HOST" "remaining=5; while [ \$remaining -gt 0 ]; do identity=\$(cat $S/run.identity 2>/dev/null || true); case \"\$identity\" in '$LAUNCH_ID '*) printf '%s\\n' \"\$identity\"; exit 0 ;; esac; sleep 1; remaining=\$((remaining - 1)); done; cat $S/run.identity") &&
       native_process_script | python3 - publish "$record" "$LAUNCH_ID" "$IDENTITY"; then exec 7>&-; return 0; fi
    echo "hbox_native: identity readback failed for $HOST:$S; use status $LABEL --dir or adopt $LABEL to re-run readback" >&2
    return 3
}
# status / attach / stop LABEL: read the record this worktree's start wrote.
attach_run() {
    record=$HERE/build/hbox-native/$2.run
    case $2 in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: $1 takes the run's LABEL" >&2; exit 2 ;; esac
    case $1 in stop|adopt) LABEL=$2; lock_label ;; esac
    [ -f "$record" ] || { echo "hbox_native: no record $record (runs started here: $(ls "$HERE/build/hbox-native" 2>/dev/null | sed 's/\.run$//' | tr '\n' ' '))" >&2; exit 2; }
    HOST=$(sed -n 's/^box=//p' "$record")
    S=$(sed -n 's/^dir=//p' "$record")
    [ -n "$HOST" ] && [ -n "$S" ] || { echo "hbox_native: $record names no box or dir" >&2; exit 2; }
    case $S in /*) ;; *) echo "hbox_native: bad run directory in $record" >&2; exit 2 ;; esac
    case $S in *[!A-Za-z0-9_./-]*) echo "hbox_native: bad run directory in $record" >&2; exit 2 ;; esac
    if [ "$1:${3:-}" = status:--dir ]; then echo "$HOST:$S"; exit 0; fi
    if [ "$1" = adopt ]; then
        LAUNCH_ID=$(sed -n 's/^launch_id=//p' "$record")
        case $LAUNCH_ID in ''|*[!0-9a-f]*) echo "hbox_native: record lacks a launch id" >&2; exit 2 ;; esac
        readback_identity || exit $?
        echo "hbox_native: adopted $LABEL ($HOST:$S)"; exit 0
    fi
    PID=$(sed -n 's/^pgid=//p' "$record")
    case $PID in ''|*[!0-9]*|0|1) echo "hbox_native: $record names no safe process group; use adopt $2 (directory: $HOST:$S)" >&2; exit 2 ;; esac
    if [ "$1" = stop ]; then
        STARTTIME=$(sed -n 's/^starttime=//p' "$record")
        case $STARTTIME in ''|*[!0-9]*|0) echo "hbox_native: refused stop: $record lacks a safe starttime" >&2; exit 2 ;; esac
        GRACE=${3:-90}
        case $GRACE in ''|*[!0-9]*) echo "hbox_native: --grace takes seconds (a nonnegative integer)" >&2; exit 2 ;; esac
        native_process_script | ssh "$HOST" "python3 - stop $PID $STARTTIME $S $GRACE"
        exit $?
    fi
    if [ "$1" = status ]; then
        cat "$record"
        ssh -n "$HOST" "if /bin/kill -0 -- -$PID 2>/dev/null; then echo 'pgid $PID: running'; else echo 'pgid $PID: not running'; fi; if [ -f $S/status ]; then status=\$(cat $S/status); case \$status in 143) if [ -f $S/stopped ]; then echo 'status: stopped (143)'; else echo 'status 143'; fi ;; *) echo \"status \$status\" ;; esac; else echo 'status: none yet'; fi; tail -n 12 $S/run.log 2>/dev/null"
        exit $?
    fi
    DEADLINE=${3:-$DEADLINE}
    echo "hbox_native: attached to $HOST:$S (pgid $PID)"
    ssh -n "$HOST" "if /bin/kill -0 -- -$PID 2>/dev/null; then echo 'pgid $PID: running'; else echo 'pgid $PID: not running'; fi"
    set +e
    sh "$FN_HBOX_NATIVE_COPY/wait_for.sh" --host "$HOST" --deadline "$DEADLINE" --interval 30 --file "$S/status" 7>&- >/dev/null
    waited=$?
    set -e
    ssh -n "$HOST" "cat $S/run.log; echo '== SHA256SUMS'; cat $S/SHA256SUMS 2>/dev/null"
    if [ $waited -ne 0 ]; then
        echo "hbox_native: no status after ${DEADLINE}s (wait_for exit $waited); the run may still be going in $HOST:$S (attach again)" >&2
        exit 124
    fi
    status=$(ssh -n "$HOST" "cat $S/status")
    case $status in
        143) if ssh -n "$HOST" "[ -f $S/stopped ]"; then
            echo "hbox_native: stopped (143) ($HOST:$S)"
        else echo "hbox_native: status 143 ($HOST:$S)"; fi ;;
        *) echo "hbox_native: status $status ($HOST:$S)" ;;
    esac
    exit "$status"
}
case ${1:-} in
    status|attach|stop|adopt)
        [ $# -ge 2 ] || usage
        case "$1:${3:-}" in
            stop:--grace|attach:--deadline) [ $# -eq 4 ] || usage; set -- "$1" "$2" "$4" ;;
            status:--dir) [ $# -eq 3 ] || usage ;;
            stop:|attach:|status:|adopt:) [ $# -eq 2 ] || usage ;;
            *) usage ;;
        esac
        attach_run "$@" ;;
esac
while [ $# -gt 0 ]; do
    case $1 in
        --name) NAME=$2; shift 2 ;;
        --label) LABEL=$2; shift 2 ;;
        --images) IMAGES=$2; IMAGES_GIVEN=1; shift 2 ;;
        --mem) MEM=$2; shift 2 ;;
        --allow-certify) ALLOW_CERTIFY=--allow-certify; shift ;;
        --jobs)
            case $2 in auto) ;; ''|*[!0-9]*|0) echo "hbox_native: --jobs takes auto or a positive integer" >&2; exit 2 ;; esac
            MODULE_JOBS=$2; shift 2 ;;
        --certify-jobs) JOBS=$2; shift 2 ;;
        --no-build) BUILD=0; shift ;;
        # --build-only: certify, acquire, host-ld and the --images saves, no
        # modules (they run afterwards, sharded, through tools/boxq.py against
        # the published set).  --publish: on success, tools/image_set.py
        # publish the tree's images as REV's set on this box (REV a commit).
        --build-only) BUILD_ONLY=1; shift ;;
        --publish) PUBLISH=1; shift ;;
        --image-set)
            case $2 in *[!0-9a-f]*|'') echo "hbox_native: --image-set takes a commit sha" >&2; exit 2 ;; esac
            IMAGE_SET=$2; BUILD=0; shift 2 ;;
        --box)
            case $2 in
                hbox|persvati|auto) BOX=$2 ;;
                *) python3 "$HERE/tools/box_table.py" names | grep -qx -- "$2" || {
                       echo "hbox_native: --box takes hbox, persvati, auto or a live box in ~/.config/fn/boxes.json" >&2; exit 2; }
                   BOX=$2 ;;
            esac
            shift 2 ;;
        --reuse-image)
            case $2 in /*) REUSE=$2 ;; */native-*) REUSE=__BASE__/$2 ;;
                native-*) REUSE=__NAME__/$2 ;;
                *) echo "hbox_native: --reuse-image takes NAME/native-LABEL or the box's absolute run path" >&2; exit 2 ;;
            esac
            case $REUSE in *..*|*[!A-Za-z0-9._/-]*) echo "hbox_native: bad --reuse-image $2" >&2; exit 2 ;; esac
            BUILD=0; shift 2 ;;
        --overlay) OVERLAY=1; shift ;;
        --from-train) FROM_TRAIN=1; shift ;;
        --keyed-images) KEYED=1; shift ;;
        --detach) DETACH=1; shift ;;
        --wait) DETACH=0; shift ;;
        --dry-run) DRY=1; shift ;;
        # A module gated by an unset opt-in (FN_RUN_*_E2E ...) is refused at
        # launch unless this is given (tools/native_env.py plan; item 45).
        --allow-skips) ALLOW_SKIPS=--allow-skips; shift ;;
        --all) ALL=1; shift ;;
        --deadline) DEADLINE=$2; shift 2 ;;
        # The ACL2 wrapper the IMAGE builds run under (certification keeps
        # the toolchain's, whose identity the cache keys on).  The world is
        # past SBCL's --tls-limit 16384 since batch AV ("Thread local
        # storage exhausted"; recover-memory-2's packet); the default is the
        # tls64k wrapper above.
        --image-acl2)
            case $2 in /*) ;; *) echo "hbox_native: --image-acl2 takes an absolute path" >&2; exit 2 ;; esac
            case $2 in *[!A-Za-z0-9_./-]*) echo "hbox_native: bad --image-acl2 path" >&2; exit 2 ;; esac
            IMAGE_ACL2=$2; shift 2 ;;
        --env)
            case $2 in
                ?*=*) ;;
                *) echo "hbox_native: --env takes NAME=VALUE" >&2; exit 2 ;;
            esac
            # Spelled out: a locale's [A-Z] range can match lower case.
            case ${2%%=*} in [0-9]*|*[!ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_]*) echo "hbox_native: bad --env name ${2%%=*}" >&2; exit 2 ;; esac
            # A comma is inert in the box script's unquoted `export NAME=VALUE`
            # and native_env.py splits a value only at its first `=` (C15: a
            # comma-separated value was refused).
            case ${2#*=} in *[!A-Za-z0-9_./:,\$-]*) echo "hbox_native: --env value may hold only A-Za-z0-9_./:,-\$" >&2; exit 2 ;; esac
            ENVS="$ENVS $2"; shift 2 ;;
        -h|--help) usage ;;
        -*) echo "hbox_native: unknown option $1" >&2; usage ;;
        # An option may follow REV or a module: positionals are
        # collected and every option still applies.  REV and module names
        # hold no blank (each is validated below), so the list re-splits.
        *) POSITIONAL="$POSITIONAL $1"; shift ;;
    esac
done
# shellcheck disable=SC2086
set -- $POSITIONAL
if [ -n "$BUILD_ONLY" ]; then [ $# -eq 1 ] || { echo "hbox_native: --build-only takes REV and no modules" >&2; exit 2; }
else [ $# -ge 2 ] || usage; fi
if [ -n "$PUBLISH" ]; then
    [ "$BUILD" = 1 ] && [ -z "$OVERLAY" ] || { echo "hbox_native: --publish publishes images this run builds (not --image-set, --overlay, --reuse-image or --no-build)" >&2; exit 2; }
    case $1 in .) echo "hbox_native: --publish needs REV to be a commit, not ." >&2; exit 2 ;; esac
fi
REV=$1; shift
for module in "$@"; do
    case $module in
        tests.[A-Za-z_]*) ;;
        *) echo "hbox_native: $module is not a unittest module name (tests.test_...)" >&2; exit 2 ;;
    esac
    case $module in *[!A-Za-z0-9_.]*) echo "hbox_native: bad module name $module" >&2; exit 2 ;; esac
done
case $NAME in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: bad --name $NAME" >&2; exit 2 ;; esac
# Without --images, the list is what the modules read, over developer
# (tools/native_env.py images): a module reading FN_NATIVE_HOST gets the
# production image built. An explicit --images is taken as given; a module reading
# an image it leaves out is refused by name below.
if [ "$IMAGES_GIVEN" = 0 ]; then
    DERIVE_ENV=
    for assignment in $ENVS; do DERIVE_ENV="$DERIVE_ENV --env $assignment"; done
    # shellcheck disable=SC2086
    IMAGES=$(python3 "$HERE/tools/native_env.py" images --images "$IMAGES" $DERIVE_ENV "$@") || exit 2
fi
DTN=0
DTN_PRODUCTION=0
DTN_DEVELOPER=0
for image in $(echo "$IMAGES" | tr ',' ' '); do
    case $image in
        developer|production|reference|developer-stripped|prof) ;;
        dtn) DTN=1; DTN_PRODUCTION=1 ;;
        dtn-developer) DTN=1; DTN_DEVELOPER=1 ;;
        *) echo "hbox_native: --images takes developer,production,dtn,dtn-developer,reference,developer-stripped,prof" >&2; exit 2 ;;
    esac
done
if [ -n "$OVERLAY" ] && [ -z "$IMAGE_SET" ]; then
    echo "hbox_native: --overlay applies REV over a published set: give --image-set SHA" >&2; exit 2
fi
if [ -n "$IMAGE_SET" ] && [ -n "$REUSE" ]; then
    echo "hbox_native: --image-set and --reuse-image both name the images; give one" >&2; exit 2
fi
if [ -n "$FROM_TRAIN" ]; then
    if [ "$REV" = . ] || [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ] || [ -n "$OVERLAY" ] || [ $BUILD -ne 1 ]; then
        echo "hbox_native: --from-train starts an image build from the train's certified tree of the commit REV; it takes a commit and no --image-set, --reuse-image, --overlay or --no-build" >&2; exit 2
    fi
fi
if [ -n "$KEYED" ]; then
    if [ "$REV" = . ] || [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ] || [ -n "$OVERLAY" ] || [ -n "$FROM_TRAIN" ] || [ $BUILD -ne 1 ]; then
        echo "hbox_native: --keyed-images keys the images of a commit REV this run would build; it takes no --image-set, --reuse-image, --overlay, --from-train or --no-build, and REV is a commit" >&2; exit 2
    fi
    case ",$IMAGES," in *,prof,*) echo "hbox_native: --keyed-images does not key the prof image" >&2; exit 2 ;; esac
fi
if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ]; then
    for image in $(echo "$IMAGES" | tr ',' ' '); do
        case $image in production|developer|dtn|dtn-developer) ;;
            *) echo "hbox_native: an image set holds production, developer, dtn and dtn-developer, not $image" >&2; exit 2 ;;
        esac
    done
fi
if [ -n "$IMAGE_SET" ]; then
    IMAGE_SET=$(git -C "$HERE" rev-parse --verify --quiet "$IMAGE_SET^{commit}" || echo "$IMAGE_SET")
    case $IMAGE_SET in *[!0-9a-f]*) exit 2 ;; esac
    [ ${#IMAGE_SET} -eq 40 ] || { echo "hbox_native: --image-set $IMAGE_SET: not a commit here; give the full sha" >&2; exit 2; }
fi
if [ $DTN_DEVELOPER -eq 1 ] && [ $DTN_PRODUCTION -eq 0 ]; then
    case " $ENVS" in *" FN_NATIVE_BP_HOST="*) ;; *) ENVS="FN_NATIVE_BP_HOST=\$T/build/fn-host-dtn-developer$ENVS" ;; esac
fi
# What each module reads, against what this run builds.
ENVARGS=
for assignment in $ENVS; do ENVARGS="$ENVARGS --env $assignment"; done
if [ -n "$BUILD_ONLY" ]; then PLAN=
else PLAN=$(python3 "$HERE/tools/native_env.py" plan --images "$IMAGES" $ENVARGS $ALLOW_SKIPS "$@") || exit 2; fi
if [ -n "$MEM" ]; then
    PLAN=$(printf '%s\n' "$PLAN" | python3 "$HERE/tools/test_budget.py" --memory-plan --memory-override "$MEM") || exit 2
else
    PLAN=$(printf '%s\n' "$PLAN" | python3 "$HERE/tools/test_budget.py" --memory-plan) || exit 2
fi
if [ "$MODULE_JOBS" = auto ]; then
    MODULE_JOBS=$(printf '%s\n' "$PLAN" | python3 "$HERE/tools/test_budget.py" --memory-jobs) || exit 2
fi
if [ "$REV" = . ]; then
    # The image's declared source: HEAD, marked +dirty for uncommitted edits.
    SOURCE_ID=$(git -C "$HERE" rev-parse HEAD)$(git -C "$HERE" diff --quiet HEAD -- 2>/dev/null || echo '+dirty')
    SOURCE="worktree $SOURCE_ID"
    [ -n "$LABEL" ] || LABEL=wt-$(date -u +%Y%m%dT%H%M%SZ)
else
    FULL=$(git -C "$HERE" rev-parse --verify "$REV^{commit}") || { echo "hbox_native: no commit $REV" >&2; exit 2; }
    SOURCE_ID=$FULL
    SOURCE="commit $FULL"
    [ -n "$LABEL" ] || LABEL=$(echo "$FULL" | cut -c1-12)
fi
# The tree the modules run in; the images' identity source (SOURCE_ID) may
# differ under --image-set or --reuse-image.  train.py image accepts a run
# at HEAD's tree whose images come from another commit only when no image
# input differs between the two (READY-image reuse).
TREE_ID=$SOURCE_ID
case $LABEL in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: bad --label $LABEL" >&2; exit 2 ;; esac
# The overlay's plan, here where git is: a refusal stops the launch, naming
# each change an image build must carry instead.
if [ -n "$OVERLAY" ]; then
    OVERLAY_DIR=$HERE/build/native-overlay/$LABEL
    python3 "$HERE/tools/native_overlay.py" plan "$IMAGE_SET" "$REV" --out "$OVERLAY_DIR" >&2 \
        || { echo "hbox_native: --overlay refused (above); run without --overlay to build images" >&2; exit 2; }
    REFUSED_IMAGES=$(python3 -c 'import json,sys; p=json.load(open(sys.argv[1])); print(" ".join(i for i in sys.argv[2].split(",") if p["images"][i].get("refused")))' "$OVERLAY_DIR/plan.json" "$IMAGES")
    if [ -n "$REFUSED_IMAGES" ]; then
        echo "hbox_native: --overlay cannot carry this change into: $REFUSED_IMAGES (above); drop the modules that read them or build images" >&2
        exit 2
    fi
fi
# The images' own source is the set's commit, whatever tree runs the tests.
[ -z "$IMAGE_SET" ] || SOURCE_ID=$IMAGE_SET
# A keyed run's images are either a stored set's (built at an older commit) or
# this run's own: the box writes build/KEYED_SOURCE once it knows which.
REAL_SOURCE_ID=$SOURCE_ID
[ -z "$KEYED" ] || SOURCE_ID='$(cat build/KEYED_SOURCE)'
# The box and its row (item 67).  auto takes hbox for --image-set and
# --reuse-image (the published sets and the earlier runs live there) and for
# a dry run (no ssh); otherwise the lower load per core now.
if [ "$BOX" = auto ]; then
    if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ] || [ $DRY -eq 1 ]; then
        BOX=hbox
    else
        BOX=$(sh "$FN_HBOX_NATIVE_COPY/boxes.sh" --pick) || { echo "hbox_native: no build box answers (tools/boxes.sh --pick)" >&2; exit 3; }
    fi
fi
HOST=$BOX
ROW=$(sh "$FN_HBOX_NATIVE_COPY/native_box.sh" "$BOX" "$HERE") || exit 2
eval "$ROW"
case "$BASE $CACHE" in
    '~/'*|*' ~/'*)
        if [ $DRY -eq 0 ]; then
            # Absolute paths in every ssh command and in the box script.
            REMOTE_HOME=$(ssh -n "$HOST" 'echo $HOME') || { echo "hbox_native: cannot reach $HOST" >&2; exit 3; }
            ROW=$(sh "$FN_HBOX_NATIVE_COPY/native_box.sh" "$BOX" "$HERE" "$REMOTE_HOME") || exit 2
            eval "$ROW"
        fi ;;
esac
# The test OpenSSL (the CLI of the same 3.5.8 the node ships).
openssl_setup() {
    case $OPENSSL in
        bundled) cat <<'OSSL'
printf '%s\n' '#!/bin/sh' 'LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib exec /tank/fn/toolchains/openssl-3.5.8/bin/openssl "$@"' > $S/bin/openssl-test
OSSL
        ;;
    esac
    echo 'chmod 0755 $S/bin/openssl-test'
}
if [ -n "$IMAGE_SET" ] && [ -z "$IMAGES_BASE" ]; then
    echo "hbox_native: $BOX holds no published image sets (they are published on hbox); use --box hbox with --image-set" >&2; exit 2
fi
S=$BASE/$NAME/native-$LABEL
case $REUSE in __NAME__/*) REUSE=$BASE/$NAME/${REUSE#__NAME__/} ;; __BASE__/*) REUSE=$BASE/${REUSE#__BASE__/} ;; esac
if [ -n "$REUSE" ]; then
    [ "$REUSE" != "$S" ] || { echo "hbox_native: --reuse-image $REUSE is this run's own tree (use --no-build)" >&2; exit 2; }
    # The images' identity source is the reused run's, read on the box from
    # the file link-run writes (its run.log's `== source` line).
    SOURCE_ID='$(cat build/REUSED_SOURCE)'
fi
case $S in /tank/fn/node*) echo "hbox_native: refusing the live node path" >&2; exit 2 ;; esac

# --from-train: the image run starts from the train's certified tree of this
# commit (tools/native_reuse.py).  The records are read here; the tree itself
# is checked on the box before anything starts (below).  Any refusal says why
# and leaves REUSE_TREE empty: the run then installs, certifies and acquires
# as it always did, in its own freshly shipped tree.
REUSE_TREE=
REUSE_RUN=
CERT_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k  # the certify launcher (tools/farm.py HOSTS)
reuse_refused() {
    echo "hbox_native: --from-train refused: $1" >&2
    echo "hbox_native: falling back to the install, certify and acquire path in a freshly shipped tree" >&2
    REUSE_TREE=
}
if [ -n "$FROM_TRAIN" ]; then
    if PLAN_OUT=$(python3 "$FN_HBOX_NATIVE_COPY/native_reuse.py" plan --repo "$HERE" --rev "$FULL" --box "$HOST"); then
        REUSE_TREE=$(printf '%s' "$PLAN_OUT" | python3 -c 'import json,sys; print(json.load(sys.stdin)["remote_path"])')
        REUSE_RUN=$(printf '%s' "$PLAN_OUT" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["run"] + " " + d["certify_id"])')
    else
        reuse_refused "${PLAN_OUT#native_reuse: }"
    fi
fi

# The box half.  Every step logs to $S/logs and a failure stops the run with
# that step's code in $S/status.
box_script() {
    if [ -n "$REUSE_TREE" ]; then TREE_EXPR=$REUSE_TREE; else TREE_EXPR='$S/tree'; fi
    cat <<BOX
#!/bin/sh
set -u
S=$S
trap 'if [ \${RUN_OWNS_DIRECTORY:-0} = 1 ]; then printf "TERM %s\\n" "\$(date -u +%Y-%m-%dT%H:%M:%SZ)" > \$S/stopped; echo 143 > \$S/status; if command -v wait_group >/dev/null 2>&1; then trap "STOPPED=1" TERM; wait_group; fi; fi; exit 143' TERM
STOPPED=0
# Only a live run.sh holds this remote lock; children close fd 8.
exec 8> \$S/run.lock
flock -n 8 || { echo "hbox_native: run already locked by leader \$(cat \$S/run.pid 2>/dev/null)" >&2; exit 2; }
RUN_OWNS_DIRECTORY=1
wait_group() {
    polls=0
    while :; do
        # exec eliminates the command-substitution shell; only the
        # Python polling helper joins the group and excludes itself.
        members=\$(exec 8>&-; exec python3 \$S/process.py group-members \$\$ 2>/dev/null) || members="membership scan failed; retaining anchor"
        [ -n "\$members" ] || break
        if [ \$((polls % 60)) -eq 0 ]; then
            echo "hbox_native: waiting for group members: \$members"
        fi
        sleep 1 8>&-
        polls=\$((polls + 1))
    done
}
T=$TREE_EXPR
L=\$S/logs
cat > \$S/process.py <<'PROCESS'
$(native_process_script)
PROCESS
FN_NATIVE_SCOPE_PREFIX=\$(python3 \$S/process.py identity \$\$ \$S \$FN_NATIVE_LAUNCH_ID 8>&-) || { echo 3 > \$S/status; exit 3; }
export FN_NATIVE_SCOPE_PREFIX
ACL2=$CERT_ACL2  # the certify launcher (tools/farm.py HOSTS)
CACHE=$CACHE  # this box's (tools/farm.py HOSTS)
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
mkdir -p \$S/bin
$(openssl_setup)
export FN_TEST_OPENSSL_BIN=\$S/bin/openssl-test
# Durable scratch for stores that must sit on durable storage (a mission's
# init: store-mount-identity), read through tests/native_harness.py
# durable_root: hbox's root ext4 on NVMe, where an init's fsyncs cost 0.24 s;
# the tank's ZFS cost 4.7 s at load 33 and one command 194 s (tooling-truth-3).
export FN_TEST_DURABLE_TMP=\${FN_TEST_DURABLE_TMP:-/var/tmp}
# The box's fixture stores (tools/native_box.sh FIXTURES); tools/native_env.py
# sets FN_OPEN_DEPTH_FIXTURES from it for each module that reads it.
export FN_FIXTURES_DIR=$FIXTURES
export FN_ACL2=\$ACL2 FN_CERT_CACHE=\$CACHE FN_CERT_ORIGIN_KIND=run
# One install per run (tools/certs.py INSTALL_RECORD): the install step and
# the incremental certify share this id, so the certify reuses the install
# step's selection instead of running it again.
export FN_INSTALL_RUN=\$S-\$\$
# One content-hash memo per certificate cache (tools/certs.py content_hash),
# shared by every run on this box: the install, certify and acquire steps of
# this run, and the next run's, stat a cache file an earlier step already read
# (the key is the file's inode, size, mtime and ctime, so a rewritten file is
# read again).  A fresh run tree no longer re-reads ~20,000 cache files.
export FN_CONTENT_HASH_FILE=\$CACHE/.content-hashes.json
# One resolution plan per run tree (tools/certs.py _planned_entries): the
# install, acquire and acquire-dtn steps read the cache entries the resolve step
# below listed once for the union closure, redoing only what changed since.
export FN_RESOLUTION_PLAN=\$T/build/.resolution-plan.json
# The book reader's per-text cache (tools/ledger.py), shared by this box's
# runs: content-addressed, so a fresh tree reads only what changed.
export FN_LEDGER_FORMS_CACHE=\${FN_LEDGER_FORMS_CACHE:-$BASE/.ledger-forms}
mkdir -p \$L
rm -f \$S/status
cd \$T || { echo 9 > \$S/status; exit 9; }
step() {
    name=\$1; shift
    echo "== \$name \$(date -u +%H:%M:%SZ)"
    ( exec 8>&-; case \$(command -v "\$1") in /*) exec "\$@" ;; *) "\$@" ;; esac ) > \$L/\$name.log 2>&1 &
    wait \$!
    rc=\$?
    [ \$STOPPED -eq 0 ] || rc=143
    echo "   \$name exit \$rc (\$L/\$name.log)"
    if [ \$rc -ne 0 ]; then
        tail -n 15 \$L/\$name.log | sed 's/^/   | /'
        finish \$rc
    fi
}
# Steps that may run at once (the image saves: each its own ACL2 session
# over the same certified books, writing only its own build/fn-host* files;
# the foreign libraries are built first, once).  pstep starts one in the
# background; pwait waits for all of them and stops the run at the first that
# failed, in the order they were started.  Batch 6: six serial saves were
# 10m44s of a 36-minute run, the longest single one 2m06s.
# At most one save per 6 GiB available (a save holds the world, about 4-5 GiB;
# cloud2's 22 GiB takes three at once, lat1 all six).
PSTEPS=
PPIDS=
PMAX=\$(awk '/MemAvailable/{n=int(\$2/6291456); print (n<1)?1:n}' /proc/meminfo)
pstep() {
    name=\$1; shift
    n=0; first=
    for p in \$PPIDS; do n=\$((n + 1)); [ -n "\$first" ] || first=\$p; done
    if [ \$n -ge \$PMAX ]; then wait \$first; PPIDS=\${PPIDS#* \$first}; fi
    echo "== \$name \$(date -u +%H:%M:%SZ) (parallel, at most \$PMAX)"
    ( exec 8>&-; "\$@" > \$L/\$name.log 2>&1; echo \$? > \$L/\$name.rc ) &
    PPIDS="\$PPIDS \$!"
    PSTEPS="\$PSTEPS \$name"
}
pwait() {
    wait
    prc=0
    for name in \$PSTEPS; do
        rc=\$(cat \$L/\$name.rc 2>/dev/null || echo 3)
        echo "   \$name exit \$rc \$(date -u -r \$L/\$name.rc +%H:%M:%SZ 2>/dev/null) (\$L/\$name.log)"
        if [ \$rc -ne 0 ] && [ \$prc -eq 0 ]; then
            tail -n 15 \$L/\$name.log | sed 's/^/   | /'
            prc=\$rc
        fi
    done
    PSTEPS=
    [ \$prc -eq 0 ] || finish \$prc
}
# A module reads an image variable: the image must be in the tree.
need() {
    [ -x "\$3" ] || { echo "hbox_native: \$1 reads \$2: \$3 is not in the tree (build it with --images)"; finish 2; }
}
finish() {
    # Further stop signals during artifact collection mark cancellation;
    # they must not recursively enter finish or restore the step's exit code.
    trap 'STOPPED=1' TERM
    finish_status=\$1
    mark_stopped() {
        STOPPED=1
        COLLECT_INTERRUPTED=1
        printf 'TERM %s\\n' "\$(date -u +%Y-%m-%dT%H:%M:%SZ)" > \$S/stopped
        echo 143 > \$S/status
    }
    trap mark_stopped TERM
    [ \$STOPPED -eq 0 ] || mark_stopped
    echo "== load at end: \$(uptime)"
    collect() {
        ( exec 8>&-; exec "\$@" ) &
        collector=\$!
        while :; do
            COLLECT_INTERRUPTED=0
            wait \$collector || :
            [ \$COLLECT_INTERRUPTED -ne 0 ] || break
        done
    }
    collect timeout -k 5 120 sh -c 'cd "\$1" && { find tree/build -maxdepth 1 -name "fn-host*" -type f -exec sha256sum {} + ; sha256sum logs/*.log; }' sh \$S > \$S/SHA256SUMS 2>/dev/null
    collect timeout -k 5 120 python3 \$T/tools/gate_walls.py \$S > \$S/gate_walls.json 2>/dev/null
    cancel_finished_run() {
        # Repeated TERM must never release the group-signal anchor.
        trap 'STOPPED=1' TERM
        mark_stopped
        echo "== done status 143; \$S/SHA256SUMS"
        wait_group
        exit 143
    }
    # Cover TERM in the final normal-finish window too. The cancellation
    # handler writes its own marker/status and retains the same anchor.
    trap cancel_finished_run TERM
    [ \$STOPPED -eq 0 ] || cancel_finished_run
    trap '' TERM
    echo \$finish_status > \$S/status
    echo "== done status \$finish_status; \$S/SHA256SUMS"
    exit \$finish_status
}
trap 'STOPPED=1; finish 143' TERM
echo "== source $SOURCE"
# The images' source record (tools/build_native_host.sh writes it beside each
# image; tools/image_set.py publish requires \`commit SHA\`): this tree is a
# shipped copy, not a git checkout, so the shipper names it.
FN_NATIVE_SOURCE="$SOURCE"; export FN_NATIVE_SOURCE
echo "== load at start: \$(uptime)"
# The toolchain SBCL (tools/farm.py HOSTS) first on PATH and as FN_SBCL:
# Refuse a bare sbcl outside that toolchain before any step.
eval "\$(python3 tools/native_env.py sbcl --export)"
step sbcl-check python3 tools/native_env.py sbcl-check
BOX
    if [ $BUILD -eq 1 ]; then
        cat <<BOX
python3 tools/proof_artifacts.py roots --profile default > \$L/roots.txt || finish 13
BOX
        if [ $DTN -eq 1 ]; then
            # The dtn profile's roots are not a subset of default's
            # (books/records-concrete at 804896a1): certify their union.
            cat <<BOX
python3 tools/proof_artifacts.py roots --profile dtn >> \$L/roots.txt || finish 13
sort -u -o \$L/roots.txt \$L/roots.txt
BOX
        fi
        cat <<BOX
# Run static pre-image gates before certification, acquire and image building.
static_gate() {
    gate=\$1; shift
    if [ -f tools/native_preflight.py ]; then
        python3 tools/native_preflight.py --cache "$BASE/.native-preflight-cache" --gate "\$gate"
    else
        # The selected historical revision may predate the receipt tool.
        python3 "\$@"
    fi
}
step world-check static_gate world-check tools/extract/world.py --check
step interfaces-check static_gate interfaces-check tools/interface_emit.py --check
# A repository declaration is not evidence its book is in this image.
# Reject a missing native entry before spending time on certification.
step host-books static_gate host-books tools/host_check.py --books
# A certified host file attaches the image's stobj implementation before the
# generic it implements (tools/host_check.py --attach-order).
step attach-order static_gate attach-order tools/host_check.py --attach-order
step one-world static_gate one-world tools/one_world_check.py
BOX
        if [ -n "$KEYED" ]; then
            KEYSTORE=${IMAGES_BASE:-/tank/fn/images}/keyed
            cat <<BOX
# Content-keyed images (tools/image_key.py): a stored set whose keys are this
# tree's links in and skips everything that builds an image.
KEYED=0
mkdir -p build
echo "$REAL_SOURCE_ID" > build/KEYED_SOURCE
echo "== image-key \$(date -u +%H:%M:%SZ)"
python3 tools/image_key.py reuse --no-link --store $KEYSTORE --tree \$T --acl2 "\$ACL2" --image-acl2 "${IMAGE_ACL2:-\$ACL2}" --images $IMAGES --record \$S/image-keys.json > \$L/image-key.log 2>&1 8>&-
key_rc=\$?
sed 's/^/   | /' \$L/image-key.log
if [ \$key_rc -eq 0 ]; then
    # The wire grammar is a function of the wire book's sources (the box's
    # wire store, tools/protocol_emit.py): a tree with no certificate makes it
    # only from that store, and a store without it is a miss.
    if [ -f tools/box_artifacts.py ] && ! python3 tools/protocol_emit.py --wire --write > \$L/box-wire.log 2>&1 8>&-; then
        echo "   image-key: the wire grammar is not in the box's store; the full path runs"
        tail -n 3 \$L/box-wire.log | sed 's/^/   | /'
    elif python3 tools/image_key.py reuse --store $KEYSTORE --tree \$T --acl2 "\$ACL2" --image-acl2 "${IMAGE_ACL2:-\$ACL2}" --images $IMAGES >> \$L/image-key.log 2>&1 8>&-; then
        KEYED=1
        echo "   image-key: HIT, the stored images are linked; resolve, install, certify, acquire and the image saves are skipped"
    else
        echo "   image-key: the stored set was refused; the full path runs"
        tail -n 3 \$L/image-key.log | sed 's/^/   | /'
        # A refused link may have placed some: only a build's own files may stay.
        python3 tools/image_key.py unlink --store $KEYSTORE --tree \$T
    fi
else
    echo "   image-key: miss (exit \$key_rc); the full path runs and publishes the set"
fi
if [ \$KEYED -eq 0 ]; then
BOX
        fi
        if [ -n "$REUSE_TREE" ]; then
            # The train's certified tree stands in for the install, the
            # incremental certify, box-wire (the train's protocol_emit
            # --wire --write made build/box there) and acquire.  native_reuse.py
            # verify proved, before this script was written, that the tree is
            # the commit and holds the cache pair of every book of the roots;
            # validate below still loads the roots in the image's launcher.
            cat <<BOX
echo "== reuse: the train's certified tree \$T (farm run $REUSE_RUN); install, certify, box-wire and acquire skipped"
BOX
        else
            cat <<BOX
toolchain=\$(python3 tools/acl2_toolchain.py identity "\$ACL2") || finish 14
ACQUIRED_DEFAULT=0
BOX
        if [ $DTN -eq 0 ]; then
            cat <<BOX
# A successful acquisition of this exact source closure and toolchain is a
# hint only: acquire still re-enumerates, installs and ACL2-loads the cache
# set. Without that content-keyed hint, keep the incremental path rather than
# paying for a full acquisition known to miss newly generated world books.
source_identity=\$(python3 tools/proof_artifacts.py identity --profile default) || finish 13
cached_receipt=
for receipt in $BASE/*/native-*/logs/acquire.log; do
    [ -f "\$receipt" ] || continue
    if grep -F "source=\$source_identity toolchain=\$toolchain " "\$receipt" >/dev/null 2>&1; then
        cached_receipt=\$receipt
        break
    fi
done
if [ -n "\$cached_receipt" ]; then
    echo "== acquire-cached \$(date -u +%H:%M:%SZ) (hint \$cached_receipt)"
    python3 tools/proof_artifacts.py acquire --profile default --root \$T --cache \$CACHE --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}" > \$L/acquire.log 2>&1 8>&-
    cached_rc=\$?
    echo "   acquire-cached exit \$cached_rc (\$L/acquire.log)"
    if [ \$cached_rc -eq 0 ]; then
        ACQUIRED_DEFAULT=1
    else
        mv \$L/acquire.log \$L/acquire-cached-refused.log
    fi
fi
BOX
        fi
        cat <<BOX
# The union closure of the default and DTN roots, listed once (roots.txt).
step resolve python3 tools/certs.py --cache \$CACHE --toolchain-identity "\$toolchain" resolve \$(cat \$L/roots.txt)
if [ \$ACQUIRED_DEFAULT -eq 0 ]; then
    step install python3 tools/certs.py --cache \$CACHE --toolchain-identity "\$toolchain" --acl2 "\$ACL2" install-partial \$(cat \$L/roots.txt)
fi
# Prints "== certify plan: N books to certify of M in the roots' closure";
# refuses with status 16 without --allow-certify before either certify step.
certify_plan() {
    python3 \$S/bin/native_certify_plan.py --tree "\$T" --mode "\$1" --toolchain-identity "\$toolchain" --acl2 "\$ACL2" --box $BOX $ALLOW_CERTIFY \$(cat \$L/roots.txt)
    rc=\$?
    [ \$rc -eq 0 ] || finish \$rc
}
if [ \$ACQUIRED_DEFAULT -eq 0 ]; then
    step certify-plan certify_plan incremental
    step certify $WRAP python3 tools/certify_books.py --incremental --images ${FN_CERT_IMAGES:-on} --jobs $JOBS --timeout-seconds 900 \$(cat \$L/roots.txt)
else
    echo "== cached closure acquired: install, certify plan and certify skipped"
fi
# The wire grammar is a box artifact (tools/box_artifacts.py: build/box/,
# never committed), absent from a shipped tree: made here from the certified
# books/wire-export (test_native_store_identity reads it).  A revision before
# the registers left git has neither the tool nor the need.
if [ -f tools/box_artifacts.py ]; then step box-wire $WRAP python3 tools/protocol_emit.py --wire --write; fi
# Acquire needs one complete cache origin; incremental certification may leave
# none. On NO_SET (exit 3) only, allow-certify permits one whole-closure
# certification in this tree and another acquire. Any further failure stops.
ORIGIN_DONE=0
acquire_step() {
    name=\$1; profile=\$2
    echo "== \$name \$(date -u +%H:%M:%SZ)"
    python3 tools/proof_artifacts.py acquire --profile \$profile --root \$T --cache \$CACHE --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}" > \$L/\$name.log 2>&1 8>&-
    rc=\$?
    echo "   \$name exit \$rc (\$L/\$name.log)"
    if [ \$rc -eq 3 ] && [ \$ORIGIN_DONE -eq 0 ]; then
        ORIGIN_DONE=1
        certify_plan closure
        echo "   \$name: no complete single-origin set in the cache; certifying the roots' closure in this tree (one coherent origin), then acquiring once more"
        mv \$L/\$name.log \$L/\$name-first.log
        step certify-origin $WRAP python3 tools/certify_books.py --closure --images ${FN_CERT_IMAGES:-on} --jobs $JOBS --timeout-seconds 900 \$(cat \$L/roots.txt)
        echo "== \$name-retry \$(date -u +%H:%M:%SZ)"
        python3 tools/proof_artifacts.py acquire --profile \$profile --root \$T --cache \$CACHE --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}" > \$L/\$name.log 2>&1 8>&-
        rc=\$?
        echo "   \$name-retry exit \$rc (\$L/\$name.log)"
    fi
    if [ \$rc -ne 0 ]; then
        tail -n 15 \$L/\$name.log | sed 's/^/   | /'
        finish \$rc
    fi
}
if [ \$ACQUIRED_DEFAULT -eq 0 ]; then acquire_step acquire default; fi
BOX
        fi
        cat <<BOX
step validate python3 tools/proof_artifacts.py validate --profile default --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
# The ld host files in the image's order, before any image build: statically
# (a call before its definition, seconds), then through ACL2 in the certified
# world (tools/host_check.py's default).
step host-forward python3 tools/host_check.py --forward
# Check the requested image prefixes explicitly. host_check.py without a mode
# also demands the DTN prefix, whose certificates a default-only run does not
# acquire. The same translator underlies that aggregate check.
step host-ld env FN_ACL2="${IMAGE_ACL2:-\$ACL2}" python3 tools/host_translate_check.py --build host/native/build.lisp --log \$L/host-translate-default.log
BOX
        if [ $DTN -eq 1 ]; then
            # hbox-image-build.sh's dtn acquire/validate, before a DTN image.
            [ -n "$REUSE_TREE" ] || echo 'acquire_step acquire-dtn dtn'
            cat <<BOX
step validate-dtn python3 tools/proof_artifacts.py validate --profile dtn --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
step host-ld-dtn env FN_ACL2="${IMAGE_ACL2:-\$ACL2}" python3 tools/host_translate_check.py --build host/native/build-dtn.lisp --log \$L/host-translate-dtn.log
BOX
        fi
        # More than one image: build the foreign libraries once, then every
        # save at once (pstep/pwait); one image keeps the plain step.
        # grep -c prints 0 but exits 1; tolerate that under set -e.
        NIMG=$(echo "$IMAGES" | tr ',' '\n' | grep -vc '^prof$' || true)
        if [ "$NIMG" -gt 1 ] && [ "${FN_NATIVE_SERIAL_IMAGES:-}" != 1 ]; then
            ISTEP=pstep
            cat <<BOX
step image-libs sh -c 'sh tools/build_mldsa65.sh build/lib && sh tools/build_deflate.sh build/lib && sh tools/build_blake3.sh build/lib'
BOX
        else
            ISTEP=step
        fi
        for image in $(echo "$IMAGES" | tr ',' ' '); do
            # The (profile, session script, image) triple per image, as
            # tools/runbooks/hbox-image-build.sh's four build lines.
            if [ "$image" = prof ]; then
                # The profiling entry is loaded before build.lisp's
                # save-exec; the script owns the (developer, full) triple.
                cat <<BOX
step image-prof env FN_ACL2=${IMAGE_ACL2:-\$ACL2} $WRAP sh tools/profile/build_native_profile.sh build/fn-host-prof
BOX
                continue
            fi
            case $image in
                production) profile=production build=host/native/build.lisp out=build/fn-host world=stripped ;;
                developer) profile=developer build=host/native/build.lisp out=build/fn-host-developer world=full ;;
                reference) profile=production build=host/native/build.lisp out=build/fn-host-reference world=full ;;
                developer-stripped) profile=developer build=host/native/build.lisp out=build/fn-host-developer-stripped world=stripped ;;
                dtn) profile=production build=host/native/build-dtn.lisp out=build/fn-host-dtn world=stripped ;;
                dtn-developer) profile=developer build=host/native/build-dtn.lisp out=build/fn-host-dtn-developer world=full ;;
            esac
            cat <<BOX
$ISTEP image-$image env FN_ACL2=${IMAGE_ACL2:-\$ACL2} FN_NATIVE_PROFILE=$profile FN_NATIVE_WORLD=$world FN_NATIVE_BUILD=$build FN_NATIVE_IMAGE=$out FN_NATIVE_LOG=\$L/native-build-$image.log $WRAP sh tools/build_native_host.sh
BOX
        done
        [ "$ISTEP" != pstep ] || echo pwait
        # The build's own provenance stamp (TREE_SHA, MANIFEST.json in
        # build/): a composed fixture binds its launchers to it when the
        # run tests images it does not publish (CONVERGE-20261007-1 red #3).
        cat <<BOX
step stamp-images python3 tools/image_set.py stamp \$T
BOX
        if [ -n "$PUBLISH" ]; then
            cat <<BOX
step publish python3 tools/image_set.py publish \$T $SOURCE_ID --base ${IMAGES_BASE:-/tank/fn/images}
BOX
        fi
        if [ -n "$KEYED" ]; then
            # The set key was recorded before the build; a published set stays
            # as built (an existing one is left alone, a refusal is only said).
            cat <<BOX
echo "== publish-keyed \$(date -u +%H:%M:%SZ)"
python3 tools/image_key.py publish --store $KEYSTORE --tree \$T --record \$S/image-keys.json --source $REAL_SOURCE_ID 8>&- || echo "   publish-keyed: not published (exit \$?)"
fi
BOX
        fi
    fi
    if [ -n "$BUILD_ONLY" ]; then
        echo 'echo "== build only: no modules"'
        echo 'finish 0'
    fi
    if [ -n "$REUSE" ]; then
        cat <<BOX
echo "== images: reused from the earlier run $REUSE"
step image-reuse python3 \$S/bin/image_set.py link-run $REUSE \$T $(echo "$IMAGES" | tr ',' ' ')
BOX
    fi
    if [ -n "$IMAGE_SET" ]; then
        cat <<BOX
echo "== images: the published set $IMAGE_SET ($IMAGES_BASE/$IMAGE_SET)"
step image-set python3 \$S/bin/image_set.py link --base $IMAGES_BASE $IMAGE_SET \$T $(echo "$IMAGES" | tr ',' ' ')
BOX
        if [ -n "$OVERLAY" ]; then
            cat <<BOX
echo "== overlay: $SOURCE over the published set $IMAGE_SET (plan \$(sed -n 's/.*"digest": "\\(.\\{12\\}\\).*/\\1/p' \$S/overlay/plan.json))"
step overlay $WRAP python3 \$S/bin/native_overlay.py build \$S/overlay --image-set $IMAGES_BASE/$IMAGE_SET --tree \$T --images $IMAGES
BOX
        fi
    fi
    # The wire grammar in a run that built nothing here (--no-build,
    # --reuse-image, an image set): build/ outlives a re-ship, so it is made
    # again for this source, only from a certified books/wire-export the tree
    # kept; without one it is absent, and a module reading it is refused by
    # tools/box_artifacts.py rather than handed another revision's grammar.
    if [ $BUILD -ne 1 ]; then
        cat <<BOX
if [ -f tools/box_artifacts.py ]; then
    if [ -f books/wire-export.cert ]; then
        step box-wire $WRAP python3 tools/protocol_emit.py --wire --write
    else
        rm -f build/box/wire-grammar.json
        echo "== box: no certified books/wire-export in this tree; no build/box/wire-grammar.json"
    fi
fi
BOX
    fi
    # Every run stamps the artifact with its source (box_artifacts.load).
    cat <<BOX
if [ -f tools/box_artifacts.py ]; then
    step box-stamp python3 -c "import sys; sys.path.insert(0, 'tools'); import box_artifacts; from pathlib import Path; box_artifacts.write_stamp(Path('.'), '$SOURCE_ID', '$BOX', '$SOURCE_ID')"
fi
BOX
    # The production image's identity (tests/test_native_peering and
    # test_native_admin check the running process against it), computed by
    # tools/native_env.py identity from the image FN_NATIVE_HOST names by
    # --env, else build/fn-host, when the tree holds it; an --env below
    # still wins.
    identity_image=build/fn-host
    for assignment in $ENVS; do
        case $assignment in FN_NATIVE_HOST=*) identity_image=${assignment#FN_NATIVE_HOST=} ;; esac
    done
    cat <<BOX
if [ -x "$identity_image" ]; then
    eval "\$(python3 tools/native_env.py identity --image "$identity_image" --source $SOURCE_ID --export)"
fi
if [ -x build/fn-host-developer ]; then
    eval "\$(python3 tools/native_env.py identity --image build/fn-host-developer --prefix FN_NATIVE_DEVELOPER_ --export)"
fi
BOX
    for assignment in $ENVS; do
        echo "export $assignment"
    done
    echo "$PLAN" | while read -r module module_mem module_bigmem assignments; do
        [ -n "$module" ] || continue
        for assignment in $assignments; do
            case ${assignment#*=} in
                '$T/build/fn-host'*) echo "need $module ${assignment%%=*} ${assignment#*=}" ;;
            esac
        done
    done
    # A scope of 40G or more waits for every other such scope on the box
    # (one flock, held for the module).
    # The modules run from $S/module.sh, one process per module, --jobs at
    # a time (xargs -P; 1 keeps the old serial order).  Each writes its exit
    # code to $S/rc/test-MODULE and prints its verdict as one line when it
    # ends, so parallel modules never share a counter or split a block;
    # the tally below reads the codes in the order the modules were named.
    # Parallel modules are independent processes: each harness Node binds
    # its own ephemeral ports and makes its own temporary directories, and
    # each module keeps its own MemoryMax scope (N jobs can hold N x --mem).
    echo "export S T L FN_TEST_OPENSSL_BIN"
    echo "export FN_VERDICT_STORE=\${FN_VERDICT_STORE:-$BASE/.verdicts} FN_NATIVE_ALL=$ALL"
    echo "rm -rf \$S/rc; mkdir -p \$S/rc"
    cat <<'SCOPE'
cat > $S/scope.sh <<'SCOPERUN'
#!/bin/sh
set -eu
# Called after the bigmem flock is acquired, immediately before the unit starts.
printf '%s\n' "$FN_NATIVE_SCOPE_UNIT" >> "$S/scopes"
exec 8>&-
exec systemd-run --user --scope --unit="$FN_NATIVE_SCOPE_UNIT" "$@"
SCOPERUN
export FN_NATIVE_SCOPE_PREFIX
SCOPE
    echo "cat > \$S/module.sh <<'MODULE'"
    cat <<'MOD'
#!/bin/sh
set -u
cd "$T" || exit 0
# A test module runs to the end whatever the others did; its verdict goes in
# run.log: OK (N ran, K skipped), FAILED, or SKIPPED (N of N), with every
# skip's reason (a skipped witness is not evidence).  SKIPPED is status 4.
# The box's verdict store (tools/native_verdicts.py): a module whose stored
# verdict is for exactly these inputs is replayed (OK, SKIPPED) or re-run on
# its red cases only; FN_NATIVE_ALL=1 (--all) runs everything.  CASES is read
# by the module's command line.
CASES=
tcached() {
    name=$1; module=$2; shift 2
    CASES=
    [ "${FN_NATIVE_ALL:-0}" != 1 ] || return 1
    verdict=$(env "$@" python3 tools/native_verdicts.py lookup $module 2>/dev/null) || return 1
    case $verdict in
        *": OK ("*|*": SKIPPED ("*)
            echo "== $name $(date -u +%H:%M:%SZ) cached"
            echo "   $name cached: $verdict"
            case $verdict in *": SKIPPED ("*) echo 4 ;; *) echo 0 ;; esac > $S/rc/$name
            return 0 ;;
    esac
    reds=$(env "$@" python3 tools/native_verdicts.py lookup $module --red-cases 2>/dev/null | paste -sd, -)
    [ -n "$reds" ] || return 1
    CASES="--cases $reds"
    echo "   $name: re-running $(echo "$reds" | tr , '\n' | wc -l | tr -d ' ') red case(s) of the cached verdict; the rest carried: $verdict"
    return 1
}
tstep() {
    name=$1; shift
    echo "== $name $(date -u +%H:%M:%SZ) unit=$FN_NATIVE_SCOPE_UNIT MemoryMax=$FN_NATIVE_MEMORY load $(cut -d' ' -f1-3 /proc/loadavg)"
    # A failed test's processes' stderr lands in $L/stderr/$name (and its
    # digest in the module log after the failure): tools/test_budget.py.
    FN_NATIVE_STDERR_DIR=$L/stderr/$name FN_NATIVE_MODULE_LOG=$L/$name.log "$@" > $L/$name.log 2>&1
    rc=$?
    verdict=$(python3 tools/test_budget.py --verdict $L/$name.log)
    vrc=$?
    [ $rc -ne 0 ] || rc=$vrc
    case $verdict in *"FAILED (node dead)"*) rc=1 ;; esac
    echo "   $name exit $rc $(date -u +%H:%M:%SZ): $verdict ($L/$name.log)"
    if [ -d $L/stderr/$name ]; then
        echo "   $name: stderr of each failed test's processes in $L/stderr/$name ($(ls $L/stderr/$name | wc -l) files)"
    fi
    echo $rc > $S/rc/$name
}
case $1 in
MOD
    i=0
    echo "$PLAN" | while read -r module module_mem module_bigmem assignments; do
        [ -n "$module" ] || continue
        i=$((i+1))
        BIGMEM=
        [ "$module_bigmem" != 1 ] || BIGMEM="flock $BASE/.hbox-native-bigmem.lock"
        cat <<BOX
$i)
export FN_NATIVE_MEMORY=$module_mem
export FN_NATIVE_SCOPE_UNIT=\$FN_NATIVE_SCOPE_PREFIX-$i.scope
tcached test-$module $module $assignments ||
tstep test-$module $BIGMEM env $assignments sh \$S/scope.sh --quiet --slice=swarm.slice -p MemoryMax=$module_mem -p MemorySwapMax=0 -- sh -c "echo 0 > /proc/self/oom_score_adj 2>/dev/null; exec python3 tools/test_budget.py --one $module \$CASES"
;;
BOX
    done
    echo "esac"
    echo "exit 0"
    echo "MODULE"
    count=$(echo "$PLAN" | grep -c . || true)  # 0 modules (--build-only): grep exits 1
    echo "echo \"== modules: $count, $MODULE_JOBS at a time\""
    echo "step modules sh -c 'seq 1 $count | xargs -P $MODULE_JOBS -n 1 sh \$S/module.sh'"
    echo 'failed=0 passed=0 skipped=0 broke=0'
    echo "for name in $(echo "$PLAN" | while read -r module module_mem module_bigmem assignments; do printf 'test-%s ' "$module"; done); do"
    cat <<'BOX'
    rc=$(cat $S/rc/$name 2>/dev/null || echo 125)
    case $rc in 0) passed=$((passed+1)) ;; 4) skipped=$((skipped+1)) ;; *) broke=$((broke+1)) ;; esac
    [ $rc -eq 0 ] || [ $failed -ne 0 ] || failed=$rc
done
BOX
    echo 'echo "== modules: $passed OK, $skipped SKIPPED (no test executed), $broke FAILED"'
    echo "finish \$failed"
}

if [ $DRY -eq 1 ]; then
    box_script "$@"
    exit 0
fi

lock_label
record=$HERE/build/hbox-native/$LABEL.run
if [ -f "$record" ] && [ -z "$(sed -n 's/^pgid=//p' "$record")" ]; then
    echo "hbox_native: unresolved pending launch in $record; use adopt $LABEL before relaunching" >&2
    exit 2
fi
LAUNCH_ID=$(python3 -c 'import uuid; print(uuid.uuid4().hex)')
# A box reserved for a measurement (tools/boxes.sh reserve) waits here, printing
# who holds it and until when; the holder's own runs (this worktree) pass.
FN_BOX_AS=${FN_BOX_AS:-$(basename "$HERE")} sh "$FN_HBOX_NATIVE_COPY/boxes.sh" wait "$HOST" 7>&- || exit 3
# Refuse a live run before any remote mutation. Local exclusion serializes
# all launchers for this worktree/label across shipping and record publication.
ssh -n "$HOST" "if [ -f $S/run.lock ]; then if ! flock -n $S/run.lock true; then echo \"hbox_native: launch refused: run.lock held by live leader \$(cat $S/run.pid 2>/dev/null || echo unknown)\" >&2; exit 2; fi; fi" || exit 2
# --no-build requires this label's images before shipping; refuse naming
# the runs of NAME on the box that hold them (a
# worktree run's default label is a fresh wt-TIMESTAMP: pass --label).
if [ $BUILD -eq 0 ] && [ -z "$IMAGE_SET" ] && [ -z "$REUSE" ]; then
    NEEDED=
    for image in $(echo "$IMAGES" | tr ',' ' '); do
        needed=
        case $image in
            production) needed=build/fn-host ;;
            developer) needed=build/fn-host-developer ;;
            reference) needed=build/fn-host-reference ;;
            developer-stripped) needed=build/fn-host-developer-stripped ;;
            dtn) needed=build/fn-host-dtn ;;
            dtn-developer) needed=build/fn-host-dtn-developer ;;
        esac
        [ -z "$needed" ] || NEEDED="$NEEDED $needed"
    done
    if [ -n "$NEEDED" ]; then
        MISSING=$(ssh -n "$HOST" ": fn-no-build-images; if cd $S/tree 2>/dev/null; then for f in $NEEDED; do [ -x \$f ] || echo \$f; done; else echo $NEEDED; fi" | tr '\n' ' ' | sed 's/ *$//')
        if [ -n "$MISSING" ]; then
            RUNS=$(ssh -n "$HOST" ": fn-no-build-runs; cd $BASE/$NAME 2>/dev/null && for d in native-*; do ok=1; for f in $NEEDED; do [ -x \$d/tree/\$f ] || ok=0; done; [ \$ok = 1 ] && echo \${d#native-}; done" | tr '\n' ' ' | sed 's/ *$//')
            echo "hbox_native: --no-build reuses $HOST:$S/tree (--label $LABEL), which lacks: $MISSING" >&2
            if [ -n "$RUNS" ]; then
                echo "hbox_native: runs of $NAME on $HOST holding every image this run needs: $RUNS -- pass --label ONE (or --reuse-image $NAME/native-ONE)" >&2
            else
                echo "hbox_native: no run of $NAME on $HOST holds them: drop --no-build to build, or --image-set SHA / --reuse-image RUN" >&2
            fi
            exit 2
        fi
    fi
fi
# The local record names the images' identity source.  A reused run's is the
# one its run.log names (the box script reads it from build/REUSED_SOURCE,
# which link-run writes later), so read it here; train.py image compares it
# with HEAD.
RECORD_SOURCE=$SOURCE_ID
if [ -n "$REUSE" ]; then
    RECORD_SOURCE=$(ssh -n "$HOST" "grep '^== source ' $REUSE/run.log" \
        | sed -nE 's/^== source (commit|worktree) ([^ ]+) *$/\2/p' | head -n 1)
    [ -n "$RECORD_SOURCE" ] || { echo "hbox_native: --reuse-image $REUSE: its run.log names no \`== source\` line on $HOST; its images' source is unknown" >&2; exit 2; }
fi
# Persist a recoverable launch handle before the first shipping mutation.
printf 'box=%s\ndir=%s\nlaunch_id=%s\nlog=%s\nstatus=%s\nsource=%s\ntree=%s\n' "$HOST" "$S" "$LAUNCH_ID" "$S/run.log" "$S/status" "$RECORD_SOURCE" "$TREE_ID" > "$record.tmp"
mv "$record.tmp" "$record"
# --from-train: prove, on the box and just before the start, that the farm
# tree is this commit and holds the cache pair of every book of the image's
# roots (tools/native_reuse.py verify).  Reading only; a difference of any
# kind refuses (said, with the first differences) and the run ships its own
# tree and installs, certifies and acquires as before.
REUSE_LINKED=
if [ -n "$REUSE_TREE" ]; then
    EXPECT=$(mktemp "${TMPDIR:-/tmp}/hbox_native_expect.XXXXXX") || exit 3
    PROFILES="--profile default"
    [ $DTN -eq 0 ] || PROFILES="$PROFILES --profile dtn"
    if ! ssh -n "$HOST" "[ -d $REUSE_TREE/books ] && { [ ! -e $S/tree ] || [ -L $S/tree ]; }"; then
        reuse_refused "$HOST:$REUSE_TREE is not a tree, or $S/tree already exists as a directory (use another --label)"
    elif ! python3 "$FN_HBOX_NATIVE_COPY/native_reuse.py" expect --repo "$HERE" --rev "$FULL" --out "$EXPECT"; then
        reuse_refused "cannot list $FULL's tracked files"
    elif ! { ssh "$HOST" "mkdir -p $S/bin $S/logs && cat > $S/reuse-expect.json" < "$EXPECT" \
            && ssh "$HOST" "cat > $S/bin/native_reuse.py" < "$FN_HBOX_NATIVE_COPY/native_reuse.py"; }; then
        reuse_refused "cannot ship the check to $HOST"
    else
        VERDICT=$(ssh -n "$HOST" "cd $REUSE_TREE && python3 $S/bin/native_reuse.py verify --root $REUSE_TREE --expect $S/reuse-expect.json --cache $CACHE --acl2 $CERT_ACL2 $PROFILES" 2>&1) \
            && echo "$VERDICT" \
            || reuse_refused "$VERDICT"
    fi
    rm -f "$EXPECT"
    if [ -n "$REUSE_TREE" ]; then
        # One image run per train tree: two builds in its one build/ clobber
        # each other.  The claim stays while the run's images are there.
        if CLAIMED=$(ssh -n "$HOST" "python3 $S/bin/native_reuse.py claim --root $REUSE_TREE --owner $S" 2>&1); then
            echo "$CLAIMED"
            ssh -n "$HOST" "ln -sfn $REUSE_TREE $S/tree" || {
                ssh -n "$HOST" "rm -rf $REUSE_TREE/build/native-reuse.claim" || true  # no image is in the tree yet
                reuse_refused "cannot link $S/tree"; }
        else
            reuse_refused "${CLAIMED#native_reuse: }"
        fi
    fi
    [ -z "$REUSE_TREE" ] || REUSE_LINKED=1
fi
echo "hbox_native: $SOURCE -> $HOST:$S"
if [ -n "$REUSE_LINKED" ]; then
    echo "hbox_native: $SOURCE -> the train's tree $HOST:$REUSE_TREE (farm run $REUSE_RUN); nothing shipped"
else
ssh -n "$HOST" "mkdir -p $S/tree $S/logs" || { echo "hbox_native: cannot create $S on $HOST" >&2; exit 3; }
# --no-build preserves the certificates used by the images and REPL sessions.
# A build run re-installs them.
# Compress the complete immutable archive at level 1. Historical evidence is
# part of that tree too: compressing its transport retains every tracked path
# while avoiding repeated uncompressed transfers before the detached run starts.
KEEP=
[ $BUILD -eq 1 ] || KEEP="--exclude=*.cert --exclude=*.port --exclude=*.fasl"
if [ "$REV" = . ]; then
    # shellcheck disable=SC2086
    rsync -a --delete --exclude=build/ --exclude=.git/ --exclude=__pycache__/ \
        --exclude=.venv/ --exclude='*.pyc' --exclude=LANEDUMP.md $KEEP \
        "$HERE/" "$HOST:$S/tree/" || { echo "hbox_native: rsync failed" >&2; exit 3; }
elif [ $BUILD -eq 0 ]; then
    ssh -n "$HOST" "find $S/tree -mindepth 1 -path $S/tree/build -prune -o -type f ! -name '*.cert' ! -name '*.port' ! -name '*.fasl' -exec rm -f {} +" || exit 3
    git -C "$HERE" archive --format=tar.gz -1 "$FULL" | ssh "$HOST" "tar -xz -C $S/tree" \
        || { echo "hbox_native: shipping $FULL failed" >&2; exit 3; }
else
    ssh -n "$HOST" "find $S/tree -mindepth 1 -maxdepth 1 ! -name build -exec rm -rf {} +" || exit 3
    git -C "$HERE" archive --format=tar.gz -1 "$FULL" | ssh "$HOST" "tar -xz -C $S/tree" \
        || { echo "hbox_native: shipping $FULL failed" >&2; exit 3; }
fi
fi
box_script "$@" | ssh "$HOST" "cat > $S/run.sh" || exit 3
ssh "$HOST" "mkdir -p $S/bin && cat > $S/bin/native_certify_plan.py" < "$FN_HBOX_NATIVE_COPY/native_certify_plan.py" || exit 3
if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ]; then
    ssh "$HOST" "mkdir -p $S/bin && cat > $S/bin/image_set.py" < "$FN_HBOX_NATIVE_COPY/image_set.py" || exit 3
fi
if [ -n "$OVERLAY" ]; then
    ssh -n "$HOST" "rm -rf $S/overlay && mkdir -p $S/overlay" || exit 3
    tar -C "$OVERLAY_DIR" -cf - . | ssh "$HOST" "tar -xf - -C $S/overlay" || exit 3
    ssh "$HOST" "cat > $S/bin/native_overlay.py" < "$FN_HBOX_NATIVE_COPY/native_overlay.py" || exit 3
fi
ssh -n "$HOST" "rm -f $S/status $S/stopped $S/run.starttime; : > $S/scopes; nohup setsid env FN_NATIVE_LAUNCH_ID=$LAUNCH_ID sh -c 'echo \$\$ > $S/run.pid || exit 3; exec sh $S/run.sh' > $S/run.log 2>&1 < /dev/null &" || { echo "hbox_native: ambiguous launch at $HOST:$S; use status $LABEL --dir or adopt $LABEL" >&2; exit 3; }
readback_identity || exit $?
PID=$(sed -n 's/^pgid=//p' "$record")
echo "hbox_native: started; progress in $HOST:$S/run.log"
[ -z "$REUSE_LINKED" ] || ssh -n "$HOST" "python3 $S/bin/native_reuse.py claim --root $REUSE_TREE --owner $S --pid $PID" >/dev/null 2>&1 || true
if [ $DETACH -eq 1 ]; then
    echo "hbox_native: detached (pgid $PID on $HOST); re-attach with: tools/hbox_native.sh attach $LABEL   (status: tools/hbox_native.sh status $LABEL)"
    exit 0
fi
attach_run attach "$LABEL"
