#!/bin/sh
# witness: needs-image
# tools/deploy_fresh.sh against a THROWAWAY node, on the node's host (hbox).
# Nothing here reads or touches /tank/fn/node or fn-node.service: the "old
# node" is a fixture built from the release tarball under
# /tank/fn/scratch/deploy-fresh/, served on loopback by a scratch user unit.
#
#   sh tests/test_deploy_fresh.sh [TARBALL [REV40]]
#
# TARBALL's digest comes from TARBALL.sha256 or a SHA256SUMS beside it; a
# release-product tarball (top directory fn) names REV40 itself in
# libexec/fn/source-revision, so REV40 is needed only to override it.
#
# Run it under a memory cap, e.g.
#   systemd-run --user --scope -p MemoryMax=8G sh tests/test_deploy_fresh.sh 2>&1 | tee LOG
# Cases: the refusals (no mode, developer variables, a tank target, a bad
# digest) change nothing; --choose-disk never names tank; --dry-run changes
# nothing; the import deploy serves the old article; a second --go is a no-op;
# the rollback restores the old node; the fresh deploy starts empty; its
# rollback restores again.  Exit 0 only when every case held.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
D=$root/tools/deploy_fresh.sh
PROBE=$root/tools/node_probe.py
TARBALL=${1:-/tank/fn/scratch/qual-69046a76/friends/release/fn-69046a76798b-linux-x86_64.tar.gz}
if [ -f "$TARBALL.sha256" ]; then TAR_SHA=$(cut -d' ' -f1 "$TARBALL.sha256")
else TAR_SHA=$(awk -v f="$(basename "$TARBALL")" '$2 == f || $2 == "*" f { print $1 }' "$(dirname "$TARBALL")/SHA256SUMS")
fi
[ -n "$TAR_SHA" ] || { echo "no digest for $TARBALL"; exit 2; }
REV=${2:-$(tar -xzOf "$TARBALL" fn/libexec/fn/source-revision 2>/dev/null || echo 69046a76798b8be6169eeed5a66cc46fbe399e51)}
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
RUN=/tank/fn/scratch/deploy-fresh/t-$STAMP
BASE=$RUN/tank-fn
OLD=$BASE/node
UNIT=deploy-fresh-t$STAMP.service
UNIT_FILE=${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user/$UNIT
case $OLD in /tank/fn/scratch/deploy-fresh/*) ;; *) echo "bad fixture path $OLD"; exit 2 ;; esac
mkdir -p "$OLD/log" "$OLD/tls"
fails=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fails=$((fails+1)); }
check() { label=$1; shift; if "$@"; then ok "$label"; else bad "$label"; fi; }
cleanup() {
  systemctl --user stop "$UNIT" 2>/dev/null || true
  rm -f "$UNIT_FILE"; systemctl --user daemon-reload || true
  echo "run dir kept: $RUN"
}
trap cleanup EXIT

# ---- the fixture: an old node on loopback, a login, one article -----------
PORT=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
mkdir "$RUN/unpack"; tar -xzf "$TARBALL" -C "$RUN/unpack"
mv "$RUN/unpack/$(ls "$RUN/unpack")" "$OLD/fn-old"; rmdir "$RUN/unpack"
OFN=$OLD/fn-old/bin/fn
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 \
  -subj /CN=deploy-fresh.invalid -addext subjectAltName=IP:127.0.0.1 \
  -keyout "$OLD/tls/key.pem" -out "$OLD/tls/cert.pem" 2>/dev/null
chmod 600 "$OLD/tls/key.pem"
cat >"$OLD/fn.toml" <<EOF
[store]
path = "$OLD/store"

[listener]
host = "127.0.0.1"
port = $PORT
tls_cert = "$OLD/tls/cert.pem"
tls_key = "$OLD/tls/key.pem"

[auth]
required = true
protected_only = true
path = "$OLD/store/auth.toml"

[posting]
enabled = true

[control]
path = "$OLD/store/control.sock"

[log]
path = "$OLD/log/fn.log"
EOF
PW=$(openssl rand -hex 16)
printf 'tester %s\n' "$PW" >"$OLD/credentials.txt"; chmod 600 "$OLD/credentials.txt"
# The small preset's fields (docs/operator-internals.md, "The process heap"): with no
# profile flag, init writes the D27 default on a machine of 4 GiB or more (this
# scope's memory.max included), which a release's bin/fn refuses (PKT-582).
SMALL="--max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-article-octets 32768 --max-groups-per-article 16 --max-open-suffix 128"
env ACL2_CUSTOMIZATION=NONE "$OFN" operator "$OLD/fn.toml" init $SMALL fn.test
printf '%s\n%s\n' "$PW" "$PW" | env ACL2_CUSTOMIZATION=NONE setsid "$OFN" operator "$OLD/fn.toml" principal set-password tester --posting
mkdir -p "$(dirname "$UNIT_FILE")"
cat >"$UNIT_FILE" <<EOF
[Unit]
Description=deploy-fresh test fixture (old node)

[Service]
Type=simple
Environment=ACL2_CUSTOMIZATION=NONE
Environment=FN_DEPLOY_FRESH_TEST_MARK=dropped-by-the-rewrite
ExecStart=$OFN operator $OLD/fn.toml run
Restart=on-failure
KillSignal=SIGTERM
TimeoutStopSec=120
EOF
systemctl --user daemon-reload
systemctl --user start "$UNIT"
i=0; until ss -Hltn "sport = :$PORT" | grep -q . || [ $i -ge 60 ]; do sleep 1; i=$((i+1)); done
probe() { # NODE_DIR JSON
  FN_PROBE_USER=tester FN_PROBE_PASSWORD=$PW python3 "$PROBE" 127.0.0.1 "$PORT" \
    --cafile "$1/tls/cert.pem" --group fn.test --json "$2" >/dev/null 2>&1
}
check "fixture: the old node serves and takes a post" probe "$OLD" "$RUN/fixture-probe.json"
active() { [ "$(systemctl --user is-active "$UNIT")" = active ]; }
execstart() { sed -n 's/^ExecStart=//p' "$UNIT_FILE"; }
untouched() { [ -f "$OLD/fn.toml" ] && active && [ "$(execstart)" = "$OFN operator $OLD/fn.toml run" ]; }

COMMON="--old-node $OLD --unit $UNIT --tarball $TARBALL --sha256 $TAR_SHA --expect-rev $REV --groups fn.test --probe-group fn.test --scratch"
NEW1=$RUN/new-import
NEW2=$RUN/new-fresh
# shellcheck disable=SC2086
dfr() { sh "$D" "$@"; }

# ---- refusals change nothing -----------------------------------------------
refuses() { # PATTERN CMD...
  pat=$1; shift
  set +e; "$@" >"$RUN/refusal.out" 2>&1; rc=$?; set -e
  [ $rc -eq 2 ] && grep -q "$pat" "$RUN/refusal.out" && untouched && [ ! -e "$NEW1" ]
}
check "refuses without --go or --dry-run" refuses 'go or --dry-run is required' dfr $COMMON "$NEW1"
check "refuses FN_NATIVE_HOST in its environment" refuses 'FN_NATIVE_HOST' env FN_NATIVE_HOST=/x sh "$D" --go $COMMON "$NEW1"
check "refuses FN_TEST_* in its environment" refuses 'FN_TEST_X' env FN_TEST_X=1 sh "$D" --go $COMMON "$NEW1"
check "refuses a tank target without --scratch" refuses 'never tank' dfr --go --old-node "$OLD" --unit "$UNIT" --tarball "$TARBALL" --sha256 "$TAR_SHA" "$NEW1"
check "refuses a scratch flag outside /tank/fn/scratch" refuses 'never tank' dfr --go --old-node "$OLD" --unit "$UNIT" --tarball "$TARBALL" --sha256 "$TAR_SHA" --scratch /tank/fn/deploy-fresh-never
check "refuses a wrong tarball digest before touching anything" refuses 'tarball sha256' dfr --go --old-node "$OLD" --unit "$UNIT" --tarball "$TARBALL" --sha256 0000 --scratch "$NEW1"
# S140: no default release; a deploy that names none is refused before the stop.
check "refuses a deploy that names no tarball" refuses 'tarball PATH and --sha256 HEX are required' dfr --go --old-node "$OLD" --unit "$UNIT" --scratch "$NEW1"
check "refuses a deploy that names no revision" refuses 'expect-rev REV40 is required' dfr --go --old-node "$OLD" --unit "$UNIT" --tarball "$TARBALL" --sha256 "$TAR_SHA" --scratch "$NEW1"
check "refuses a rollback of a directory it never retired" refuses 'not a node this script retired' dfr --go $COMMON --rollback "$OLD"

# ---- the disk choice -------------------------------------------------------
disk=$(sh "$D" --choose-disk 2>"$RUN/choose.err")
echo "     choose-disk: $disk ($(cat "$RUN/choose.err"))"
case $disk in /tank*|"") bad "--choose-disk names $disk" ;; *) ok "--choose-disk names a non-tank directory" ;; esac
[ -e "$disk" ] && echo "     (it exists already; choose-disk created nothing)" || ok "--choose-disk created nothing"

# ---- dry run ----------------------------------------------------------------
set +e; dfr --dry-run $COMMON --store import "$NEW1" >"$RUN/dry.out" 2>&1; rc=$?; set -e
check "--dry-run exits 0" [ $rc -eq 0 ]
check "--dry-run prints the retire, install, store and unit steps" \
  sh -c "grep -q 'would: mv -T $OLD $OLD-retired-' '$RUN/dry.out' && grep -q 'would: cp -a' '$RUN/dry.out' && grep -q 'would: rewrite' '$RUN/dry.out' && grep -q 'would: systemctl --user start $UNIT' '$RUN/dry.out'"
check "--dry-run changed nothing" sh -c "[ ! -e '$NEW1' ] && [ -z \"\$(ls -d '$OLD'-retired-* 2>/dev/null)\" ]"
untouched && ok "--dry-run left the old unit running" || bad "--dry-run left the old unit running"

# ---- import deploy ------------------------------------------------------------
set +e; dfr --go $COMMON --store import "$NEW1" >"$RUN/import.out" 2>&1; rc=$?; set -e
cat "$RUN/import.out" | sed 's/^/     | /'
check "import deploy exits 0" [ $rc -eq 0 ]
R1=$(ls -d "$OLD"-retired-* 2>/dev/null | head -1)
check "the old node was renamed, not deleted" sh -c "[ ! -e '$OLD' ] && [ -f '$R1/fn.toml' ] && [ -d '$R1/store' ] && [ -x '$R1/fn-old/bin/fn' ]"
check "the manifest and sums were written" sh -c "grep -q '^new_node=$NEW1\$' '$R1/DEPLOY-MANIFEST' && (cd '$R1' && sha256sum -c --quiet DEPLOY-SHA256SUMS)"
check "the imported store's config equals the retired one" cmp -s "$R1/store/config.json" "$NEW1/store/config.json"
check "the unit runs the release in the new node" sh -c "[ \"\$(sed -n 's/^ExecStart=//p' '$UNIT_FILE')\" = '$NEW1/fn-$(printf %s "$REV" | cut -c1-12)/bin/fn operator $NEW1/fn.toml run' ]"
check "the rewritten unit dropped every Environment=FN_ line" sh -c "! grep -q '^Environment=FN_' '$UNIT_FILE'"
check "the unit is active" active
check "fn.toml names no retired path" sh -c "! grep -q '${OLD}[\"/]' '$NEW1/fn.toml' && ! grep -q retired '$NEW1/fn.toml'"
check "--version printed the release" grep -Eq "fn ($REV|6\.7\.(0|[1-9][0-9]*) \($(printf %s "$REV" | cut -c1-12)\))" "$RUN/import.out"
check "health 0 and the probe held" sh -c "grep -q 'health rc=0' '$RUN/import.out' && grep -q 'probe tester@127.0.0.1:$PORT group fn.test rc=0' '$RUN/import.out'"
check "the imported article is there (GROUP 211 1 before the probe's post)" grep -q '211 1 1 1 fn.test' "$RUN/import.out"

# ---- a second --go is a no-op ---------------------------------------------------
m1=$(stat -c %Y "$NEW1/fn.toml" 2>/dev/null || echo absent)
set +e; dfr --go $COMMON --store import "$NEW1" >"$RUN/import-again.out" 2>&1; rc=$?; set -e
check "a second --go exits 0" [ $rc -eq 0 ]
check "a second --go skipped every step" sh -c "grep -q 'resuming' '$RUN/import-again.out' && grep -q 'skip: .*present' '$RUN/import-again.out' && grep -q 'skip: already points' '$RUN/import-again.out' && [ $m1 = \$(stat -c %Y '$NEW1/fn.toml') ] && [ \$(ls -d '$OLD'-retired-* | wc -l) = 1 ]"

# ---- S064: a store without its record is an interrupted run's, never done ----------
mv "$NEW1/DEPLOY-STORE" "$RUN/DEPLOY-STORE.kept"
set +e; dfr --go $COMMON --store import "$NEW1" >"$RUN/interrupted.out" 2>&1; rc=$?; set -e
check "a store without DEPLOY-STORE is refused, not skipped" sh -c "[ $rc -eq 2 ] && grep -q 'present without $NEW1/DEPLOY-STORE' '$RUN/interrupted.out' && ! grep -q 'DEPLOY DONE' '$RUN/interrupted.out' && [ -d '$NEW1/store' ]"
mv "$RUN/DEPLOY-STORE.kept" "$NEW1/DEPLOY-STORE"
set +e; dfr --go $COMMON --store import "$NEW1" >"$RUN/import-third.out" 2>&1; rc=$?; set -e
check "with its record back, --go completes again" sh -c "[ $rc -eq 0 ] && grep -q 'present and complete' '$RUN/import-third.out'"
check "with its record back, the unit is active" active

# ---- rollback ---------------------------------------------------------------------
set +e; dfr --go $COMMON --rollback "$R1" >"$RUN/rollback1.out" 2>&1; rc=$?; set -e
sed 's/^/     | /' "$RUN/rollback1.out"
check "rollback exits 0" [ $rc -eq 0 ]
check "rollback restored the old node and its unit" sh -c "[ -f '$OLD/fn.toml' ] && [ ! -e '$R1' ] && [ \"\$(sed -n 's/^ExecStart=//p' '$UNIT_FILE')\" = '$OFN operator $OLD/fn.toml run' ]"
check "rollback retired the new node beside itself" sh -c "[ ! -e '$NEW1' ] && ls -d '$NEW1'-retired-*/store >/dev/null && ls '$NEW1'-retired-*/ROLLBACK-MANIFEST >/dev/null"
check "rollback kept the replaced unit file with the retired node, nothing in the unit directory" sh -c "ls '$NEW1'-retired-*/ROLLBACK-replaced-$UNIT >/dev/null && [ -z \"\$(ls '$(dirname "$UNIT_FILE")' | grep -F '$UNIT.')\" ]"
check "rollback: the old unit is active and probed" sh -c "systemctl --user is-active '$UNIT' | grep -qx active && grep -q 'probe tester.* rc=0' '$RUN/rollback1.out'"

# ---- fresh deploy and its rollback ------------------------------------------------
sleep 1
set +e; dfr --go $COMMON --init-args "$SMALL" --store fresh "$NEW2" >"$RUN/fresh.out" 2>&1; rc=$?; set -e
sed 's/^/     | /' "$RUN/fresh.out"
check "fresh deploy exits 0" [ $rc -eq 0 ]
check "fresh: a new store, the login enrolled, health 0, probe held" sh -c "grep -q 'enrolled tester' '$RUN/fresh.out' && grep -q 'health rc=0' '$RUN/fresh.out' && grep -q 'probe tester.* rc=0' '$RUN/fresh.out'"
check "fresh: the store step's record names every login" grep -q '^store=fresh logins=1 ' "$NEW2/DEPLOY-STORE"
check "fresh: the store starts empty (GROUP 211 0 before the probe's post)" grep -q '211 0 ' "$RUN/fresh.out"
check "fresh: the credentials file is not in argv or the log" sh -c "! grep -q '$PW' '$RUN/fresh.out' && ! grep -rq '$PW' '$BASE/deploy-fresh-logs'"
R2=$(ls -d "$OLD"-retired-* 2>/dev/null | head -1)
set +e; dfr --go $COMMON --rollback "$R2" >"$RUN/rollback2.out" 2>&1; rc=$?; set -e
sed 's/^/     | /' "$RUN/rollback2.out"
check "second rollback exits 0 and the old node serves" sh -c "[ $rc -eq 0 ] && [ -f '$OLD/fn.toml' ] && grep -q 'probe tester.* rc=0' '$RUN/rollback2.out'"
check "nothing was deleted: both retired new nodes remain" sh -c "ls -d '$NEW1'-retired-* '$NEW2'-retired-* >/dev/null"

echo "== deploy-fresh test: $fails failed; logs $BASE/deploy-fresh-logs; run $RUN"
( cd "$RUN" && sha256sum import.out import-again.out rollback1.out fresh.out rollback2.out dry.out ) || true
[ $fails -eq 0 ]
