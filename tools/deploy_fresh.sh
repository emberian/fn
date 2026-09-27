#!/bin/sh
# deploy_fresh.sh: D34's deploy, a fresh install from a release tarball, never
# an upgrade in place; its rollback is the same script pointed at the retired
# node.  Run ON THE NODE'S HOST, as the node's user (hbox: user hbox).
#
#   deploy_fresh.sh --go|--dry-run [OPTIONS] TARGET
#   deploy_fresh.sh --go|--dry-run [OPTIONS] --rollback RETIRED
#   deploy_fresh.sh --choose-disk
#
# TARGET is the new node directory (it must not hold a node yet), or `auto`:
# the disk PKT-579 chose (planning/evidence/node-disk-2026-09-26.md): rpool
# when it has at least 50 GiB free AND is imported at boot (a cachefile) AND a
# dataset rpool/fn-public is mounted, else a new directory on the NVMe ext4
# root (/srv/fn-public when the user may create it, else $HOME/fn-public, the
# same file system).  Never tank: a TARGET on a tank dataset is refused unless
# --scratch is given and TARGET is under /tank/fn/scratch/ (the tests).
#
# Steps, each logged, each skipped when its postcondition already holds:
#  0. refuse: no --go/--dry-run; any FN_NATIVE_*, FN_RUN_*, FN_TEST_* in this
#     environment or in the user systemd manager's; a bad tarball digest.
#  1. stop the unit and record its status.
#  2. RETIRE the old node (its prefixes, store, tls, fn.toml, credentials):
#     one rename, OLD -> OLD-retired-STAMP, on the same file system, with
#     DEPLOY-MANIFEST (what was moved, where the new node goes, the unit file
#     copy) and SHA256SUMS of fn.toml, store/config.json and the frontier
#     (allocation-frontier.json, committed-history.json).  Nothing is deleted.
#  3. install the tarball (digest verified first, then its SHA256SUMS) into
#     TARGET/fn-REV12, from either layout: top fn-REV12 (the friends release)
#     or top fn (D35's release product, whose libexec/fn/source-revision must
#     be the expected revision); `bin/fn --version` must print it too
#     (`fn 6.7.N (REV12)` from a versioned release, `fn REV` before VERSION).
#  4. the store: `--store fresh` (default) inits TARGET/store and enrols the
#     retired credentials.txt logins (the password fed on stdin, never argv);
#     `--store import` is `cp -a` of the STOPPED retired store (the release
#     has no store import verb), control.sock* dropped, and `store STORE
#     node-secret create` when it has no keys/node-secret.key (SEC-006).
#  5. TLS: `--cert-dir DIR` with fullchain.pem and privkey.pem (a Let's
#     Encrypt layout, certbot or lego) when given; else the retired node's
#     LAN pair, copied, never regenerated.  The key must match the certificate.
#  6. TARGET/fn.toml is the retired one with OLD replaced by TARGET; the unit
#     file is the retired one with Description and ExecStart rewritten and
#     every Environment=FN_* line dropped; the retired copy is kept.
#  7. start; wait for the listener; `health` (0 required; 20 `starting` is
#     retried); the authenticated probe (node_probe.py beside this script)
#     with the first credentials.txt login; the greeting is logged.
# ROLLBACK (--rollback RETIRED): stop; retire the node the unit runs now
# (NEW -> NEW-retired-STAMP, same file system); rename RETIRED back to the
# path its manifest names; restore the kept unit file; start; health; probe.
set -eu

ME=$(basename "$0")
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
MODE=
TARGET=
ROLLBACK=
OLD_NODE=/tank/fn/node
TARBALL=/tank/fn/scratch/qual-69046a76/friends/release/fn-69046a76798b-linux-x86_64.tar.gz
TAR_SHA=1a2a61e997c086c333760cf27b2e3b1eaf0fa0101aa54dda95abbc3b9e174003
EXPECT_REV=69046a76798b8be6169eeed5a66cc46fbe399e51
UNIT=fn-node.service
UNIT_DIR=${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user
STORE=fresh
NODE_GROUPS="fn.agents fn.test"
INIT_ARGS=
CERT_DIR=
PROBE_HOST=
PROBE_GROUP=
PROBE=$HERE/node_probe.py
LOG_DIR=
SCRATCH=no
WAIT=90

usage() {
  sed -n '4,8p' "$0" | sed 's/^# \{0,1\}//' >&2
  cat >&2 <<EOF
options: --old-node DIR ($OLD_NODE)  --tarball PATH  --sha256 HEX  --expect-rev REV40
         --unit NAME ($UNIT)  --unit-dir DIR  --store fresh|import (fresh)
         --groups "G ..." ("$NODE_GROUPS")  --init-args "ARGS"  --cert-dir DIR
         --probe-host NAME (the listener host; the certificate's name for a
         Let's Encrypt pair)  --probe-group G  --log-dir DIR  --wait S  --scratch
EOF
  exit 2
}
die() { echo "$ME: REFUSED: $*" >&2; [ -n "${LOG:-}" ] && echo "REFUSED: $*" >>"$LOG"; exit 2; }

while [ $# -gt 0 ]; do
  case $1 in
    --go) MODE=go ;;
    --dry-run) MODE=dry ;;
    --choose-disk) MODE=choose ;;
    --rollback) ROLLBACK=${2:?}; shift ;;
    --old-node) OLD_NODE=${2:?}; shift ;;
    --tarball) TARBALL=${2:?}; shift ;;
    --sha256) TAR_SHA=${2:?}; shift ;;
    --expect-rev) EXPECT_REV=${2:?}; shift ;;
    --unit) UNIT=${2:?}; shift ;;
    --unit-dir) UNIT_DIR=${2:?}; shift ;;
    --store) STORE=${2:?}; shift ;;
    --groups) NODE_GROUPS=${2:?}; shift ;;
    --init-args) INIT_ARGS=${2:?}; shift ;;
    --cert-dir) CERT_DIR=${2:?}; shift ;;
    --probe-host) PROBE_HOST=${2:?}; shift ;;
    --probe-group) PROBE_GROUP=${2:?}; shift ;;
    --log-dir) LOG_DIR=${2:?}; shift ;;
    --wait) WAIT=${2:?}; shift ;;
    --scratch) SCRATCH=yes ;;
    -h|--help) usage ;;
    -*) echo "$ME: unknown option $1" >&2; usage ;;
    *) [ -z "$TARGET" ] || usage; TARGET=$1 ;;
  esac
  shift
done

# ---- the disk (PKT-579) --------------------------------------------------
GIB50=53687091200
choose_disk() {
  why=
  if command -v zfs >/dev/null 2>&1 && avail=$(zfs list -H -p -o avail rpool 2>/dev/null); then
    cache=$(zpool get -H -o value cachefile rpool 2>/dev/null || echo none)
    mp=$(zfs list -H -o mountpoint rpool/fn-public 2>/dev/null || echo absent)
    if [ "$avail" -ge "$GIB50" ] && [ "$cache" != none ] && [ -d "$mp" ] && [ -w "$mp" ]; then
      echo "disk: rpool (avail $avail octets, cachefile $cache, rpool/fn-public at $mp)" >&2
      echo "$mp/node"; return
    fi
    why="rpool avail=$avail cachefile=$cache rpool/fn-public=$mp"
  else
    why="rpool absent"
  fi
  if [ -d /srv/fn-public ] && [ -w /srv/fn-public ]; then d=/srv/fn-public/node
  elif [ -w /srv ]; then d=/srv/fn-public/node
  else d=$HOME/fn-public/node; fi
  echo "disk: the NVMe ext4 root, $d ($why: not boot-imported, under 50 GiB, or no dataset)" >&2
  echo "$d"
}
fs_of() { # the device or dataset and type holding PATH's nearest existing ancestor
  p=$1; while [ ! -e "$p" ]; do p=$(dirname "$p"); done
  df --output=source,fstype "$p" | tail -1
}
check_disk() {
  set -- $(fs_of "$1")
  case $1 in
    tank|tank/*)
      if [ "$SCRATCH" = yes ]; then
        case $TARGET in /tank/fn/scratch/*) say "  disk: $1 ($2), scratch target (tests)"; return ;; esac
      fi
      die "TARGET $TARGET is on $1 ($2): never tank (PKT-579; --scratch admits /tank/fn/scratch/ only)" ;;
  esac
  say "  disk: $1 ($2)"
}

if [ "$MODE" = choose ]; then choose_disk; exit 0; fi
[ -n "$MODE" ] || { echo "$ME: REFUSED: --go or --dry-run is required" >&2; usage; }
[ -n "$TARGET" ] || [ -n "$ROLLBACK" ] || { echo "$ME: REFUSED: a TARGET (or --rollback RETIRED) is required" >&2; usage; }
[ -z "$TARGET" ] || [ -z "$ROLLBACK" ] || die "TARGET and --rollback exclude each other"
case $STORE in fresh|import) ;; *) die "--store is fresh or import" ;; esac

# ---- step 0: the environment ----------------------------------------------
bad=$(env | sed -n 's/^\(FN_NATIVE_[A-Za-z0-9_]*\|FN_RUN_[A-Za-z0-9_]*\|FN_TEST_[A-Za-z0-9_]*\)=.*/\1/p' | tr '\n' ' ')
[ -z "$bad" ] || die "developer variables set in this environment: $bad"
if [ "$MODE" = go ]; then
  mbad=$(systemctl --user show-environment 2>/dev/null | sed -n 's/^\(FN_[A-Za-z0-9_]*\)=.*/\1/p' | tr '\n' ' ')
  [ -z "$mbad" ] || die "the user systemd manager carries $mbad (systemctl --user unset-environment them)"
fi

STAMP=$(date -u +%Y%m%dT%H%M%SZ)
if [ -z "$LOG_DIR" ]; then LOG_DIR=$(dirname "$OLD_NODE")/deploy-fresh-logs; fi
if [ "$MODE" = go ]; then
  mkdir -p "$LOG_DIR"; LOG=$LOG_DIR/$STAMP.log
else LOG=/dev/null; fi
say() { echo "$*"; echo "$*" >>"$LOG"; }
step() { say ""; say "== $*"; }
# In --dry-run every mutating command is printed, not run.
run() {
  if [ "$MODE" = dry ]; then echo "  would: $*"; return 0; fi
  echo "  + $*" >>"$LOG"; "$@" >>"$LOG" 2>&1
}
clean_env() { env -u LD_LIBRARY_PATH -u SBCL_HOME ACL2_CUSTOMIZATION=NONE "$@"; }
say "$ME $MODE at $STAMP; log $LOG"
say "argv: target=${TARGET:-} rollback=${ROLLBACK:-} old-node=$OLD_NODE unit=$UNIT store=$STORE cert-dir=${CERT_DIR:-none}"

UNIT_FILE=$UNIT_DIR/$UNIT
sc() { systemctl --user "$@"; }

stop_unit() {
  step "stop $UNIT"
  st=$(sc is-active "$UNIT" 2>/dev/null || true)
  say "  status before: ${st:-unknown}"
  if [ "$MODE" = go ]; then sc status "$UNIT" --no-pager -n 5 >>"$LOG" 2>&1 || true; fi
  case $st in
    active|activating|reloading) run systemctl --user stop "$UNIT" ;;
    *) say "  skip: not active" ;;
  esac
  if [ "$MODE" = go ]; then say "  status after: $(sc is-active "$UNIT" 2>/dev/null || true)"; fi
}

# retire DIR KIND: rename DIR to DIR-retired-STAMP on its own file system.
retire() {
  src=$1; dst=$src-retired-$STAMP
  [ -e "$dst" ] && die "$dst exists"
  run mv -T "$src" "$dst"
  RETIRED=$dst
}
sums_of() { # DIR: SHA256SUMS of fn.toml, the config and the frontier
  ( cd "$1" && for f in fn.toml store/config.json store/allocation-frontier.json store/committed-history.json credentials.txt; do
      [ -f "$f" ] && sha256sum "$f"; done ) || true
}

wait_listen() { # HOST PORT
  i=0
  while [ $i -lt "$WAIT" ]; do
    if ss -Hltn "sport = :$2" 2>/dev/null | grep -q .; then say "  listening on $1:$2 after ${i} s"; return 0; fi
    sleep 1; i=$((i+1))
  done
  say "  NOT listening on $1:$2 after $WAIT s"; return 1
}
toml_get() { # FILE SECTION KEY
  awk -v s="[$2]" -v k="$3" '
    /^\[/ { in_s = ($0 == s) }
    in_s && $1 == k { sub(/^[^=]*=[ \t]*/, ""); gsub(/"/, ""); print; exit }' "$1"
}

verify_up() { # NODE FN
  node=$1; fnb=$2; conf=$node/fn.toml
  step "start $UNIT"
  run systemctl --user daemon-reload
  run systemctl --user start "$UNIT"
  [ "$MODE" = dry ] && { echo "  would: wait for [listener] of $conf, $fnb operator $conf health (0), $PROBE"; return 0; }
  host=$(toml_get "$conf" listener host); port=$(toml_get "$conf" listener port)
  say "  active: $(sc is-active "$UNIT" 2>/dev/null || true)"
  wait_listen "$host" "$port" || { sc status "$UNIT" --no-pager -n 20 >>"$LOG" 2>&1 || true; die "the listener did not come up"; }
  step "health"
  i=0
  while :; do
    set +e; clean_env "$fnb" operator "$conf" health >"$LOG_DIR/$STAMP.health" 2>&1; hrc=$?; set -e
    cat "$LOG_DIR/$STAMP.health" >>"$LOG"
    [ $hrc -eq 20 ] && [ $i -lt 10 ] && { i=$((i+1)); sleep 2; continue; }
    break
  done
  say "  health rc=$hrc: $(head -1 "$LOG_DIR/$STAMP.health")"
  [ $hrc -eq 0 ] || die "health exit $hrc (0 required): $(head -1 "$LOG_DIR/$STAMP.health")"
  step "authenticated probe"
  cred=$node/credentials.txt
  [ -f "$cred" ] || die "no $cred: no login to probe with"
  user=$(awk 'NF>=2 {print $1; exit}' "$cred")
  ph=${PROBE_HOST:-$host}
  grp=${PROBE_GROUP:-${NODE_GROUPS%% *}}
  [ -f "$PROBE" ] || die "no probe at $PROBE"
  set +e
  FN_PROBE_USER=$user FN_PROBE_PASSWORD=$(awk -v u="$user" '$1==u {print $2; exit}' "$cred") \
    python3 "$PROBE" "$ph" "$port" --cafile "$node/tls/cert.pem" --group "$grp" \
      --json "$LOG_DIR/$STAMP.probe.json" >>"$LOG" 2>&1
  prc=$?; set -e
  say "  probe $user@$ph:$port group $grp rc=$prc json $LOG_DIR/$STAMP.probe.json"
  say "  greeting: $(python3 -c 'import json,sys; s=json.load(open(sys.argv[1]))["steps"]; o=s[0]["observed"]; print((" ".join(o) if isinstance(o, list) else str(o))[:160])' "$LOG_DIR/$STAMP.probe.json" 2>/dev/null || echo '?')"
  say "  group: $(python3 -c 'import json,sys; s=json.load(open(sys.argv[1]))["steps"]; print(" | ".join(str(x["observed"])[:80] for x in s if "GROUP" in x["step"] or "211" in str(x["observed"])))' "$LOG_DIR/$STAMP.probe.json" 2>/dev/null || echo '?')"
  [ $prc -eq 0 ] || die "probe exit $prc (0 required)"
  say "  sha256 $(sha256sum "$LOG_DIR/$STAMP.probe.json")"
}

# ---- rollback --------------------------------------------------------------
if [ -n "$ROLLBACK" ]; then
  M=$ROLLBACK/DEPLOY-MANIFEST
  [ -f "$M" ] || die "no $M: not a node this script retired"
  orig=$(sed -n 's/^original=//p' "$M"); newn=$(sed -n 's/^new_node=//p' "$M")
  munit=$(sed -n 's/^unit=//p' "$M")
  [ "$munit" = "$UNIT" ] || die "the manifest names unit $munit, this run $UNIT"
  say "rollback: $ROLLBACK -> $orig; the node now at $newn is retired beside itself"
  [ -e "$orig" ] && die "$orig exists: nothing to roll back into (retire it first)"
  stop_unit
  RETIRED=
  step "retire the current node $newn"
  if [ -d "$newn" ]; then
    retire "$newn"
    [ "$MODE" = go ] && printf 'original=%s\nretired_at=%s\nreason=rollback to %s\nunit=%s\n' "$newn" "$STAMP" "$ROLLBACK" "$UNIT" >"$RETIRED/ROLLBACK-MANIFEST"
    say "  retired to $RETIRED"
  else say "  skip: $newn absent"; fi
  step "restore $ROLLBACK -> $orig"
  run mv -T "$ROLLBACK" "$orig"
  step "restore the unit file"
  if [ "$MODE" = go ]; then
    # the unit file being replaced is kept with the node it ran
    if [ -n "${RETIRED:-}" ] && [ -f "$UNIT_FILE" ]; then cp -p "$UNIT_FILE" "$RETIRED/ROLLBACK-replaced-$UNIT"; fi
    cp -p "$orig/DEPLOY-unit/$UNIT" "$UNIT_FILE"
    grep -E '^(Description|ExecStart)=' "$UNIT_FILE" | sed 's/^/  /' | tee -a "$LOG"
  else echo "  would: cp -p $orig/DEPLOY-unit/$UNIT $UNIT_FILE"; fi
  ofn=$( [ "$MODE" = go ] && sed -n 's/^ExecStart=\([^ ]*\) .*/\1/p' "$UNIT_FILE" || echo "$orig/fn-OLD/bin/fn")
  verify_up "$orig" "$ofn"
  say ""; say "ROLLBACK DONE: $orig on $(sc is-active "$UNIT" 2>/dev/null || echo '?')"
  exit 0
fi

# ---- deploy ----------------------------------------------------------------
if [ "$TARGET" = auto ]; then TARGET=$(choose_disk); fi
case $TARGET in /*) ;; *) die "TARGET must be absolute" ;; esac
TARGET=${TARGET%/}
REV12=$(printf %s "$EXPECT_REV" | cut -c1-12)
REL=$TARGET/fn-$REV12
FN=$REL/bin/fn
step "disk"; check_disk "$TARGET"

say "  free: $(df -P -h "$(p=$TARGET; while [ ! -e "$p" ]; do p=$(dirname "$p"); done; echo "$p")" | tail -1)"

step "tarball $TARBALL"
[ -f "$TARBALL" ] || die "no tarball $TARBALL"
got=$(sha256sum "$TARBALL" | cut -d' ' -f1)
[ "$got" = "$TAR_SHA" ] || die "tarball sha256 $got, expected $TAR_SHA"
say "  sha256 $got ok"

# Where the retired node is: this run's, or an earlier run's (idempotent).
RETIRED=
if [ -d "$OLD_NODE" ]; then
  [ -f "$OLD_NODE/fn.toml" ] || die "$OLD_NODE has no fn.toml"
  [ -e "$TARGET/fn.toml" ] && die "$TARGET already holds a node while $OLD_NODE still does"
else
  RETIRED=$(ls -d "$OLD_NODE"-retired-* 2>/dev/null | while read -r d; do
    [ "$(sed -n 's/^new_node=//p' "$d/DEPLOY-MANIFEST" 2>/dev/null)" = "$TARGET" ] && echo "$d"; done | tail -1)
  [ -n "$RETIRED" ] || die "$OLD_NODE absent and no retired node names $TARGET"
  say "resuming: $OLD_NODE was retired to $RETIRED by an earlier run"
fi

stop_unit

step "retire $OLD_NODE"
if [ -z "$RETIRED" ]; then
  [ -f "$UNIT_FILE" ] || die "no unit file $UNIT_FILE"
  retire "$OLD_NODE"
  if [ "$MODE" = go ]; then
    # a node restored by an earlier rollback carries that deploy's record: keep it
    for f in DEPLOY-unit DEPLOY-MANIFEST DEPLOY-SHA256SUMS; do
      [ -e "$RETIRED/$f" ] && mv -T "$RETIRED/$f" "$RETIRED/$f.before-$STAMP"; done
    mkdir "$RETIRED/DEPLOY-unit"; cp -p "$UNIT_FILE" "$RETIRED/DEPLOY-unit/$UNIT"
    { printf 'original=%s\nretired_at=%s\nnew_node=%s\nunit=%s\nunit_file=%s\ntarball=%s\ntarball_sha256=%s\nstore=%s\n' \
        "$OLD_NODE" "$STAMP" "$TARGET" "$UNIT" "$UNIT_FILE" "$TARBALL" "$TAR_SHA" "$STORE"
      echo "moved:"; ls -la "$RETIRED"; } >"$RETIRED/DEPLOY-MANIFEST"
    sums_of "$RETIRED" >"$RETIRED/DEPLOY-SHA256SUMS"
    sed 's/^/  /' "$RETIRED/DEPLOY-SHA256SUMS" | tee -a "$LOG"
  fi
  say "  retired to $RETIRED (renamed, nothing deleted)"
else say "  skip: already $RETIRED"; fi
[ "$MODE" = dry ] && RETIRED=$OLD_NODE-retired-$STAMP

step "install into $REL"
if [ -x "$FN" ]; then say "  skip: $FN present"
else
  run mkdir -p "$TARGET"
  if [ "$MODE" = go ]; then
    stage=$TARGET/.unpack-$STAMP; mkdir "$stage"
    tar -xzf "$TARBALL" -C "$stage"
    # Two layouts: the friends release (top fn-REV12) and D35's release
    # product (top fn, its revision in libexec/fn/source-revision).
    top=$(ls "$stage")
    case $top in
      "fn-$REV12") ;;
      fn) src=$(cat "$stage/fn/libexec/fn/source-revision" 2>/dev/null || true)
          [ "$src" = "$EXPECT_REV" ] || die "the release's source-revision is '$src', expected $EXPECT_REV" ;;
      *) die "the tarball's top directory is $top, not fn-$REV12 or fn" ;;
    esac
    ( cd "$stage/$top" && sha256sum -c --quiet SHA256SUMS ) >>"$LOG" 2>&1 || die "the release's SHA256SUMS do not verify"
    mv -T "$stage/$top" "$REL"; rmdir "$stage"
    say "  unpacked, SHA256SUMS verified"
  else echo "  would: tar -xzf $TARBALL into $REL; sha256sum -c SHA256SUMS"; fi
fi
if [ "$MODE" = go ]; then
  ver=$(clean_env "$FN" --version 2>&1 || true)
  say "  $FN --version: $ver"
  case $ver in
    "fn $EXPECT_REV") ;;
    "fn 6.7."*" ($REV12)") n=${ver#fn 6.7.}; n=${n% ($REV12)}
      case $n in 0) ;; ''|0*|*[!0-9]*) die "--version printed '$ver', not a release version 6.7.N" ;; esac ;;
    *) die "--version printed '$ver', expected 'fn 6.7.N ($REV12)' or 'fn $EXPECT_REV'" ;;
  esac
else echo "  would: $FN --version (must print fn 6.7.N ($REV12), or fn $EXPECT_REV before VERSION)"; fi

step "configuration"
if [ -f "$TARGET/fn.toml" ]; then say "  skip: $TARGET/fn.toml present"
elif [ "$MODE" = go ]; then
  sed "s#$OLD_NODE/#$TARGET/#g; s#\"$OLD_NODE\"#\"$TARGET\"#g" "$RETIRED/fn.toml" >"$TARGET/fn.toml"
  grep -q "$RETIRED\|\"$OLD_NODE/" "$TARGET/fn.toml" && die "fn.toml still names the retired node"
  # the directories fn.toml names outside the store (log, tls); the store
  # itself is made by init or by the import below, never here
  for d in $(grep -o "\"$TARGET/[^\"]*\"" "$TARGET/fn.toml" | tr -d '"'); do
    case $d in "$TARGET/store"|"$TARGET/store/"*) ;; *) mkdir -p "$(dirname "$d")" ;; esac; done
  say "  written from the retired fn.toml, $OLD_NODE -> $TARGET"
else echo "  would: sed s#$OLD_NODE/#$TARGET/#g $RETIRED/fn.toml > $TARGET/fn.toml"; fi

step "TLS"
if [ -f "$TARGET/tls/cert.pem" ] && [ -f "$TARGET/tls/key.pem" ]; then say "  skip: pair present"
else
  if [ -n "$CERT_DIR" ]; then c=$CERT_DIR/fullchain.pem; k=$CERT_DIR/privkey.pem; src="Let's Encrypt ($CERT_DIR)"
  else c=$RETIRED/tls/cert.pem; k=$RETIRED/tls/key.pem; src="the retired LAN pair"; fi
  if [ "$MODE" = go ]; then
    [ -f "$c" ] && [ -f "$k" ] || die "no certificate pair at $c / $k"
    a=$(openssl x509 -in "$c" -noout -pubkey | sha256sum); b=$(openssl pkey -in "$k" -pubout | sha256sum)
    [ "$a" = "$b" ] || die "$k does not match $c"
    openssl x509 -in "$c" -noout -checkend 86400 >/dev/null || die "$c expires within a day"
    mkdir -p "$TARGET/tls"; cp "$c" "$TARGET/tls/cert.pem"; cp "$k" "$TARGET/tls/key.pem"; chmod 600 "$TARGET/tls/key.pem"
    say "  from $src: $(openssl x509 -in "$TARGET/tls/cert.pem" -noout -subject -enddate | tr '\n' ' ')"
  else echo "  would: copy $c and $k (from $src) to $TARGET/tls/"; fi
fi

step "credentials"
if [ -f "$TARGET/credentials.txt" ]; then say "  skip: present"
else run cp -p "$RETIRED/credentials.txt" "$TARGET/credentials.txt"; fi

step "store ($STORE)"
if [ -d "$TARGET/store" ]; then say "  skip: $TARGET/store present"
elif [ "$STORE" = import ]; then
  run cp -a "$RETIRED/store" "$TARGET/store"
  [ "$MODE" = go ] && for s in "$TARGET"/store/control.sock*; do [ -e "$s" ] && mv "$s" "$TARGET/store.dropped-$(basename "$s")-$STAMP"; done
  say "  imported by cp -a of the stopped store"
  # SEC-006: a store from before the node key files gets its secret once
  # (`run' refuses a store without one and never creates it).
  if [ ! -f "$TARGET/store/keys/node-secret.key" ]; then
    run clean_env "$FN" --fn store "$TARGET/store" node-secret create
  fi
  # PKT-579: the copy is a deliberate move onto TARGET's filesystem (and a
  # store older than the filesystem record has none): record where it is
  # now, keeping its durability policy.
  run clean_env "$FN" operator "$TARGET/fn.toml" store rebind-filesystem
else
  # shellcheck disable=SC2086
  run clean_env "$FN" operator "$TARGET/fn.toml" init $INIT_ARGS $NODE_GROUPS
  if [ "$MODE" = go ]; then
    awk 'NF>=2 {print $1}' "$TARGET/credentials.txt" | while read -r u; do
      pw=$(awk -v u="$u" '$1==u {print $2; exit}' "$TARGET/credentials.txt")
      printf '%s\n%s\n' "$pw" "$pw" | clean_env setsid "$FN" operator "$TARGET/fn.toml" principal set-password "$u" --posting >>"$LOG" 2>&1 \
        || die "principal set-password $u failed"
      say "  enrolled $u (posting)"
    done
  else echo "  would: principal set-password LOGIN --posting for each credentials.txt login (stdin)"; fi
fi
if [ "$MODE" = go ]; then clean_env "$FN" operator "$TARGET/fn.toml" status 2>&1 | head -3 | sed 's/^/  /' | tee -a "$LOG"; fi

step "unit $UNIT_FILE"
if [ "$MODE" = go ]; then
  if grep -q "^ExecStart=$FN operator $TARGET/fn.toml run\$" "$UNIT_FILE"; then say "  skip: already points at $TARGET"
  else
    grep -v '^Environment=FN_' "$RETIRED/DEPLOY-unit/$UNIT" \
      | sed "s#^Description=.*#Description=fn native news node ($REV12, fresh $STAMP)#; s#^ExecStart=.*#ExecStart=$FN operator $TARGET/fn.toml run#" >"$UNIT_FILE.new-$STAMP"
    mv "$UNIT_FILE.new-$STAMP" "$UNIT_FILE"
  fi
  grep -q FN_NATIVE "$UNIT_FILE" && die "the unit still carries FN_NATIVE"
  grep -E '^(Description|ExecStart|Environment)=' "$UNIT_FILE" | sed 's/^/  /' | tee -a "$LOG"
else echo "  would: rewrite $UNIT_FILE from $RETIRED/DEPLOY-unit/$UNIT (ExecStart=$FN operator $TARGET/fn.toml run; no Environment=FN_*)"; fi

verify_up "$TARGET" "$FN"
say ""; say "DEPLOY DONE: $TARGET ($REV12, store $STORE) on $UNIT; rollback: $ME --go --rollback $RETIRED${UNIT:+ --unit $UNIT}"
