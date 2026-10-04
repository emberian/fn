#!/bin/sh
# Make an x86-64 Linux host a drop-in build box for fn, from this laptop.
#
#   tools/box_bootstrap.sh NAME TARGET --seed BOX [--until ISO-UTC] [--cores N]
#                          [--check-jobs N] [--no-pick] [--identity KEYFILE]
#                          [--forget-host-key] [--dry-run]
#
# NAME is the box's name from now on (lower-case word: its ssh alias, its
# hostname, its row in ~/.config/fn/boxes.json, what --box/--host/farm take).
# TARGET is how to reach the fresh host now: user@address, where user is root
# or has passwordless sudo, and this laptop's ssh key is authorized (the
# provider's provisioner put it there; --identity names which key, and it
# goes into the box's ssh alias).  --seed BOX is a box that already
# holds the replica (a live row in ~/.config/fn/boxes.json, or hbox); its
# /tank/fn is copied host to host (seed -> new box), never through the
# laptop.  Seed from a rented box rather than hbox when one exists: hbox
# uploads at about 8-10 MB/s and its cache is on a busy pool.
#
# Steps (each stops the run on failure, with the step named):
#   probe     arch x86_64, the kernel, glibc at least what the seed's SBCL
#             runtime needs (its highest GLIBC_ symbol version), apt-get,
#             systemd, free disk; --dry-run stops after this and prints the plan
#   system    packages (python3 3.12+, git, rsync, libssl3, libsodium, zlib,
#             build tools, zstd, docker.io, pip + dilithium-py 1.4.0), user fn with
#             this laptop's and the seed's keys, linger (systemd user scopes), hostname NAME,
#             /tank/fn/{sbcl,acl2-8.7,toolchains,certcache,images,scratch,gates},
#             the farm mirror path (this worktree's parent of build/), and
#             /usr/local/bin/swarm-build (hbox's wrapper: a systemd user scope
#             under swarm.slice, MemoryMax per build and for the slice, 85% of RAM)
#   seed      rsync from the seed box: sbcl, acl2-8.7, toolchains (not src),
#             every published image set, the certificate cache, the evidence
#             archive (a mirror: FN_EVIDENCE_ARCHIVE=/tank/fn/evidence in
#             /etc/environment, since a certify run reads every archived
#             manifest and the box cannot reach hbox by name; keep it fresh
#             with tools/box_mirror.sh)
#   verify    tools/acl2_toolchain.py identity of the certify and load
#             launchers equal to the seed's; every image set's SHA256SUMS;
#             ldd of each image binary resolves; ACL2 starts under swarm-build
#   register  ~/.ssh/fn-boxes.conf alias NAME (Include'd from ~/.ssh/config),
#             the row in ~/.config/fn/boxes.json (--until is required: a
#             rented box always has an end), and that file copied to every
#             live box so each knows its own row
#
# Removing a box: delete its row (or let `until` pass) and its Host block;
# nothing in the repository names it.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
usage() { sed -n '2,/^set -eu/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//' >&2; exit 2; }
[ $# -ge 2 ] || usage
NAME=$1; TARGET=$2; shift 2
SEED=; UNTIL=; CORES=; CHECK_JOBS=; PICK=true; DRY=0; IDENTITY=; FORGET=0
while [ $# -gt 0 ]; do
    case $1 in
        --seed) SEED=$2; shift 2 ;;
        --until) UNTIL=$2; shift 2 ;;
        --cores) CORES=$2; shift 2 ;;
        --check-jobs) CHECK_JOBS=$2; shift 2 ;;
        --no-pick) PICK=false; shift ;;
        --dry-run) DRY=1; shift ;;
        --identity) IDENTITY=$2; shift 2 ;;
        --forget-host-key) FORGET=1; shift ;;
        *) usage ;;
    esac
done
case $NAME in hbox|persvati|laptop|''|*[!a-z0-9-]*) echo "box_bootstrap: bad NAME $NAME" >&2; exit 2 ;; esac
[ -n "$SEED" ] || { echo "box_bootstrap: --seed BOX is required" >&2; exit 2; }
[ $DRY = 1 ] || [ -n "$UNTIL" ] || { echo "box_bootstrap: --until ISO-UTC is required (a rented box has an end)" >&2; exit 2; }
case $TARGET in *@*) ;; *) echo "box_bootstrap: TARGET is user@address" >&2; exit 2 ;; esac
ADDR=${TARGET#*@}
# Rented hosts reuse addresses (a deleted VM's IP comes back with a new host
# key), so their keys live in their own file, never ~/.ssh/known_hosts.
KNOWN=$HOME/.ssh/known_hosts.fn-boxes
SSH="ssh -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=accept-new -o UserKnownHostsFile=$KNOWN"
[ -z "$IDENTITY" ] || SSH="$SSH -i $IDENTITY -o IdentitiesOnly=yes"
FARM_MIRROR=$(dirname "$(dirname "$HERE")")   # .../fn/build/lanes/X -> .../fn/build; farm mirrors at the laptop's path
case $FARM_MIRROR in */build) ;; *) FARM_MIRROR=$HERE/build ;; esac
step() { echo "== $1 $(date -u +%H:%M:%SZ)"; }
die() { echo "box_bootstrap: $*" >&2; exit 1; }

# --forget-host-key: the address is a new host (the provider re-used it).
[ $FORGET = 0 ] || [ ! -f "$KNOWN" ] || ssh-keygen -R "$ADDR" -f "$KNOWN" >/dev/null 2>&1 || true
step probe
NEED_GLIBC=$($SSH "$SEED" "grep -ao 'GLIBC_2\.[0-9]*' /tank/fn/sbcl/bin/sbcl | sort -u -t. -k2,2n | tail -1 | cut -d_ -f2") \
    || die "seed $SEED: cannot read /tank/fn/sbcl/bin/sbcl"
PROBE=$($SSH "$TARGET" 'S=; [ "$(id -u)" = 0 ] || S="sudo -n"; echo "arch=$(uname -m) kernel=$(uname -r) glibc=$(getconf GNU_LIBC_VERSION | cut -d" " -f2) sudo=$($S true 2>/dev/null && echo ok || echo no) apt=$(command -v apt-get >/dev/null && echo yes || echo no) systemd=$(command -v systemd-run >/dev/null && echo yes || echo no) cores=$(nproc) memG=$(awk "/MemTotal/{print int(\$2/1048576)}" /proc/meminfo) diskG=$(df -Pk / | awk "NR==2{print int(\$4/1048576)}") os=$(. /etc/os-release; echo $ID-$VERSION_ID)"') \
    || die "cannot ssh $TARGET"
echo "   target $TARGET: $PROBE"
echo "   seed $SEED: SBCL needs glibc >= $NEED_GLIBC"
get() { echo "$PROBE" | tr ' ' '\n' | sed -n "s/^$1=//p"; }
[ "$(get arch)" = x86_64 ] || die "arch $(get arch): the toolchain is x86_64"
[ "$(get sudo)" = ok ] || die "$TARGET is not root and has no passwordless sudo"
[ "$(get apt)" = yes ] || die "no apt-get on $TARGET (Debian/Ubuntu only for now)"
[ "$(get systemd)" = yes ] || die "no systemd-run on $TARGET (swarm-build needs it)"
have=$(get glibc)
[ "$(printf '%s\n%s\n' "$NEED_GLIBC" "$have" | sort -t. -k1,1n -k2,2n | head -1)" = "$NEED_GLIBC" ] \
    || die "glibc $have < $NEED_GLIBC needed by /tank/fn/sbcl/bin/sbcl"
kmaj=$(get kernel | cut -d. -f1)
[ "$kmaj" -ge 4 ] || die "kernel $(get kernel) too old"
[ "$(get diskG)" -ge 60 ] || die "only $(get diskG) GiB free on / ($TARGET)"
CORES=${CORES:-$(get cores)}
[ -n "$CHECK_JOBS" ] || CHECK_JOBS=$(( CORES > 8 ? 8 : CORES ))
echo "   plan: $NAME = $TARGET ($CORES cores, $(get memG) GiB), seeded from $SEED, until ${UNTIL:-?}, pick $PICK, check_jobs $CHECK_JOBS"
if [ $DRY = 1 ]; then echo "box_bootstrap: --dry-run: probe passed; nothing changed"; exit 0; fi

step system
SEED_PUB=$($SSH "$SEED" 'test -f ~/.ssh/id_ed25519 || ssh-keygen -q -t ed25519 -N "" -f ~/.ssh/id_ed25519 -C "fn@$(hostname)"; cat ~/.ssh/id_ed25519.pub')
# hbox pushes evidence and image sets (tools/box_mirror.sh) and pulls the
# box's new certificates back at teardown, so its key is authorized too.
HBOX_PUB=$(ssh -o BatchMode=yes -o ConnectTimeout=15 hbox 'cat ~/.ssh/id_ed25519.pub' 2>/dev/null) || HBOX_PUB=
[ -n "$HBOX_PUB" ] || echo "   (hbox did not answer: its key is not authorized; add it before the mirror or teardown runs)"
SEED_PUB=$(printf '%s\n%s' "$SEED_PUB" "$HBOX_PUB")
$SSH "$TARGET" 'S=; [ "$(id -u)" = 0 ] || S="sudo -n"; exec $S env NAME='"$NAME"' SEED_PUB="'"$SEED_PUB"'" FARM_MIRROR='"$FARM_MIRROR"' bash -s' <<'SYS'
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update -q >/dev/null
ssl=libssl3; apt-cache show libssl3t64 >/dev/null 2>&1 && ssl=libssl3t64
apt-get install -y -q rsync git python3 python3-venv "$ssl" libsodium23 zlib1g build-essential pigz zstd openssl >/dev/null
# docker: tests.test_native_reader_clients builds the slrn/pan container
# (tools/reader_clients/Dockerfile) and skips on a box without it (lat1,
# 2026-10-04); fn must be in the docker group (reset any ssh ControlMaster so
# the new group is seen).
apt-get install -y -q docker.io >/dev/null
systemctl enable --now docker >/dev/null 2>&1 || true
id fn >/dev/null 2>&1 || useradd -m -s /bin/bash fn
usermod -aG docker fn
# dilithium-py: tools/fn_verify.py (the consumer independent verifier) has no ML-DSA-65
# implementation without it and answers undecided, so tests.test_native_consumer_exchange
# fails 7 of 11 (lat1, 2026-10-04).  Pure Python, pinned to the version hbox runs.
apt-get install -y -q python3-pip >/dev/null
su - fn -c 'python3 -m pip install --user --break-system-packages -q dilithium-py==1.4.0'
python3 -c 'import sys; assert sys.version_info >= (3, 12), sys.version' || { echo "python3 < 3.12" >&2; exit 1; }
id fn >/dev/null 2>&1 || useradd -m -s /bin/bash fn
install -d -o fn -g fn -m 700 /home/fn/.ssh
{ cat /root/.ssh/authorized_keys 2>/dev/null; for h in /home/*/.ssh/authorized_keys; do cat "$h" 2>/dev/null; done; printf '%s\n' "$SEED_PUB"; } | grep . | sort -u > /home/fn/.ssh/authorized_keys.new
mv /home/fn/.ssh/authorized_keys.new /home/fn/.ssh/authorized_keys
chown fn:fn /home/fn/.ssh/authorized_keys; chmod 600 /home/fn/.ssh/authorized_keys
loginctl enable-linger fn
hostnamectl set-hostname "$NAME" 2>/dev/null || hostname "$NAME"
grep -qw "$NAME" /etc/hosts || echo "127.0.1.1 $NAME" >> /etc/hosts
install -d -o fn -g fn /tank /tank/fn /tank/fn/scratch /tank/fn/certcache /tank/fn/images /tank/fn/toolchains /tank/fn/gates /tank/fn/evidence
# The evidence archive is a local mirror here (hbox's is canonical; certify
# reads every archived manifest), so tools/evidence_store.py reads it as local.
grep -q '^FN_EVIDENCE_ARCHIVE=' /etc/environment || echo 'FN_EVIDENCE_ARCHIVE=/tank/fn/evidence' >> /etc/environment
d=; for part in $(echo "$FARM_MIRROR" | tr / ' '); do d=$d/$part; install -d -o fn -g fn "$d"; done
N=$(nproc); MEMG=$(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo); CAP=$(( MEMG * 85 / 100 ))
cat > /usr/local/bin/swarm-build <<SB
#!/usr/bin/env bash
# swarm-build (rented fn box, tools/box_bootstrap.sh): hbox's wrapper -- a
# systemd user scope under swarm.slice with an enforced MemoryMax, made
# killable, pinned to this box's $N cores.  SWARM_MEM_MAX overrides the cap.
set -euo pipefail
if [ -n "\${SWARM_BUILD_INNER:-}" ]; then
  echo 0 > /proc/self/oom_score_adj 2>/dev/null || true
  exec taskset -c 0-$((N-1)) nice -n 15 "\$@"
fi
export SWARM_BUILD_INNER=1
export XDG_RUNTIME_DIR=\${XDG_RUNTIME_DIR:-/run/user/\$(id -u)}
exec systemd-run --user --scope --slice=swarm.slice --quiet \\
  -p MemoryMax="\${SWARM_MEM_MAX:-${CAP}G}" -p MemorySwapMax=0 -p CPUWeight=50 \\
  -- "\$0" "\$@"
SB
chmod 755 /usr/local/bin/swarm-build
install -d -o fn -g fn /home/fn/.config /home/fn/.config/fn /home/fn/.config/systemd /home/fn/.config/systemd/user /home/fn/.config/systemd/user/swarm.slice.d
printf '[Slice]\nMemoryMax=%sG\n' "$CAP" > /home/fn/.config/systemd/user/swarm.slice.d/50-memcap.conf
chown -R fn:fn /home/fn/.config
echo "   system ok: $(hostname), $N cores, swarm.slice cap ${CAP}G"
SYS
FN="fn@$ADDR"
$SSH "$FN" 'swarm-build true' || die "swarm-build does not run as fn on $ADDR"

step seed
$SSH "$SEED" "set -e; for d in sbcl acl2-8.7; do rsync -a -e 'ssh -o BatchMode=yes -o StrictHostKeyChecking=accept-new' /tank/fn/\$d fn@$ADDR:/tank/fn/; done
rsync -a --exclude=src -e 'ssh -o BatchMode=yes' /tank/fn/toolchains/ fn@$ADDR:/tank/fn/toolchains/
rsync -a -e 'ssh -o BatchMode=yes' /tank/fn/images/ fn@$ADDR:/tank/fn/images/
rsync -a --exclude=incoming -e 'ssh -o BatchMode=yes' /tank/fn/evidence/ fn@$ADDR:/tank/fn/evidence/
rsync -a --exclude=.entry.lock --exclude='.*' -e 'ssh -o BatchMode=yes' /tank/fn/certcache/ fn@$ADDR:/tank/fn/certcache/
echo \"   seeded: \$(ls /tank/fn/certcache | wc -l) cache keys, image sets \$(ls /tank/fn/images | cut -c1-9 | tr '\n' ' ')\""

step verify
for launcher in acl2-literal-4g-tls64k acl2-literal-4g-tls256k; do
    a=$($SSH "$SEED" "python3 - identity /tank/fn/toolchains/w28/$launcher" < "$HERE/tools/acl2_toolchain.py" 2>/dev/null; true)
    b=$($SSH "$FN" "python3 - identity /tank/fn/toolchains/w28/$launcher" < "$HERE/tools/acl2_toolchain.py" 2>/dev/null; true)
    [ -n "$a" ] && [ "$a" = "$b" ] || die "toolchain identity of $launcher differs: seed '$a' box '$b'"
    echo "   $launcher identity $(echo "$b" | cut -c1-16)"
done
$SSH "$FN" 'set -e; for s in /tank/fn/images/*/; do (cd "$s" && sha256sum -c --quiet SHA256SUMS) || { echo "image set $s fails SHA256SUMS"; exit 1; }
  for b in "$s"fn-host*; do case $b in *.core|*.world-deps|*.catalog) continue ;; esac
    [ -x "$b" ] || continue; m=$(LD_LIBRARY_PATH=${s}lib ldd "$b" 2>&1 | grep "not found" || true)
    [ -z "$m" ] || { echo "$b: $m"; exit 1; }; done; done
echo "   images: $(ls /tank/fn/images | wc -l) set(s) verified, binaries resolve"
out=$(echo "(+ 20 22) (good-bye)" | timeout 180 swarm-build /tank/fn/toolchains/w28/acl2-literal-4g-tls64k 2>&1) || true
echo "$out" | grep -q "ACL2 Version 8.7" || { echo "ACL2 did not start: $(echo "$out" | tail -3)"; exit 1; }
echo "   ACL2 8.7 starts under swarm-build"' || die "verify failed on $NAME"

step register
CONF=$HOME/.ssh/fn-boxes.conf
touch "$CONF"; chmod 600 "$CONF"
grep -q '^Include ~/.ssh/fn-boxes.conf' "$HOME/.ssh/config" 2>/dev/null || {
    real=$(readlink "$HOME/.ssh/config" 2>/dev/null || echo "$HOME/.ssh/config")
    { echo "Include ~/.ssh/fn-boxes.conf"; echo; cat "$real"; } > "$real.fn-boxes.new" && cat "$real.fn-boxes.new" > "$real" && rm "$real.fn-boxes.new"; }
python3 - "$CONF" "$NAME" "$ADDR" "$IDENTITY" <<'PY'
import re, sys
conf, name, addr, identity = sys.argv[1:]
text = open(conf).read()
text = re.sub(rf"(?ms)^Host {re.escape(name)}\n(?:[ \t]+.*\n?)*", "", text)
text = text.rstrip("\n") + ("\n" if text.strip() else "") + (
    f"Host {name}\n\tHostName {addr}\n\tUser fn\n\tStrictHostKeyChecking accept-new\n"
    f"\tServerAliveInterval 30\n\tUserKnownHostsFile ~/.ssh/known_hosts.fn-boxes\n"
    + (f"\tIdentityFile {identity}\n\tIdentitiesOnly yes\n" if identity else ""))
open(conf, "w").write(text)
PY
python3 - "$NAME" "$UNTIL" "$CORES" "$CHECK_JOBS" "$PICK" <<'PY'
import json, os, sys
name, until, cores, jobs, pick = sys.argv[1:]
path = os.path.expanduser(os.environ.get("FN_BOXES_FILE") or "~/.config/fn/boxes.json")
os.makedirs(os.path.dirname(path), exist_ok=True)
try:
    data = json.load(open(path))
except FileNotFoundError:
    data = {}
data.setdefault("boxes", {})[name] = {"like": "hbox", "until": until, "cores": int(cores),
                                      "check_jobs": int(jobs), "pick": pick == "true"}
open(path + ".new", "w").write(json.dumps(data, indent=2) + "\n")
os.replace(path + ".new", path)
PY
for box in $(python3 "$HERE/tools/box_table.py" names); do
    scp -q -o BatchMode=yes "${FN_BOXES_FILE:-$HOME/.config/fn/boxes.json}" "$box:.config/fn/boxes.json" || echo "   (could not update $box's copy)"
done
ssh -o BatchMode=yes "$NAME" true || die "alias $NAME does not answer"
echo "box_bootstrap: $NAME ready: --box $NAME / farm.py submit $NAME / proof_repl --host $NAME (until $UNTIL)"
