#!/bin/sh
# Qualify a rented build box: may boxq give it work?  Run from the laptop.
#
#   tools/box_qualify.sh BOX [--quick] [--set SHA] [--modules "tests.a tests.b"]
#
# Checks, each printed PASS/FAIL with what it saw:
#   arch        x86_64, glibc at least what /tank/fn/sbcl/bin/sbcl needs
#   toolchain   tools/acl2_toolchain.py identity of the certify and load
#               launchers equal to hbox's (so hbox's certificates install there)
#   packages    box_bootstrap.sh's package list is installed (dpkg), python3 is
#               3.12+, dilithium_py imports, the OpenSSL 3.5.8 test tool runs,
#               docker answers INSIDE a swarm-build scope (lat1, 2026-10-04: the
#               group alone was not enough)
#   tools       every box-aware tool resolves BOX: farm HOSTS, certs caches,
#               proof_repl trees, native_box.sh, box_table env, gate_reap
#               (tests/test_box_table.py holds the same list)
#   sets        each published image set on the box has MANIFEST.json and
#               SHA256SUMS (tests/native_image_provenance.py reads the manifest
#               beside a linked launcher)
#   certify     (not --quick) farm.py submit BOX books/store-reclaim-stream:
#               every book from the box's cache, certify 0, exit 0
#   natives     (not --quick) the environment-sensitive modules (docker, ML-DSA,
#               fsync) against the newest set the box holds (--set): OK, as on hbox
# The verdict goes into BOX's row in ~/.config/fn/boxes.json as
# "qualified": {"ok": true|false, "at": ISO, "failed": [...]}; tools/boxq.py
# places work only on a row whose qualified.ok is true.  Exit 0 qualified, 1 not.
set -u
HERE=$(cd "$(dirname "$0")/.." && pwd)
BOX=${1:?usage: box_qualify.sh BOX [--quick] [--set SHA] [--modules LIST]}; shift
QUICK=0; SET=; MODULES="tests.test_native_reader_clients tests.test_native_consumer_exchange tests.test_native_group_name_bound"
while [ $# -gt 0 ]; do
    case $1 in
        --quick) QUICK=1; shift ;;
        --set) SET=$2; shift 2 ;;
        --modules) MODULES=$2; shift 2 ;;
        *) echo "box_qualify: unknown option $1" >&2; exit 2 ;;
    esac
done
FAILED=
pass() { echo "PASS $1: $2"; }
fail() { echo "FAIL $1: $2"; FAILED="$FAILED $1"; }
SSH="ssh -n -o BatchMode=yes -o ConnectTimeout=15"

out=$($SSH "$BOX" 'echo "$(uname -m) $(getconf GNU_LIBC_VERSION | cut -d" " -f2) $(grep -ao "GLIBC_2\.[0-9]*" /tank/fn/sbcl/bin/sbcl | sort -u -t. -k2,2n | tail -1 | cut -d_ -f2)"') \
    || { fail reach "ssh $BOX failed"; out=; }
set -- $out
if [ "${1:-}" = x86_64 ] && [ -n "${3:-}" ] && [ "$(printf '%s\n%s\n' "$3" "$2" | sort -t. -k1,1n -k2,2n | head -1)" = "$3" ]; then
    pass arch "$1, glibc $2 >= $3"
else fail arch "${out:-no answer}"; fi

for l in acl2-literal-4g-tls64k acl2-literal-4g-tls256k; do
    a=$(ssh -o BatchMode=yes hbox "python3 - identity /tank/fn/toolchains/w28/$l" < "$HERE/tools/acl2_toolchain.py" 2>/dev/null)
    b=$(ssh -o BatchMode=yes "$BOX" "python3 - identity /tank/fn/toolchains/w28/$l" < "$HERE/tools/acl2_toolchain.py" 2>/dev/null)
    if [ -n "$b" ] && [ "$a" = "$b" ]; then pass toolchain "$l $(echo "$b" | cut -c1-12) = hbox"
    else fail toolchain "$l box '${b:-none}' hbox '${a:-none}'"; fi
done

PKGS=$(sed -n 's/^FN_BOX_PACKAGES="\(.*\)"$/\1/p' "$HERE/tools/box_bootstrap.sh")
missing=$($SSH "$BOX" "for p in $PKGS; do dpkg -s \$p >/dev/null 2>&1 || dpkg -s \${p}t64 >/dev/null 2>&1 || echo \$p; done" | tr '\n' ' ')
[ -z "$PKGS" ] && fail packages "no FN_BOX_PACKAGES list in box_bootstrap.sh" \
    || { [ -z "$missing" ] && pass packages "$(echo $PKGS | wc -w | tr -d ' ') installed" || fail packages "missing: $missing"; }
probe=$($SSH "$BOX" 'python3 -c "import sys; assert sys.version_info >= (3, 12)" && echo py; python3 -c "import dilithium_py" 2>/dev/null && echo dil; LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib /tank/fn/toolchains/openssl-3.5.8/bin/openssl version 2>/dev/null | grep -q "3.5.8" && echo ossl; systemd-run --user --scope --quiet docker info >/dev/null 2>&1 && echo dock' | tr '\n' ' ')
for w in py:python3.12 dil:dilithium-py ossl:openssl-3.5.8-test-tool dock:docker-in-a-user-scope; do
    case " $probe " in *" ${w%%:*} "*) pass packages "${w#*:}" ;; *) fail packages "${w#*:} absent" ;; esac
done

res=$(cd "$HERE" && python3 - "$BOX" <<'PY'
import subprocess, sys
sys.path.insert(0, "tools")
box = sys.argv[1]
bad = []
import acl2_slots, certs, box_table
if box not in acl2_slots.farm_hosts(): bad.append("farm HOSTS")
if box not in certs.REMOTE_CACHES: bad.append("certs.REMOTE_CACHES")
import proof_repl
if box not in proof_repl.REMOTE_TREES: bad.append("proof_repl REMOTE_TREES")
import gate_reap
if box not in gate_reap.DEFAULT_ROOTS: bad.append("gate_reap")
if box_table.env_line(box) is None: bad.append("box_table env")
if subprocess.run(["sh", "tools/native_box.sh", box, "."], capture_output=True).returncode: bad.append("native_box.sh")
print(" ".join(bad))
PY
)
[ -z "$res" ] && pass tools "farm, certs, proof_repl, gate_reap, box_table env, native_box.sh" \
    || fail tools "does not resolve $BOX: $res"

sets=$($SSH "$BOX" 'for s in /tank/fn/images/*/; do n=$(basename $s); case $n in *.partial) continue;; esac; [ -f $s/MANIFEST.json ] && [ -f $s/SHA256SUMS ] && echo "ok $n" || echo "bad $n"; done')
bad=$(echo "$sets" | sed -n 's/^bad //p' | cut -c1-9 | tr '\n' ' ')
[ -z "$bad" ] && pass sets "$(echo "$sets" | grep -c '^ok') sets, each with MANIFEST.json and SHA256SUMS" || fail sets "without MANIFEST.json or SHA256SUMS: $bad"
[ -n "$SET" ] || SET=$($SSH "$BOX" 'ls -t /tank/fn/images | grep -v partial | head -1')

if [ $QUICK = 0 ]; then
    run=$(cd "$HERE" && python3 tools/farm.py submit "$BOX" --jobs 4 books/store-reclaim-stream 2>&1 | tail -1)
    case $run in run-*)
        v=$(cd "$HERE" && python3 tools/farm.py wait "$BOX" "$run" 2>&1 | grep -E 'certified here|verdict' | tr '\n' ' ')
        case $v in *"exit 0"*"passed 0, failed 0"*|*"passed 0, failed 0"*"exit 0"*) pass certify "$run from the cache, certify 0" ;;
            *) fail certify "$run: $v" ;; esac ;;
        *) fail certify "submit: $run" ;;
    esac
    label=qualify-$(date -u +%m%d%H%M%S)
    if (cd "$HERE" && sh tools/hbox_native.sh --box "$BOX" --name qualify --label "$label" --wait --jobs 3 \
            --image-set "$SET" --images developer,production "$SET" $MODULES) > /tmp/box_qualify.$$ 2>&1; then
        pass natives "$MODULES OK on $(echo "$SET" | cut -c1-9) ($BOX:/tank/fn/scratch/qualify/native-$label)"
    else
        fail natives "$(grep -E 'FAILED|refus|status' /tmp/box_qualify.$$ | tail -3 | tr '\n' ' ')"
    fi
    rm -f /tmp/box_qualify.$$
fi

python3 - "$BOX" "$FAILED" "$QUICK" <<'PY'
import datetime, json, os, sys
box, failed, quick = sys.argv[1], sys.argv[2].split(), sys.argv[3] == "1"
path = os.path.expanduser(os.environ.get("FN_BOXES_FILE") or "~/.config/fn/boxes.json")
data = json.load(open(path))
row = data.get("boxes", {}).get(box)
if row is not None:
    row["qualified"] = {"ok": not failed, "at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                        "failed": sorted(set(failed)), "quick": quick}
    open(path + ".new", "w").write(json.dumps(data, indent=2) + "\n")
    os.replace(path + ".new", path)
PY
if [ -z "$FAILED" ]; then echo "box_qualify: $BOX QUALIFIED"; exit 0; fi
echo "box_qualify: $BOX NOT qualified:$FAILED"; exit 1
