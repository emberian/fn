#!/bin/sh
# tools/extract/check.sh TREE IMAGE -- the extraction differential (e4, lane
# extract-2): A-EXTRACT's qualification of one build (specs/failures.md).
# Run on hbox, in a tree whose books are certified and whose developer image
# IMAGE is built (tools/hbox_native.sh makes both; `make extract-check` runs
# this there).  Steps, each fatal, the first failure named:
#   1. build: extract from the image's world, the backend, csc (build.sh);
#   2. transcripts: the served differential's chunk files through IMAGE's
#      `--fn model' and the program's model and socket verbs: byte-identical;
#   3. probes: host entries called with guard-violating arguments, the
#      image's fnn-call against the program's boundary (probes.py): identical;
#   4. store: a copy of a real format-9 store (EXTRACT_STORE, default the
#      n1k-2k fixture), rebound, opened and read through IMAGE and through the
#      program's read-only open (host/store-open-host.lisp): identical replies;
#   5. functions: the per-function differential (fcheck.py): guard-derived
#      inputs, ACL2's value (the certified world) against the extracted
#      procedure's; any DIFFER, RAISE or HANG fails naming the function.
# Writes TREE/build/extract/check/ and prints `extract-check: PASS' or
# `extract-check: FAIL at STEP: ...'.
set -u
TREE=$(cd "$1" && pwd)
IMAGE=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
ACL2=${FN_EXTRACT_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}
CHICKEN=${CHICKEN:-/tank/fn/toolchains/chicken-5.4.0}
STORE=${EXTRACT_STORE:-/tank/fn/scratch/fixtures/n1k-2k/store}
PER=${EXTRACT_FCHECK_PER:-20}
X=$TREE/tools/extract
E=$TREE/build/extract
C=$E/check
export LD_LIBRARY_PATH=$CHICKEN/lib
fail() { echo "extract-check: FAIL at $1"; exit 1; }
rm -rf "$C"; mkdir -p "$C"

echo "== 1 build"
sh "$X/build.sh" "$TREE" > "$C/build.log" 2>&1 || fail "build: $(tail -3 "$C/build.log" | tr '\n' ' ')"
tail -2 "$C/build.log"

echo "== 2 transcripts"
( cd "$TREE" && python3 "$X/transcripts.py" "$C/transcripts" > /dev/null ) || fail "transcripts: chunk files"
sh "$X/compare.sh" "$IMAGE" "$E/served" "$C/transcripts" "$C/cmp" > "$C/transcripts.log" 2>&1
cat "$C/transcripts.log" | tail -1
first=$(grep -v IDENTICAL "$C/transcripts.log" | grep -v '^==' | head -1)
[ -z "$first" ] || fail "transcripts: $first"

echo "== 3 probes"
( cd "$TREE" && python3 "$X/probes.py" run-sbcl "$IMAGE" "$C/probes.sbcl" ) > /dev/null 2>&1
"$E/served" probe > "$C/probes.chicken" 2> "$C/probes.chicken.err"
python3 "$X/probes.py" compare "$C/probes.sbcl" "$C/probes.chicken" > "$C/probes.log" 2>&1
st=$?; cat "$C/probes.log" | tail -1
[ $st = 0 ] || fail "probes: $(grep -A2 DIFFER "$C/probes.log" | head -3 | tr '\n' ' ')"

echo "== 4 store"
[ -d "$STORE" ] || fail "store: no store at $STORE (EXTRACT_STORE)"
rm -rf "$C/store"; cp -a "$STORE" "$C/store"; touch "$C/store/writer.lock"; chmod 600 "$C/store/writer.lock"
env ACL2_CUSTOMIZATION=NONE "$IMAGE" --fn store "$C/store" rebind-filesystem > "$C/rebind.log" 2>&1 \
    || fail "store: rebind $(tail -1 "$C/rebind.log")"
python3 - "$C/store-read.chunks" <<'PY'
import sys
cmds = (b"CAPABILITIES\r\nMODE READER\r\nLIST\r\nLIST ACTIVE\r\nGROUP fn.test\r\nSTAT\r\nHEAD\r\nBODY\r\n"
        b"ARTICLE 1\r\nARTICLE 2\r\nNEXT\r\nLAST\r\nOVER 1-3\r\nHDR Subject 1-3\r\nLISTGROUP fn.test 1-5\r\n"
        b"ARTICLE 999\r\nARTICLE <nonexistent@example.invalid>\r\nNEWNEWS * 20000101 000000\r\nQUIT\r\n")
open(sys.argv[1], "wb").write(b"%d\n" % len(cmds) + cmds)
PY
for t in store-read reader-commands session-200; do
  f=$C/$t.chunks; [ -f "$f" ] || f=$C/transcripts/$t.chunks
  env ACL2_CUSTOMIZATION=NONE "$IMAGE" --fn model "$f" "$C/store" > "$C/$t.store.sbcl" 2> "$C/$t.store.sbcl.err"; s1=$?
  "$E/served" model "$f" "$C/store" > "$C/$t.store.chicken" 2> "$C/$t.store.chicken.err"; s2=$?
  if [ $s1$s2 = 00 ] && cmp -s "$C/$t.store.sbcl" "$C/$t.store.chicken"; then
    echo "$t over the store: $(wc -c < "$C/$t.store.sbcl") bytes IDENTICAL"
  else
    fail "store: $t DIFFER (exit $s1/$s2; $(head -1 "$C/$t.store.chicken.err"))"
  fi
done

echo "== 5 functions"
python3 "$X/fcheck.py" gen "$E/served.json" --out "$C/cands" --per "$PER" --seed 1 > "$C/gen.log" || fail "functions: gen"
cat "$C/gen.log"
{
  echo '(ld "tools/extract/world.lisp")'
  echo '(ld "tools/extract/world-host.lisp")'
  echo '(ld "tools/extract/frontend.lisp")'
  echo '(ld "tools/extract/fcheck.lisp")'
  for f in "$C"/cands.*; do echo "(xt-fcheck \"$f\" \"$f.vec\" state)"; done
} > "$C/fcheck.lsp"
( cd "$TREE" && swarm-build "$ACL2" < "$C/fcheck.lsp" > "$C/fcheck-acl2.log" 2>&1 )
ls "$C"/cands.*.vec > /dev/null 2>&1 || fail "functions: ACL2 wrote no vectors ($C/fcheck-acl2.log)"
python3 "$X/fcheck.py" scheme "$C"/cands.*.vec --ir "$E/served.json" --out "$E/vectors.scm" > /dev/null
( cd "$E" && cp "$X/fcheck-main.scm" . && PATH=$CHICKEN/bin:$PATH swarm-build csc -O2 -d0 fcheck-main.scm -o fcheck -L -lcrypto > "$C/fcheck-csc.log" 2>&1 ) \
    || fail "functions: csc fcheck-main ($C/fcheck-csc.log)"
"$E/fcheck" "$E/vectors.scm" > "$C/fcheck.log" 2>&1
python3 "$X/fcheck.py" report "$E/served.json" "$C/fcheck.log" --json "$C/fcheck.json" | tail -3
first=$(grep -E '^(DIFFER|RAISE|HANG)' "$C/fcheck.log" | head -1 | cut -f1,2)
[ -z "$first" ] || fail "functions: first divergent function $first ($C/fcheck.log)"
echo "extract-check: PASS"
