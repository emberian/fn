#!/bin/sh
# w31/duplicate-outcome: does a second submission of one Message-ID answer
# DUPLICATE or REFUSED, and what decides it?
set -u
ROOT=/home/ember/fn-gates/w31-duplicate
IMG=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host
N=$ROOT/node
CFG=$N/fn.toml
PORT=11317
GROUP=fn.letters
export FN_NATIVE_HOST=$IMG

rm -rf "$N"
mkdir -p "$N"
mkdir -p "$ROOT"

echo "=== image ==="
ls -la "$IMG" "$IMG.core"
sha256sum /home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/build-source.sha256

echo "=== store init ==="
"$ROOT/fn-native" store "$N/store" init "$GROUP"
echo "init rc=$?"

printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' \
  "$N/store" "$PORT" "$N/control.sock" > "$CFG"
cat "$CFG"

echo "=== start owner ==="
nohup env FN_NATIVE_HOST="$IMG" "$ROOT/fn-native" operator "$CFG" run > "$ROOT/owner.log" 2>&1 &
OWNER=$!
echo "owner pid=$OWNER" | tee "$ROOT/owner.pid"
i=0
while [ $i -lt 60 ]; do
  [ -S "$N/control.sock" ] && break
  i=$((i+1)); sleep 1
done
echo "control socket after ${i}s: $(ls -la "$N/control.sock" 2>&1)"

# One article, built with an explicit Date so the bytes are ours.
mkart() { # mkart FILE DATE SUBJECT BODY MSGID
  printf 'From: gate@example.invalid\r\nSubject: %s\r\nNewsgroups: %s\r\nDate: %s\r\nMessage-ID: %s\r\n\r\n%s\r\n' \
    "$3" "$GROUP" "$2" "$5" "$4" > "$1"
}
post() { # post FILE MSGID LABEL
  out=$("$ROOT/fn-native" operator "$CFG" post --message-id "$2" --payload "$1" --group "$GROUP" 2>&1)
  rc=$?
  echo "[$3] rc=$rc out=$out"
}

echo
echo "=== E1: byte-identical resubmission, ten times, fixed Date ==="
M1='<e1@example.invalid>'
mkart "$N/e1.article" 'Mon, 22 Sep 2026 03:08:46 +0000' 'fixed date' 'body one' "$M1"
sha1=$(sha256sum "$N/e1.article" | cut -c1-16)
echo "e1 payload digest=$sha1"
post "$N/e1.article" "$M1" "E1 submit 1"
k=2
while [ $k -le 10 ]; do
  post "$N/e1.article" "$M1" "E1 submit $k (identical bytes)"
  k=$((k+1))
done
echo "digest unchanged: $(sha256sum "$N/e1.article" | cut -c1-16)"

echo
echo "=== E2: same Message-ID, Date one second later ==="
M2='<e2@example.invalid>'
mkart "$N/e2a.article" 'Mon, 22 Sep 2026 03:08:46 +0000' 'fixed date' 'body two' "$M2"
mkart "$N/e2b.article" 'Mon, 22 Sep 2026 03:08:47 +0000' 'fixed date' 'body two' "$M2"
echo "diff of the two payloads:"; diff "$N/e2a.article" "$N/e2b.article"
post "$N/e2a.article" "$M2" "E2 submit 1"
k=1
while [ $k -le 3 ]; do
  post "$N/e2b.article" "$M2" "E2 submit with Date+1s, try $k"
  k=$((k+1))
done
post "$N/e2a.article" "$M2" "E2 submit the original bytes again"

echo
echo "=== E3: same Message-ID, different body ==="
M3='<e3@example.invalid>'
mkart "$N/e3a.article" 'Mon, 22 Sep 2026 03:08:46 +0000' 'fixed date' 'body three' "$M3"
mkart "$N/e3b.article" 'Mon, 22 Sep 2026 03:08:46 +0000' 'fixed date' 'body three, edited' "$M3"
post "$N/e3a.article" "$M3" "E3 submit 1"
post "$N/e3b.article" "$M3" "E3 submit with a different body"

echo
echo "=== E4: the driver's own pattern, six trials ==="
echo "each trial regenerates the article with date -u just before each of the two"
echo "submissions, exactly as tools/v0_matrix.py article() does"
t=1
while [ $t -le 6 ]; do
  M="<e4-$t@example.invalid>"
  F="$N/e4-$t.article"
  D1=$(date -u '+%a, %d %b %Y %H:%M:%S +0000')
  mkart "$F" "$D1" "driver pattern $t" "body four $t" "$M"
  post "$F" "$M" "E4 trial $t submit 1 Date=$D1"
  D2=$(date -u '+%a, %d %b %Y %H:%M:%S +0000')
  mkart "$F" "$D2" "driver pattern $t" "body four $t" "$M"
  post "$F" "$M" "E4 trial $t submit 2 Date=$D2"
  if [ "$D1" = "$D2" ]; then echo "E4 trial $t dates_equal=yes"; else echo "E4 trial $t dates_equal=NO"; fi
  t=$((t+1))
done

echo
echo "=== E5: what the node holds ==="
"$ROOT/fn-native" operator "$CFG" status; echo "status rc=$?"
echo "--- Date lines inside the transaction journal ---"
grep -a -o 'Date: [^\r]*' "$N"/store/transactions/*.txn 2>/dev/null | sed 's/\r//' | sort | uniq -c
echo "--- Message-ID lines inside the transaction journal ---"
grep -a -o 'Message-ID: <[^>]*>' "$N"/store/transactions/*.txn 2>/dev/null | sort | uniq -c
echo "--- the held octets for E1, extracted and compared with the submitted file ---"
for f in "$N"/store/transactions/*.txn; do
  if grep -aq "$M1" "$f"; then
    echo "E1 lives in $f"
    python3 - "$f" "$N/e1.article" <<'PY'
import sys
blob = open(sys.argv[1],'rb').read()
want = open(sys.argv[2],'rb').read()
i = blob.find(want)
print("submitted octets len", len(want), "found verbatim in the record at offset", i)
print("record len", len(blob))
PY
  fi
done

echo
echo "=== stop the owner ==="
kill -TERM "$OWNER"
k=0
while [ $k -lt 30 ]; do
  kill -0 "$OWNER" 2>/dev/null || break
  k=$((k+1)); sleep 1
done
kill -0 "$OWNER" 2>/dev/null && echo "owner still alive after ${k}s" || echo "owner exited after ${k}s"
echo "=== owner log tail ==="
tail -n 20 "$ROOT/owner.log"
