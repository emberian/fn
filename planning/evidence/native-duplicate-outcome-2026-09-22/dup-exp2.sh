#!/bin/sh
# E4': the driver's own generator, with the gap between the two submissions
# varied across a second boundary.  Records dates_equal against the word.
set -u
ROOT=/home/ember/fn-gates/w31-duplicate
IMG=/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host
N=$ROOT/node2
CFG=$N/fn.toml
PORT=11318
GROUP=fn.letters
export FN_NATIVE_HOST=$IMG
rm -rf "$N"; mkdir -p "$N"
"$ROOT/fn-native" store "$N/store" init "$GROUP" >/dev/null
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' \
  "$N/store" "$PORT" "$N/control.sock" > "$CFG"
nohup env FN_NATIVE_HOST="$IMG" "$ROOT/fn-native" operator "$CFG" run > "$ROOT/owner2.log" 2>&1 &
OWNER=$!
echo "owner pid=$OWNER"
i=0; while [ $i -lt 60 ]; do [ -S "$N/control.sock" ] && break; i=$((i+1)); sleep 1; done
mkart() {
  printf 'From: gate@example.invalid\r\nSubject: %s\r\nNewsgroups: %s\r\nDate: %s\r\nMessage-ID: %s\r\n\r\n%s\r\n' \
    "$3" "$GROUP" "$2" "$5" "$4" > "$1"
}
post() {
  out=$("$ROOT/fn-native" operator "$CFG" post --message-id "$2" --payload "$1" --group "$GROUP" 2>&1)
  rc=$?
  WORD=$out; RC=$rc
}
echo "gap dates_equal word rc"
t=1
for gap in 0 0.25 0.5 0.75 1.0 1.25 0 0.4 0.8 1.2 0.6 0.9; do
  M="<e4p-$t@example.invalid>"
  F="$N/e4p-$t.article"
  D1=$(date -u '+%a, %d %b %Y %H:%M:%S +0000')
  mkart "$F" "$D1" "gap $gap" "body $t" "$M"
  post "$F" "$M"
  first="$WORD"
  sleep "$gap"
  D2=$(date -u '+%a, %d %b %Y %H:%M:%S +0000')
  mkart "$F" "$D2" "gap $gap" "body $t" "$M"
  post "$F" "$M"
  if [ "$D1" = "$D2" ]; then eq=yes; else eq=NO; fi
  echo "gap=$gap dates_equal=$eq second=[$WORD] rc=$RC first=[$first]"
  t=$((t+1))
done
kill -TERM "$OWNER"
k=0; while [ $k -lt 30 ]; do kill -0 "$OWNER" 2>/dev/null || break; k=$((k+1)); sleep 1; done
kill -0 "$OWNER" 2>/dev/null && echo "owner still alive" || echo "owner exited after ${k}s"
echo "=== status with no owner holding the writer ==="
"$ROOT/fn-native" operator "$CFG" status; echo "status rc=$?"
