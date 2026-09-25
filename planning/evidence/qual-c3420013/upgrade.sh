#!/bin/sh
# qual-c3420013 upgrade rehearsal: a store made by the 4eca4148 production image
# (no committed-history marker), COPIED, opened by the c3420013 production image.
set -u
S=/tank/fn/scratch/qual-c3420013
OLD=/tank/fn/gates/qual-4eca4148-20260924/build/images/4eca4148/fn-host
NEW=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host
W=$S/upgrade; rm -rf $W; mkdir -p $W/orig
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
P=11397
ss -ltn | grep -q ":$P " && { echo "port $P busy"; exit 1; }
say() { echo "## $*"; }
toml() { printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' "$1/store" "$P" "$1/control.sock" > "$1/fn.toml"; }
art() { printf 'From: upgrade@campaign.invalid\r\nNewsgroups: fn.letters\r\nSubject: upgrade %s\r\nMessage-ID: <upgrade-%s@campaign.invalid>\r\n\r\nupgrade rehearsal %s\r\n' "$1" "$1" "$1" > "$2"; }
owner() { # img dir tag
  "$1" --fn operator "$2/fn.toml" run > "$2/owner-$3.out" 2> "$2/owner-$3.err" & OP=$!
  i=0; while [ $i -lt 120 ] && ! grep -q '^LISTENING' "$2/owner-$3.out"; do sleep 1; i=$((i+1)); done
  echo "owner $3 pid=$OP $(head -1 $2/owner-$3.out)"; }
stop() { kill -TERM $OP; wait $OP; echo "owner exit $?"; }
post() { # img dir n
  art $3 $2/a$3.art
  "$1" --fn operator "$2/fn.toml" post --message-id "<upgrade-$3@campaign.invalid>" --payload $2/a$3.art --group fn.letters; echo "post $3 rc=$?"; }
tree() { echo "files: $(cd $1/store && ls | tr '\n' ' ')"; echo "transactions: $(ls $1/store/transactions | wc -l)"; [ -f $1/store/committed-history.json ] && echo "marker: $(cat $1/store/committed-history.json)" || echo "marker: ABSENT"; }
say "old image $OLD"; sha256sum $OLD $OLD.core $NEW $NEW.core
say "1. store made by 4eca4148: init, three posts through its owner"
"$OLD" --fn store $W/orig/store init fn.letters; echo "init rc=$?"
toml $W/orig; owner $OLD $W/orig old
for n in 1 2 3; do post $OLD $W/orig $n; done
stop; tree $W/orig
say "2. copy (cp -a) and open with c3420013 production"
cp -a $W/orig $W/copy; toml $W/copy
"$NEW" --fn store $W/copy/store recover; echo "first open (recover) rc=$?"; tree $W/copy
owner $NEW $W/copy new1; tree $W/copy
say "3. one post through the c3420013 owner"
post $NEW $W/copy 4
stop; tree $W/copy
say "4. next open admits it"
"$NEW" --fn store $W/copy/store recover; echo "second open (recover) rc=$?"
owner $NEW $W/copy new2; printf 'GROUP fn.letters\r\nQUIT\r\n' | timeout 10 nc -q 2 127.0.0.1 $P; stop
cp -a $W/copy $W/copy-before-loss
say "5. newest transaction file deleted"
N=$(ls $W/copy/store/transactions | sort | tail -1); echo "deleting transactions/$N"; rm $W/copy/store/transactions/$N; tree $W/copy
"$NEW" --fn store $W/copy/store recover; echo "open after loss (recover) rc=$?"
"$NEW" --fn operator $W/copy/fn.toml run > $W/copy/owner-lost.out 2> $W/copy/owner-lost.err & OP=$!
i=0; while [ $i -lt 60 ] && kill -0 $OP 2>/dev/null && ! grep -q '^LISTENING' $W/copy/owner-lost.out; do sleep 1; i=$((i+1)); done
if kill -0 $OP 2>/dev/null; then echo "owner after loss STILL RUNNING: $(cat $W/copy/owner-lost.out)"; kill -TERM $OP; wait $OP; else wait $OP; echo "owner after loss exit $?"; fi
echo "owner-lost stdout: $(cat $W/copy/owner-lost.out)"; echo "owner-lost stderr: $(tail -3 $W/copy/owner-lost.err)"
say "6. the original 4eca4148 store is untouched"; tree $W/orig
echo UPGRADE-DONE
