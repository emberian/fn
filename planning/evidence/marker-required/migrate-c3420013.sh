#!/bin/sh
# marker-required: the deployed store's migration, rehearsed on copies.
# A store written by the c3420013 production image (the deployed node's:
# format 7, committed-history marker since that deploy) is COPIED and
# migrated by this lane's developer image with
#   operator CONFIG store upgrade-profile --history-marker required
# then damaged two ways.  A second store has its marker one behind (the
# c3420013 developer image killed at marker-created: a durable record whose
# marker never caught up), so the migration's open catches it up first.
# The live node (/tank/fn/node) is not touched.
set -u
S=/tank/fn/scratch/marker-required
OLD=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host
OLDDEV=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host-developer
NEW=$S/src/build/fn-host-developer
NEWPROD=$S/src/build/fn-host
W=$S/migrate; rm -rf $W; mkdir -p $W
export ACL2_CUSTOMIZATION=NONE; unset ACL2_SYSTEM_BOOKS
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
P=11431
ss -ltn | grep -q ":$P " && { echo "port $P busy"; exit 1; }
say() { echo "## $*"; }
toml() { printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[control]\npath = "%s"\n' "$1/store" "$P" "$1/control.sock" > "$1/fn.toml"; }
art() { printf 'From: migrate@campaign.invalid\r\nNewsgroups: fn.letters\r\nSubject: migrate %s\r\nMessage-ID: <migrate-%s@campaign.invalid>\r\n\r\nmigration rehearsal %s\r\n' "$1" "$1" "$1" > "$2"; }
owner() { # img dir tag
  "$1" --fn operator "$2/fn.toml" run > "$2/owner-$3.out" 2> "$2/owner-$3.err" & OP=$!
  i=0; while [ $i -lt 120 ] && ! grep -q '^LISTENING' "$2/owner-$3.out"; do sleep 1; i=$((i+1)); done
  echo "owner $3 pid=$OP $(head -1 $2/owner-$3.out)"; }
stop() { kill -TERM $OP; wait $OP; echo "owner exit $?"; }
post() { # img dir n
  art $3 $2/a$3.art
  "$1" --fn operator "$2/fn.toml" post --message-id "<migrate-$3@campaign.invalid>" --payload $2/a$3.art --group fn.letters; echo "post $3 rc=$?"; }
tree() { echo "transactions: $(ls $1/store/transactions | wc -l)"; [ -f $1/store/committed-history.json ] && echo "marker: sha256 $(sha256sum < $1/store/committed-history.json | cut -c1-16) octets $(stat -c %s $1/store/committed-history.json)" || echo "marker: ABSENT"; echo "config: sha256 $(sha256sum < $1/store/config.json | cut -c1-16)"; }
status() { "$1" --fn operator "$2/fn.toml" status | grep -E '^profile|^headroom' ; }
say "images"; sha256sum $OLD.core $OLDDEV.core $NEW.core $NEWPROD.core
say "1. the deployed kind of store: c3420013 production, init, three posts through its owner"
mkdir -p $W/orig; "$OLD" --fn store $W/orig/store init fn.letters; echo "init rc=$?"
toml $W/orig; owner $OLD $W/orig old
for n in 1 2 3; do post $OLD $W/orig $n; done
stop; tree $W/orig; status $OLD $W/orig
say "2. copy; the new image reads it as format 7, unmarked"
cp -a $W/orig $W/copy; toml $W/copy
status $NEW $W/copy
say "3. migrate: store upgrade-profile --history-marker required"
cp -a $W/copy $W/copy-before
"$NEW" --fn operator $W/copy/fn.toml store upgrade-profile --history-marker required; echo "upgrade rc=$?"
tree $W/copy; status $NEW $W/copy
"$NEW" --fn store $W/copy/store recover; echo "reopen rc=$?"
say "3a. a downgrade is refused"
"$NEW" --fn operator $W/copy/fn.toml store upgrade-profile --history-marker unmarked; echo "downgrade rc=$?"
say "3b. the old image cannot open the migrated store (no rollback in place: restore the copy)"
"$OLD" --fn store $W/copy/store recover; echo "c3420013 open of migrated rc=$?"
say "4. the served owner of the new production image serves the migrated store"
owner $NEWPROD $W/copy newprod; post $NEWPROD $W/copy 4; stop; tree $W/copy
say "5. the newest transaction file deleted: damage"
cp -a $W/copy $W/loss
N=$(ls $W/loss/store/transactions | sort | tail -1); echo "deleting transactions/$N"; rm $W/loss/store/transactions/$N
"$NEW" --fn store $W/loss/store recover; echo "open after loss rc=$?"
"$NEWPROD" --fn store $W/loss/store recover; echo "production open after loss rc=$?"
say "6. the marker deleted: damage, not legacy"
cp -a $W/copy $W/nomarker; rm $W/nomarker/store/committed-history.json
"$NEW" --fn store $W/nomarker/store recover; echo "open without marker rc=$?"
say "6a. contrast: the unmigrated copy with its marker deleted opens (legacy) and the open writes it"
cp -a $W/copy-before $W/legacy; rm $W/legacy/store/committed-history.json
"$NEW" --fn store $W/legacy/store recover; echo "legacy open rc=$?"; tree $W/legacy
say "7. a c3420013 store whose marker is behind (developer image, killed at marker-created)"
mkdir -p $W/behind; "$OLD" --fn store $W/behind/store init fn.letters; toml $W/behind
owner $OLD $W/behind old; for n in 1 2; do post $OLD $W/behind $n; done; stop
art 3 $W/behind/a3.art
FN_NATIVE_POST_FAULT=marker-created:kill "$OLDDEV" --fn store $W/behind/store post "<migrate-3@campaign.invalid>" $W/behind/a3.art - - fn.letters; echo "killed post rc=$?"
tree $W/behind
cp -a $W/behind $W/behind-orig
"$NEW" --fn operator $W/behind/fn.toml store upgrade-profile --history-marker required; echo "upgrade rc=$?"
tree $W/behind; status $NEW $W/behind
"$NEW" --fn store $W/behind/store post "<migrate-3@campaign.invalid>" $W/behind/a3.art - - fn.letters; echo "retry rc=$?"
N=$(ls $W/behind/store/transactions | sort | tail -1); rm $W/behind/store/transactions/$N
"$NEW" --fn store $W/behind/store recover; echo "open after loss rc=$?"
say "8. the originals are untouched"; tree $W/orig; tree $W/behind-orig
echo MIGRATE-DONE
