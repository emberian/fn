set -u
# Task 4 of width-producers-2: the served POST (the owner, `operator run`)
# refuses an article whose worst-case figure exceeds the remaining history,
# with its named verdict, and the store reopens.  Developer image of a9ed4dc2
# (the served budget call, host/owner-host.lisp fn-owner-prepare ->
# fn-sbud-article-budget-for, is byte-identical on dev 23eed13e).
IMG=/tank/fn/scratch/bounds-p6/tree-a9ed4dc2/build/fn-host-developer
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 ACL2_CUSTOMIZATION=NONE
unset ACL2_SYSTEM_BOOKS
D=/tank/fn/scratch/width-producers-2/served; rm -rf $D; mkdir -p $D; cd $D
PORT=11297
$IMG --fn store $D/store init --max-transactions 4 --max-history-octets 250000 --max-record-octets 196608 --max-article-octets 150000 --max-groups-per-article 8 --max-open-suffix 4 fn.test > init.out 2>&1; echo "init exit=$?"
$IMG --fn store $D/store status | sed -n 2p | cut -c1-160
printf "[store]\npath = \"%s\"\n[listener]\nhost = \"127.0.0.1\"\nport = %s\n[control]\npath = \"%s\"\n" "$D/store" "$PORT" "$D/control.sock" > fn.toml
systemd-run --user --unit=wp2-served -p MemoryMax=24G --working-directory=$D -E FN_OPENSSL_PREFIX=$FN_OPENSSL_PREFIX -E ACL2_CUSTOMIZATION=NONE $IMG --fn operator $D/fn.toml run > /dev/null 2>&1
sleep 5
python3 ../nntp_post.py $PORT "<served-1@example.invalid>" 149000
python3 ../nntp_post.py $PORT "<served-2@example.invalid>" 149000
systemctl --user stop wp2-served; sleep 1
journalctl --user -u wp2-served --no-pager | tail -5 > node.journal
echo "committed files: $(ls $D/store/transactions | wc -l), octets: $(cat $D/store/transactions/* | wc -c)"
$IMG --fn store $D/store recover; echo "reopen exit=$?"
$IMG --fn store $D/store status | sed -n 1,3p | cut -c1-160
