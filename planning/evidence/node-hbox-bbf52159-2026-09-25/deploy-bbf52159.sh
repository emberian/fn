#!/bin/sh
# deploy-bbf52159.sh PHASE : the in-place shape for bbf52159 (qualified by qual-bbf52159).
# Run ON HBOX. PHASE 1 = install, start on the format-7 store, verify.
# PHASE 2 = stop, snapshot, keep config.json.format-7, upgrade-profile (format 8, unmarked), verify, start.
set -eu
PHASE=$1
REV=bbf52159dcab19228bd6cd0b855b99dd6d68758d; SHORT=bbf52159
GATE=/tank/fn/gates/qual-$SHORT-20260925; IMG=$GATE/build/images/$REV; NODE=/tank/fn/node; REL=$NODE/fn-$SHORT
UNIT=$HOME/.config/systemd/user/fn-node.service
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib
FN="$REL/bin/fn operator $NODE/fn.toml"
if [ "$PHASE" = 1 ]; then
  (cd "$IMG" && sha256sum -c image.sha256 >/dev/null) && echo "image digests ok" || { echo "DIGEST FAIL"; exit 2; }
  cd "$GATE"
  if [ -x "$REL/bin/fn" ]; then echo "already installed $REL"; else
    FN_NATIVE_HOST=$IMG/fn-host FN_NATIVE_SOURCE_REVISION=$REV PREFIX=$REL sh packaging/install-native.sh >/dev/null && echo "installed $REL"; fi
  # The production image refuses developer selectors (exit 5).  `status` is no
  # probe here: with the old owner running it answers "refused" (exit 1) first.
  FN_STORE_TEST_STOP=x "$REL/bin/fn" --version >/dev/null 2>&1 && rc=0 || rc=$?; echo "refusal probe exit $rc (5 expected)"; [ "$rc" -eq 5 ] || exit 3
  cp "$UNIT" "$UNIT.pre-$SHORT"
  systemctl --user stop fn-node.service; sleep 2
  sed -i "s#^Description=.*#Description=fn native news node ($SHORT)#; s#^ExecStart=.*#ExecStart=$REL/bin/fn operator $NODE/fn.toml run#" "$UNIT"
  grep -E '^(Description|ExecStart)=' "$UNIT"
  systemctl --user daemon-reload
  systemctl --user start fn-node.service; sleep 8
  echo "active: $(systemctl --user is-active fn-node.service)"
  ss -ltn | grep ':1119 ' || true
  $FN status 2>&1 | head -8
fi
if [ "$PHASE" = 2 ]; then
  systemctl --user stop fn-node.service; sleep 2
  SNAP=$NODE/store.snapshot-pre-$SHORT-format8
  [ -e "$SNAP" ] && { echo "snapshot exists: $SNAP"; exit 4; }
  cp -a "$NODE/store" "$SNAP" && echo "snapshot $SNAP"
  cp -p "$NODE/store/config.json" "$NODE/store/config.json.format-7" && echo "kept config.json.format-7"
  $FN store upgrade-profile 2>&1 | tail -2
  $FN store needs-upgrade 2>&1 | tail -1
  $FN store rollback-check "$NODE/store/config.json.format-7" 2>&1 | tail -1
  $FN status 2>&1 | grep -E 'format=|history-marker' | head -3
  systemctl --user start fn-node.service; sleep 8
  echo "active: $(systemctl --user is-active fn-node.service)"
  ss -ltn | grep ':1119 ' || true
  journalctl --user -u fn-node.service --since '-30s' --no-pager 2>/dev/null | tail -3 || true
fi
