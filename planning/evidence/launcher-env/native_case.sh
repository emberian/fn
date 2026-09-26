#!/bin/sh
# launcher-env native case (PKT-481 (a)); run on hbox from /tank/fn/scratch/launcher-env/tree
set -eu
S=/tank/fn/scratch/launcher-env
REV=dfa810fceabedde937ba7e4bfa46b43fd599ac62
I=/tank/fn/gates/qual-dfa810fc-20260926/build/images/$REV
OLDI=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d
OLDTAR=/tank/fn/scratch/qual-dfa810fc/friends/friend/fn-dfa810fceabe
cd "$S/tree"
env -u FN_NATIVE_HOST sh packaging/release-tarball.sh "$I" "$REV" "$S/release" > "$S/release.log" 2>&1
mkdir -p "$S/install"
(cd "$S/install" && cp "$S/release/fn-dfa810fceabe-linux-x86_64.tar.gz"* . \
  && sha256sum -c fn-dfa810fceabe-linux-x86_64.tar.gz.sha256 && tar xzf fn-dfa810fceabe-linux-x86_64.tar.gz \
  && cd fn-dfa810fceabe && sha256sum -c --quiet SHA256SUMS) >> "$S/release.log" 2>&1
FN=$S/install/fn-dfa810fceabe/bin/fn
cmp "$FN" packaging/fn
{ echo "== installed bin/fn = this lane's packaging/fn: $(sha256sum "$FN")"
  echo "== with FN_NATIVE_HOST=$OLDI/fn-host (bbf52159)"
  FN_NATIVE_HOST=$OLDI/fn-host "$FN" --version; echo "rc=$?"
} > "$S/with-var.log" 2>&1
{ echo "== without FN_NATIVE_HOST"
  env -u FN_NATIVE_HOST "$FN" --version; echo "rc=$?"
} > "$S/without-var.log" 2>&1
set +e
{ echo "== control: the qualification tarball's own (old) bin/fn, same variable"
  echo "$(sha256sum "$OLDTAR/bin/fn")"
  FN_NATIVE_HOST=$OLDI/fn-host "$OLDTAR/bin/fn" --version; echo "rc=$?"
  env -u FN_NATIVE_HOST "$OLDTAR/bin/fn" --version; echo "rc=$?"
} > "$S/control-old-launcher.log" 2>&1
set -e
cd "$S" && sha256sum with-var.log without-var.log control-old-launcher.log release.log | tee SHA256SUMS
