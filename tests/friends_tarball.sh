#!/bin/sh
# The friend's install step, scripted (PKT-400's repeatable session): freeze
# the production image of one built tree, package the release tarball, unpack
# it under a scratch prefix exactly as docs/peering-with-a-friend.md section 1
# says (sum, unpack, SHA256SUMS), and run tests.test_native_friends_feed with
# the friend's node on the tarball's bin/fn and the author on FN_NATIVE_HOST.
#
#   sh tests/friends_tarball.sh TREE REV SCRATCH
#
# TREE is a tree whose build/ holds fn-host (production) and
# fn-host-developer (tools/hbox_native.sh --images developer,production);
# REV its 40-digit source revision; SCRATCH an absolute, absent directory
# (never /tank/fn/node).  The system provides libssl (OpenSSL 3.0+); the
# tarball bundles no TLS library (HST-016).  Prints the tarball's SHA-256
# and the module's result; exit is the module's.  The install is --reader
# too: before `mission' it only says to run it again; after, the node's
# fn.toml gains one [web] table (the node's own web face), and a third run
# leaves it as it is.
#
# The freeze bundles the glibc-floor SBCL runtime (packaging/floor-runtime.sh's
# output, the build's SBCL rebuilt on glibc 2.36): the package's runpath step
# (tools/runpath_check.py GLIBC_FLOOR) refuses the build host's own runtime.
# FN_FREEZE_RUNTIME names it; unset, it is hbox's floor runtime, the one
# tools/cut_release.sh bundles.  Refused by name (exit 4) when it is absent.
set -eu
[ "$#" -eq 3 ] || { echo 'usage: friends_tarball.sh TREE REV SCRATCH' >&2; exit 2; }
tree=$1 rev=$2 scratch=$3
case $scratch in /tank/fn/node*) echo 'friends_tarball: never the live node' >&2; exit 2;; /*) ;; *) echo 'friends_tarball: SCRATCH must be absolute' >&2; exit 2;; esac
[ ! -e "$scratch" ] || { echo "friends_tarball: exists: $scratch" >&2; exit 4; }
short=$(printf '%s' "$rev" | cut -c1-12)
runtime=${FN_FREEZE_RUNTIME:-/tank/fn/scratch/glibc-floor/runtime-2.6.8/sbcl}
[ -x "$runtime" ] || {
  echo "friends_tarball: no glibc-floor SBCL runtime at $runtime (packaging/floor-runtime.sh builds one; FN_FREEZE_RUNTIME names it)" >&2; exit 4; }
mkdir -p "$scratch"
cd "$tree"
FN_FREEZE_VARIANTS='fn-host fn-host-developer' FN_FREEZE_RUNTIME=$runtime \
  sh packaging/freeze-native-image.sh "$tree/build" "$scratch/frozen"
sh packaging/release-tarball.sh --frozen "$scratch/frozen" linux-x86_64 "$rev" "$scratch/release"
# The --frozen form's name: fn-VERSION+REV12-PLATFORM.tar.gz (VERSION from this tree).
name=fn-$(sed -n 1p VERSION)+$short-linux-x86_64.tar.gz
# The friend's side: no checkout, only the tarball and SHA256SUMS
# (docs/install.md section 1; --no-service: the harness runs the node).
mkdir -p "$scratch/friend"
cp "$scratch/release/$name" "$scratch/release/SHA256SUMS" "$scratch/friend/"
(cd "$scratch/friend" && sha256sum -c --ignore-missing SHA256SUMS \
   && tar xzf "$name" \
   && sh fn/install.sh --prefix "$scratch/friend/opt/fn" --node "$scratch/friend/node" --no-service --reader)
echo "friends_tarball: installed $scratch/friend/opt/fn"
# The web face is the node's: `mission' writes fn.toml, then --reader adds
# [web] to it, once (docs/web.md 1).
friend=$scratch/friend
[ ! -e "$friend/node/fn.toml" ] || { echo 'friends_tarball: fn.toml before mission' >&2; exit 4; }
"$friend/opt/fn/bin/fn" operator "$friend/node/fn.toml" mission small-community --host 127.0.0.1 --port 11919
for round in 1 2; do
  sh "$friend/opt/fn/install.sh" --prefix "$friend/opt/fn" --node "$friend/node" --no-service --reader
done
[ "$(grep -c '^\[web\]' "$friend/node/fn.toml")" = 1 ] && grep -q '^port = 8920$' "$friend/node/fn.toml" \
  && grep -q '^proxied = true$' "$friend/node/fn.toml" || {
  echo 'friends_tarball: --reader did not add exactly one [web] table' >&2; exit 4; }
[ -s "$friend/opt/fn/share/fn/caddy/fn-web.caddy" ] && [ ! -e "$friend/opt/fn/clients/bin/fn-reader" ] || {
  echo 'friends_tarball: the release still ships the Python reader, or no Caddy block' >&2; exit 4; }
python3 tools/runpath_check.py --quiet --tree "$friend/opt/fn"
echo "friends_tarball: --reader turned on the node's web face"
FN_NATIVE_HOST="$scratch/frozen/fn-host-developer" \
FN_FRIEND_FN="$scratch/friend/opt/fn/bin/fn" \
  python3 -m unittest -v tests.test_native_friends_feed
