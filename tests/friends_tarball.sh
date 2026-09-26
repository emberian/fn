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
# (never /tank/fn/node).  Needs FN_OPENSSL_PREFIX (the OpenSSL 3.5 pair the
# freeze copies).  Prints the tarball's SHA-256 and the module's result;
# exit is the module's.
set -eu
[ "$#" -eq 3 ] || { echo 'usage: friends_tarball.sh TREE REV SCRATCH' >&2; exit 2; }
tree=$1 rev=$2 scratch=$3
case $scratch in /tank/fn/node*) echo 'friends_tarball: never the live node' >&2; exit 2;; /*) ;; *) echo 'friends_tarball: SCRATCH must be absolute' >&2; exit 2;; esac
[ ! -e "$scratch" ] || { echo "friends_tarball: exists: $scratch" >&2; exit 4; }
: "${FN_OPENSSL_PREFIX:?set FN_OPENSSL_PREFIX to the OpenSSL 3.5 prefix}"
short=$(printf '%s' "$rev" | cut -c1-12)
mkdir -p "$scratch"
cd "$tree"
FN_FREEZE_VARIANTS='fn-host fn-host-developer' \
  sh packaging/freeze-native-image.sh "$tree/build" "$scratch/frozen" "$FN_OPENSSL_PREFIX"
sh packaging/release-tarball.sh "$scratch/frozen" "$rev" "$scratch/release"
# The friend's side: no checkout, only the tarball and its sum.
mkdir -p "$scratch/friend"
cp "$scratch/release/fn-$short-linux-x86_64.tar.gz" \
   "$scratch/release/fn-$short-linux-x86_64.tar.gz.sha256" "$scratch/friend/"
(cd "$scratch/friend" && sha256sum -c "fn-$short-linux-x86_64.tar.gz.sha256" \
   && tar xzf "fn-$short-linux-x86_64.tar.gz" \
   && cd "fn-$short" && sha256sum -c --quiet SHA256SUMS)
echo "friends_tarball: installed $scratch/friend/fn-$short"
FN_NATIVE_HOST="$scratch/frozen/fn-host-developer" \
FN_FRIEND_FN="$scratch/friend/fn-$short/bin/fn" \
  python3 -m unittest -v tests.test_native_friends_feed
