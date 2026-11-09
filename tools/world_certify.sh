#!/bin/sh
# tools/certify.sh from the saved world images (tools/cert_images.py, its fn2
# section), on the box. Same arguments as certify.sh. ACL2 is the toolchain
# launcher; FN_WORLD_STORE (default ~/fn2-images) holds the images that
# tools/box_world_image_bb2.sh builds; FN_WORLD_IMAGES=off certifies every book
# in the plain world (and removes the tree's .image files).
#  1. Each image root in the closure of the named books that the store has an
#     image of is certified first (smallest first, itself from the images
#     current by then), so its certificate is current when it is keyed.
#  2. world-select writes <book>.image (the image's launcher) for every book
#     of the closure whose largest applicable image matches this tree's key,
#     and removes every other .image: a stale image is never named.
#  3. certify.sh; cert.pl runs the launcher a book's .image names.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/.." && pwd)
store=${FN_WORLD_STORE:-$HOME/fn2-images}
cd "$root"
if [ "${FN_WORLD_IMAGES:-on}" = off ]; then
  python3 tools/cert_images.py world-select --off --store "$store"
  exec sh tools/certify.sh "$@"
fi
# The -j option (if any) for the root phase; every other option stays with
# the final certify.
jobs=
prev=
for arg do
  case "$prev" in -j) jobs="-j $arg" ;; esac
  case "$arg" in -j[0-9]*) jobs=$arg ;; esac
  prev=$arg
done
for book in $(python3 tools/cert_images.py world-roots --store "$store" "$@"); do
  python3 tools/cert_images.py world-select --store "$store" "$book"
  sh tools/certify.sh $jobs "$book"
done
python3 tools/cert_images.py world-select --store "$store" "$@"
exec sh tools/certify.sh "$@"
