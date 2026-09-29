#!/bin/sh
# tools/extract/world_image.sh TREE -- print the path of a saved ACL2 image
# holding the extraction world (tools/extract/world.lisp and world-host.lisp
# loaded), building it once per world: the cache key is the SHA-256 over the
# two world files, every host file they load and every certificate they
# include (tools/extract/world.py --digest), so a changed book, cert or host
# file is a new image.  Loading the world is 12-20 min of redundant
# include-books; a cached image starts it in a second.  build.sh and core.sh
# use it; FN_EXTRACT_WORLD_CACHE (default /tank/fn/scratch/extract-cache)
# holds the images.  A failed save leaves no image and exits 1.
set -eu
TREE=$(cd "$1" && pwd)
ACL2=${FN_EXTRACT_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g-tls64k}
CACHE=${FN_EXTRACT_WORLD_CACHE:-/tank/fn/scratch/extract-cache}
KEY=$(python3 "$TREE/tools/extract/world.py" --digest "$TREE")
DIR=$CACHE/world-$KEY
if [ -x "$DIR/world" ] && [ -f "$DIR/world.core" ]; then
    echo "$DIR/world"; exit 0
fi
mkdir -p "$CACHE"
TMP=$(mktemp -d "$CACHE/.world-XXXXXX")
cat > "$TMP/save.lsp" <<LSP
(ld "tools/extract/world.lisp")
(ld "tools/extract/world-host.lisp")
:q
(save-exec "$TMP/world" "fn extraction world $KEY")
LSP
( cd "$TREE" && swarm-build "$ACL2" < "$TMP/save.lsp" > "$TMP/save.log" 2>&1 ) || true
if grep -q "ACL2 Error" "$TMP/save.log" || [ ! -f "$TMP/world.core" ]; then
    echo "world_image: the world did not load; see $TMP/save.log" >&2; exit 1
fi
# the launcher names the core by its path: rewrite it for the final directory
sed "s|$TMP|$DIR|g" "$TMP/world" > "$TMP/world.new" && mv "$TMP/world.new" "$TMP/world" && chmod +x "$TMP/world"
mv "$TMP" "$DIR" 2>/dev/null || { rm -rf "$TMP"; }   # another build won the race
echo "$DIR/world"
