#!/bin/sh
# Byte-compare the CHICKEN `post' verb with the SBCL reference files
# (tools/extract/post-ref.lisp wrote REF-DIR/NAME.sbcl).
# Usage: compare-post.sh CHICKEN-BINARY TRANSCRIPT-DIR REF-DIR
CHK=$1 DIR=$2 REF=$3
agree=0 differ=0
for f in "$DIR"/post/*.chunks; do
  n=$(basename "$f" .chunks)
  "$CHK" post "$f" > "$REF/$n.chicken" 2> "$REF/$n.chicken.err"
  if [ $? = 0 ] && cmp -s "$REF/$n.sbcl" "$REF/$n.chicken"; then agree=$((agree+1)); v=IDENTICAL; else differ=$((differ+1)); v=DIFFER; fi
  printf '%-16s %5s bytes sbcl %s  %s\n' "$n" "$(wc -c < "$REF/$n.sbcl")" "$(sha256sum < "$REF/$n.sbcl" | cut -c1-16)" "$v"
done
echo "== $agree identical, $differ differ"
