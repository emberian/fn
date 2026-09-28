#!/bin/sh
# Byte-compare the extracted CHICKEN model with the SBCL image's model on
# every transcript.  Usage: compare.sh IMAGE CHICKEN-BINARY TRANSCRIPT-DIR OUT-DIR
# Needs LD_LIBRARY_PATH to reach libchicken.so when the binary is dynamic.
# Exits 1 if any transcript differs or there is none.
IMAGE=$1 CHK=$2 DIR=$3 OUT=$4
mkdir -p "$OUT"
agree=0 differ=0
for f in "$DIR"/*.chunks; do
  [ -f "$f" ] || continue
  n=$(basename "$f" .chunks)
  env ACL2_CUSTOMIZATION=NONE "$IMAGE" --fn model "$f" - > "$OUT/$n.sbcl" 2> "$OUT/$n.sbcl.err"
  s1=$?
  "$CHK" model "$f" > "$OUT/$n.chicken-model" 2> "$OUT/$n.chicken.err"
  s2=$?
  "$CHK" socket "$f" > "$OUT/$n.chicken-socket" 2>> "$OUT/$n.chicken.err"
  s3=$?
  if cmp -s "$OUT/$n.sbcl" "$OUT/$n.chicken-model" && cmp -s "$OUT/$n.sbcl" "$OUT/$n.chicken-socket" && [ $s1$s2$s3 = 000 ]; then
    agree=$((agree+1)); v=IDENTICAL
  else
    differ=$((differ+1)); v="DIFFER (exit $s1/$s2/$s3)"
  fi
  printf '%-18s %6s bytes sbcl %s  %s\n' "$n" "$(wc -c < "$OUT/$n.sbcl")" "$(sha256sum < "$OUT/$n.sbcl" | cut -c1-16)" "$v"
done
echo "== $agree identical, $differ differ"
# Exit 0 only when every transcript was compared and none differs.
[ "$differ" = 0 ] && [ "$agree" -gt 0 ]
