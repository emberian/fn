#!/bin/sh
# Sizes, RSS and per-invocation wall time: the extracted CHICKEN binary
# against the SBCL developer image, on the same transcripts, pinned to one
# P-core.  Usage: measure.sh IMAGE CHICKEN-DIR TRANSCRIPT-DIR CPU
IMAGE=$1 CD=$2 T=$3 CPU=${4:-6}
LIB=/tank/fn/toolchains/chicken-5.4.0/lib
export LD_LIBRARY_PATH=$LIB
echo "== sizes (bytes)"
ls -l "$IMAGE" "$IMAGE.core" 2>/dev/null | awk '{print $5, $9}'
ls -lL "$CD/served" "$CD/served-static" "$LIB/libchicken.so" 2>/dev/null | awk '{print $5, $9}'
for b in served served-static; do [ -f "$CD/$b" ] && { strip -o "$CD/$b.stripped" "$CD/$b"; ls -l "$CD/$b.stripped" | awk '{print $5, $9}'; }; done
echo "== max RSS (KB) and wall (s), one process per transcript, cpu $CPU"
for n in bare-lf whole reader-commands session-200; do
  s=$( { /usr/bin/time -f "%M %e" taskset -c $CPU env ACL2_CUSTOMIZATION=NONE "$IMAGE" --fn model "$T/$n.chunks" - > /dev/null; } 2>&1 | tail -1)
  c=$( { /usr/bin/time -f "%M %e" taskset -c $CPU "$CD/served-static" model "$T/$n.chunks" > /dev/null; } 2>&1 | tail -1)
  echo "$n sbcl-image $s chicken-static $c"
done
