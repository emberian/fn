#!/bin/sh
# builds the partial core: core-main.lisp with the host-block load wrapped so the save still happens (measurement variant)
T=/tank/fn/scratch/extract-measure/tree; O=/tank/fn/scratch/extract-measure/core-m0
export SBCL_HOME=/tank/fn/sbcl/lib/sbcl/ FN_DEFLATE_LIBRARY=$T/build/lib/libfn-deflate.so FN_MLDSA_LIBRARY=$T/build/lib/libfn-mldsa65.so FN_BLAKE3_LIBRARY=$T/build/lib/libfn-blake3.so
cd $T && XL_OUT=$O/ XL_X=$T/tools/extract/ /tank/fn/sbcl/bin/sbcl --tls-limit 65536 --dynamic-space-size 32000 --control-stack-size 1024KB --non-interactive --no-userinit --load /tank/fn/scratch/extract-measure/core-main-partial.lisp > $O/sbcl-partial.log 2>&1
echo exit $?
