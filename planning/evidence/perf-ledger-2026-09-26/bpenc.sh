#!/bin/sh
# usage: bpenc.sh CORE -- load bpenc.lisp into the image's raw Lisp and exit (no fnn-main)
export SBCL_HOME=/tank/fn/sbcl/lib/sbcl/
exec /tank/fn/sbcl/bin/sbcl --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 --disable-ldb --core "$1" --noinform --end-runtime-options --no-userinit --eval '(load "/tank/fn/scratch/perf-ledger/bpenc.lisp")' --eval '(sb-ext:exit :code 0 :abort t)' --disable-debugger --end-toplevel-options
