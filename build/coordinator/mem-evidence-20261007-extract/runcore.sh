#!/bin/sh
# usage: runcore.sh CORE SCRIPT OUT TLS  -- run a measurement script in CORE (heap 1068MB), no fn start. INV_OUT=OUT
export SBCL_HOME=/tank/fn/sbcl/lib/sbcl/ INV_OUT=$3
exec /tank/fn/sbcl/bin/sbcl --tls-limit $4 --dynamic-space-size 1068MB --control-stack-size 1024KB --core $1 --noinform --end-runtime-options --no-userinit --no-sysinit --disable-debugger --load $2 --end-toplevel-options
