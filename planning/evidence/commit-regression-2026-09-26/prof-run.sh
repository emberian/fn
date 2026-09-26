#!/bin/sh
# usage: prof-run.sh TREE N MODE OUT  (store on tmpfs; OUT absolute)
set -u
T=$1; N=$2; MODE=$3; OUT=$4
W=/dev/shm/commit-regression/prof-$$; rm -rf $W; mkdir -p $W
export ACL2_CUSTOMIZATION=NONE LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib SBCL_HOME=/tank/fn/sbcl/lib/sbcl/
printf '[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n[control]\npath = "%s"\n' $W/store $W/c.sock > $W/c.toml
$T/build/fn-host-developer --fn operator $W/c.toml init --profile scale --max-transactions 1048576 --max-article-octets 2048 fn.letters fn.test > $W/init.out 2>&1 || { cat $W/init.out; exit 1; }
cd $T
PROF_ROOT=$W/store PROF_N=$N PROF_MODE=$MODE /tank/fn/sbcl/bin/sbcl --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 --disable-ldb --core $T/build/fn-host-developer.core --noinform --end-runtime-options --no-userinit --disable-debugger --load /tank/fn/scratch/commit-regression/prof-probe.lisp > $OUT 2>&1
echo "rc=$?"; rm -rf $W
