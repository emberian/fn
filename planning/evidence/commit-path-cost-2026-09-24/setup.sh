#!/bin/sh
# usage: setup.sh TREE LABEL  -- certify the image's book roots in place from the cache, then build the developer and profiling images
set -u
T=$1; L=$2; S=/tank/fn/scratch/commit-path-cost
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache
cd $T
sed -n 's/^(include-book "\(books\/[^"]*\)").*/\1/p' host/native/build.lisp > $S/$L-roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 900 $(cat $S/$L-roots.txt) > $S/$L-cert.log 2>&1
echo cert rc=$?; tail -3 $S/$L-cert.log
sh $S/build.sh $T prof > $S/$L-build.log 2>&1
echo build rc=$?; tail -3 $S/$L-build.log
