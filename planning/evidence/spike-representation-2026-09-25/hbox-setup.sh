#!/bin/sh
# usage: hbox-setup.sh TREE LABEL -- certify the default-profile roots in place (incremental, from the cache), then build the images
set -u
T=$1; L=$2; S=/tank/fn/scratch/spike-representation
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache FN_SPIKE=1
cd $T
python3 tools/proof_artifacts.py roots --profile default 2>/dev/null | grep "^books/\|^tests/" > $S/$L-roots.txt
swarm-build python3 tools/certify_books.py --incremental --jobs 8 --timeout-seconds 1800 $(cat $S/$L-roots.txt) > $S/$L-cert.log 2>&1
echo cert rc=$?; tail -3 $S/$L-cert.log
sh $S/hbox-build.sh $T > $S/$L-build.log 2>&1
echo build rc=$?; tail -3 $S/$L-build.log
echo SETUP-DONE
