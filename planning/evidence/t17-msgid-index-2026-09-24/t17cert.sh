#!/bin/sh
cd /tank/fn/scratch/t17/after-tree
FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g FN_CERT_CACHE=/tank/fn/certcache swarm-build python3 tools/certify_books.py --incremental --jobs 4 --timeout-seconds 600 $(tail -1 /tank/fn/scratch/t17/roots.txt)
