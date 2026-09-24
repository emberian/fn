#!/bin/sh
# native-subsets-47bdb9a4 diagnostic runner: run.sh environment, then python3 <script> from the tree root.
# Usage: sh run.sh target [target...]
# NS_TREE=tree (default: the gate copy, tests as of 47bdb9a4) or tree-dev (the
# same tree with tests/ from dev 552c763e: the stale-test fixes and the kind-8 case).
# NS_TAG=x adds .x to the log name. NS_BP_IMAGE=fn-host-dtn-developer for the
# selector cases. The image's SBCL is first on PATH and every opt-in flag is set.
set -u
G=/tank/fn/gates/qual-47bdb9a4-20260924
I=$G/build/images/47bdb9a4
S=/tank/fn/scratch/native-subsets-47bdb9a4
T=$S/${NS_TREE:-tree}
L=$S/logs
mkdir -p "$L"
cd "$T"
h() { awk -v f="$1" '$2==f {print $1}' "$I/image.sha256"; }
export PATH=$S/bin:$PATH
export SBCL_HOME=$I/runtime/sbcl-home/
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$I/fn-host
export FN_NATIVE_DEVELOPER_HOST=$I/fn-host-developer
export FN_NATIVE_CRASH_HOST=$I/fn-host-developer
export FN_NATIVE_DTN_HOST=$I/fn-host-dtn
export FN_NATIVE_DTN_DEVELOPER_HOST=$I/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$I/${NS_BP_IMAGE:-fn-host-dtn}
export FN_NATIVE_CONTACT_SENDER=$I/fn-host-dtn
export FN_NATIVE_CONTACT_RECEIVER=$I/fn-host-dtn
export FN_NATIVE_IMAGE_SOURCE_SHA=47bdb9a40742f0da40e84c21e18175b80af3fb4b
export FN_NATIVE_LAUNCHER_SHA256=$(h fn-host)
export FN_NATIVE_CORE_SHA256=$(h fn-host.core)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$(h fn-host-developer)
export FN_NATIVE_DEVELOPER_CORE_SHA256=$(h fn-host-developer.core)
export FN_NATIVE_RUNTIME_SHA256=$(h runtime/sbcl)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag
for f in TOPIC_LOCAL_E2E TOPIC_METADATA_E2E HYBRID_E2E NATIVE_READER_INDEX \
         CONSUMER_INSPECT CONSUMER_PROJECT_BOUNDS NATIVE_CLONE CONSUMER_E2E \
         CONSUMER_POLL_E2E; do export FN_RUN_$f=1; done
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR"
exec python3 "$@"
