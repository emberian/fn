# qual-harness-c18: qual-b6759850's env.sh with S set to this lane's scratch; the images are the frozen gate's.
# qual-b6759850: common paths and the test environment (sourced by every runner).
REV=b675985074cf14b009204f6eb3e5409f4a025a80
G=/tank/fn/gates/qual-b6759850-20260926
I=$G/build/images/$REV
OLDI=/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d
C342=/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013
S=/tank/fn/scratch/qual-harness-c18
T=${NS_TREE:-$S/tree}
h() { awk -v f="$1" '$2==f {print $1}' "$I/image.sha256"; }
export PATH=$S/bin:$PATH
export SBCL_HOME=$I/runtime/sbcl-home/
export PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_CERT_CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=$I/${NS_HOST:-fn-host}
export FN_FORMAT7_IMAGE=$C342/fn-host
export FN_OLD_NATIVE_HOST=$C342/fn-host
export FN_NATIVE_DEVELOPER_HOST=$I/fn-host-developer
export FN_NATIVE_CRASH_HOST=$I/fn-host-developer
export FN_NATIVE_DTN_HOST=$I/fn-host-dtn
export FN_NATIVE_DTN_DEVELOPER_HOST=$I/fn-host-dtn-developer
export FN_NATIVE_BP_HOST=$I/${NS_BP_IMAGE:-fn-host-dtn}
export FN_NATIVE_BP_NODE_HOST=$I/${NS_BP_NODE_IMAGE:-fn-host-dtn-developer}
export FN_NATIVE_CONTACT_SENDER=$I/${NS_BP_IMAGE:-fn-host-dtn}
export FN_NATIVE_CONTACT_RECEIVER=$I/${NS_BP_IMAGE:-fn-host-dtn}
export FN_NATIVE_IMAGE_SOURCE_SHA=b6759850
export FN_NATIVE_LAUNCHER_SHA256=$(h fn-host)
export FN_NATIVE_CORE_SHA256=$(h fn-host.core)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$(h fn-host-developer)
export FN_NATIVE_DEVELOPER_CORE_SHA256=$(h fn-host-developer.core)
export FN_NATIVE_RUNTIME_SHA256=$(h runtime/sbcl)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag/${NS_TAG:-x}
export FN_D23_VERIFY=1
export FN_TEST_OPENSSL=$S/bin/test-openssl
export FN_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl
export FN_INN_SRC=/tank/fn/inn/2.7.4
export FN_DTN7_REPO=/tank/fn/dtn7/repo
export FN_NATIVE_READER_HOST=$I/fn-host-developer
for f in TOPIC_LOCAL_E2E TOPIC_METADATA_E2E HYBRID_E2E NATIVE_READER_INDEX \
         CONSUMER_INSPECT CONSUMER_PROJECT_BOUNDS NATIVE_CLONE CONSUMER_E2E \
         CONSUMER_POLL_E2E VERIFY_E2E CONSUMER_EXCHANGE; do export FN_RUN_$f=1; done
mkdir -p "$FN_NATIVE_TEST_DIAGNOSTIC_DIR"
