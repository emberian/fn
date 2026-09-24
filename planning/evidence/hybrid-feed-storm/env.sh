S=/tank/fn/scratch/hybrid-feed-storm
T=$S/tree
G=${G:-/tank/fn/gates/qual-1a9dd747-20260924}
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_TEST_OPENSSL=$FN_OPENSSL_PREFIX/bin/openssl
export FN_NATIVE_SOURCE_ROOT=$T
export FN_NATIVE_HOST=${IMG:-$G/build/fn-host-developer}
export FN_RUN_HYBRID_E2E=1
cd $T
