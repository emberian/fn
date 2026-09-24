S=/tank/fn/scratch/probe-tables
GT=/tank/fn/gates/qual-6c0626c5-20260924
G=$GT/build/images/6c0626c5
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib
export FN_NATIVE_SOURCE_ROOT=$GT
export PYTHONDONTWRITEBYTECODE=1
export FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
cd $S/tree
