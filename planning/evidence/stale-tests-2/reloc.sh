#!/bin/sh
# Relocation module from the lane tree against IMAGE_DIR (arg 1), tag (arg 2); env as native-subsets reloc.sh.
S=/tank/fn/scratch/stale-tests-2; D=$1; TAG=$2
cd $S/treelane
{ echo "# image $D; $(cd $D && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"
  env -u LD_LIBRARY_PATH -u FN_OPENSSL_PREFIX -u SBCL_HOME \
    FN_RUN_RELOCATION_E2E=1 FN_NATIVE_HOST=$D/${NS_VARIANT:-fn-host} \
    FN_TEST_OPENSSL=$S/bin/test-openssl timeout 1800 python3 -m unittest -v tests.test_native_frozen_relocation 2>&1
  echo "# rc=$? end $(date -u +%FT%TZ)"
  echo "# after: $(cd $D && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"; } > $S/logs/test_native_frozen_relocation.$TAG.log
