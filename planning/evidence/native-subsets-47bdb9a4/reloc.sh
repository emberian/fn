#!/bin/sh
# Relocated-image run of test_native_frozen_relocation (same form as the 6c0626c5 run).
S=/tank/fn/scratch/native-subsets-47bdb9a4
cd $S/tree
{ echo "# relocated copy $S/reloc/fn-image; $(cd $S/reloc/fn-image && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"
  env -u LD_LIBRARY_PATH -u FN_OPENSSL_PREFIX -u SBCL_HOME \
    FN_RUN_RELOCATION_E2E=1 FN_NATIVE_HOST=$S/reloc/fn-image/fn-host \
    FN_TEST_OPENSSL=$S/bin/test-openssl timeout 1800 python3 -m unittest -v tests.test_native_frozen_relocation 2>&1
  echo "# rc=$? end $(date -u +%FT%TZ)"
  echo "# after: $(cd $S/reloc/fn-image && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"; } > $S/logs/test_native_frozen_relocation.log
