#!/bin/sh
# Relocated-image run (copy made with cp -a of the frozen image dir) of test_native_frozen_relocation (same form as the 47bdb9a4 run), stdin closed.
S=/tank/fn/scratch/qual-b6759850
rm -rf $S/reloc; mkdir -p $S/reloc; cp -a /tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80 $S/reloc/fn-image
cd $S/tree
{ echo "# relocated copy $S/reloc/fn-image; $(cd $S/reloc/fn-image && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"
  env -u LD_LIBRARY_PATH -u FN_OPENSSL_PREFIX -u SBCL_HOME \
    FN_RUN_RELOCATION_E2E=1 FN_NATIVE_HOST=$S/reloc/fn-image/fn-host \
    FN_TEST_OPENSSL=$S/bin/test-openssl timeout 1800 python3 -m unittest -v tests.test_native_frozen_relocation 2>&1 < /dev/null
  echo "# rc=$? end $(date -u +%FT%TZ)"
  echo "# after: $(cd $S/reloc/fn-image && sha256sum -c --quiet image.sha256 && echo image.sha256 OK)"; } > $S/logs/test_native_frozen_relocation.log
