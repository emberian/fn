S=/tank/fn/scratch/hybrid-feed-storm
export IMG=/tank/fn/gates/hybrid-feed-storm-7837416e/build/fn-host-developer
. $S/env.sh
export FN_NATIVE_DEVELOPER_HOST=$IMG FN_NATIVE_CRASH_HOST=$IMG
export FN_NATIVE_IMAGE_SOURCE_SHA=287c38ed739e27fc3b4e661cf3b2fa28846dcb68
export FN_NATIVE_LAUNCHER_SHA256=$(sha256sum $IMG | cut -d' ' -f1)
export FN_NATIVE_CORE_SHA256=$(sha256sum $IMG.core | cut -d' ' -f1)
export FN_NATIVE_DEVELOPER_LAUNCHER_SHA256=$FN_NATIVE_LAUNCHER_SHA256
export FN_NATIVE_DEVELOPER_CORE_SHA256=$FN_NATIVE_CORE_SHA256
export FN_NATIVE_RUNTIME_SHA256=$(sha256sum /tank/fn/sbcl/bin/sbcl | cut -d' ' -f1)
export FN_NATIVE_TEST_DIAGNOSTIC_DIR=$S/diag/peer
mkdir -p $FN_NATIVE_TEST_DIAGNOSTIC_DIR
L=$S/logs
for m in test_native_peering test_native_protected_peering; do
  log=$L/$m.log
  { echo "# module tests.$m start $(date -u +%FT%TZ)"; env | grep -E '^(FN_|LD_LIBRARY_PATH)' | sort | sed 's/^/# env /'; } > $log
  s=$(date +%s.%N); timeout 1800 python3 -m unittest -v tests.$m >> $log 2>&1; rc=$?; e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f\n' $rc $(echo "$e - $s" | bc) >> $log
  echo "$m rc=$rc $(grep -E '^(Ran|OK|FAILED)' $log | tr '\n' ' ')"
done
sha256sum $L/test_native_peering.log $L/test_native_protected_peering.log
