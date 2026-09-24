S=/tank/fn/scratch/hybrid-feed-storm
export IMG=/tank/fn/gates/hybrid-feed-storm-7837416e/build/fn-host-developer
. $S/env.sh
export FN_NATIVE_DEVELOPER_HOST=$IMG FN_NATIVE_CRASH_HOST=$IMG
L=$S/logs; mkdir -p $L
i=0
for t in test_authored_carrier_survives_native_peering_and_receiver_restart test_unenrolled_receiver_refuses_authored_carrier_once_and_both_sides_log_it; do
  i=$((i+1)); rm -rf $S/diag/k$i
  timeout 300 python3 $S/hyb_diag2.py $S/diag/k$i $t > $L/diag-k$i.log 2>&1; echo "diag k$i $t rc=$?"
done
for m in test_native_hybrid_author test_native_peering test_native_protected_peering; do
  log=$L/$m.log
  { echo "# module tests.$m image $IMG start $(date -u +%FT%TZ)"; env | grep -E '^(FN_|LD_LIBRARY_PATH)' | sort | sed 's/^/# env /'; } > $log
  s=$(date +%s.%N); timeout 1800 python3 -m unittest -v tests.$m >> $log 2>&1; rc=$?; e=$(date +%s.%N)
  printf '# rc=%s wall=%.1f\n' $rc $(echo "$e - $s" | bc) >> $log
  echo "$m rc=$rc $(grep -E '^(Ran|OK|FAILED)' $log | tr '\n' ' ')"
done
sha256sum $L/*.log $S/diag/k1/*.stderr $S/diag/k2/*.stderr $S/diag/k2/root/service.log $S/diag/k2/root/receiver.log $S/diag/k1/root/service.log
