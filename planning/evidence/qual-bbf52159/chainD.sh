#!/bin/sh
cd /tank/fn/scratch/qual-bbf52159
sh run.sh test_native_checkpoint test_native_compaction_crash_map test_native_cut_map test_native_peering test_native_protected_peering test_native_served_crash_model test_native_tls_transport test_fn_web_native test_checkpoint
sh /tank/fn/scratch/qual-bbf52159/reloc.sh
touch /tank/fn/scratch/qual-bbf52159/done.D
