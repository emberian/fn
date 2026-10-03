# sweep-store lanedump (wind-down 2026-10-03)

Branch lane/sweep-store, head ecf40c2bd (origin/dev merged in). Worktree build/lanes/sweep-store.

## Done on the branch (REPL-admitted; natives NOT yet green; certify run-20261003T021247Z-f94e on hbox in flight)
- r72-F1: fnn-log-complete-rotation completes only an all-zero (proven empty) misaligned segment; any nonzero octet -> open refused reason=segment-misaligned, nothing written (fn-store-log-partial-segment-verdict in host/store-host.lisp). Native tests in tests/test_native_initializer_fidelity.py.
- r72-F3: checkpoint plan takes the FNSI image header once (at-start flag). Native test in test_native_state_checkpoint.py.
- r72-F8/S047: recover tail zeroed from a 1 MiB reusable buffer; fd closed on failure. r72-F11: open-segment/scan fd cleanup.
- S045: books/store-checkpoint-verify.lisp (KEYSTONE fn-sccv-final-ok-is-runs-ok, twin fn-sccv-step-is-seg-step), PRF-1241; staged checkpoint read back before rename (fnn-state-checkpoint-verify); selector FN_NATIVE_STATE_CHECKPOINT_READBACK_FLIP + native test. store-checkpoint-reader exports two lemmas (disabled at its end).
- S048: books/store-log-entry-bound.lisp (fn-lgw/fn-lgdm-entry-len-bounded, keystones *-bounded-step), PRF-1250; native+extracted callers switched; tests/acl2/store-log-entry-bound-tests.lisp (removal witness for the kind-octet hypothesis still missing).
- S040/S124: quarantine via .stage-NAME + rename, idempotent (native + extracted); native test in test_native_log_damage.py.
- S116, S039 (extracted frontier joins config txids), S012 (probe developer-only, COUNT natural; doc), X09 (fnn-log-parent = fnn-parent; tests/test_log_parent.py), FN_NATIVE_POST_FAULT log-written|log-fenced:stop (S060 support; native test).

## NEXT
1. hbox interfaces-check failed: planning/interfaces.json stale (two entry-len declarations removed). Run `tools/remote_check.sh hbox --cmd 'python3 tools/interface_emit.py --write && python3 tools/ledger.py --write' --fetch planning/interfaces.json --fetch tools/extract/roots.sh --fetch planning/ledger.json` (a run b1i5fs07m was started, result unread), commit, then rerun natives:
   tools/hbox_native.sh --box hbox --detach --allow-skips --images developer,production,dtn-developer HEAD tests.test_native_initializer_fidelity tests.test_native_state_checkpoint tests.test_native_log tests.test_native_log_damage tests.test_native_recovery tests.test_native_crash_model tests.test_native_checkpoint tests.test_native_commit_log tests.test_log_parent
2. Collect certify: python3 tools/farm.py wait hbox run-20261003T021247Z-f94e.
3. Not started: Chicken LZ4 (fn-xw-compress -> fail-closed refusal or DEFLATE; drop libfn-lz4 from tools/extract/build.sh, chicken.py, gate.py, hostio.scm), r72-F5 export parent fence, S011, S013, S041, S046, S049, S069-S078, S117-S119, S125, S147. S050 moved to RECLAIM-RETENTION.
