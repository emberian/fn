# E1 notes to layer A

1. **Unmodified tiny-profile liveness assertion fails.** At `137695dfc`, run
   `fn2-sim-run-echo` with seed 20261028, one safety connection, and
   `*fn2-profile-tiny*` changed only to `:c=1`, `:accept-credits=1`.
   The driver reports `:PASS`, then live accepted 200, echoed 67, dropped 133;
   every live drop is `:unattributed`. Both capacity premises asserted by
   `tests/sim-layer-a-a4-driver.lsp` hold (H4>3; min(O8,QA4)=4 >=2C+credits+1=4).
   The final acceptance assertions at that driver's lines 87–90 do not hold.
   Exact replay reproduced all 25,921 interior records and all 16,923 PRNG
   words, with 47,230 concrete and 47,230 reference transitions in each run.
   See `mutants/qualification-ORIGINAL-20261028.sexp` and its replay.
   This is a bounded-completion applicability/summary defect in the unmodified
   tiny workload, not evidence of a general server safety defect. Investigate
   `sim/echo-evidence.lisp`'s live accept policy and `sim/echo-scenario.lisp`'s
   accepted/drop accounting: a client nonce is counted as accepted before
   listener admission, and reclamation can lag the next physical accept.
   E1 keeps this failure separate from seeded mutation detections; no A file
   was changed and the failing assertion was not removed.
