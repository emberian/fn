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

2. **Pass 2 separates missing admission capacity from attribution.** The first
   live drop at seed 20261028 is an executed refusal, not merely a counter:
   turn 54 finishes echoing old capability (0,3) and physically accepts (0,4);
   turn 56 `fn2-listener-admit` sees free-head 4294967295 and active=capacity=1;
   turn 58 the server closes (0,4); turn 59 its unchanged-nonce client drops with
   703 bytes supplied and zero echoed. QA=5 repeats exactly the QA=4 witness,
   although min(O8,QA5)=5 is strictly greater than the required 4. The observed
   294 post-profile records are equal. Thus equality in the capacity premise
   is not the cause. C.3 itself promises scheduling opportunities conditional
   on dependencies/reservations; the A4 all-physical-Accepts-echo extension
   lacks an admission reservation premise. `echo-scenario.lisp:79-83` gives
   the real refusal the imprecise `:unattributed` label, and `:334-335` accepts
   echoed+dropped reaching the target. Renaming that label cannot recover the
   missing 703 bytes. See [the executed witness and source analysis](mutants/PASS2-LIVENESS.md).
   Track physical accepts, admitted connections and refused connections
   separately; state reserved admission capacity if completion is promised
   for every physical accept. This diagnoses the first drop, not all 133.
