# lock-disc continuation
Head f663c4829 on lane/lock-discipline (pushed). Gate evidence: /tmp/lockdisc-gate.txt. Mutant harness: /tmp/lockdisc-mut.py (copies tools/ to /tmp/lockdisc-mut/*; 7 baseline test failures there are env noise, ignore).
Done: ParamRoutePruning + FletLambdaInlining test classes; write-scan fix (multiple-value-setq, psetf); Ctx cond= kwarg fix.
Open (Deputy C decides): 4 R7 swallow keys are a MODEL GAP (deferred rethrow via captured `failure` var / fnn-unwind-cleanups macro handler), exposed by the per-reference flet walk. A fix (recognise capture + later (error var)) would also stale baselined swallow rows, so it was not done.
20 R2 keys + R2 unresolved:binding are TRUE (thunks inlined under section O); need baseline rows/contracts or host fixes: see /tmp/lockdisc-added.txt.

## Quest 2 (branch lane/lock-exemptions from f663c4829, no commits yet)
A) close_sites rows: all 7 HOLD (cites drift a few lines). lambda9: lock context holds, but its stated reason is FALSE: fnn-owner-core (owner.lisp:578) = fnn-core-state wrapper, takes no mutex; the one call (bp-node.lisp:264) is bare.
B) R7 deferred rethrow design is in scratch /tmp/lockdisc-r7 (tools/, tests/ R7DeferredRethrow, 14 tests; diff /tmp/lockdisc-r7.patch; mutants /tmp/lockdisc-r7m). Not landed. Results: /tmp/lockdisc-r7.json (as-is contracts), /tmp/lockdisc-r7f.json-style run with fnn-escape-cleanup-failed added to fence_functions (/tmp/lockdisc-r7/contracts-fence.json).

## Quest 3 (lane/lock-exemptions @ 8f2e64a2c, pushed)
a71728c73 R7 deferred rethrow (strict) + 14 tests; e7a8f6ab2 lambda9 row deleted (17 NEW keys back: 9 R1, 2 R1b, 6 R7); 8f2e64a2c cites. fnn-escape-cleanup-failed NOT added to fence_functions (returns normally at io.lisp:576 by design). fnn-pull-worker: failure not lost (debt 1192 -> rethrown fnn-pull-service-close 1259). Gate /tmp/lockdisc-gate2.txt.

## Quest 4 (worktree build/lanes/lock-triage-r1r7, lane/lock-triage-r1r7 @ 76a2cb1b0, pushed)
Checker/contract fixes: before-start actor lambda (9987b04fe), dominated_escape_functions (+contract), classifying_escape_functions (+contract fnn-owner-thread-escape), always-signalling clause conversion (d2dc07c78). 5 repair items LOCK-R1/R7-*. Gate /tmp/lockdisc-gate3.txt. UNSURE: fnn-csp-worker-loop, fnn-dev-repl-loop. Stale baseline rows 4->10 (6 newly stale rows, listed in commit messages): need Deputy C to drop them.
