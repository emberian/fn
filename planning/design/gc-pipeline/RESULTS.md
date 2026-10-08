# Phase 1c — persvati ground results, 2026-10-08

All draft definitions admitted. All witnesses evaluated in the same ACL2 world,
without loading `statements.lisp`. The final run sent witness forms #4–#65:
62 forms, 0 refused; ACL2 time 0.25 s, 1,264 prover steps (the three recursive
witness checkers' termination proofs, not keystone proofs). Output:
`(:POSITIVES T T T T T T T T T)` and `(:MATRIX-CASES 325)`.
The eight `must-fail-checked` forms all translated and caught failed ground
assertions. Each also has an explicit passing negation; no proof timeout is
counted as a counterexample.

| Witness | Actual result |
| --- | --- |
| W1 initial profile hypothesis and linkedp | PASS |
| W2 second append admitted; both batches nonempty; partition, D, ACK bound | PASS; write offset 1024, length 512; D remains 1 |
| W3 whole successful step trace, including ACK and reader advance | PASS; final D=ACK=completed=3 |
| W4 reader while both batches appended | PASS; reader cut=1, D=1 |
| W5 first fence and feed resolution | PASS; D=2, next record 67 still pending, feed cut=2 |
| W6 first COMPLETE and promotion; ACK refinement/write-plan equation | PASS; ACK=2, reply rendered, B resumes at :fence without rewrite |
| W7 failed current fence and arbitrary sample late events | PASS; both members uncertain (:uncertain-reply :close), D=ACK=1 |
| W8 new-kernel TAKE membership/profile; frozen B refuses further take | PASS; :full after B appended |
| W9 25 reached prefix states × 13 event variants | PASS, 325 cases; success/uncertain/fault and invalid orders |
| T1 reply released at append | Negation PASS; positive assertion fails as intended |
| T2 reader advanced at append | Negation PASS; positive assertion fails; reader cut 2 > D=1 |
| T3 remove failure's phase premise ONLY | Negation PASS; positive assertion fails in reached :done state |
| T4 remove encoded-octet preflight, use raw fn-olr-take | Negation PASS; positive assertion fails: 512 > OMAX=5 |
| T5 remove exact count correspondence | Negation PASS; positive assertion fails: two records > BMAX=1 |
| T6 release next member's acceptance after failure | Negation PASS; positive assertion fails |
| T7 ACK-at-append corrupts incoming ACK prefix | Negation PASS; positive assertion fails: ACK=3 > D=1 |
| T8 old singleton exemption at OMAX=1 | Negation PASS; positive assertion fails: packed bytes=5 > 1 |

## Satisfiability and vacuity audit

- Kernel append/fence hypotheses: W2/W5 assert pipe-okp on reached states.
  W2 additionally asserts admission, nonempty A and B, :appended, the new bit
  and a nonempty actual codec-generated write plan. Safety is not satisfied
  merely because append refused. Partition preservation at append is simple
  because the kernel fields are shared, deliberately; the write plan and
  frozen-next admission are the new behavior. The multi-write disk relation
  remains a distinct proof obligation.
- Initial/preservation keystone: W1 asserts the full profile hypothesis and
  initial linkedp. W3/W9 assert linkedp before AND after every tested step.
  Neither transition calls linkedp, pipe-okp, reveals-okp or a successor
  invariant as an admission check. The step code must preserve coupling;
  that coupling is no longer an externally supplied successful-receipt premise.
  The initial case excludes a false/unreachable invariant as a universal claim.
- Reveal corollary: W4/W5/W6 exercise nonzero reader/feed/reply dependency cuts.
  linkedp contains neither emitted cuts nor reveals-okp. Output safety is a
  claim about outputs freshly emitted by host-step; it is not a claim about
  arbitrary injected output fields. T1/T2 reject precisely the early-output
  mutations. Actual protocol byte provenance still needs renderer refinement.
- Failure keystone: W7 asserts its ENTIRE hypothesis and conclusion with both
  record batches and member lists nonempty. T3 retains linkedp and both lists
  while dropping only current phase=:fence; the failed conclusion shows why
  the phase matters. The theorem quantifies arbitrary post-failure event lists;
  the ground witness uses a finite suffix, not a universal proof.
- Membership keystone: W8 asserts its ENTIRE hypothesis/conclusion over the new
  kernel. Hypothesis contains no okp conclusion. Bounds follow the EXECUTABLE
  preflight and exact count; exact suffix membership additionally requires
  fn-olr-take's effect, not preflight alone. T4 removes preflight at the decision
  (raw TAKE), showing why the new check is needed; T5 drops count correspondence.

## Draft changes and limits

The old readout-only contract became an initial/preserved state invariant;
append-behind emits a positioned write plan and freezes the existing BATCH;
first fence commits only INFLIGHT, then COMPLETE advances views and promotes B.
The job-phase guard allows B's append only while A's fence is pending. Failure
is sticky across late receipts. Member outcomes are separate from record counts.
Kernel and composition functions are executable logic-mode DRAFT definitions.
ACL2 rejected MV-NTH projections inside DEFUN/DEFCONST: replaced them with
MV-LET projections. A witness checker's termination proof originally expanded
the whole machine and hit 10 s; local hints closing the called functions reduced
it to 608 steps. Neither failure was presented as a witness result.

No disagreement with S's premise-shift diagnosis. This is a proposed dispatcher,
not a false claim that today's host already calls append-behind. Named equations
in statements.lisp link scheduler projections and ACKs to the existing called
cores; native generation/custody dispatch, effect/renderer and multi-write crash
refinements remain owed. D is the GUARANTEED durable record prefix: a racing
append may physically persist farther without being acknowledged. No new
assumptions, skipped proofs, production definitions, certification or commits.

## Reproduce (persvati only; normal slot/resource controls)

Both gc-pipeline-1b and gc-pipeline-1c are stopped. Before stopping, diff confirmed
all 36 named contract events matched the source. The final session ran at `fn-gates/n-gc-pipeline-repl-gc-pipeline-1c`. Its server log and per-form
outputs stay there; final client summary: `/tmp/n-gc-pipeline-1c-witnesses-final.log`.
A fresh session can reproduce the final definitions/witnesses with:

```sh
timeout 300 python3 tools/proof_repl.py start gc-pipeline-check planning/design/gc-pipeline/contracts --upto fn-lgk-pipe-make --cached-only --host persvati --lane n-gc-pipeline --lease-wait 0 --limit 10
timeout 90 python3 tools/proof_repl.py send-range gc-pipeline-check planning/design/gc-pipeline/contracts --from fn-lgk-pipe-make --host persvati --limit 10
timeout 30 python3 tools/proof_repl.py send gc-pipeline-check '(include-book "../../../tests/acl2/must-fail-checked")' --host persvati --limit 10
timeout 90 python3 tools/proof_repl.py send-range gc-pipeline-check planning/design/gc-pipeline/witnesses --from '*gc-init*' --host persvati --limit 10
timeout 30 python3 tools/proof_repl.py stop gc-pipeline-check --host persvati
```
