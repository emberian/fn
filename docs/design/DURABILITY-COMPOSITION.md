# Durability composition obligations

The certified durability book contains proved local lemmas and three
`defthm-owed` top-level formulas. Certification does not discharge those rows.
The frame book likewise leaves `fn2-transition-commit-frame` owed.

## Refuted internal statement

`fn2-env-dur-turn-preserves` quantifies over arbitrary ghost context `g`.
Its predicate contains J rows, J3 rows, the durable frontier, and acknowledged
batches durable in the fixed log. It does not require the ghost IDs to cover
the core's commit rows.

[dur-turn-counterexample](../../tests/dur-turn-counterexample.lisp) constructs
a typed, well-formed core with a commit row at `:install`, batch 1, and a valid
partner. With `g = (nil nil nil)` every antecedent holds. One actual `fn2-turn`
changes the root from `(t 0 0)` to `(t 1 0)`, falsifying the empty log's durable
frontier. The executable predicate is proved equal to the original predicate;
the control checks the whole antecedent and negated consequent.

This refutes the internal arbitrary-state invariant, not the final ACK claim.
Do not add an unestablished premise to that final claim. Build a reachable
invariant, prove its initialization and preservation, and project the existing
ACK/durability observation from it.

## Dependency graph

1. **Reachable invariant initialization.** Fix ghost IDs from the supported
   profile, with commit-slot coverage and canonical directory. Carry core
   representation, operations semantics, J/J3/frontier, J5/J6, entry and loan
   facts, F, X, and Q. Initialization establishes F/X/Q, directory/slot
   coverage and universal loan facts. `fn2-pool-init-semantic` proves the
   complete pool invariant, including exact free-chain coverage. The
   declaration-derived codec conservation proofs carry that invariant through
   group/principal genesis to the actual `fn2-init-executor`
   (`fn2-env-reach-init-pool-semantic`). General initialization of the complete
   history bundle and its aggregation remain open.
2. **Host actions and admission.** Extend the device log in action order.
   `fn2-env-dur-inv-step-but-turn` preserves the smaller invariant. Existing
   epoch and admission theorems now preserve the whole reachable bundle and
   couple the actual `fn2-env-step` state to ACK/log observation. Their
   nonempty witness starts from the actual initializer, admits two members,
   and executes collect-to-seal while satisfying the whole invariant before
   and after. General collect-to-seal currently proves structural and
   freshness/loan preservation; arbitrary history preservation remains open.
   Other host actions still need the same complete conjunction.
3. **Commit issue and completion.** Preserve J5/J6 links across issue, role
   replacement and retirement. A harvested answer must be the first matching
   answer to the relevant operation and generation. Then derive counted-write
   J3 and durable frontier facts. `fn2-env-fxq-exec-harvest-commit` assumes J5,
   operations semantics and directory/slot coverage, and concludes F/X/Q plus
   directory/slot preservation; it does not conclude J/J3/frontier/J5.
4. **All executor cuts.** Prove each generated cut preserves the entire
   reachable invariant, including non-commit visits, grants, harvests and
   administrative cuts. Instantiate `fn2-executor-inv-turn` once. An empty
   constrained-frame blocker list is not this semantic proof.
5. **Run observation.** Induct over `fn2-env-run` actions and connect observed
   acknowledgements to the durable log prefix. No hypothetical row or handler
   outside the composed executor suffices.
6. **Crash image.** Use A-FENCE-PERSISTS together with ownership/non-overwrite
   facts to connect that prefix to image bytes. Audit competing valid seals:
   the assumption promises nothing about other bytes, while recovery refuses
   ambiguous successors. The image-prefix premise alone has not been proved
   sufficient for the current completeness claim.
7. **Recovery chain and ACK.** Prove the real recovery scan/decode/link machine
   includes the held prefix when it reports completion, then compose this with
   steps 5–6 for `fn2-commit-ack-implies-recoverable`. Both top-level formulas
   remain owed. `fn2-env-recovery-done` checks phase and chain, not recovery class.

## Progress is a separate theorem

An arbitrary recovery action list can be empty or never schedule a turn.
`recovery-done => prefix recovered` cannot establish recovery progress.
A progress theorem needs an explicit recovery driver or fairness/response
contract, sufficient admitted resources, and a decreasing measure over scan,
chain, payload and install work. Bounds must depend on the represented image
and supported profile, not an arbitrary ceiling on stored data. Distinguish
successful recovery, explicit uncertain/damaged completion, and stopped or
pending recovery; reaching `:done` alone is not successful installation.

## Native trace prefixes

[native-envelope-prefix-unit](../../tests/native-envelope-prefix-unit.lisp)
refutes the current complete-wire equality using the first six recorded events:
Accept has completed but no greeting Send has occurred. All original hypotheses
hold. The full recorded trace remains a positive comparison control.

A replacement must distinguish emitted prefixes and completed observations.
Validator soundness should relate recorded effects to the logical replay under
the same schedule. Prefix monotonicity and stability of a closed capability's
wire are useful separate contracts. Actual native trace production and physical
effect correctness remain separate obligations; neither a byte-check identity
nor a same-schedule replay theorem establishes them. Equality against the fixed
canonical adapter also needs genuine completion and scheduling premises.

## Initialization evidence scope

The new pool initializer and controls passed the record-toolchain gate
`certify-20261114T015429Z-3534875` in `stride-owed-integrated`. That lane uses
baseline profile digest `b5098b84e1d92425d6476d06103939a075d957f6d74740dcd364147ec423a687`;
it is not a certification of the current integration profile. The subsequent
codec/genesis composition is source-proved on that qualified prefix and has a
separate assembled record gate. Run `certify-20261114T020934Z-3551094`
passed `layout-conservation`, then exceeded its 2 GiB cgroup limit during
`commit-reachable`; the unit book was not reached and no final run manifest
was produced. The 4 GiB retry `certify-20261114T023431Z-3577911`
subsequently certified `layout-conservation`, `commit-reachable`, and
`commit-reachable-unit` with zero triage failures. This assembled record still
covers the older baseline, not the current integration profile. Existing
top-level owed formulas remain owed.
A nonempty-group control checks actual arena consumption and pool semantics;
a broken free-link control preserves row geometry while refuting class
coverage. Removing the incoming genesis semantic premise does not repair it.
