# E2 continuation of NOTES-TO-A — pass 3

Items 1–2 remain unchanged in `../NOTES-TO-A.md`. This new file continues the
numbering because E2 forbids edits to existing tracked files. Items 3–9 record
pass 1; items 10–13 record pass 2. Current role-binding findings are in
items 14–16 below.

3. **The envelope shares; the semantics stay specialized.** E2 implements one
   `defsquare` over `sq-squares`, separate from your planned DM1 store. Q1
   supplies loop contracts and a formula builder; Q4 supplies the copied
   read-state relation, event theorems and converter. Generic per-row endpoint
   overrides are necessary for composition/G0. A thin public form and a
   common registry with specialized templates are compatible. Source counts
   alone do not establish a net saving; see `../E2-RESULTS.md`.

4. **Proof and evidence must remain separate at import.** A theorem name is
   insufficient: compare its `theorem` world property with the statement's
   translated body after removing guard holders. E2's append events replace
   only `:checks`. Refused theorem borrowing, unresolved functions, wrong
   arities, duplicate cases/owners, placeholder statements and zero-exercise
   passes have narrow controls in `defsquare-tests.lisp`. They passed ACL2
   certification; output-enabled reruns confirmed formula mismatch and arity
   translation as the intended refusal reasons.

5. **Do not call G1 evidence a check of every new invariant conjunct.** E1 G1
   evaluates five-result correspondence, normalized state equality and shape.
   E2 states a stronger loop invariant and explicitly records G1 as its checked
   projection. Entry, exit, termination, selector partition and accounting
   remain named unmet prerequisites. Interrupted checks are reached but not
   exercised. The exact old `fn2-turn-refinement` antecedent is preserved.

6. **M4 resolves the shared-handler disagreement by claim.** Q1 can correctly
   establish scheduling/refinement while both sides share the same wrong send
   offset. The client oracle checks the different semantic claim. Keep shared
   representation declarations and independent external semantic judgments;
   retain M4 as the control, not as an argument to duplicate every declaration.

7. **WORK is a totals equality, not the delayed-divergence summary example.**
   Its five additive counters compose across turns but do not furnish a
   stronger future-sensitive relation. E2 uses read-state. Its tooth rejects
   count-at-bound-2 equality; count equality at every bound would determine the
   read set. Strict strength is relative to the chosen observation, whereas
   step closure is the actual composition requirement.

8. **E2 passes its laptop author checks.** Eleven books passed `certify-book`,
   slowest 3.234 seconds wall / 2.70 seconds ACL2. Fresh ORIGINAL random and
   enumeration campaigns completed 10,004 G1 checks; 19/39 catalogue cases
   exercised, 20 unexercised, one interrupted final enumeration call. The
   actual TABLE has 45 rows (40 owed, 5 proved) and 83 evidence records, with
   proof fields unchanged after import. This is not farm/record-toolchain
   certification and discharges none of Q1's named missing boundary links.

9. **Use E1's sandbox slot-pool configuration.** Every runner subprocess gets
   `FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots` and `FN_ACL2_SLOTS=6`, as in E1.
   `timeout 1800 python3 fn2/experiments/squares/e2/run.py` runs sequential
   certification and acceptance with PID files and disk/time controls. The
   initially reported slot-lock block was a configuration error, corrected
   using the existing convention. No commit or push was made.

10. **Pass 1 did not measure Q4 statement generation.** Its row formula came
    from the same theorem property used as its proof, so the consumer's exact
    formula check compared a theorem with itself. The generic refusal controls
    worked, but that did not make Q4 an independent statement-template consumer.
    Pass 2 removes theorem introspection from Q4 formula construction.

11. **Both consumers now generate statements before proof selection.**
    `sq-fs-formula` builds event, G0 and composition claims from contract roles.
    Five new `sq-q4-generated-*` theorems prove these exact claims. The three
    event claims add both post-admissibility conjuncts; G0 adds target
    admissibility. They need bridges to the existing lemmas. One 14-line proof
    emitter and 5-line support selector handle all five: no handwritten bridge
    per event kind. The composition formula matches `rs-summary-adequate`,
    whose proof already uses `fc-rel-fold` and `fc-obs-fold` functional instances;
    functional instantiation constrains its semantics, not the builder's syntax.

12. **The same template has an evaluated false instance.** A count-at-2
    history/history contract produces false step and composition formulas at
    the original tooth-1 witness. `sq-q4-template-negative` evaluates their full
    true antecedents and false conclusions. Binding the weak generated step
    to the strong generated proof is also refused by exact-formula matching;
    neither the row nor its owner survives. This is not a failed proof search
    presented as a counterexample. The original off-by-one control still runs.

13. **Updated measurement supports SHARE, with specialized templates.**
    Q4 adds 125 physical lines over pass 1: 41 template, 58 template controls,
    and a net 26 in bindings/proof generation. Its declaration is 7 lines,
    8 including the actual wrapper; the 5-line role constant is counted in
    support. Total package is 1,990 physical source lines (1,359 new + 631
    copied), not a net LOC-saving claim. All 13 books certified locally,
    slowest 3.362 seconds wall (rounded upward). Fresh campaigns again completed
    10,004 G1 checks across 19/39 cases; 20 remain unexercised. M4 still shows
    why shared-handler refinement and client semantics need separate judgments.
    The generated Q4 proofs certify the chosen relation and observations, not
    the correctness of a shared interpretation of external protocol events.

14. **Declare the functions that occur in the generated statement.** Q1 now
    passes `*sq-q1-contract*` / `*sq-q1-sides*` through its declaration wrapper
    and into `sq-q1-case-formula(case, contract, sides)`. Its `:relation` role
    is the full successor `sq-q1-loop-invp`, also its `:pre`, because the pure
    `sq-q1-loop-relatedp` occurs only inside that invariant. Budget and advance
    are explicit roles too. All 39 translated bodies match the pass-2 SHA-256
    baseline; the composition formula remains the original owed formula.

15. **Resolution is insufficient; bind effective roles to translated calls.**
    The generic envelope now requires every endpoint in each effective role
    to occur in `all-fnnames`, after row overrides. `:unused-roles` is an exact
    list of qualified exceptions, stored in the row; unknown, duplicate and
    redundant exceptions fail. Q1 needs none. Q4 needs explicit event/fold/G0
    exceptions, listed in E2-RESULTS. This is an occurrence check, not a proof
    of role position or semantic relevance; exceptions remain reviewable
    waivers. Both consumers' divergent-relation controls fail with proof owed,
    so this safeguard is independent of proof attachment.

16. **The current measured verdict is SHARE with specialized templates.**
    All 14 books certified locally, each below 60 seconds; slowest 3.577 seconds
    wall (rounded up). Store/evidence remains 40 owed + 5 proved / 83 records;
    fresh G1 remains 10,004 completed checks over 19/39 cases, 20 unexercised.
    Current source cost is 2,085 physical lines (1,454 new + 631 copied), with
    all declaration wrappers, exceptions and controls counted. Role binding
    removes decorative declarations but does not remove M4's shared-semantics
    limit: retain independent client meaning and avoid a universal-template or
    net-size-saving claim. No commit or push was made.
