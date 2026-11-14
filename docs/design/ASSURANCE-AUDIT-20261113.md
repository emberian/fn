# Assurance audit — 2026-11-13

Read-only scout review of `85f8817b6`, commissioned by ember. These findings
distinguish admitted local proofs, registered obligations, finite checks, and
unproved implementation correspondence. Certification is not a proof of every
proposition mentioned in the certified book. Draft lane results are separate.

The [completion plan](ASSURANCE-PLAN-20261113.md) records proof dependencies,
concrete pilot gates, shared interfaces and the subsequent swarm partition.

## Completion criterion

For each advertised guarantee, identify the actual served entrypoint, exact
statement and admissible domain, admitted proof, composition/refinement links,
current artifact identity, and explicit environment/trust assumptions. Safety,
progress, resource bounds, and deployment qualification are different claims.
No count of books, witnesses, or generated candidates substitutes for this chain.

## Confirmed gaps and owners

1. **Top-level durability remains owed.** `commit-durable-all.lisp` registers
   turn preservation (4484), recovery completeness (4550), and ACK/recoverability
   (8528) with `defthm-owed`. That macro creates a proposition and an owed row,
   not an admitted theorem (`books/owed.lisp:85`). The ACK statement assumes
   recovery reaches done; recovery progress needs a separate claim and explicit
   environment fairness. Owner: durability lane; discharge exact useful claims.
   The lane also confirms the current turn invariant omits J5/F/X/Q and slot
   coverage required by supporting lemmas. Audit inductiveness and reachable
   states; a stronger preserved invariant may be needed to prove the original
   externally visible guarantee, rather than more tactics on the same statement.
   Follow-up: lane commit `319620bed` preserves an executed counterexample to
   the current turn-invariant statement, with all its antecedents true and the
   consequent false after one actual turn. Qualified baseline REPL evidence is
   recorded by the lane; record certification is pending. This does not refute
   the user-facing ACK guarantee on initialized/reachable states.

2. **Turn composition and resource contracts are incomplete.**
   `books/reference.lisp:310` and `books/executor.lisp:328,364,370` remain owed.
   Generated machine run constraints in `books/machines.lisp:3832` preserve
   frames/types but do not relate returned charges to the supplied budget.
   An unchanged-state run returning budget+1 descriptors is the countermodel
   to reject. The reference conclusion also retains a 4129 constant while
   current declared machine budgets exceed it; obtain a reachable witness and
   establish the correct profile-derived bound. Owner: composed-build lane.
   Declared step charges alone do not establish actual CPU/allocation cost.
   Q1 shares application handlers with the implementation, so it establishes
   scheduler representation rather than independent application semantics.
   Its independent contract registry omits CNS/auth/cursor/boot/commit; connect
   independent observable contracts and shared-handler mutations for these too.

3. **Native/model correspondence is unproved.**
   `books/owed-native.lisp:81` is owed, excludes DATE, and allows at most four
   connections. Source checks explicitly report host refinement unchecked and
   cut mapping incomplete. Physical I/O return and ACL2 completion posting need
   distinct crash states, including short/error outcomes. Owner: durability and
   native lanes. A legal trace prefix ending after Accept may refute the current
   equality with a complete canonical run: this is an UNEXECUTED counterexample
   candidate. Test it; if confirmed, prove prefix refinement and equality under
   a genuine completion condition instead.

4. **Lean model proofs do not yet establish ACL2 execution equivalence.**
   The checker explicitly excludes closure-wide exported-body evaluation and
   primitive-domain adequacy (`meta/emit/check_served_certificate.py:618`).
   The recovered package's 58 passing candidates are a regression result;
   205 roots remain ungenerated and the run lacked live ACL2 metadata validation.
   Prove canonical-body evaluation and primitive correspondence on reachable
   domains, then compose through all served roots. Owner: Lean lane.
   The cache also omits resolved external import artifacts and LEAN_PATH from
   its keys; the compile invocation honoring that path does not bind cache
   evidence to it. Add an external-import mutation control and repair provenance.

5. **Witness registration does not enforce semantic relevance.**
   `books/owed.lisp:84,130` accepts named zero-argument evaluators returning T;
   it does not bind them to the whole antecedent/conclusion or a meaningful
   hypothesis removal/mutation. README's stronger universal wording overclaims.
   Two distinct names alone cannot fix this. Owner: integration/compiler lane;
   generate checkable formula/witness bindings and audit consequential consumers.

6. **Native substitutions and the environment remain trusted.**
   `host/b3-native.lisp:277` installs raw function replacements after finite
   qualification. Logical native-span/integrity assumptions are not connected
   to those installed implementations by a refinement theorem. Either prove
   their outputs and effects or explicitly include them in the trusted base.
   Successful SIGKILL recovery does not test power loss: device fence semantics,
   filesystem/kernel, runtime/compiler, FFI and hardware assumptions remain.

## Evidence hygiene

Regenerate `docs/OWED.md` from the converged certified world. Its existing
969/964/2/97 census is stale and counts registered obligations, not all ACL2
theorems. Repair README and layer-document overclaims against the claim map.
Provide a strict assurance gate distinct from candidate regression: all required
claims discharged, current canonical/live identity, domain and native-boundary
obligations accounted for, no silently omitted roots or trusted substitutions.

These gaps do not invalidate the admitted local lemmas or successful native
regressions. They identify the missing arguments needed to compose that evidence
into a product-level guarantee.
