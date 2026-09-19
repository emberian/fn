# Proof strategy and evidence

Status: component theorems are being certified as implementation advances. The
[proof registry](../planning/proofs.json) is the authoritative ledger for the
larger targets, which remain open until their complete statements are supported.
See [implementation status](implementation.md) for executable scope. Partial
lemmas do not close an entire subsystem proof target.

## Assurance grows with the implemented surface

Each new reachable command, persistent record, transition, codec or adapter
operation adds assurance obligations. A proof about an older component does not
automatically cover a new caller or the composition between components. Keep
three things distinct in the [closure inventory](../planning/assurance-closure.md):
evidence for implemented behavior, missing evidence for implemented behavior,
and requirements for features that have not been implemented.

For each behavior-changing batch, record the affected stable requirement/proof/
scenario IDs and the following change in scope:

| Changed surface | Evidence to add or explicitly leave open |
| --- | --- |
| State or transition | Meaningful initial/reachable invariant, rejection behavior, preservation of prior accepted facts, and finite traces |
| Caller or composition | Relation to the actual callee's state and hypotheses, including pending work; shape validity alone is insufficient |
| Durable record or side effect | Byte/record correspondence, barriers and uncertainty, live-versus-replay agreement, restart and lost-completion cuts |
| External bytes or raw execution | Decoder domain/canonicality, limits and work, guard status of the executed call graph |
| Authority or release | Exact evidence/context binding, durable decision, explicit policy/crypto/peer premises, preservation of independent obligations |
| Transport or scheduling | Duplicate/reorder/expiry/contact behavior; safety and conditional progress stated separately |

A feature checkpoint may remain experimental with an exact open list. It does
not count as assurance closure until its applicable claims have evidence.
Changing a profile or a trust assumption to avoid an obligation changes the
contract and must be recorded as such. Keep critical missing composition/recovery
evidence in a bounded closure batch before building dependent behavior on it.

Theorem, root, test and guarded-function counts describe artifacts, not a
percentage of system correctness. Report the property, supported domain,
source digest and assumptions. A growing count does not demonstrate that the
assurance gap is shrinking. Review the frozen batch once, fix concrete defects,
and keep independent work moving; this discipline adds no approval ceremony.

## Refinement ladder

1. **Abstract executable state:** finite maps/records and event transitions.
   Prove recognizer preservation, identity/allocation invariants, and phase rules.
2. **Bounded bytes:** refine external parsing/encoding to the accepted object and
   NNTP domains. Prove decoding, deterministic preimages, and framing properties.
3. **Crash storage model:** relate logical acceptance to records, writes, barriers,
   recovery, and checkpoint selection under named platform assumptions.
4. **Concrete execution:** use guard verification and explicit correspondence
   between logical maps and efficient representations, including abstract stobjs
   where useful. Include range-query completeness in index obligations.
5. **Multiple nodes:** reason about validated fact sets, obligation transitions,
   duplicate/reordered exchange, and explicitly conditional progress properties.

The program used by the host must be these definitions or a justified refinement.
An abstract model plus an independently written server is insufficient evidence
for claims about the running server.

## Shape of the claims

State preservation has the schematic form
`inv(s) and permitted-event(s,e) => inv(next(s,e))`. Prefer total, guarded
interfaces that explicitly reject malformed events rather than assume away
untrusted wire inputs. An invariant must include meaningful initial states and
reachable examples, so a theorem is not satisfied by an empty state domain.

Trace induction lifts one-step safety properties to finite executions. Eventual
delivery additionally needs a scheduling/contact/resource model and A-FAIRNESS.
Do not describe a safety theorem as proving inevitable delivery.

Crash refinement relates a logical transaction history to stable and volatile
storage state. A completed barrier constrains crashes; it does not simply assert
the result we intended to prove. Unacknowledged commits may survive. Index
reconstruction, checkpoint replacement, and compaction require their own
correspondence results.

Retention theorems cover protected dependency closure, not just body objects.
Handoff theorems identify cooperative-peer and node-survival hypotheses. A
cryptographic verification result alone does not establish an honest disk write.

## Trust and executable efficiency

Record assumptions from [the failure model](../specs/failures.md) per target.
Do not introduce unrestricted injectivity axioms for finite hashes. Cryptographic
properties and implementations need separately scoped arguments or assumptions.
Do not turn `skip-proofs`, trust tags, or axioms into a certification shortcut.

Termination admission, guard verification, theorem proof, book certification,
and platform tests are different evidence. A certified book can still depend on
trusted facilities; disclose those explicitly. Run certification in a clean
environment separated from host raw-I/O integration.

## Registry states

Requirements: `specified`, `implemented`, `validated`, or `deferred`.
Proof targets: `planned`, `in-progress`, `certified`, or `deferred`.

Implemented/validated requirements and certified proof targets require evidence
paths. A proof's evidence must name actual events/books, exact ACL2/Lisp versions,
command, input revision or content digest, result, assumptions, and limitations.
The scaffold checker checks references/status consistency; it cannot certify a
theorem by inspecting an evidence file.

Store generated logs under `build/` and durable human-reviewable evidence summaries
in versioned files as implementation arrives. Do not commit a placeholder proof
log or create a `certify` command that passes without running ACL2.
