# Proof strategy and evidence

Status: all targets planned. [The proof registry](../planning/proofs.json) is the
authoritative status ledger; none is currently admitted or certified.

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
