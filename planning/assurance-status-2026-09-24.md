# Assurance and development snapshot — 2026-09-24

Snapshot during the wide Sol cycle, after the topic/index integration and
native BP fragment activation reached dev (`a74e091c`). This is an assessment
of evidence and open work, not a release declaration. Later scoped lane
results are explicitly distinguished from integrated image results.

fn has substantial executable-core proofs and several working native exchanges.
It does not yet have a closed assurance argument for the entire composed
service. The last fully source-qualified shared image in this cycle is
`e160442f`. The later `8c61c098` combined run failed and produced no image:
five direct failures, two deliberately bounded proof-cost aborts and their
missing-certificate dependents. Repairs are underway. The protected live
service has not been upgraded by this cycle.

## What the argument consists of

The executable ACL2 core decides admission, allocation, protocol transitions,
replay and obligation changes. The native Common Lisp host calls those
functions rather than reimplementing their decisions in Python. A useful
proof must concern the called function or a named correspondence to it.

ACL2 checks general equations and induction over arbitrary finite traces under
explicit hypotheses; that is stronger than exercising a finite list of traces.
But it is only useful if those hypotheses describe reachable service states.
Maintained-state invariants, actual-caller correspondence, nonempty positive
witnesses and premise-removal counterexamples connect the argument. Several
such connections and witnesses remain incomplete. A named theorem alone does
not settle them.

Certification evidence is tied to source bytes, include dependencies and a
pinned toolchain. A separate native image identity ties runtime tests to what
was built. Interoperability, process-death and I/O-failure tests examine the
host/model boundary. These tests have found actual defects; they are not a
proof of every possible environment behavior.

ACL2, SBCL/compiler/runtime, native I/O and platform assumptions, OpenSSL and
other signature/TLS primitives remain in the trust boundary. SHA-256 is
implemented in guard-verified ACL2, with standard-vector evidence; this does
not prove collision resistance or prove that a specification document and
its implementation agree on every input. Required Ed25519 plus ML-DSA-65
verification is not a theorem about either primitive's security.

## Properties that matter to the finished system

- An acknowledged article has a durable history entry and survives modeled
  crashes under the byte/kernel relation and platform assumptions. This lets
  a sender sleep without silently losing a promise. Establishing that relation
  across every supported native publication/recovery path remains open.
- Allocation and duplicate/conflict decisions preserve local identities and
  existing evidence. Retries must not allocate a different meaning to the same
  held Message-ID or silently replace earlier content.
- Authentication gates refuse unauthorized commands before they submit work;
  protected-only policy orders credentials after TLS. Exact-source author
  binding separates signed content from mutable relay projections. These
  protect shared infrastructure without making a signed claim true or granting
  execution authority merely because it arrived.
- Pinned readers and recorded policy/author contexts preserve the meaning of a
  read while new posts or configuration changes happen. This matters when an
  agent resumes a conversation or evaluates older evidence.
- A carrier ACK, fn durable acceptance, application processing ACK and retention
  release have different meanings. BP and consumer state machines preserve
  those distinctions, preventing receipt of some bytes from erasing a duty.
- Refused, uncertain and accepted outcomes remain distinct. Ambiguous durable
  publication fences mutation until recovery; it is not an ordinary retryable
  refusal. Per-bundle clock uncertainty is separately modeled.
- Consumer progress is durable and scoped to a Store history/incarnation,
  principal and view. Polling does not acknowledge processing. Mini must commit
  its own durable transaction before advancing fn's cursor.
- Indexed served paths have correspondence to the simpler logical answer.
  Optimizing a lookup should not change which article or cursor is returned.
  Bounds and measured whole-workflow costs remain separate claims.

These are mostly safety properties: what cannot be lost, confused, authorized
or released incorrectly. They do not establish eventual delivery without
contacts/resources, arbitrary agent side-effect exactly-once execution,
Byzantine consensus, or truthful message contents.

## Development by dimension

| Dimension | Strongest existing result | Current boundary / next completion |
| --- | --- | --- |
| Native NNTP and peering | Native reader/posting/admin/authentication, INN interoperability, historical reader tests and protected two-host exchange on named earlier images. | Requalify the combined new source and close remaining release-matrix and composed proof obligations; this is not a v0 declaration. |
| Authorship and authority | Exact-source hybrid signing/verification, recorded historical verdicts, tamper refusal and signed peering/reopen tests. | Broader key custody/succession and cross-silo authority policies; primitive security remains trusted. |
| Storage and recovery | Conditional crash scanning/reopen/acknowledged-record survival, increasingly connected to actual publication cuts; native process-death and isolated filesystem-EIO evidence. | General establishment/preservation of the byte/kernel relation through all supported caller paths, compaction/recovery composition and wider physical-platform qualification. |
| BP/DTN | Earlier native whole-bundle/contact/application-receipt paths and deletion-report recovery tested. Fragment custody plus persisted expiry-safe reassembly are now integrated source. | Source-matched interrupted-fragment/restart/dispatch/receipt run; full selection, MRU and journal-debt contract remains incomplete. A newer-live versus older-clock-uncertain selector slice is certified on its lane. |
| Durable consumption | Native poll, unchanged ACK on repeat, durable advancing ACK/lost-reply/reopen and cursor inspection/status tests. | Indexed owner poll is integrated but its new image/cost gate is pending. The lane has reduced the outer theorem's hypotheses; one independent premise witness remains open. |
| Mini / agent conversation | Synthetic real fn poll → Mini signed durable transaction and immutable Q → reopen → fn ACK → no repeat has passed. | Durable reply preparation/signature reuse and post/reopened readback are being joined. First B3 attempt correctly refused a source lacking Date; no reply-post success yet. Two independently administered Stores and the complete crash trace remain open. |
| Topic histories | Source-level local administrator/root/report admission, historical source binding, parent/roster/quota checks and replay; now integrated with the Store/index shape. | Combined native admission/reopen and negative cases. General portable succession/governance is not supplied by this fixed experimental profile. |
| Preservation and efficiency | Selected pack/reclaim/cold-clone tests, new incarnation refusing old cursors, indexed Message-ID/LISTGROUP/OVER paths; bounded consumer event index source. | Full reclamation/active-reader/crash correspondence, pruning policy, large-workload measurement and remaining scans. Mini replay cost also remains material. |
| Human/operator experience | Native CLI plus separate loopback web reader/composer; real native posting, bounded page navigation and HTML escaping tested. | Durable drafts/outbox, clearer provenance and uncertain-post recovery workflows, packaging polish. The Python web client is outside the native fn server. |
| Assurance engineering | Source/closure-aware cache, generated ledger, scoped native evidence and bounded proof iteration. Certified-claim warnings now reuse existing event and closure checks. | Current combined proof regressions, guard/witness gaps, slow successful books and stale narrative claims. Streaming live proof logs/PID mapping is ready on a tooling lane; cross-manifest proof-cost aggregation remains open. |

## What this cycle taught us

The new topic event exposed a genuine classification defect: article replay
needed to exclude topic events. Other failures came from proofs assuming the
old Store shape or expanding irrelevant branches of growing recognizers. Both
matter, but only the first changes behavior. The owner idle/replay projection
that ran for hundreds of seconds admits immediately with the irrelevant
relation arms closed; whole-book certification remains a separate gate.

The registry is not a complete, automatically current explanation of the
system. Some in-progress rows retain historical limitations after the relevant
runtime behavior improved. The new certified-claim check addresses event and
source/closure support, not every prose assertion or coverage question. This
snapshot uses concrete evidence rather than interpreting every old note as
current truth.

The next useful milestones are complete recoverable exchanges: the Mini
report/receipt/reply path, and an interrupted BP transfer through durable
reassembly, Store dispatch and matching return evidence. Their proofs,
caller refinements and hostile/fault traces advance alongside them. A green
closure is necessary evidence; it is not the final system-level conclusion.

## Evidence entry points

- [Last shared qualified image and selected tests](evidence/native-luna-e160-selected-2026-09-24.md).
- [New combined cut and its failures](evidence/topic-index-8c61-full-gate-red-2026-09-24.md).
- [Native Mini transaction-to-ACK join](evidence/native-mini-live-join-2026-09-24.md).
- [Reader, consumer and cold-clone experiment](evidence/native-poll-reader-clone-1d26-2026-09-23.md).
- [Protected two-host exchange](evidence/relocated-native-1836ed01-2026-09-23.md).
- [Earlier native BP admission](evidence/native-bp-admission-c1bb-2026-09-23.md).
- [Isolated filesystem EIO experiment](evidence/t16-private-eio-2026-09-23.md).
- [Assurance review follow-up](evidence/assurance-review-followup-e160442f-2026-09-23.md).
- [Proof registry](proofs.json), [trust and proof scope](../docs/proofs.md), and [active work](now.md).
