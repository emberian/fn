# Assurance and development snapshot — 2026-09-24

Snapshot at dev `f277823d` during the wide Sol cycle, after topic/index and
native BP fragment source integration. This is an assessment of evidence and
open work, not a release declaration. Scoped book results are distinguished
from combined closure and source-matched image results.

fn has substantial executable-core proofs and several working native exchanges.
It does not yet have a closed assurance argument for the entire composed
service. The last fully source-qualified shared image in this cycle is
`e160442f`. The later `8c61c098` combined run failed; its repaired
`f0d67034` run also failed, with two direct proof failures and thirteen
missing-certificate dependents. Neither produced an image. The configuration
proof is repaired and scoped-certified; the consumer Store proof has been
admitted in a bounded REPL but still needs certification. Source at
`f277823d` is newer than the qualified image. The protected live service has
not been upgraded by this cycle.

## What the argument consists of

The executable ACL2 core decides admission, allocation, protocol transitions,
replay and obligation changes. The native Common Lisp host calls those
functions rather than reimplementing their decisions in Python. A useful
proof must concern the called function or a named correspondence to it.
For example, the frontier callback evidence follows native `fnn-owner-observe`
through `fn-owner-step` to `fn-sn-io`; topic retry follows
`fn-owner-topic-propose` to `fn-th-local-propose`. These are narrower than a
proof about every native call entry or every filesystem outcome.

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
  a sender sleep without silently losing a promise. The successful owner
  callback-to-Store frontier projection has scoped certification; establishing
  the byte/kernel relation at every served call entry and across all native
  publication/recovery outcomes remains open.
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
  The host-reached retention preparation guard is verified for a valid Store;
  the owner path still needs its maintained-guard and physical release argument.
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
| Storage and recovery | Conditional crash scanning/reopen/acknowledged-record survival, native process-death and isolated filesystem-EIO evidence. The shared-owner successful frontier callback now has an exact ACL2 owner-to-Store projection and a four-event relation witness. | Establish and preserve the byte/kernel relation at every served call entry, including errors and torn barriers; then compose compaction/recovery and qualify the physical platform. The frontier result alone is not that whole claim. |
| BP/DTN | Earlier native whole-bundle/contact/application-receipt paths and deletion-report recovery tested. Fragment custody plus persisted expiry-safe reassembly are now integrated source. | Source-matched interrupted-fragment/restart/dispatch/receipt run; full selection, MRU and journal-debt contract remains incomplete. A newer-live versus older-clock-uncertain selector slice is certified on its lane. |
| Durable consumption | Native poll, unchanged ACK on repeat, durable advancing ACK/lost-reply/reopen and cursor inspection/status tests on named earlier images. | Indexed owner poll and joined status need a new source-matched image/cost gate; the broader consumer Store invariant is one direct red in the latest combined run, with a bounded REPL admission but no certificate yet. |
| Mini / agent conversation | A real fn poll → Mini signed durable transaction and immutable Q → reopen → fn ACK → no repeat passed. Separately, B3 durably prepared and signed a reply, reused it without private keys in another process, posted via native fn, reopened, and verified exact source and full keyset on the `e160442f` image. | The successful B3 test is one synthetic reply/one Store; two independently administered Stores, complete process-death cuts, broader replay cost and general application side-effect recovery remain open. The earlier missing-Date refusal and prepared slot remain recorded. |
| Topic histories | The experimental local administrator/root/report Store path has scoped historical source binding, roster/parent/quota and reopen proofs. The actual owner-called report selector now gives exact admitted-source retries a distinct success without another event or charge. | The combined native install/anchor/report/reopen/retry fixture has not run on a source-matched image. Version-1 anchors bind the installed administrator ID but omit its separate installation generation; that stronger binding needs a versioned migration. Portable succession/governance is outside this fixed local profile. |
| Preservation and efficiency | Selected pack/reclaim/cold-clone tests, new incarnation refusing old cursors, indexed Message-ID/LISTGROUP/OVER paths; bounded consumer event index source. | Full reclamation/active-reader/crash correspondence, pruning policy, large-workload measurement and remaining scans. Mini replay cost also remains material. |
| Human/operator experience | Native CLI plus separate loopback web reader/composer; real native posting, bounded page navigation and HTML escaping tested. | Durable drafts/outbox, clearer provenance and uncertain-post recovery workflows, packaging polish. The Python web client is outside the native fn server. |
| Assurance engineering | Source/closure-aware cache, generated ledger, scoped native evidence and bounded proof iteration. The called retention prepare guard is verified under `fn-sn-statep`. Store and pinned-peer proof-only repairs reduced named book costs on measured runs without changing theorem statements. | Restore combined certification after the consumer Store red, requalify a matching image, close maintained-guard/witness and reverse-closure gaps, and measure whole workflows. Proof speedups are iteration results, not new runtime correctness claims. |

## What this cycle taught us

The new topic event exposed a genuine classification defect: article replay
needed to exclude topic events. Other failures came from proofs assuming the
old Store shape or expanding irrelevant branches of growing recognizers. Both
matter, but only the first changes behavior. The second combined gate narrowed
the direct failures to consumer Store projection and configuration live state.
The configuration proof now certifies with its updater kept closed. The
consumer theorem's bounded REPL admission is a useful diagnosis, not a
certificate; a combined gate must still pass before an image is built.

Proof iteration is itself being measured. Closing irrelevant Store/index
definitions reduced two Store book wall times from 111.945 to 86.919 seconds
and 77.061 to 52.013 seconds on the named runs. The pinned-peer inbound book
fell from 55.35 to 8.79 seconds of ACL2 certification time on different source
closures. These numbers describe proof cost under their recorded toolchains,
not runtime throughput or an assurance percentage.

The registry is not a complete, automatically current explanation of the
system. Some in-progress rows retain historical limitations after the relevant
runtime behavior improved. The new certified-claim check addresses event and
source/closure support, not every prose assertion or coverage question. This
snapshot uses concrete evidence rather than interpreting every old note as
current truth.

The next useful milestones are a complete two-Store Mini exchange and an
interrupted BP transfer through durable reassembly, Store dispatch and
matching return evidence. Mini's one-Store B3 reply has now succeeded; its
remaining crash and independent-administration cuts are material. Their proofs,
caller refinements and hostile/fault traces advance alongside them. A green
closure is necessary evidence; it is not the final system-level conclusion.

## Evidence entry points

- [Last shared qualified image and selected tests](evidence/native-luna-e160-selected-2026-09-24.md).
- [Latest failed combined gate and its two direct proof reds](evidence/topic-index-f0d-combined-red-2026-09-24.md); [earlier combined gate](evidence/topic-index-8c61-full-gate-red-2026-09-24.md).
- [Scoped configuration proof repair](evidence/config-live-v6-proof-repair-2026-09-24.md).
- [Mini B3 signed reply, native post and cold verification on e160](evidence/mini-b3-e160-native-join-2026-09-24.md); [transaction-to-ACK join](evidence/native-mini-live-join-2026-09-24.md).
- [Owner frontier callback projection and limits](evidence/k0-owner-frontier-caller-2026-09-24.md).
- [Topic historical retry and anchor-generation gap](evidence/topic-history-historical-retry-p3-2026-09-24.md).
- [Host-reached retention preparation guard](evidence/retention-prepare-guard-2026-09-24.md).
- [Measured Store proof-cost repair](evidence/store-proof-cost-2026-09-24.md); [pinned-peer proof-cost repair](evidence/peer-inbound-pinned-cost-2026-09-24.md).
- [Reader, consumer and cold-clone experiment](evidence/native-poll-reader-clone-1d26-2026-09-23.md).
- [Protected two-host exchange](evidence/relocated-native-1836ed01-2026-09-23.md).
- [Earlier native BP admission](evidence/native-bp-admission-c1bb-2026-09-23.md).
- [Isolated filesystem EIO experiment](evidence/t16-private-eio-2026-09-23.md).
- [Assurance review follow-up](evidence/assurance-review-followup-e160442f-2026-09-23.md).
- [Proof registry](proofs.json), [trust and proof scope](../docs/proofs.md), and [active work](now.md).
