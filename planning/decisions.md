# Decision workbook

Status: D01, D02, D03, D04, and D17 have selected directions from the user on
2026-09-18; D07's native-only runtime boundary was reaffirmed on 2026-09-21.
Exact native encodings and cryptographic profiles remain open; other
choices remain proposals. This is the agenda for discussion, not an approval
gate for routine work. Record answers here with their rationale and consequences.
No unanswered recommendation is silently promoted to an agreed decision.

**This is the full decision backlog, not the next questionnaire.** The
[current work](now.md) can proceed without answering the remaining rows. The
coordinating agent owns routine reversible implementation choices and brings
user-facing tradeoffs forward with concrete examples as they become relevant.

The archived [three-cycle plan](archive/swarm-cycles.md) scheduled concrete
decision packets alongside implementation. Independent local service, storage and DTN work can
proceed under explicit experimental profiles. Its proposed sequencing and UI
placement do not independently select a source grammar, cryptographic suite or
release scope. The later D01/D17 answers below now fix the source boundary and
NNTP/command-line-first sequencing.

## Already agreed

| ID | Direction |
| --- | --- |
| A01 | fn serves human and AI communication, with NNTP as its initial news interface. |
| A02 | Use executable ACL2 semantics and pursue meaningful proofs of the running core. |
| A03 | Build a specialized persistent store: immutable objects, local transactions, recoverable state. |
| A04 | Represent retention/delivery obligations explicitly and persist them alongside content. |
| A05 | Sites remain independently useful while disconnected; batches can travel by network or carried media. |
| A06 | BPv7 disconnected exchange is a current architectural path; integrate it early with durable fn work and receipts. LTP/long-delay profiles and mission qualification retain explicit limits and assumptions. |
| A07 | Do substantial design up front, implement in stages, and keep evidence distinct from intent. |

These record the user's architectural choices. Exact schemas, cryptographic
suites, and deployment profiles remain open. Local retention and first-release
authorship support are resolved below.

## Decisions to make together

D01–D04, D07 and D17 now have selected directions. The remaining table is a long-term
backlog; detailed byte profiles and key lifecycle still need design. The
[privacy note](../specs/privacy.md) keeps the eventual group-encryption protocol choice open.

| ID | Question | Recommendation | Main alternative / cost | Needed by |
| --- | --- | --- | --- | --- |
| D01 — decided | What is the durable source of a native article? | **Selected:** sign the exact authored source bytes; mutable Path/Xref and gateway injection records live in separate projections. Preserve unknown headers and MIME bytes. Envelope/signature encoding remains D08/D09. | Treat every wire variant as the only source; simpler ingestion, harder portable authorship and semantic conflict handling. | M1 model, M2 bytes |
| D02 — decided | Do native messages support author signatures in the first release? | **Selected:** native author signatures plus explicit gateway provenance for ordinary unsigned NNTP clients. | Gateway-only first was declined. Concrete suites/key workflow remain D09. | M1 identity model, M3 release |
| D03 — decided | What does a successful local post promise to retain? | **Selected:** keep until explicit authorized release, no automatic expiry; refuse new obligations when capacity is unavailable. | Automatic bounded retention was declined. Exact release authority/terms still need specification. | M1 obligation model |
| D04 — decided | Is private encrypted communication in the first release? | **Selected:** shared community groups first; design confidentiality and metadata boundaries now. | Private encrypted groups in the initial release are deferred. The later cryptosystem remains open. | M1 scope |
| D05 | How much NNTP constitutes the first usable release? | Complete proposed READER + mandatory commands + POST + OVER; configured unmoderated groups. | A smaller experimental subset, explicitly without full bundle advertisement or broad client compatibility claims. | M1 session scope, M3 |
| D06 | How far down should we implement indexes initially? | Journal/checkpoint authority with rebuildable in-memory indexes; add disk indexes when scale demands. | Disk-resident indexes immediately; earlier scale, larger recovery/refinement proof surface. | M2 |
| D07 — decided | What execution host should we target? | **Selected:** native Lisp deployment, executing ACL2 definitions directly; no Python in the deployed node, CLI, launchers or runtime helpers. Continue the existing ACL2/SBCL integration with pinned versions. Python remains development/test tooling. | Python service/bridge retained only as a development oracle; it cannot satisfy the production v0 gate. | v0 across all waves |
| D08 | What portable encoding and evolution policy? | Restricted deterministic CBOR, exact schema versions, bounded parsing; unknown objects may be carried opaquely but not interpreted as authority. | A custom binary grammar, or textual encoding; different tooling, size, and canonicalization costs. | M2 |
| D09 — suite selected; custody/succession details open | How do keys, algorithms, and signatures evolve? | **Selected 2026-09-21:** native signatures require Ed25519 **and** ML-DSA-65 from the first release, for long-lived authenticity. Both must verify against the enrolled key set; no classical-only fallback. Algorithm-tagged containers bind the required profile. Custody and recovery authority remain separate design work. | Ed25519-first with later hybrid upgrade was declined. | M2 |
| D10 | How do we handle time, old backups, and forks? | Local counters plus explicit origin incarnations; causal references; restore/clone procedure creates or validates a fresh sequence namespace. | Depend on a central identity/sequence service; reduces offline autonomy. | M1 model, M4 restore tooling |
| D11 | Who controls group identity and policy? | Local aliases over an explicit group authority/configuration identity; initially simple owner/admin succession. | Globally shared mutable names or general multi-party governance from v1; more conflict and authorization rules. | M1 local, M4 portable |
| D12 | When may a forwarding node release responsibility? | Only after committed, matching application evidence satisfies named terms; start with cooperative trusted peers and explicit archive pins. | Require multiple independent retainers before release; stronger failure tolerance, more capacity and failure-domain policy. | M1 model, M4 |
| D13 | When may history and evidence be forgotten? | Preserve duplicate history initially; add proved pruning with an explicit old-input/resurrection policy. | Finite age/epoch windows from v1; bounded metadata sooner, delayed old letters may become inadmissible. | M1 invariants, M5 pruning |
| D14 | Which platform and fault claims come first? | Pure crash model first; qualify one Linux local-filesystem profile before deployment durability claims, while supporting macOS development. | Qualify macOS and Linux together; more adapter/platform work before the first durability claim. | M2 |
| D15 | How should long-delay exchange use scarce contacts? | Bounded proactive batches, resumable objects, cached peer knowledge, explicit quotas; add optimized reconciliation later. | Interactive inventory negotiation first; efficient on good links, consumes more round trips. | M4 |
| D16 | What resource envelope are we designing for? | Define a small-community reference profile and a simulator stress profile; measure before fixing article/chunk/segment sizes. | Select hard universal limits now; earlier ABI certainty but less evidence. | M1 bounds, M2 layout |
| D17 — decided | What is the first human interface? | **Selected:** NNTP and command-line clients first; web later. Prioritize native signing/posting and operator CLI tools in the current cycles. | Build the web experience before reader interoperability; earlier bespoke UX, weaker early protocol feedback. | M3 validation, M6 |
| D18 | How much should we prove before calling the first release usable? | Core invariants, codec properties, and conditional crash recovery first; state host/crypto/platform assumptions explicitly. | Ship an experimental server sooner with a smaller proved subset and equally explicit limits. | M1 proof scope, M3 release |

## Consequences worth thinking through

### D07: native runtime, development tools outside it

The 2026-09-21 user clarification says they do not want Python in a running fn
process. `cv` recovery also found the earlier 2026-09-19T14:47:06.020Z criticism
in Claude session `8d4521d3-3e8f-4a05-a722-a9c843463a45`: “I don't understand why
we have so much going on in Python anyway, maybe it was a crutch we shouldn't
have reached for?” The later Python service work did not close that concern.

The production boundary is now explicit in [the host contract](../specs/host.md#selected-production-runtime),
HST-001 and SCN-015. This selects native execution and excludes Python runtime
helpers; it does not freeze a new crypto suite, turn raw Lisp into proved code,
or remove any selected v0 feature. Keep Python tools for development/evidence,
and carry the actual ACL2 machines into the native host rather than translating
their decisions into a second implementation.

### Production raw insertion (selected 2026-09-23)

The user selected: raw `store ROOT post` is developer-only; production
posting uses the normal submission path. This closes the policy question in
the da5fd8cb campaign's N1 finding. A later import/repair interface needs its
own explicit authority and provenance contract; raw insertion is not that
interface. Inspection and recovery remain production operations.

Implementation and image evidence are still owed. HST-001 and SCN-015 track
rejection of raw insertion before opening or mutating the store, alongside
successful ordinary production submission and developer diagnostic use.
See [the native host contract](../specs/host.md#the-native-host).

### D01: source bytes and compatibility

We need a concrete example containing native author data, generated injection
fields, relay-mutated headers, an unknown header, and a legacy unsigned article.
The [article-byte examples](../docs/article-byte-examples.md) now supply those
views and two candidate signing-preimage encodings. D01 selects exact authored
source bytes, with mutable trace and gateway injection records outside that
source signature in separate projections. The encoding candidates, precise
profile grammar and legacy-variant comparison policy remain design work.
Do not settle this by saying “canonicalize headers”: that hides the difficult
part. Acceptance must still handle ordinary NNTP clients without fn extensions.

### D02 and D09: who holds the keys

Native author-signature support does not require every post to be signed. It
requires honest distinctions among an author's signature, a host signing on an
authorized principal's behalf, and a gateway attesting only to submission.
The user selected mandatory Ed25519 plus ML-DSA-65 from the first release on
2026-09-21 and reaffirmed post-quantum support. Both component signatures must
verify; unknown/absent components do not downgrade the requirement. This is a
suite decision, not a claim that its implementation or security is proved.
Key custody on agent hosts, human signing workflow, rotation/recovery authority
and offline revocation semantics remain to be specified. Private-group encryption
is a separate decision and is not selected by this signature choice.

The local-control implementation may let a same-owner operator install the
next durable public-key snapshot or a principal-specific revocation tombstone.
That is a choice about this Store's permission for *new local* `hybrid-author`
requests: the newest recognized snapshot for A supersedes A's older local
permission, while enrolling or revoking B does not change A. It is not a
decision that the operator speaks for the principal at remote sites, that an
old signature ceases to verify, or that accepted historical verdicts change.
The separate [succession proposal](author-key-succession-proposal.md) keeps
the unselected custody, portable authority and partition policies explicit.

### D03 and D13: keeping a letter versus keeping a promise

A local archive pin can have an explicit owner-controlled release operation.
That operation does not automatically erase downstream copies or discharge an
independently accepted forwarding obligation. Indefinite terms trade automatic
expiry for admission refusal at capacity. History retention also consumes space;
decide acceptable behavior for a letter reappearing years after its body was removed.

### D04: privacy scope

Transport authentication, private membership, and end-to-end content secrecy are
different features. An encrypted design must state what group names, object sizes,
inventories, receipts, and relationships disclose, and what an offline revoked
member can still read. Shared groups first is a scope choice, not a claim that
unconfigured public access is acceptable.

The user's stated priority is cryptographic quality. The current recommendation
is shared groups first, explicit privacy boundaries now, and evaluation of an
established group protocol/implementation before private groups ship. MLS is a
candidate, not a selected dependency. The [privacy note](../specs/privacy.md)
compares its integration questions with Megolm and explains the archive/key-
retention distinction. D04's release scope is selected; the protocol choice and
its requirements remain open. MLS is one candidate, not a default commitment.

### D05 and D11: groups and cross-posts

Proposed initial local policy: reject a new local cross-post if any requested
group is unknown or disallowed, so the author's requested local acceptance is
all-or-none. Later incoming transfers may retain the original group list while
indexing only configured admissible groups. Define each separately and make
authorization explicit. An article naming a group does not create it.

### D12: trusted relays and failure tolerance

One successor's matching retention receipt can discharge one handoff obligation
under a cooperative-peer model. Requiring two independent durable copies is a
different contract. Decide the failure domains and whether the origin's archive
copy remains independently pinned. Signature verification alone cannot prove the
peer physically honored its promise.

### D14 and D18: what the proof covers

Choose a disk failure model and an adapter contract before claiming crash
durability. Distinguish process death, power loss, detected corruption, and
replacement by an old valid snapshot. The last requires an independent freshness
anchor if it must be detected. Flight qualification is a later deployment effort,
not the consequence of choosing an algorithm with a proof.

## Engineering decisions to close with evidence

These belong on the agenda, but arbitrary numbers would be premature. Each gets
a recorded choice before its dependent format or algorithm is frozen.

| Detail | Evidence / artifact needed | Parent |
| --- | --- | --- |
| Native/legacy article profile | Byte examples, collision/variant policy, RFC dependency audit | D01 |
| Hash/signature suites and preimages | Threat/longevity goals, supported libraries, test vectors | D09 |
| Sector/write isolation and commit marker | Crash model, barrier sequence, platform experiment | D14 |
| Checkpoint generation selection | Recovery algorithm and exhaustive small-state crash traces | D06, D14 |
| Chunk/segment sizes and dedup strategy | Representative workloads, transfer interruption costs | D15, D16 |
| Group/range index representation | Memory and query measurements, completeness argument | D06 |
| Maximum article, nesting, queues, reservations | Explicit resource profile and denial-of-service cases | D16 |
| Receipt field grammar | Lost/replayed receipt trace and authority rules | D12 |
| Tombstone/history compaction | Old-media reimport trace and bounded-space argument | D13 |
| Deployment authentication and transport protection | Concrete clients, principal mapping, exposure model | D04, D07 |

## Resolution log

When deciding, append a dated entry: decision ID, selected choice, rationale,
affected requirements, consequences, and superseded entries if any. Update the
table and dependent specifications in the same change. Preserve why a choice was
made. Only explicit answers are recorded as selected choices.

### 2026-09-18: D02 — portable authorship

User selected native author signatures plus legacy gateway provenance for the
first release. This establishes the capability and honest provenance distinction;
it does not require every legacy post to carry an author signature. Affects
OBJ-003, OBJ-007, ENC-003, NNT-004, D01, D09, and the M3 release criteria. Key custody,
delegation, recovery, and concrete signature profiles remain open.

### 2026-09-18: D03 — local retention

User selected keeping posts until explicit authorized release, with no automatic
expiry and refusal of new obligations when reserved capacity runs out. Affects
RET-001, RET-002, RET-005, RET-006, NNT-005, and STO-002. This defines the default
local archive pin; it does not automatically release separate peer obligations
or promise that independent remote copies can be erased. Receipt/release details
remain D12 and history pruning remains D13.

### 2026-09-18: D04 — shared groups first, encryption design open

The user agreed with shared community groups first and privacy boundaries now,
while emphasizing that MLS's requirements may not fit disconnected operation.
Evaluate the requirements and relevant established or research protocols before
selecting a private-group system. Do not equate an interesting ePrint proposal
with a production-ready implementation or invent a new ratchet in the meantime.
This resolves release scope, not D09's cryptographic profiles or key management.

### 2026-09-18: A06 — BP is central to the active path

The user corrected the placement of BP as a future additional interface: its
disconnected store-and-forward capabilities are central to fn. BPv7 integration,
durable transfer work and application receipts now proceed alongside local
service development. They do not wait for complete NNTP, compaction, indexes or
UI work. This selects architectural priority, not a particular BPA, EID scheme,
cryptographic suite, portable encoding or qualified mission profile. The
[BP path](../specs/bp-path.md) defines the first complete experimental slice.

### 2026-09-18: D01 — exact authored source and separate projections

User selected “Yes, exact source bytes plus separate projections.” Native author
signatures bind the exact authored source octets, preserving unknown allowed
headers, folding and MIME/body bytes. Mutable NNTP Path/Xref and gateway injection
records belong to separate projections/provenance, outside that source signature.
Projection changes must not rewrite the signed source or require stripping fields
after signing. Legacy received bytes and gateway evidence remain explicit; this
does not infer an unsigned legacy article's original authored bytes.

This resolves the architectural source/signature boundary for OBJ-003, OBJ-007,
ENC-003 and NNT-004. It does not select the concrete native envelope, either
example preimage encoding, CBOR/COSE, a hash/signature suite, key lifecycle, or
legacy equivalence/quarantine policy. D08/D09 and those profile details remain
open. C1-11 can now design against this fixed boundary rather than compare the
two source architectures. No implementation or proof completion follows.

### 2026-09-18: D17 — NNTP and command-line clients first

User selected “NNTP and command-line clients first; web later.” The next cycles
prioritize ordinary newsreader interoperability, native signing/posting tools
and operator/agent CLI workflows over the same durable owner path. C2-11 becomes
that client/operator task; a web reader/composer stays later M6 interface work.
This supersedes the provisional proposal to bring web into C2. It introduces no
new protocol or release requirement and does not defer the selected D02 native
signature capability.

### 2026-09-20: D14-a — the pending transaction name in the byte-store/kernel relation

An engineering decision under D14 (`Sector/write isolation and commit marker`),
resolved from the host's own commit program rather than from taste, on the
question lane `w9/storage-2` raised and did not decide.

**Selected:** keep `books/byte-store-scan.lisp`'s
`(fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))`; the form
[`specs/crash-model-v2.md`](../specs/crash-model-v2.md) §3.2 proposed,
`(fn-bs-txn-name (len (fn-sf-records ks)))`, is withdrawn. The unreachable
image §3.2 was worried about is excluded instead by a phase-indexed clause on
the record LIST, not by a blanket equality of counts.

**Evidence: every cut between the record write and the pending link's removal,
in `tools/run_store.py` at `ca8a2ef`.** The link is issued at
`Store.publish:1334` and is removed from the pending list either by
`fsync_dir(self.transactions)` at `publish:1348` (the process survives) or by
`fsync_dir(self.transactions)` at `Store.recover:1187` (the process died with
it pending and the next one drains it). That gives two windows and six cut
states, and the two forms disagree in the second window.

*The publish window.* With `R = (fn-sf-records ks)` at the link: the only
transition that appends to `fn-sf-records` is `fn-sf-record-dir-result` with
`:ok` (`books/store-files.lisp:507`), which the host issues at
`publish:1353`, strictly after `fsync_dir` at 1348 returned — and that
`fsync_dir` is the model's `fn-bs-fsync-dir :transactions`, which empties that
directory's pending list (`books/byte-store.lisp:549`, `fn-bs-fence-dir` 370).
So at `record-linked` (1338) and `record-attempted` (1346), and on the
`record-link :error` branch (1336, kernel `:fenced-record`, records
unchanged), the transaction directory is non-quiet and the durable record list
is still exactly `R`. At `record-durable` (1352) the durable list is
`R + [candidate]` — and there the directory is quiet. Both forms name
`(fn-bs-txn-name (len R))` at every cut of this window: they agree.

*The recovery window, which decides it.* A process-death cut at
`record-linked` leaves the entry operation pending in the kernel's cache, not
lost: process death is not power loss. The next process's
`Store.durable_records` (1100) scans the live directory — the view — so it
reads `R + 1` records, and `acl2.recover` (1164) builds its `:replaying` image
from that scan (`host/store-node-host.lisp:39`, "constructs its own replaying
kernel image"). At `recover-replayed` (1179) and at the first two
`recover-barrier` cuts (1200, after the config and frontier file fences and
before `fsync_dir(self.transactions)` at 1187) the durable namespace still
holds `R` names while `(fn-sf-records ks)` already holds `R + 1`. There
`(fn-bs-txn-name (len (fn-sf-records ks)))` is `(fn-bs-txn-name (1+ R))` and
names nothing; `(fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))`
is `(fn-bs-txn-name R)`, which is the pending entry's actual name. This is
also the campaign's ordinary path, not a corner: `tests/campaign` kills at
`record-linked` and reopens.

**Consequences.** (1) The candidate equality
`(equal (len (fn-bs-durable-records bs)) (len (fn-sf-records ks)))` "whenever
the transaction directory is not quiet" is REJECTED: it is false at those
three recovery cuts. (2) `fn-bs-pending-matches-phase`'s transaction arm
becomes three-way — quiet; the publish window, which carries
`(equal (fn-bs-durable-records bs) (fn-sf-records ks))` and so excludes the
duplicate image outright; and a new recovery window
(`fn-bs-replay-visiblep`: `:replaying`, `:recovering`, `:fenced-recovery`),
which carries `(equal (fn-sf-records ks) (append (fn-bs-durable-records bs)
(list <the pending link's record>)))`. (3) §3.2's claim that the relation is
established at process start "because the image has no pending operations" is
withdrawn in the same change: after a process-death cut it is established with
a non-empty pending list, which is what the recovery window is.

**What this exposes and does not close.** In the recovery window a crash can
still produce the `R`-record image, and `fn-sf-crash-imagep`
(`books/store-files.lisp:593`) does not admit it: the kernel's phase
vocabulary has no freedom for "replayed, not yet re-fenced". K2 therefore
takes `(not (fn-bs-replay-visiblep ks))` as a hypothesis and the recovery
window is recorded as the open obligation K2r, whose content is that such a
state carries no success (`fn-sn-initial nil 0`; `Store.recover` runs exactly
once per process, at open — `run_store.py:1674`, `run_owner.py:660`,
`fn9p.py:428`, `run_reader.py:313`, `run_bp_ingress.py:132`), so nothing
acknowledged can be lost there. Widening the kernel predicate instead was not
taken: it is a change to the interface `books/store-observed.lisp` and the
store-node closure take as a premise, and it is not this lane's to make
silently.

### 2026-09-20: D14-b — the recovery freedom is a second recognizer, not a wider gate

The companion to D14-a, taking the cross-cluster proposal `w9/storage-3` left on
the board, and deciding it against the shape that proposal named.

**The question.** D14-a established that in the recovery window
(`:replaying`, `:recovering`, `:fenced-recovery`) a process's record list is its
own scan of the VIEW, so its last record may be the entry operation a dead
process left pending, and a crash before the five recovery fences drops it.
`fn-sf-crash-imagep` (`books/store-files.lisp:593`) had no freedom for that, so
`K2` took `(not (fn-bs-replay-visiblep ks))` and the window became the open row
`K2r`. The proposal was to widen `fn-sf-crash-imagep` itself.

**Selected:** add `fn-sf-recovery-crash-imagep`, a second recognizer with the
third arm, and leave `fn-sf-crash-imagep` byte-for-byte unchanged.
`fn-sf-crash-imagep` is the RELIANCE predicate — the gate of `fn-own-reopen`
(`books/owner.lisp:911`) and the premise of every reopen theorem — and
`fn-sf-recovery-crash-imagep` is what the PLATFORM may leave. `K2`'s conclusion
names the second; nothing takes it as a hypothesis.

**Why not the proposal: a counterexample, mechanized.** `*own-reopened*`
(`tests/acl2/owner-tests.lisp`) is an ordinary reachable owner. Its store is a
recovery-window state; its own success history is empty, because
`fn-sn-open-observed` keeps no ghost
(`fn-sn-open-observed-success-exact-history`); and its LEDGER still names both
of its records, the second of which an earlier process completed and
acknowledged and which is therefore fenced. The emptiness gate the proposal
relied on — "such a state carries no success" — is a fact about *this state's*
success list, not about what earlier processes promised, and it does not
protect that record. A widened `fn-sf-crash-imagep` therefore lets
`fn-own-reopen` take the rolled-back image, after which
`fn-own-ledger-durablep` is false and `fn-own-reopen-preserves-relation` is
FALSE. `fn-bprv-crash-image-extends-history` and
`fn-bprv-observed-reopen-facts` fail the same way. Both halves of the
counterexample are `assert-event`s: the kernel half in
`tests/acl2/store-observed-traces-tests.lisp`, the owner half in
`tests/acl2/owner-tests.lisp`.

**And no narrower kernel gate exists.** Which of a state's records are fenced
is a fact about the byte store's pending list
(`fn-bs-store-relation`, `books/byte-store-scan.lisp`), not about the kernel
state: a `:replaying` state reached by `fn-sn-open-observed` and one reached by
`fn-sf-crash ... :absent` are the same tuple, and only the first may lose its
tail. A marker field would not help, because the reopening process is the one
that cannot know. So the freedom cannot be a gate on what a consumer may rely
on, and must be a separate conclusion.

**For the same reason `fn-sf-crash-choicep` gains no third choice.** Giving the
trace language's crash event a rollback choice would let a trace drop a record
an earlier process acknowledged and would falsify
`fn-snrt-acknowledged-record-retained-across-observed-reopen`. The second
constructor is `fn-sf-crash-rollback`, and `fn-sf-image-crash` selects between
the two.

**What this closes.** `K2` loses its hypothesis: its conclusion is
`fn-sf-recovery-crash-imagep`, whose recovery arm carries the empty success
history as a conjunct. `K2r` stops being an open row and becomes
`fn-sf-recovery-admissible-image-facts`, a proved kernel theorem: an
acknowledged pair of the pre-crash state names a record of *every* image the
platform may leave, the rolled-back one included, because that arm and a
non-empty success history cannot both hold. `K3` extends to all three arms
(`fn-sf-recovery-crash-realizes-every-admissible-image`) and its old form
stands unchanged beside it. `fn-sf-stable-records` is the prefix no image can
lose and `fn-sf-recovery-crash-image-extends-stable-records` is the exact
retention guarantee.

**What it does not close.** `K2` itself is still open: it rests on `K1`, whose
namespace clause D14-a's lane closed and whose other three clauses are not
proved. And a second, distinct freedom was found while checking `K2` and is NOT
taken here: in the recovery window the pending operation may be the FRONTIER
rename rather than a transaction link, so a crash can also roll the frontier
back to the durable one — a value the kernel does not hold, since
`fn-sf-frontier-candidate` is `nil` in that window. `K2` as
`specs/crash-model-v2.md` §3.3 states it is therefore still false when the
recovery window is entered with a pending `:root` entry operation (die at
`frontier-replaced`, `tools/run_store.py:1305` at `b79b29c`; reopen; the rename
is drained only by `fsync_dir(self.root)` at `:1216`, the fourth of the five
recovery barriers, while the cuts are `recover-replayed` at `:1207` and
`recover-barrier` at `:1228`). Closing it needs a clause in
`fn-bs-replay-matches-scan` saying the durable frontier is the scanned one
minus one, and a matching frontier arm here; that is the next packet, not this
one. **Taken 2026-09-20 as D14-c below**, in that shape, with the gate
`fn-sf-frontier-rollback-visiblep` and one conjunct D14-b did not name: the
two rollbacks are exclusive.

### 2026-09-20: D14-c — the frontier rollback is a fourth arm with a record-list gate, and the two rollbacks are exclusive

The packet D14-b named and did not take (lane `w11/bytestore-k2`). Nothing in
D14-a or D14-b is reopened: `fn-sf-crash-imagep` stays byte-for-byte unchanged
and is still the reliance predicate, and the counterexample from
`*own-reopened*` still says why.

**The question.** The recovery window is entered with a pending `:root` rename
as well as with a pending `:transactions` link. `Store.advance_frontier`
issues `os.replace` and the host cuts at `frontier-replaced`
(`tools/run_store.py:1305`); the next process's `_load_frontier` reads the
VIEW, so the kernel it builds holds `old+1` while the durable name still holds
`old`; and `:root` is drained only by `fsync_dir(self.root)` at `:1216`, the
FOURTH of the five recovery barriers, with cuts at `recover-replayed`
(`:1207`) and `recover-barrier` (`:1228`). A crash at any of those rolls the
frontier back to a value the kernel holds nowhere — `fn-sf-frontier-candidate`
is `nil` in the window, and `fn-sf-frontier-new-visiblep` is false there. So
`specs/crash-model-v2.md` K2 was FALSE in that sub-case.

**Selected:** a fourth arm on `fn-sf-recovery-crash-imagep`,

    (and (fn-sf-frontier-rollback-visiblep s)
         (equal frontier (1- (fn-sf-frontier s)))
         (equal records (fn-sf-records s)))

gated by

    (defun fn-sf-frontier-rollback-visiblep (s)
      (and (fn-sf-recovery-visiblep s)
           (null (fn-sf-successes s))
           (posp (fn-sf-frontier s))
           (fn-sf-record-listp (fn-sf-records s) 0 0 (1- (fn-sf-frontier s)))))

with `fn-sf-crash-frontier-rollback` as its constructor and
`fn-sf-image-crash` selecting among the three. The matching byte-side clause
is in `fn-bs-replay-matches-scan`.

**Why the record-list conjunct is the gate and not a convenience.** It admits
exactly the reachable window. `fn-sf-statep` requires every record's txid below
the frontier, and the allocator reserves txid `frontier-1` for the record
published *after* the rename is durable (`fn-sf-candidatep`: the candidate's
txid is `frontier-1`). So while the rename is pending no record holds that
txid — which is exactly the conjunct — and the moment that record is published
the conjunct is false and the frontier can no longer roll back. The same
conjunct does three jobs: it makes the rolled-back value a kernel state
(`fn-sf-crash-frontier-rollback-preserves-state`), it keeps
`fn-sf-recovery-admissible-image-facts` true of the image, and it makes the
image replayable at its own frontier
(`fn-snt-recovery-admissible-crash-image-is-recoverable`, through
`fn-snt-history-recoverable-under-record-bound`).

**Why there IS a success-history conjunct, and it is not the record
rollback's reason.** Rolling the frontier back drops no record, so every
acknowledged pair still names one and nothing needs protecting. The conjunct
is the only kernel-visible mark that separates a `:replaying` state built by
`fn-sn-open-observed` from *this process's scan* — where the rename may still
be pending — from one reached by `fn-sf-crash`, where the model already knows
it is not. A crash from `:reserved` has observed `(:frontier-directory :ok)`,
so `fsync_dir(self.root)` returned and the rename is durable; and a crash from
`:frontier-attempted` is already covered by `fn-sf-crash`'s `:old` choice,
because `fn-sf-frontier-new-visiblep` holds there. Without the conjunct the
predicate would admit, on a crashed `:reserved` state, an image the same model
refutes — `*fn-so-reserved-crashed*` in
`tests/acl2/store-observed-traces-tests.lisp` is that state, and it is the
tooth. `fn-sn-open-observed` keeps no ghost
(`fn-sn-open-observed-success-exact-history`) and `Store.recover` runs once
per process, so the conjunct costs nothing reachable; and
`fn-bs-replay-matches-scan` already carries `(equal (fn-sf-successes ks) nil)`,
so it costs `K2` nothing either. As in D14-b it is necessary and not
sufficient, which is why the predicate is a conclusion and never a premise.

**Why the two rollbacks are exclusive.** The arm carries
`(equal records (fn-sf-records s))`, so the image that loses the rename AND the
link is not admitted. A recovery window holds at most one pending authority
entry operation: `advance_frontier` fences `:root` and `publish` fences
`:transactions` before either returns, and neither runs before recovery
completes, so a dead process leaves at most one un-fenced authority entry
behind. Outside the window `fn-bs-pending-matches-phase` gets that for free —
`fn-sf-frontier-new-visiblep` and `fn-sf-record-present-visiblep` are disjoint
phase sets — and inside it the phase says nothing, so the relation says it:
`fn-bs-replay-matches-scan` now carries `(null txn-ops)` under `root-ops`.

**`fn-sf-crash-choicep` again gains no choice**, for D14-b's reason in its
frontier spelling: a trace that could roll the frontier back would let a later
trace re-issue a txid an earlier process had already published under. The
record-list gate is what excludes that, and a trace event carries no gate.

**What this closes and what it does not.** K2's *statement* is now true of
every image the platform can leave in the recovery window; K2 itself is still
open, and what it waits on is unchanged — K1's other three scan clauses. The
byte-side clause is an obligation on K0, not a theorem.

### 2026-09-20: D19 — the header-value wildmat profile, and what fn's 501 was

**The question.** RFC 2980 §2.9's XPAT matches a pattern against a *header
value*. RFC 3977 §4.1's `<wildmat-exact>` excludes SP, and §2.9 says "If there
are additional arguments the are joined together separated by a single space
to form one complete pattern", so every multi-token XPAT pattern carries an
SP. fn joined correctly (`fn-nntp-xpat-join`) and then parsed the join with
the §4.1 grammar, so it answered `501` to every one of them and could not
phrase-search a header, which is XPAT's ordinary use. Where does the grammar
for a header-value pattern live?

**Which of the three the 501 was.** Not an RFC requirement, and not a stronger
fn guarantee. §2.9.1's response list is `221 / 430 / 502` and contains no 501
at all; §4.1's grammar governs `newsgroup-name = 1*wildmat-exact` (§9.8), and
§4.1's own note gives its reason — "This should not be a problem, since these
characters cannot occur in newsgroup names, which is the only current use of
wildmats" — which is exactly the assumption XPAT breaks. So the 501 was **a
local policy choice, and an unintended one**: the consequence of reusing the
newsgroup-name grammar in a position the RFC did not put it in. It is not
justified by the RFC and it is not a guarantee anyone wanted, so it is
withdrawn rather than defended. A pattern that parses and does not match is
§2.9's 221 with an empty list, which is also what INN 2.7.4 answers for the
same command (`planning/evidence/inn-xpat-2026-09-20.md`).

**Selected: a second character profile over ONE parser.** The three candidates
were a second recognizer beside `fn-wildmat-exactp`, a profile parameter
threaded through the existing scanner, and a separate parser. The costs
decided it.

- *A separate parser* duplicates the scanner, `fn-wildmat-parse-one` and the
  whole result-shape induction — including `fn-wm-parse-one-success-pattern-listp`,
  whose proof carries twelve subgoal hints. Two copies of that is the most
  expensive of the three and the one that rots.
- *A profile parameter* on `fn-wildmat-scan-pattern` and
  `fn-wildmat-parse-one` changes their arity, which restates every theorem in
  `books/wildmat-parser-invariants` and `books/wildmat-utf8-invariants` and
  moves the subgoal names those twelve hints are attached to.
- *Selected:* the scanner scans the **wider** set, and the newsgroup-name
  entry point `fn-wildmat-parse` recovers §4.1 with a **precheck** on the
  decoded code points (`fn-wildmat-rfc3977-codepointsp`) before scanning.
  Arities do not change, no statement in the matcher book changes, and the
  twelve subgoal hints did not move. The measured cost was a predicate rename
  in two books and one new induction; all five wildmat roots certified on the
  first attempt after it.

**The profile, in one rule.** A pattern is a fragment of a command line, so
every printable US-ASCII character, SP, and every UTF-8 non-ASCII character is
a literal, less the four wildmat metacharacters `!` `*` `,` `?`. Controls and
DEL stay out, as they are out of §4.1. Against `<wildmat-exact>` that is
exactly four more code points — `%x20 SP`, `%x5B [`, `%x5C \`, `%x5D ]` —
and `fn-wildmat-text-exactp-adds-exactly-four-code-points` says the difference
is no larger.

**What licenses it.** §4.3: "An NNTP server or extension MAY extend the syntax
or semantics of wildmats provided that all wildmats that meet the requirements
of Section 4.1 have the meaning ascribed to them by Section 4.2." fn discharges
that proviso rather than asserting it: `fn-wildmat-parse` accepts and refuses
exactly the octet lists it did before, with the same reason keyword, because
the precheck runs first; and
`fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items` states that the
widened matcher test is the pre-D19 body, verbatim, on every §4.1 item.

**The cost, named.** §4.1 omitted `[`, `\` and `]` because "A future extension
to this specification may provide semantics for these characters" — brackets
for sets, backslash for quoting. Reading them as literals in the *header*
profile spends that reserved syntax there, and adopting a future §4.3
bracket-set extension for header patterns would then be a behaviour change for
fn. It is spent knowingly: `[PATCH]` in a Subject is the ordinary case and
refusing it is the same defect as refusing SP. §4.1 conformance is untouched
either way, since no §4.1 wildmat can contain those characters. The
newsgroup-name profile keeps all three reserved.

**Not changed, and confirmed unaffected.** fn reads `,` in an XPAT pattern as
wildmat alternation where INN's `uwildmat_simple` reads it as a literal; §2.9's
"At least one pattern in wildmat must be specified" is on fn's side. 44 is an
exact item in neither profile, so D19 does not touch it, and the assertion that
pins it is unchanged.

Affects NNT requirements for XPAT, `specs/wildmat.md`, `specs/nntp-audit.md`
§2.9, `books/wildmat.lisp` and the three wildmat invariants books. Closes
OB-XPAT-SPACE. Supersedes nothing.


### 2026-09-20: D20 — the outbound guard is cured by a total take and drop, not by a carried length

The send-side half of the served-path guard cost that
`planning/lanes/HANDOFF-w9-dtn-e2e.md` §7 opened and `w11/tcpcl-theory` closed
on the receive side. `specs/tcpcl.md` §6 named two candidate cures and left the
choice open; this entry takes one and says why the other is worse.

**The question.** The native host reaches the session machine through the ACL2
executable counterpart of `fnn-call` (`host/native/io.lisp`), which checks the
callee's guard on every call. `fn-tcl-session-cheapp` is that guard, and it
carries `(fn-tcl-outboundp (fn-tcl-session-outbound s))` whole. Two of
`fn-tcl-outboundp`'s conjuncts measure the unsent suffix —
`(fn-cbor-octet-listp remaining)` and
`(equal (+ sent-len (len remaining)) total)` — so a send of n octets re-walked
the suffix once per socket chunk: O(n²/chunk) in guard checking alone. The two
conjuncts could not simply be dropped, because the length equation was the only
fact that discharged `fn-tcl-pump`'s `(fn-tcl-take k remaining)` and
`(fn-tcl-drop k remaining)`, whose guard was `(fn-tcl-has octets k)`.

**Selected:** make `fn-tcl-take` and `fn-tcl-drop` guard-total — guard
`(natp n)`, the `fn-wire-ag-car` `mbe` pattern of `books/wire.lisp`, logical
definitions unchanged — and split `fn-tcl-outbound-cheapp` off
`fn-tcl-outboundp` exactly as `fn-tcl-inbound-cheapp` was split off
`fn-tcl-inboundp`, with `fn-tcl-outboundp-is-cheap` as the only link. The
ordering `(<= sent-len total)` that the length equation used to imply is carried
explicitly, because `fn-tcl-pump` needs it to know its chunk is a natural. Every
keystone still speaks of `fn-tcl-sessionp`, which still carries both dropped
conjuncts and is still proved preserved.

**Rejected: a `remaining`-length scalar carried in the outbound record.** It
does not discharge the obligation. `(fn-tcl-has remaining k)` is a statement
about the list, not about a scalar, so a carried `rem-len` relieves it only
through the agreement `(equal rem-len (len remaining))` — and that agreement
costs a walk of the suffix to check, so it cannot live in the cheap recognizer
either. The carried length would therefore have to be combined with guard-total
take and drop anyway; on its own it renames the equation rather than removing
it from the served path. It is also strictly more change for that: the outbound
record widens from seven fields to eight, every `fn-tcl-make-outbound` call site
and the records book move with it, and the new field is state that can disagree
with reality, so the agreement becomes one more conjunct of `fn-tcl-sessionp` to
prove preserved by every transition. The third shape considered and rejected
with it — letting `fn-tcl-pump` test `(fn-tcl-has remaining k)` itself, which is
only O(chunk) — buys the guard at the price of a branch the composed machine
cannot reach, which the assurance rules forbid as evidence.

**What the relaxed guard gives up, and what still holds.** The old guard proved
at each call site that a take is a genuine prefix. The decoders of
`books/tcpcl-octets.lisp` still ask `fn-tcl-has` before every take — it is their
own branch test, returning `(fn-tcl-parse-need)` when it fails — and an
over-take pads with `nil`, which is not `fn-cbor-octet-listp`, so
`fn-tcl-decode-message-yields-message` and the round trip would both fail if one
ever happened. The property moves from a guard obligation to the codec
keystones; it is not dropped.

Affects `specs/tcpcl.md` §3 and §6, `books/tcpcl-octets.lisp`,
`books/tcpcl-session.lisp`, `tests/acl2/tcpcl-tests.lisp`. Supersedes nothing.
### 2026-09-21: D10-a — a clock the host contradicts is a clock the owner drops

**Question.** A connection pins one clock observation at accept so that time
does not move under a reader mid-session. Every *decision* is taken under the
reading the host supplied with that event. What happens when the owner cannot
accept the reading it was handed?

**Selected.** `fn-own-observe` answers one of three distinct outcomes and a
refusal costs the owner its clock.

- `:observed` — the reading is a later observation of the same clock
  (`fn-clock-later-observationp`) and becomes the owner's. A reading **equal**
  to the one held is observed, not refused: it is admitted, and nothing moves
  because nothing has to.
- `:refused` — the monotonic counter went backwards, `has-wall` changed, or a
  widened error bound moved the earliest admissible true time back. The owner
  keeps no clock at all.
- `:invalid` — the host supplied no observation. Nothing changes.

`host/owner-host.lisp` reports that word. It used to compute one by comparing
the owner before and after the event, which put the decision in the host and
spelled an admitted equal reading exactly like a contradicted clock.

**Why the owner forgets.** [The clock spec](../specs/time.md) already says a
node that discovers its clock was wrong is allowed to stop being sure. Keeping
the contradicted reading is the opposite: `books/injection.lisp` derives a
generated Message-ID from the reading alone, so every POST after the first in
that window mints the identity of the first, the durable path refuses it as a
duplicate, and the poster is told `441 posting failed; the article was
refused`. That is an article verdict for a clock fault, and it is the shape of
the defect two earlier lanes recorded. With no clock the owner refuses to
inject (`fn-inj-decide`'s `:clock-unusable`, `441 posting failed; this server
has no usable clock reading`), refuses to declare a group, and answers DATE
with `503 no clock observation supplied` — three distinct, honest answers. A
clock-less owner is not a new state: `fn-own-start` and `fn-own-reopen` both
leave one and `fn-own-relation` admits it.

**What it costs.**

- A POST or a DECLARE-GROUP attempted between a contradicted reading and the
  next accepted one is refused, with its own reason. The window is one event:
  the clock being absent, the very next reading is admitted whatever it says.
- A connection accepted inside that window pins no observation and answers
  DATE 503 for its whole session. That is the already-modelled behaviour of a
  node with no clock, not a new one.
- After a backwards correction the node may mint a generated Message-ID it
  already used in the lost interval; the durable path refuses that as the
  duplicate it is. Recorded, not claimed away.

**Rejected: keep the contradicted reading** (the behaviour before this). The
node then goes on deciding under a clock its host has withdrawn, and the
symptom reaches the client as an article verdict.

**Rejected: a fourteenth owner field remembering the last reading a generated
identity was minted under.** It would additionally separate two submissions
inside one millisecond, which the reading-level rule cannot, because
`fn-clock-later-observationp` is non-strict and an equal reading is admitted.
It costs a field through every `fn-own-make` call site and the whole
served/owner/peer closure, and the case it buys needs two durable barriers
inside one millisecond. Recorded open instead, under NNT-005.

Registry: PRF-033. Keystones
`fn-own-observe-refusal-names-a-contradiction` (`books/owner-invariants.lisp`)
and `fn-post-without-a-clock-refuses-with-the-clock-line`
(`books/nntp-post.lisp`).

### 2026-09-21: D21 — the served statement index is a slot on `fn-sn-state`, and the keyring it was computed under is the slot beside it

`w11/node-index` measured that a fifth slot on `fn-node-statep` is a dependency
cycle and named `fn-sn-statep` (`books/store-node.lisp`) as the carrier that
works. It left one question open and called it the real design question: the
index is a function of `(store, keyring)`, and **no state or configuration
record in the tree holds a keyring.** This entry answers it, and answers a
second one the first answer exposes.

**Q1: where does the keyring come from? Taken: a carried field beside the
index, initialised empty, replaced only by an explicit reconfiguration
transition that recomputes the index over the store.**

Three candidates were open.

- *Derived from the configuration `fn-sn-state` already carries.* Closed by
  inspection: that configuration is `(groups capacity)`, neither of which
  mentions a principal. The nearest thing to a key table inside the node is
  `fn-node-bindings`, and `books/node.lisp:126` shows it is
  msgid-to-archive-obligation, not principal-to-key. Today a keyring reaches
  ACL2 only as a file the operator names on the command line
  (`bin/fn:782 --keyring`, read by `tools/stx.py:159`), which is a value
  arriving from outside, not a value derived from anything held.
- *Carried in a form that needs no keyring.* Closed by the invariant's shape:
  `fn-stx-index-invariantp` is `(equal index (fn-stx-index-of-store store
  keyring))`. Two different keyrings give two different indexes over the same
  store, so a carried index whose keyring is not also carried is not
  determined by the state, and the conjunct cannot be stated of the state
  alone. Boxing the pair into one slot is this decision with an extra record
  in front of it; it is not a third option.
- **Taken: a `keyring` field.** It is configuration, and it is the third piece
  of configuration `fn-sn-state` carries, beside `groups` and `capacity`.

Its cost, stated where the brief asked for it.

- **`fn-sn-initial` keeps arity 2 and `fn-sn-update` keeps arity 3.** The
  initial keyring is `nil`, which satisfies `fn-prin-keyringp`, and
  `(fn-stx-index-of-store nil k)` is `(fn-stx-index-empty)` for every `k`, so
  the empty store's invariant holds under any keyring and the initial state
  needs no keyring argument. A node that knows no principal's key verifies no
  statement, so its lace and its index are both empty: that is the correct
  answer for an unconfigured node, not a degenerate one.
- **`fn-sn-finish` pays one cons.** The delta of the article the durable branch
  publishes, through `fn-stx-index-add`. This is the D3 property the index
  exists for and it is proved:
  `fn-stx-index-grows-by-at-most-one-binding` bounds the growth and
  `fn-sn-finish-preserves-indexedp` carries the agreement.
- **Three sites recompute over the whole store, and none of them is a served
  path.** `fn-sn-recover`, whose node comes from a replay; `fn-sn-set-keyring`,
  the reconfiguration transition; and `fn-sn-crash`, where the recomputation is
  free because the node is reset to `fn-node-initial-state` and the empty
  store's index is `fn-stx-index-empty` by definition.
- **The two fresh-state sites `w11/node-index` flagged do not bite.**
  `books/node-config.lisp:405` and `books/replay.lisp:198` build a fresh
  `fn-node-make-state`, not a fresh `fn-sn-state`, and neither book is in
  `books/store-node`'s include closure nor above it. Because the carrier is on
  `fn-sn-state` and not on `fn-node-state`, their recomputation lands once, at
  the `fn-sn-recover` that consumes `fn-sf-replay-node`.

**Q2: the agreement is NOT a conjunct of `fn-sn-statep`. It is a second
recognizer, `fn-sn-indexedp`.** This is the part `w11/node-index`'s §6.1
proposal got wrong, and D20 is why.

D20 records that "the native host reaches the session machine through the ACL2
executable counterpart of `fnn-call` (`host/native/io.lisp`), which checks the
callee's guard on every call." `fn-sn-statep` is the guard of `fn-sn-prepare`,
`fn-sn-io`, `fn-sn-finish` and `fn-sn-recover`. Putting
`(fn-stx-index-invariantp (fn-sn-index s) (fn-sn-node s) (fn-sn-keyring s))`
into it would therefore **re-derive the index — and so re-run `fn-stx-verdict`,
and so re-verify every signature in the store — on every host call into the
store machine.** That is the no-whole-state-revalidation rule (D3) violated by
the very change made to satisfy it, and it is strictly worse than the whole-
store walk the index removes, because the walk gains a signature check per
article. It is also the exact shape D20 cured on the send path, and the cure is
the same one: a second recognizer.

So `fn-sn-statep` gains only the **cheap** conjunct,
`(fn-prin-keyringp (fn-sn-keyring s))`, which walks the keyring and never the
store. `fn-sn-indexedp` is `fn-sn-statep` plus the agreement; it is the guard of
nothing, it is established at `fn-sn-initial` and proved preserved by every
transition, and it is the hypothesis of the query's correctness theorem. It is a
carried invariant in the sense of the fourth micro-discipline rule — held by a
theorem about the reachable states, never re-run per operation.

**Rejected: a wrapper record above `fn-sn-state`** holding `(sn keyring index)`
with its own five transitions. It would cost `books/store-node.lisp` nothing and
leave all 59 books above it untouched, which is why it was considered. It is
rejected because the index would then be maintained only on the paths the
wrapper reimplements, and `fn-sn-refuse-reservation`, `fn-sn-known-abort`,
`fn-sn-sweep-staging` and `fn-sn-open-observed` move the state without going
through it. Every transition that the wrapper did not mirror would silently
desynchronise the index from the store, and "silently" is the word that decides
it: a stale index answers a query wrongly with no fault anywhere. The slot has
no such hole, because every one of those transitions already rebuilds the state
through `fn-sn-update`, which carries the two new fields across by
construction.

**The price of the slot, stated plainly.** `books/store-node.lisp` must include
`books/stx-index`, so its include closure goes from 13 books to 26 and the 59
books whose closure contains `books/store-node` inherit those 13. That is real
and it is paid by the store and BP-receiver clusters. It is smaller than the
alternative `w11/node-index` priced, where the same 13 books would have been
inherited by the 70 books above `books/node`.

Registry: PRF-023. Keystone `fn-sn-statement-lookup-is-the-lace-lookup`
(`books/store-node-invariants.lisp`), with `fn-sn-initial-is-indexed` and the
five `fn-sn-*-preserves-indexedp` theorems as the reachability chain that
discharges its hypothesis.

### 2026-09-20: D22 — the freshness anchor carries its root, and fn reports a Roughtime response it cannot describe as uncertain

**The question.** `fn-anchor-root` was not an accessor: it was
`(fn-anchor-leaf-digest (fn-anchor-nonce a))`, and the nine fields the durable
record carried did not include the root. So every keystone about the signed
octets — `fn-anchor-signed-octets-determine-the-root` above all — described a
one-nonce tree, empty `PATH` and `INDX` 0, while `tools/roughtime.py` admitted
a `PATH` up to 32 nodes deep and `anchor_verdict` ran Ed25519 over the root
**from the wire**. For a batched response the host held a verdict about one
message and `fn-anchor-node-accept-observed-is-node-accept`'s hypothesis was
about another, and nothing anywhere noticed: `anchor_verdict`'s own
consistency check passed, because it had fed ACL2 the wire root. The captured
`roughtime-int08h-2026-09-19-later2.json` vector is batched: its PATH contains
a sibling and its INDX is 1. The mismatch therefore occurred in the existing
restore test, not only in a hypothetical server response. The
[anchor-root handoff](lanes/HANDOFF-w11-anchor-root.md) records the measurement.

**Taken.** The root is a tenth field on `fn-anchor` and on both FNAN kinds, so
`fn-anchor-signed-octets` is the octets that were verified for a batch of any
size. `fn-anchor-one-nonce-p` — `(equal (fn-anchor-root a)
(fn-anchor-leaf-digest (fn-anchor-nonce a)))` — is a separate branch in
accept, advance and restore. A response whose binding the model cannot
establish returns **`:uncertain :unmodelled-tree`**, with CLI exit 3, and
does not become the durable anchor. `fn-anchor-verifiedp` continues to describe
the signatures and delegation window. A valid signature over an unsupported
tree is not evidence that the response is invalid. This limits use of actual
batched int08h responses until the Merkle binding has an executable model.

**The host supplies two distinct seam observations.** `verdict` corresponds
to `fn-anchor-signatures-okp` (the Ed25519 checks), and `one-nonce` corresponds
to `fn-anchor-one-nonce-p` (the SHA-512 leaf comparison). Their correspondence
assumptions remain explicit; a host boolean is not a cryptographic proof.
The delegation window is arithmetic on fields the record carries, so ACL2 owns
it — `fn-anchor-verifiedp-observed` applies `fn-anchor-window-okp` inside the
entry the host calls. Until now `mint <= midpoint <= maxt` was *half* the
discharge of that hypothesis, copied at `tools/roughtime.py:258`, with
`anchor_verdict` supplying the other half from a different file; if the copy
and `books/anchor.lisp` had ever disagreed, every anchor keystone would have
stopped describing the run with no test failing.

**Rejected: a stated hypothesis without an executable gate.** Carrying
`fn-anchor-one-nonce-p` only as a theorem hypothesis would leave the host
free to record a batched anchor while the theorem did not apply. The
uncertain branch enforces the supported binding before durable acceptance.

**Rejected: an `A-*` assumption covering the fold.** There is no fold in the
logic to hypothesise about, so no theorem could take the assumption — it would
be the prose assumption AGENTS.md forbids. The fold is recorded as a trusted
facility in `specs/anchor.md` instead, with its file, its lines and what it
decides named.

**Rejected: `books/sha512.lisp` and the fold in this packet.** Stating the
fold over a constrained digest without attaching a realiser would leave Python
deciding while looking proved. The design is
`planning/lanes/HANDOFF-w11-one-owner.md` §3 steps 1 to 3; it is a packet of
its own and admitting batched responses is what it buys.

Registry: FLR-004, OBJ-006. Keystones
`fn-anchor-signed-octets-determine-the-root` (`books/anchor.lisp`, now over
the field and so covering any batch size) and
`fn-anchor-verifiedp-observed-is-verifiedp` (`books/anchor-invariants.lisp`,
the seam hypothesis discharged once for all three host entries). Teeth in
`tests/acl2/anchor-teeth-tests.lisp` and `tests/test_anchor.py`.

### 2026-09-23: wider, self-coordinating swarm

The user supports at least doubling the previous five-agent width, provided
each added agent advances substantive work rather than duplicating cached
proofs or competing wastefully for compute. Start around ten useful agents,
mostly GPT-6-Sol; execution capacity remains separately bounded.

The user explicitly rejected mandatory disjoint ownership. Work claims are
intentions, not locks: agents can collaborate on shared books and negotiate
changes through direct peer channels, with a durable coordination summary.
Combined source still needs its actual invariant and runtime evidence. Keep
iteration fast by reusing matching artifacts, sharing costly runs and
investigating regressions instead of merely raising timeouts. These choices
supersede the old width and exclusive-file rules; they do not relax assurance.

### 2026-09-23: first application experiment and silo boundary

After the [architectural reassessment](ambition-2026-09-23.md), the user selected:

- First dregg exchange: an immutable report/receipt and reply between sleeping
  agents. Application evidence stays in versioned payloads; this does not add a
  dregg executor to fn or change the selected v0 gate.
- Durable consumer progress: a consumer-owned durable inbox/outbox, with an
  explicit fn cursor/acknowledgement contract. The existing printed-output
  watermark does not establish durable processing. Cursor semantics and the
  application transaction still need their specification and crash witnesses.
- First cross-silo trust boundary: separate stores and administrators with
  explicitly trusted transport peers. Untrusted relay receipt substitution and
  hostile co-resident processes are later qualification targets, not properties
  of this first deployment.

These choices select the first experiment and its design direction. They do not
claim an implemented consumer API or authenticated receipts through untrusted
relays. Native authorship, retention receipts and application outcomes remain
distinct evidence.

### 2026-09-22: the eight questions of the trajectory plan

ember answered the eight questions in `plan-2026-09-22-trajectory.md` §0,
quoted there. Consequences: DTN is v0 (A06 and the purpose); native author
signatures are v0 (D02, D09); LTP follows the node machine; the acceptance
stamp is a v0 schema step (ENC-004's first exercise); the six-wave release
shape, its checklist and the fiber records are retired; the lane worktrees
are removed with every checkpointed branch dispositioned in the plan's
§5.2; the Codex role names are retired; five lanes converge every two to
three batches; peering is measured on one box first.

(Note added 2026-09-24: the role-name retirement was not carried out. The
Codex swarm used Sol, Luna and Astra as GPT-6 role names through 2026-09-24;
see the 2026-09-24 entries below. The five-lane width was superseded by the
2026-09-23 width entry above.)

### 2026-09-24: broad concurrent capability wave (05:37 UTC)

The user asked to replace serial prerequisite-sized advances with a large
concurrent implementation wave, accepting temporary development breakage and
converging afterwards. This changed sequencing, not the required end state or
the standard for an assurance claim: intermediate failures are recorded,
never silently removed or replaced with a claim about an easier API. The wave's
targets are in the archived [capability wave](archive/capability-wave-2026-09-24.md);
its convergence obligations now live in [how we work](how-we-work.md#convergence-obligations).

### 2026-09-24: bounded implementers hand proof work to the proof owner

In the Codex swarm's trial the user kept proof development with GPT-6-Sol:
GPT-6-Luna lanes implemented bounded features, client/UI work and fixtures
against an explicit contract and ran prescribed checks, and handed a failed
certification's exact source, failed event and log to Sol rather than
searching for proofs themselves. The trial record is
[luna-feature-trial-2026-09-24](experiments/luna-feature-trial-2026-09-24.md).
The rule is kept model-neutrally in [how we work](how-we-work.md#who-implements-and-who-proves).

### 2026-09-24: wind-down and consolidation (06:23 UTC)

The user requested all current work consolidated into dev and the swarm
quiesced over about an hour, with no new feature wave and no live-service
deployment. The result is the [wind-down handoff](handoff-2026-09-24-winddown.md):
all source packets integrated, `863c2141` the last completed image, the
final `8a1b31f9` cut red on three BP roots, the live node unchanged.

### 2026-09-24: Claude takes over (07:25 UTC)

When GPT-6 wrote `ALLDONE.marker`, Claude took over as coordinator (Claude
Fable coordinating, lanes on Claude Opus 5.5 in `build/lanes/<name>`
worktrees). ember set four items by which the night is judged: a frozen image
past `863c2141` with the three red roots fixed and BP N03 plus the
interrupted-fragment native cases passing; one end-to-end signed peering into
Mini consumption across two Stores as a stretch; proof cost down (books over
10 s from 30 to at most 20, and `tools/proof_cost.py` and
`tools/certified_claims.py` failing `make check` instead of warning); and
planning consolidated. [Now](now.md) carries the goal and the lanes. Role
names are neutral from here: a lane is named by its worktree and its model
is written in its brief.

### 2026-09-24: retry after a death following a durable kind 8 (candidate; default adopted by the coordinator 2026-09-24, pending ember)

A forwarding attempt with a durable kind-8 record and no kind-9 result when
its process died is **uncertain**: the peer may or may not hold the bundle.
The default, parallel to NNTP's K5 ([peering](../specs/peering.md)) and to
M4's recorded "explicit retry after uncertain BPA restart":

- after recovery the row is re-eligible for forwarding with its **original**
  held bundle (same source, creation timestamp and sequence; nothing is
  re-authored and no sequence is allocated), offered by the ordinary
  arrival-order selection on the next negotiated session to its next hop;
- duplicate control is the receiver's: a bundle whose id it already holds
  (held, delivered or tombstoned) is absorbed at admission by bundle id;
- each re-offer counts; after `*fn-bpnp-max-forward-retries*` (3) re-offers
  without a result the row is a **stranded obligation**: it stays held with
  its attempt and its reserved result debt, is never re-offered or dropped,
  and a session to its next hop that offers nothing reports
  `(:forward-stranded arrival peer retries)`.

One clause of the default does not match the machine: the default says a
held or delivered duplicate is *refused* and the refused re-offer settles as
kind 9 with the refusal. fn's receiver answers a duplicate with XFER_ACK
(`fn-bpnf-callback-result`, `:duplicate` gives `(:accepted nil)`), so the
re-offer settles as kind 9 `:sent`, which is terminal like `(:refused 1)`.
Exactly one copy is held either way; sending XFER_REFUSE reason 1
("Completed", RFC 9174 §5.2.4 Table 6) for a duplicate, and carrying the
reason code to the sender (`fn-bpnp-tcpcl-outcome` maps every refusal to
`:failed`), is left for ember. Machine: `books/bp-forward-attempt.lisp`,
`books/bp-node-progress.lisp`; spec: [bp-node-machine §4.3.1](../specs/bp-node-machine.md).

### 2026-09-24: D02's scope includes a served POST that carries a signature (candidate; adopted by the p8-signed-post lane, pending ember)

D02 selected native author signatures alongside gateway provenance for
ordinary unsigned clients; it did not say what a served NNTP POST that
carries an `FN-Authorship` carrier gets. Until this entry it got the
unsigned arm: stored as a legacy `fn-r` record, no kind-4 verdict, and
`HDR :fn-verified` reported no record, while the same bytes over protected
transit or the control socket's `hybrid-author` got a durable verdict. The
[peer-authored ingress record](evidence/peer-authored-ingress-2026-09-24.md)
names one acceptance helper for NNTP and BP; the served POST was the missing
caller.

The default: a served POST, a local control `post` and a BP application
submission take exactly the classification transit takes, the one ACL2
decision `fn-pa-current-plan` over the submitted octets and this Store's
keyring snapshots.

- **Absent carrier**: the unsigned arm, unchanged (gateway provenance).
- **Present and valid under this node's current enrollment of the
  principal**, both primitive observations verified: a durable kind-4
  acceptance whose verdict `HDR :fn-verified` reports.
- **Present and invalid**: refused, never the unsigned arm, with the reason
  on the wire as its own 441 line (`:carrier`, `:carrier-shape`, `:article`,
  `:local-enrollment`, `:signature`; `fn-pa-served-word`,
  `fn-post-store-refusal-line`).

A consequence recorded as a design decision, not changed here: a correctly
signed article whose principal this node has not enrolled is refused with
`local-enrollment` (441 on POST, 439 on transit, as the hybrid-feed-storm lane
surfaced), not stored unsigned. An agent that wants to post through a node
that does not know its key must post without the carrier. Whether an
unenrolled signature should instead be accepted as unverified is ember's
question, listed with the other P8 decisions on the scoreboard. Evidence:
[p8-signed-post](evidence/p8-signed-post-2026-09-24.md).
*Superseded for transit by D23 below: an allowlisted, unenrolled author's
article is carried with a `:carried` verdict
([d23-nntp-relay](evidence/d23-nntp-relay-2026-09-24.md)).*

### 2026-09-24: ember's answers to the day's open questions (~22:30 UTC)

Asked by the coordinator with the recommended option first; ember chose the
recommended option in each case. Recorded as decisions; the lanes that act
on them are named in `planning/now.md`.

- **D23, relay trust: a boundary trusts what a neighbour carries only by
  allowlist, and the receiver verifies against the author's own enrollment,
  never the carrier's.** Today (`bp-app-handoff.lisp:104-136` with
  `bp-session-admission.lisp:62-113`; `fn-pa-current-plan`'s
  `:local-enrollment` refusal) a request or a signed article is trusted only
  when its source identity equals the delivering neighbour's, so nothing
  relays through dtn7-rs and a signed article cannot pass an fn node that
  has not enrolled its author. Now each enrolled boundary carries a list of
  source identities the neighbour may carry; a carried item is admitted on
  that list and its acceptance rests on the author's enrollment at the
  receiver; a node that carries but cannot verify holds and forwards the item
  with a verdict that says so, never `verified`. fn's disconnected pillar
  means a store-and-forward network, not only pairs of mutually trusting
  nodes. (Overrides the "consequence recorded" of the 2026-09-24 D02 entry.)
- **D24, the peer arms' per-event node check is carried, not memoized.**
  The host calls a guard-verified carried copy of the peer step whose
  premise is proved at open and preserved by every step, as the reader path
  already does; no trusted facility enters the trust boundary.
- **D25, duplicate versus conflict keys on the poster's bytes.** The
  comparison drops the fields the node injects (Path, Xref, Injection-Date,
  Injection-Info; the authored-source projection `fn-hc-authored-source`
  already names them) and compares what the poster sent. A resend of the
  same bytes is "already stored here"; different poster bytes under one
  Message-ID is "a different article with this Message-ID is stored here".
  The stored record keeps the injected headers.
- **D26, the ten-second rule's number is the 2-job scoped measurement.**
  Combined closures at higher job counts are recorded but do not ratchet.

Adopted defaults ember did not overrule, standing until said otherwise:
P5's sentence, restated with its fault domain (2026-09-24 evening, after
gpt-6's direction review): a demonstrably connection-local fault costs that
connection; a fault inside a shared owner action fences the store and stops
the service (exit 4) because the shared authority is uncertain (specs/host.md
HST-005); D02's scope covering a served POST (the 2026-09-24 entry above);
the kind-8 retry default with a duplicate re-offer acknowledged rather than
refused, the retry count derived from the durable kind-8 rows so a restart
cannot reset it, a stranded row reported and held with no automatic resume
(an operator release verb is open), and on the sender a TCPCL XFER_REFUSE
reason 1 (Completed) settled as `:sent` while every other reason is kept as
its own kind-9 result (spec bp-node-machine 4.3.1); RFC 5536 s3.1.4's
specific-purpose group names, by its patterns (first or only component `to`
or `control`, any component `all` or `ctl`, exactly `junk`), admitted at init
and create as an explicit local-agreement profile that confers no authority
(docs/operator.md, Add a group).

### 2026-09-24: a store identity on the wire (candidate, not implemented; pending ember)

The M6 web client keeps read marks and resume points per (node, group,
local number). A node whose store is replaced (a fresh `store init` behind
the same host, port and configuration) restarts its local numbers at 1, and
the client's marks then name different articles. The m6-list-counts lane
was asked for the smallest honest wire value that lets a client detect it,
to be implemented only if it is a rendered value of an existing ACL2 state.

**No existing ACL2 value identifies a store instance.** What the Store holds
(`fn-sn-state`: groups, capacity, keyring snapshots, the statement identity
sequence, the acceptance state) is a function of the configuration and of
what was accepted, so two stores initialised from one configuration and
serving the same first posts are indistinguishable by it. The Path identity
names the node, not the store. A digest of the initial configuration record
is equal across a re-initialisation with the same configuration, which is
exactly the replacement to detect. So nothing was added to the wire.

**What already detects it, now.** A resume point is (group, local number,
Message-ID) and `/resume` checks the Message-ID the node serves at that
number (409 "not the same article"). Since this lane, `ARTICLE`/`STAT`
`<msgid>` after `GROUP` answer the article's local number there (RFC 3977
§6.2.1.2), so a client can check any remembered (group, number, Message-ID)
triple in one command. That detects a replaced store whenever the client
remembers one Message-ID per group, which the web client already does (the
resume point), without a new wire value.

**Candidate (for ember):** a store incarnation created by ACL2 at `store
init` from a host-supplied random observation, persisted in the Store's
first record, carried in `fn-sn-state`, and rendered by ACL2 as a private
capability label (RFC 3977 §3.3.1 reserves labels beginning with `X` for
private use), for example `XFN-STORE <hex>`. Cost: a new Store record field
and its codec, recovery and upgrade proofs (the profile upgrade must carry
it), and an assumption that the observation is unpredictable (`A-*`, an
`encapsulate` in `books/assumptions.lisp`). Alternative: rely on the
Message-ID check above and add nothing. The lane's recommendation is the
alternative until a client that keeps marks without a Message-ID exists.

### 2026-09-25: D27 — bound work, never data; concrete representations at runtime (~02:40 UTC)

ember: "Using octet lists continues to be unacceptable at runtime. We need to
have fewer bullshit restrictions. Each of those is a branch that someday
will fail during operation for no meaningful reason except during
development we were fearful and installed a footgun. Octet lists are an
absurd amount of overhead. Let's endeavor to have efficient
representations; otherwise the software is not useful as a system."

Two rules follow, and they supersede the habit that produced today's
inventory of caps (`planning/design-2026-09-25-bounds.md` when it lands):

- **A constant that bounds data is a defect.** Work per request stays
  bounded (a parser still refuses input it cannot finish in bounded steps;
  a served command still does bounded work), but the size of an article,
  the number of groups it names, the number of transactions a store holds,
  the bytes a store may reach, and every similar quantity are the
  operator's to set, in the store profile, with defaults the hardware can
  honour and refusal only when the operator's own bound is reached. Codec
  widths are chosen so the codec never caps below any profile the operator
  can write. Every `*fn-*-max-*` that limits data moves into the profile or
  goes; the ones that limit work stay and say so.
- **The logical model stays octet lists; the executable path does not.**
  Record bodies, frames, headers, the Message-ID index and the in-memory
  history get concrete representations (stobj byte arrays, strings, arrays)
  with a correspondence theorem to the list definition at every boundary
  the host calls, guard-verified, and measured before and after on the same
  image. No statement of an existing theorem moves. This is the
  "explicit correspondence arguments" clause of AGENTS.md made mandatory
  rather than optional.

Order: the representation boundaries by measured share, and the profile
fields with the codec widths, run in parallel; whole-history replay at open
(the checkpoint slice) follows, because a large transaction bound without
it only makes open slow.
