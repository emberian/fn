# Decision workbook

Status: architectural direction recorded; D02, D03, and D04 resolved by the user on
2026-09-18; other choices remain proposals. This is the agenda for discussion, not an approval
gate for routine work. Record answers here with their rationale and consequences.
No unanswered recommendation is silently promoted to an agreed decision.

**This is the full decision backlog, not the next questionnaire.** The
[current acceptance cycle](now.md) can proceed without answering the remaining
rows. Astra owns routine reversible implementation choices and will bring
user-facing tradeoffs forward with concrete examples as they become relevant.

## Already agreed

| ID | Direction |
| --- | --- |
| A01 | fn serves human and AI communication, with NNTP as its initial news interface. |
| A02 | Use executable ACL2 semantics and pursue meaningful proofs of the running core. |
| A03 | Build a specialized persistent store: immutable objects, local transactions, recoverable state. |
| A04 | Represent retention/delivery obligations explicitly and persist them alongside content. |
| A05 | Sites remain independently useful while disconnected; batches can travel by network or carried media. |
| A06 | Design for eventual BP/LTP integration and long delays, with explicit limits and assumptions. |
| A07 | Do substantial design up front, implement in stages, and keep evidence distinct from intent. |

These record the user's architectural choices. Exact schemas, cryptographic
suites, and deployment profiles remain open. Local retention and first-release
authorship support are resolved below.

## Decisions to make together

The first three questions put to the user, D02, D03, and D04, are resolved. The
remaining table is a long-term backlog. The [privacy note](../specs/privacy.md)
keeps the eventual group-encryption protocol choice open.

| ID | Question | Recommendation | Main alternative / cost | Needed by |
| --- | --- | --- | --- | --- |
| D01 | What is the durable source of a native article? | Immutable source bytes plus a versioned envelope; NNTP trace fields belong to an explicit projection. Preserve legacy wire input separately. | Treat every wire variant as the only source; simpler ingestion, harder portable authorship and semantic conflict handling. | M1 model, M2 bytes |
| D02 — decided | Do native messages support author signatures in the first release? | **Selected:** native author signatures plus explicit gateway provenance for ordinary unsigned NNTP clients. | Gateway-only first was declined. Concrete suites/key workflow remain D09. | M1 identity model, M3 release |
| D03 — decided | What does a successful local post promise to retain? | **Selected:** keep until explicit authorized release, no automatic expiry; refuse new obligations when capacity is unavailable. | Automatic bounded retention was declined. Exact release authority/terms still need specification. | M1 obligation model |
| D04 — decided | Is private encrypted communication in the first release? | **Selected:** shared community groups first; design confidentiality and metadata boundaries now. | Private encrypted groups in the initial release are deferred. The later cryptosystem remains open. | M1 scope |
| D05 | How much NNTP constitutes the first usable release? | Complete proposed READER + mandatory commands + POST + OVER; configured unmoderated groups. | A smaller experimental subset, explicitly without full bundle advertisement or broad client compatibility claims. | M1 session scope, M3 |
| D06 | How far down should we implement indexes initially? | Journal/checkpoint authority with rebuildable in-memory indexes; add disk indexes when scale demands. | Disk-resident indexes immediately; earlier scale, larger recovery/refinement proof surface. | M2 |
| D07 | What execution host should we target? | ACL2 on SBCL with a small Common Lisp host, versions and integration path pinned in M1. | Another supported Lisp or an external-process bridge; different packaging and boundary costs. | M1 |
| D08 | What portable encoding and evolution policy? | Restricted deterministic CBOR, exact schema versions, bounded parsing; unknown objects may be carried opaquely but not interpreted as authority. | A custom binary grammar, or textual encoding; different tooling, size, and canonicalization costs. | M2 |
| D09 | How do keys, algorithms, and signatures evolve? | Algorithm-tagged containers and explicit signing profiles; stable principals with recorded authorized key succession. Choose concrete suites after the threat/longevity discussion. | A fixed key-is-identity scheme; simpler v1, harder rotation and long-lived migration. | M2 |
| D10 | How do we handle time, old backups, and forks? | Local counters plus explicit origin incarnations; causal references; restore/clone procedure creates or validates a fresh sequence namespace. | Depend on a central identity/sequence service; reduces offline autonomy. | M1 model, M4 restore tooling |
| D11 | Who controls group identity and policy? | Local aliases over an explicit group authority/configuration identity; initially simple owner/admin succession. | Globally shared mutable names or general multi-party governance from v1; more conflict and authorization rules. | M1 local, M4 portable |
| D12 | When may a forwarding node release responsibility? | Only after committed, matching application evidence satisfies named terms; start with cooperative trusted peers and explicit archive pins. | Require multiple independent retainers before release; stronger failure tolerance, more capacity and failure-domain policy. | M1 model, M4 |
| D13 | When may history and evidence be forgotten? | Preserve duplicate history initially; add proved pruning with an explicit old-input/resurrection policy. | Finite age/epoch windows from v1; bounded metadata sooner, delayed old letters may become inadmissible. | M1 invariants, M5 pruning |
| D14 | Which platform and fault claims come first? | Pure crash model first; qualify one Linux local-filesystem profile before deployment durability claims, while supporting macOS development. | Qualify macOS and Linux together; more adapter/platform work before the first durability claim. | M2 |
| D15 | How should long-delay exchange use scarce contacts? | Bounded proactive batches, resumable objects, cached peer knowledge, explicit quotas; add optimized reconciliation later. | Interactive inventory negotiation first; efficient on good links, consumes more round trips. | M4 |
| D16 | What resource envelope are we designing for? | Define a small-community reference profile and a simulator stress profile; measure before fixing article/chunk/segment sizes. | Select hard universal limits now; earlier ABI certainty but less evidence. | M1 bounds, M2 layout |
| D17 | What is the first human interface? | Use an existing newsreader for interoperability, then a web reader over the same acceptance path. | Build the web experience before reader interoperability; earlier bespoke UX, weaker early protocol feedback. | M3 validation, M6 |
| D18 | How much should we prove before calling the first release usable? | Core invariants, codec properties, and conditional crash recovery first; state host/crypto/platform assumptions explicitly. | Ship an experimental server sooner with a smaller proved subset and equally explicit limits. | M1 proof scope, M3 release |

## Consequences worth thinking through

### D01: source bytes and compatibility

We need a concrete example containing native author data, generated injection
fields, relay-mutated headers, an unknown header, and a legacy unsigned article.
The [article-byte examples](../docs/article-byte-examples.md) now supply those
views and two candidate signing preimages; they remain proposals for discussion.
Specify which exact bytes are signed and how an ordinary reader sees the article.
Do not settle this by saying “canonicalize headers”: that hides the difficult
part. Acceptance must still handle ordinary NNTP clients without fn extensions.

### D02 and D09: who holds the keys

Native author-signature support does not require every post to be signed. It
requires honest distinctions among an author's signature, a host signing on an
authorized principal's behalf, and a gateway attesting only to submission.
Decide key custody on agent hosts, human signing workflow, rotation/recovery,
offline revocation semantics, and whether post-quantum or hybrid signatures are
an initial requirement or a future profile. No suite has been selected here.

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
