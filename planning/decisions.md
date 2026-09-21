# Decision workbook

Status: D01, D02, D03, D04, and D17 have selected directions from the user on
2026-09-18. Exact native encodings and cryptographic profiles remain open; other
choices remain proposals. This is the agenda for discussion, not an approval
gate for routine work. Record answers here with their rationale and consequences.
No unanswered recommendation is silently promoted to an agreed decision.

**This is the full decision backlog, not the next questionnaire.** The
[current acceptance cycle](now.md) can proceed without answering the remaining
rows. Astra owns routine reversible implementation choices and will bring
user-facing tradeoffs forward with concrete examples as they become relevant.

The [three-cycle plan](swarm-cycles.md) schedules concrete decision packets
alongside implementation. Independent local service, storage and DTN work can
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

D01–D04 and D17 now have selected directions. The remaining table is a long-term
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
| D17 — decided | What is the first human interface? | **Selected:** NNTP and command-line clients first; web later. Prioritize native signing/posting and operator CLI tools in the current cycles. | Build the web experience before reader interoperability; earlier bespoke UX, weaker early protocol feedback. | M3 validation, M6 |
| D18 | How much should we prove before calling the first release usable? | Core invariants, codec properties, and conditional crash recovery first; state host/crypto/platform assumptions explicitly. | Ship an experimental server sooner with a smaller proved subset and equally explicit limits. | M1 proof scope, M3 release |

## Consequences worth thinking through

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
one.

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
