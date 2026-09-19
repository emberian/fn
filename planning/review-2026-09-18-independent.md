# Independent review of fn at `a5a30d8`

Status: **review record**, 2026-09-18 late evening, by a Claude session with five
parallel adversarial auditors (core logic, storage, BP, codec/NNTP, host). Every
finding cites a file and line at `a5a30d8`. This is not new implementation
evidence. It changes no registry status. It exists so the next work cycle can
repair concrete defects and re-sequence around the structural ones.

The standard applied is the one `~/dev/minidregg/ATLAS.md` §6 uses: a keystone
theorem must be satisfiable, must have teeth, must have inhabited premises, and
its name and prose must not outrun its statement. Green is not true.

## 1. Verdict

The tree is honest about scope in most prose and clean of every forbidden
facility. The bridge between Python and ACL2 is sound by construction. Several
keystone theorems are real inductions over production functions. But the
assurance ledger points at weak siblings of the real theorems, several
"certified" rows rest on tautologies or on functions the host never calls, and
the model has seven shape-level naiveties that would be expensive to build on.
Two host bugs can brick a store or wedge the reader.

**Fix now** (§3): fourteen concrete defects, two of them availability bugs.
**Re-sequence** (§6): substrate before service. Identity, causality, time and
an adversary are currently deferred to C1-11, C2-06 and C2-12; they gate
everything that would otherwise be built on decision bits and Python twins.
**Import, do not design** (§7): the portable fact model fn is re-deriving is
the blocklace that `~/dev/breadstuffs` already proves and `~/dev/minidregg`
already refines.

## 2. What was run

| Check | Result |
| --- | --- |
| `make check` | passed: 74 Markdown files, 49 requirements, 18 proof targets, 18 scenarios |
| `python3 tools/run_simulator.py` | passed; real ACL2, one three-step scenario over `books/acceptance` only |
| Forbidden-facility scan of `books/` and `tests/acl2/` | none: no `skip-proofs`, `defaxiom`, `defttag`, `include-raw`, `:program`, `set-raw-mode`; also no `encapsulate` at all |
| Digests in `tests/evidence/2026-09-18-bp-composition-assurance.json` vs HEAD | all 387 match |
| Digests in `tests/evidence/2026-09-18-composed-store.json` vs HEAD | 60 of 446 changed since the last all-roots run at `80afcbe` |
| Full `make certify` at HEAD | in progress at time of writing; see §2.1 |
| Unverified-guard sweep | `bp-outbound` 2, `bp-receipt-records` 9, `bp-workflow-records` 10, `checkpoint` 13 declared `:verify-guards nil` and never verified; BP total 97 as the evidence states |

No Python test suite was run. Auditors read; they did not certify.

### 2.1 Certification at HEAD

`make certify` at `a5a30d8` passed all 113 requested roots in 25 minutes 44
seconds wall on ACL2 8.7 / SBCL 2.6.8 (macOS arm64). Every root returned exit
code 0 with its nonce-tagged success marker observed and its certificate
digest recorded; the runner digest was unchanged and the forbidden-facility
audit found nothing. Evidence directory: `build/acl2/certify-20260919T021623Z-57755`.
This is the first all-roots run since `80afcbe`; it establishes that HEAD
certifies, not that any claim in §3 or §4 is closed.

## 3. Concrete defects to fix

Ordered by consequence. "Bug" means observable wrong behavior; "hole" means a
proof or model gap that a stated claim depends on.

| # | Kind | Where | Defect |
| --- | --- | --- | --- |
| D1 | Bug | `tools/run_bp_receive.py:164-186` | No `max_transactions` check on the BP accept path. `run_store.py:842` and `run_bp_ingress.py:228` have it. A 129th distinct request publishes `00000000000000000128.txn` and reports accepted; every later `Store.recover()` raises `StoreFault("transaction count exceeds configured bound")` at `run_store.py:528`. Store is unopenable with no recovery path. |
| D2 | Bug | `tools/run_store.py:158-173, 243-250` | No request/response correlation on the ACL2 pipe. A single `read_prompt` timeout or output-bound trip leaves the pipe permanently off by one; the next call receives the previous result. `run_reader.py:152-183` catches and continues, so the reader wedges. Fixed 20 s per call; recorded maximum-profile reopen is 11.7 s on this machine. |
| D3 | Bug | `books/nntp.lisp:1115-1116, 612-615` | `fn-nntp-projectionp` is re-run inside every `fn-nntp-step` and requires every committed article to be projectable. `fn-articlep` (`acceptance.lisp:303-313`) admits payloads the projection rejects; `nntp-tests.lisp:144-163` constructs one. One such article answers 503 to every command including `CAPABILITIES` and `QUIT`, and each command costs quadratic work in article count. |
| D4 | Hole | `books/store-files.lisp:455-480` | The crash constructor omits the two crash points `tests/store_crash_child.py:30-59, 80-109` actually hit: after `os.replace`/`os.link` return but before ACL2 observes `:ok`. In `:frontier-data-durable`/`:record-data-durable` a modeled crash yields old/absent only; reality is old-or-new / absent-or-present. The host survives only because it reopens via `fn-sn-open-observed`, never via `fn-sf-crash`. |
| D5 | Hole | `books/store-observed.lisp:64-68, 280-300`; `store-files-traces.lisp:639`; `store-node-traces.lisp:485` | Acknowledged-history retention is proved over the ghost `successes` list, and production recovery constructs `successes = nil`. Across a real restart the premise is unsatisfiable, so those theorems never apply to the state the host resumes from. Record survival holds only because `fn-sf-crash` cannot drop a record by construction: A-DURABILITY is the crash constructor, not a hypothesis constraining it. |
| D6 | Hole | `books/store-observed.lisp:13`; `store-node-traces.lisp:115` | No theorem connects `fn-sn-open-observed` (the host's entry on every process start, `host/store-node-host.lisp:27`) to `fn-snt-relation`. Every trace theorem is rooted at `fn-sn-initial`. The missing lemma is small. |
| D7 | Hole | `books/bp-workflow-records.lisp` (0 theorems); `host/workflow-host.lisp:9, 27, 40` | The host calls `fn-bp-replay-journal` and `fn-bp-apply-journal-record`. Every sender theorem is about `fn-bp-step`/`fn-bp-trace`. The replay interpreter is not a trace: it fabricates a `:storage-complete :indeterminate` event (`:165-168`) and appends `:restart` (`:157`). |
| D8 | Hole | `books/bp-workflow.lisp:483-490, 514-522`; `specs/bp-path.md:124-125` | "Durable intent before submission" is listed as a required safety result and is not a theorem anywhere. It is a definition shape, one `assert-event`, and Python ordering in `workflow_journal.py:359-366`. |
| D9 | Hole | `books/bp-workflow-records.lisp:92-97`; `tools/workflow_journal.py:59-65`; `receipt_journal.py:14, 32-34` | The A-POLICY verdict is not durable. Sender replay passes literal `t`; the FNWF record has no policy field; FNRJ stores the constant `t`. On disk, "record exists" is the authorization. The in-process guards `fn-bp-unchecked-receipt-is-no-op` and `fn-bpo-receipt-success-requires-local-policy` protect only the live call. |
| D10 | Bug | `books/bp-receipt.lisp:54-59, 143`; `host/bp-receive-host.lisp:49`; `run_bp_receive.py:69` | Receiver work identity is the work-id string alone; `specs/bp-adu.md:32` claims scoping by EID, incarnation, policy and terms. A second sender presenting any request with the same work-id is a permanent `:conflict`. Work-id squatting is an identity denial of service. |
| D11 | Bug | `tools/run_bp_receive.py:69-79` after `:182-183` | Receipt-id length is checked after the article is charged and the context persisted. A work-id of 249 to 256 octets is valid metadata but unreceiptable; retries land in `:context` and hit the same error; the BID is never deleted. |
| D12 | Bug | `tools/run_store.py:77-87`; `workflow_journal.py:85-88`; `receipt_journal.py` | Plain `os.fsync` only. On APFS, `fsync(2)` does not flush the drive cache; `F_FULLFSYNC` is required for the barrier the docstrings claim. The spec disclaims power loss generically and never names this. |
| D13 | Bug | `tools/run_store.py:942-944`; `run_bp_ingress.py:280-282`; `run_store.py:699-700` | Exit codes conflate uncertain, known failure and durable acceptance. `BpDeletePending` (a durable acceptance) exits 2. A post-link ACL2 rejection is labeled fault rather than indeterminate. HST-003 requires these distinct. |
| D14 | Bug | `tools/bpa_dtn7.py:182-184`; `workflow_journal.py:387-391, 438-441` | A lost BPA delete reply is unresolvable. Retry finds the BID absent from inventory and raises `JournalError("BID is not present in inventory")`; absence is never reconciled as completion. |

Smaller items, all confirmed: `run_store.py:423-451` writes `config.json` and the
frontier in place at init (torn write makes the store un-initialisable);
`test_bp_receive_process_crash.py:122-132` skips `killpg` when the child exits
on its own and orphans ACL2; journal lock files lack `O_NOFOLLOW`/`S_ISREG`
(`workflow_journal.py:196`, `receipt_journal.py:80`) while the store's do;
`fn-wire-begin-article` (`wire.lisp:212-220`) silently no-ops on non-empty
`line-rev`; `fn-wire-feed-byte` re-validates `fn-wire-statep` per byte, quadratic
in article mode (latent: nothing calls `fn-wire-begin-article` yet); the octet
regex at `run_store.py:187` is exponential on malformed output; `os._exit` fault
injection lives inside `WorkflowJournal.publish`.

## 4. Tautologies, unreachable branches, and ledger drift

These are not false theorems. They are theorems whose names, or whose registry
citations, claim more than the statement supports.

| Where | What the theorem actually says | What the prose or ledger says |
| --- | --- | --- |
| `retention.lisp:359-365` `fn-retain-wrong-evidence-does-not-release` | The else-branch of the definition: hypothesis is the negation of the `if` test at `:256`. Evidence is `(equal evidence admit-string)` at `:227-234`; no issuer, nonce, incarnation or authorization. | "evidence-gated release" (`docs/implementation.md:33`, `planning/assurance-closure.md:33`); cited by PRF-004 with A-POLICY |
| `node.lisp:139-157` binding relation | Passes the pin's own evidence to itself; binding is a `(msgid subject id)` string triple; `subject` never related to payload (`:17-18` admits) | "committed article-to-archive-pin relation" |
| `node-invariants.lisp:117-161`, `acceptance-invariants.lisp:243-272` | Six `*-preserves-*` theorems are `inv ⇒ inv` with a conjunct projected out; the hints name the two lemmas | PRF-002 cites these corollaries, not the keystone `fn-install-preserves-state` (`:188`) with `fn-watermark-does-not-conflict` (`:172`) |
| `node-traces.lisp:329` | Bindings-subset over traces; no transition removes a binding, so trivially true; article-record persistence is one-step only (`acceptance-invariants:206-240`) | "preserves all article-to-membership-to-pin bindings" (assurance-closure row 26) |
| `acceptance.lisp:615-619, 693-712`; `host/store-node-host.lisp:61-63` | `:durable` is a caller-chosen keyword; production passes `next-txid` for both txid and generation, so stale-generation rejection is unreachable from the live path; `host/reader-host.lisp:10-14` fabricates a durable completion at load | `fn-durable-completion-*` names; "rejects stale generations" |
| `journal.lisp:444-446, 448-507` | Nine theorems, none mentions `fn-journal-crash`; all definitional or single-slot; all unguarded | Header: "conditional on the crash constructor's stated platform assumptions"; PRF-007 cites four |
| `replay.lisp:61-66` | `fn-replay-faultp` requires the diagnostic prefix to be a valid node; no theorem forbids adopting it; every consumer gates on `fn-replay-okp` by convention | "last-good prefix on fault is diagnostic only" |
| `index.lisp:128-131, 204-207` | `fn-index-build-complete` instantiates `index := (fn-index-build articles)` and proves X ⊆ X; `sound` and `correspondence` likewise. Only `fn-index-range-query-correct` (`:183`) has content, for a fresh build | "both directions for rebuilds" (`specs/index.md`); "soundness/completeness over source memberships" (`reader-checkpoint-index.md`) |
| `store-files-traces.lisp:619-650` | "Externally emitted" retention assumes emitted ⇒ ghost member and renames the ghost theorem | Name suggests an external claim |
| `store-files-exploration-tests.lisp` | 9,038 = 211 × 43 − 35: the state-by-event product including no-op self-loops; two fixed records; no txid-gap record; no D4 crash points | "9,038 edges including allocator/record crash choices" |
| `checkpoint.lisp:293` | Both sides reduce to the same expression via `fn-sn-replay-loop-append`; the checkpoint frontier's rejecting role is outside the theorem; all 12 functions unguarded | "restore does not call full replay" |
| `transfer-public-bound.lisp:1041` | Hypothesis-free degree-4 bound on `fn-transfer-missing-ranges`, which has zero callers outside the transfer books; `reserve`/`add-chunk` uncosted; byte-identical partial overlap is `:overlap-conflict` with no byte comparison (`transfer.lisp:566-572`), a hard stall for re-fragmented objects | "full public validation/lookup/missing-range work bound certified"; counted for REP-003 |
| `wire.lisp:405-415` | Partition theorem over `fn-wire-feed-proper`; host calls `fn-wire-next` (`reader-host.lisp:91`); no theorem relates them | PRF-006; "Wire book proves partition behavior" |
| `nntp-effects.lisp:8-13`; `nntp-invariants.lisp:18-28` | Effect typing is "2-list `(:reply octets)` or close"; `(:reply (65))` passes. Session invariant admits NIL cursor unconditionally. A LISTGROUP 211 line with a 497-octet group name is 549 octets, over the RFC 3977 §3.1 limit | "effect typing certified" |
| `article-fields.lisp:311-314` | `fn-af-message-id-equalp` is `(and idp idp equal)`; the theorem is its definition | Cited for RFC 3977 App. A.2 / OBJ-002 |
| `article-invariants.lisp:117-121` | Source preservation is real for header and body; the `fields` view that `bp-ingress` consumes for Message-ID and Newsgroups has shape theorems only | "preserving original field order and folding" |
| `article-public-bound.lisp:112, 128` | Value side proved; cost side is an instrumented shadow checked by reading; the closed form is about 16,000× above the real cost | "exact correspondence with the actual parser for every ACL2 input" (true of the value only) |
| `bp-ingress.lisp` (0 theorems) | `fn-bpi-node-record-committedp` is a conjunct of the receiver's accepted-record predicate; `fn-bpi-adu-durably-acceptedp` is the host's basis for BPA delete; 35 functions unguarded | "certifies" (`specs/bp-ingress.md:73`) means 25 `assert-event`s |
| `bp-receiver-*` | The Store is a positional parameter; the same `store` appears on both sides of every relation theorem; the host passes a different Store each call (`bp-receipt-journal-host.lisp:12, 18-23`) mutated by ingress between calls; the relation is false mid-ingress because it demands phase `:ready` | Evidence discloses "fixed Store" honestly; the theorems cannot express the evolving case, so the seam is not a missing hypothesis discharge but a restatement |
| `bp-workflow-binding-invariants-tests.lisp:78-90` | The one "fabricated work" witness exercises only the missing-msgid clause; subject and archive equality are never separated | "structural validity alone does not imply binding" |
| `host/bp-receive-host.lisp:37-60`; `run_bp_receive.py:122-152` | Production duplicate recognition is `:program` host logic; the `:duplicate` branch of `fn-bpr-accept-request` is unreachable in production | Duplicate recognition described as core behavior |

Stale evidence: `transfer-public-work.lisp:352-353` says certification is
deferred while its `.cert` exists; `2026-09-18-fields-transfer.md` records a
pre-rewrite `transfer.lisp` digest; `specs/article-parser.md:88` contradicts
`specs/article-work.md`; the receiver process-death cuts check disk reopen only,
consistent with D4.

Twins across the host boundary, all confirmed:

| Decision | Python | ACL2 | Note |
| --- | --- | --- | --- |
| Message-ID validity | `run_store.py:793` (1..250 octets, ≤127, no bracket check) | `store-host.lisp:29` (3..512, 33..126, angle brackets); `article-fields.lisp:14` (250) | 250 vs 512 disagree |
| Group ↔ code | `run_store.py:29-31, 778-785` | `store-host.lisp:8, 38-40`; `bp-ingress-host.lisp:8-10`; `reader-host.lisp:5` | four hand-synchronised copies |
| Transaction bound 128 | `run_store.py:528, 842`; `run_bp_ingress.py:228` | none | adapter-only; missing at one site (D1) |
| Content identity | `run_store.py:771-775`: subject = `sha256:`hex(payload); obligation = `archive:`hex(sha256(msgid ‖ 0 ‖ subject)) | never derived; only compared (`bp-receive-host.lisp:61-66`) | the core identity rule lives in the adapter; two tests re-derive it |
| Charge policy | `run_store.py:788`: 1 + ⌈len/4096⌉ | checks `posp` and accounts | adapter-owned |
| Framing and integrity trailer | FNST/FNWF/FNRJ/FNBI + SHA-256, Python only | inner CBOR record only | no ACL2 encoder exists to compare against |

## 5. What is genuinely strong

Build on these; do not rewrite them.

- **Local-number freshness is real arithmetic.** `fn-install-preserves-state` with `fn-watermark-does-not-conflict` and `fn-allocate-at-watermark` (`acceptance-invariants.lisp:65-192`); `fn-statep` is inhabited by multi-article reachable witnesses.
- **The node install step discharges its hard premises from the invariant** rather than assuming them (`node-invariants.lisp:70-101`). This is the opposite of hypothesis smuggling.
- **Acknowledgement cannot be forged.** `fn-sn-new-success-requires-actual-matching-durable-node-completion` and `fn-sn-actual-durable-completion-installs-record`; every single-field mismatch blocks `finish` (`store-node-tests.lisp:31-68`). The five-barrier gate is structural through `fn-sf-phase-shapep`.
- **`fn-snt-relation` preservation** has real per-phase content and its trace dispatchers quantify over raw events with no recognizer.
- **The trace inductions are real**: node traces with a 17-event all-branch witness plus an improper-tail witness; exchange traces; `fn-bp-trace-preserves-node` is an unconditional equality.
- **`fn-bprv-replayed-receipt-is-grounded`**: one hypothesis, twelve conjuncts tying emitted receipt bytes to a ready Store record and node binding, with three separating witnesses. `fn-bp-record-contextp` makes a forged sender journal record fail replay.
- **Codecs are closed both directions**: CBOR and the schema-0 record prove `decode(encode(v)) = v` and `encode(decode(b)) = b` for accepted `b`, with non-minimal heads rejected at the CBOR level; the BP ADU profile is canonical and 41/41 guarded.
- **Wildmat**: the matcher is proved equal to an independent backtracking reference; rightmost-wins is proved against a left-to-right last-match reference, which is RFC 3977 §4.2; the UTF-8 decoder is table-exact to RFC 3629.
- **Article source preservation** is a genuine induction with the sole premise "parse succeeded", for all inputs.
- **No wrapper laundering anywhere.** The host calls exactly the theorem subjects (`fn-sn-*`, `fn-wire-next`, `fn-nntp-step`, `fn-bpr-receipt-adu`). Guards in the executed core graphs are genuinely verified; `mbe` equalities are global rewrite rules; the guard-audit test books check `:common-lisp-compliant` and guard `t`.
- **The bridge is sound by construction.** Every external byte crosses as a decimal octet list; results are regex-constrained and whitelisted; stderr is merged and any noise fails closed into a fence. No injection vector was constructible.
- **Durability sequences are textbook** apart from D12 and the init path: `O_EXCL` staging with pid and random names, fsync file, link or replace, fsync directory, fence before every post-syscall ACL2 call, in-memory state advanced only after the last barrier and acknowledgement, link `EEXIST` treated as indeterminate.
- **`tools/certify_books.py` cannot be fooled** by a book that prints an error: nonce-tagged markers in order, digests before and after, closure audit of forbidden facilities, exit code plus marker plus certificate all required.
- **The tests are real**: no skips, no `expectedFailure`, no commented assertions; fault matrices assert post-recovery txids, counts, payloads and lock release.
- **The evidence prose is unusually honest** about fixed-Store, tested-versus-proved, and the 97-function guard gap.

## 6. Structural naiveties

These are shape problems. Each is currently a deferred packet; the argument here
is that the deferral order produces the defects in §3 and §4, and should invert.

1. **No adversary.** Every theorem is honest-but-crashy hosts under A-HOST and
   cooperative peers under A-PEER. A DTN node's job is carrying strangers'
   bytes. Admission control with a hostile peer is the theorem that matters,
   and capacity is one global number with no principal to charge (D10 is the
   first symptom).
2. **No identity, no causality.** Facts are a flat set keyed by exact
   Message-ID. Authority is a boolean that becomes the constant `t` on disk
   (D9). Receipts therefore commit to a decision bit, not to a policy term and
   evidence hash, and cannot be re-verified later. Meanwhile D10 (restore/fork)
   is designed around an external freshness anchor, when a causal block
   structure gives fork detection for free: a restored node reusing a sequence
   number is an equivocator, and both blocks are kept as evidence, which is
   OBJ-004 falling out of the substrate.
3. **Durability is testimony.** The core theorem shape is "host reports durable
   for generation g, therefore publish". The forced direction (replay from
   bytes) exists but framing, the integrity trailer, the content-identity
   derivation, fsync, and the errno-to-outcome mapping all live in Python
   outside the proof (§4 twins, D5, D12). The crash constructor is the
   assumption (D4, D5).
4. **BP is three verbs on one BPA.** Submit, inventory, download-and-delete. No
   primary block, no creation-timestamp-plus-sequence identity, no
   fragmentation, no lifetime semantics, no BPSec, and the BID is a dtn7-rs
   table key. A relay cannot be built on that identity; ION would not fit the
   adapter. C1-12 (LTP feasibility) is premature until the model has a primary
   block.
5. **No time.** Neither NNTP injection nor bundle expiry can be modeled;
   expiry correctness is clock-error correctness (FLR-004 knows). Clocks are
   deferred to C1-05 and C2-06.
6. **Two journals per node, fixed Store in the proofs, no obligation
   release.** Nothing in `fn-bp` ever calls `fn-retain-release`; a work with a
   receipt merely stops being outstanding. Cross-journal recovery is the actual
   hard theorem and the receiver theorems cannot state it.
7. **Single owner, single session.** No version pin for readers concurrent with
   the mutable owner that C1-05 introduces; D3 shows the reader already couples
   every command to the whole store.

Two assurance-discipline gaps sit underneath all seven:

- **There is no `encapsulate` in the tree.** A-DURABILITY, A-HOST, A-CRYPTO,
  A-PEER, A-POLICY exist only as prose. ACL2's constrained functions with local
  witnesses are the native mechanism for named, mechanically listable
  assumptions whose satisfiability is proved once.
- **There is no teeth discipline.** One fabricated witness exists (and it
  separates the predicates by their weakest clause). No keystone has a
  systematic must-fail sibling per hypothesis. The proof registry's `events`
  lists are hand-maintained and, as §4 shows, point at corollaries.

## 7. Bedrock: fn and dregg/minidregg

The portable layer fn is specifying is already built and proved one directory
over.

| fn concept | dregg / minidregg artifact |
| --- | --- |
| OBJ-006 origin event: origin, incarnation, sequence, causal predecessors | `Block { creator, sequence, predecessors, payload, signature, pq_signature }` (`~/dev/breadstuffs/blocklace/src/lib.rs`; `metatheory/Dregg2/Authority/Blocklace.lean:58`) |
| REP-002: set union of validated immutable facts is associative, commutative, idempotent | `LaceMerge`: `laceIds (mergeLace B Δ) = laceIds B ∪ laceIds Δ`, CRDT laws read off `Finset ∪` (`Dregg2/Distributed/LaceMerge.lean`; ported and strengthened in `~/dev/minidregg/Theory/LaceMerge.lean`) |
| OBJ-001 digest collision ⇒ quarantine; A-CRYPTO | `CrossCanonical`, the named seam that was carried anonymously until named; in minidregg derived from the typed `ContentAddressing.BindingPremise` realizer slot |
| D10 restore/fork; PRF-017 origin non-reuse | `Equivocator B p`: a creator with an incomparable in-lace pair. Detection is structural; no external anchor is needed to detect, only to choose which fork is live |
| D09/D11 principals, keys, group authority, PQ | `CellId = derive_key(pubkey, token)`; capability chains (`Crypto/CapabilityChain.lean`, `Authority/BiscuitGraph.lean`); `HybridBlockSigner` ed25519 + ML-DSA (`blocklace/src/pq.rs`) |
| statement (issuer, scope, subject, terms) | signed turn / strand entry; helm's "posts as signed turns, receipts on chain" |

fn's contribution to that family is what dregg lacks: a delay-tolerant,
resource-accounted, obligation-bearing **carrier** with NNTP as its human
interface. That is the thing to design in ACL2. The block, the merge, the
collision seam, equivocation and the principal model should be imported.

The two-tower question (ACL2 here, Lean there) has a defensible split under
ATLAS laws 5 and 13: Lean authors the portable object profile (block and
statement CBOR, golden vectors, emitted), and ACL2 proves fn **carries** it
(NNTP, BP, the store machine, guard-verified fast execution) and must pass the
emitted vectors. The twin becomes a checked conformance rather than a second
implementation. The Python twins in §4 go away for the same reason.

## 8. Recommended re-sequencing of C1

Keep the packet IDs from `swarm-cycles.md`. Move the substrate first, add five
packets, and reshape three. Model tiers follow the user's 2026-09-18 guidance:
Sonnet for well-specified mechanical work, Opus for ordinary implementation and
proof, Fable for refinement and composition seams.

| Order | Packet | Change | Tier |
| --- | --- | --- | --- |
| 0 | **C1-00 repair** (new) | D1, D2, D3, D10, D11, D12, D13, D14 and the small items; registry hygiene from §4 (cite keystones, retitle tautologies, retract "certified" where the theorem is on an uncalled API); stale evidence lines | Sonnet |
| 1 | **C1-11 substrate** (promoted, reshaped) | Adopt the block shape as the fn statement header; import CellId and capability-chain authority; hybrid signature profile; policy **term** plus evidence hash in every receipt and journal record (closes D9). Emits the profile and vectors from Lean; ACL2 consumes. Gates C1-06 and all of C2 | Fable design, Opus implementation |
| 2 | **C1-13 bytes into ACL2** (new) | Frame codecs (FNST/FNWF/FNRJ/FNBI + trailer), content-identity derivation, Message-ID bound, charge policy, group table: one owner in ACL2; Python becomes a byte pump. Kills the §4 twins | Opus |
| 3 | **C1-14 crash-model fidelity** (new) | Add the two syscall-returned-unobserved crash points (D4); restate acknowledged-history retention over records or make `successes` survive `open-observed` (D5); prove `open-observed ⇒ fn-snt-relation` (D6); `F_FULLFSYNC` and staged init | Fable |
| 4 | **C1-15 assumptions as encapsulates** (new) | A-DURABILITY, A-HOST, A-CRYPTO, A-PEER, A-POLICY as constrained functions with local witnesses; functional instantiation is the platform-qualification hook | Opus |
| 5 | **C1-16 teeth ledger** (new) | For every keystone: a must-fail sibling per hypothesis, checked as `must-fail`; `proofs.json` `events` generated from the books, not hand-listed | Sonnet |
| 6 | C1-01 BP guards | Unchanged | Sonnet |
| 7 | C1-02 / C1-03 FNWF / FNRJ refinement | Add: lift sender theorems to `fn-bp-replay-journal` and `fn-bp-apply-journal-record` (D7); state "durable intent before submit" as a theorem (D8); fix status regression to `:intent` | Fable |
| 8 | C1-04 evolving Store | Reshape: the Store must be indexed by the relation, not positional; depends on C1-14 | Fable |
| 9 | C1-05 mutable owner | Add: reader version pin; clock observation type (naivety 5 and 7) | Opus |
| 10 | C1-07 reader | Fix D3 first; real effect typing (status code, CRLF, dot-stuffing, 512-octet initial line) | Opus |
| 11 | C1-08 resource | Per-principal accounting; depends on C1-11 | Opus |
| 12 | C1-09 index / C1-10 checkpoint | Fix X ⊆ X; verify checkpoint guards; strengthen the equivalence to exhibit the frontier's rejecting role | Sonnet / Opus |
| 13 | C1-06 POST | After C1-11 and C1-13 | Opus |
| 14 | C1-12 LTP | Reshape: model the BP primary block first (naivety 4); LTP feasibility only against that | Opus |

Non-negotiable prompt content for every lane, learned from this tree: paste real
signatures and absolute paths; forbid `inv ⇒ inv` corollaries as deliverables;
require a must-fail witness per hypothesis; require that the theorem subject be
the function the host calls, named; build the whole tree after any shared-struct
edit; report the pessimistic number with its covered scope in the same sentence.

## 9. Per-cluster auditor summaries

The five auditors' full reports, with per-book theorem-by-theorem verdict
tables, are retained in the session scratchpad and summarised above.

| Auditor | Cluster | Feeds |
| --- | --- | --- |
| Core | acceptance, node, node-traces, retention, replay, exchange, journal | §4 rows 1 to 7; §5 first three items |
| Storage | store-files, store-node, store-observed, checkpoint, index, records | D4, D5, D6; §4 rows 8 to 11 |
| BP | bp-workflow, bp-receipt, bp-receiver-*, bp-outbound, bp-ingress, bp-adu | D7 to D11; §4 rows 18 to 20 |
| Codec | wire, nntp, wildmat, article, cbor, transfer | D3; §4 rows 12 to 17 |
| Host | tools, host, tests | D1, D2, D12 to D14; the twins table; §5 bridge and durability items |
