# fn2 layer B: the crash and log models, the formats, the commit batch, the allocator, recovery, checkpoint, cleaner

Present state, rewritten whole by the layer-B seat. The contract is
`build/coordinator/briefs/FN2-LAYER-B-DURABILITY.md`; the decisions it serves are
`build/coordinator/fn2/EXECUTION-MODEL.md` rule 8, `fn2/EXECUTION-MODEL-ROUND2-ASTRA.md` §E (the
durability protocol) and §F (checkers HISTORY, RECOVERY, RECLAIM; scenarios 13-17),
`fn2/STORAGE-DESIGN.md` (§4 as amended, §7 the decisive demonstration) and the concrete format of
`fn2/STORAGE-DESIGN-ASTRA.md` "The concrete storage format and root-selection algorithm with recovery
invariants" (§A-§J below means that section's lettered parts). Layer A's decisions
(`fn2/docs/a-pool-host-sim.md`) bind this layer too. A departure from a decision that is not
recorded here is a defect.

## 1. Where each piece lives
| piece | file(s) | quest |
|---|---|---|
| crash model (block device, the papers table's faults) | `fn2/books/crash-model.lisp` | B1 |
| shared named tuple readers and updaters | `fn2/books/tuple.lisp` | BR1 |
| log model (abstract history, acknowledgement, allowed recoveries) | `fn2/books/log-model.lisp` | B1 |
| layout codec compiler and list specification | `fn2/books/layout.lisp` | B2a |
| incremental BLAKE3 over the pool | `fn2/books/blake3.lisp` | B2b |
| the on-disk format as layouts | `fn2/books/format.lisp` | B2c |
| format integrity readers and sealing | `fn2/books/format-check.lisp`, `fn2/books/format-context.lisp` | B2d |
| semantic Merkle event frontier and proof verification | `fn2/books/merkle.lisp` | B2e |
| commit-batch machine (declared through layer A's `defmachine`) | `fn2/books/commit.lisp` (**owed**) | B3 |
| allocator with typed edges | `fn2/books/alloc.lisp` | B4 |
| recovery | `fn2/books/recovery.lisp` (**owed**) | B5 |
| checkpoint and cleaner machines | `fn2/books/checkpoint.lisp`, `fn2/books/cleaner.lisp` (**owed**) | B6 |
| HISTORY, RECOVERY, RECLAIM checkers | `fn2/sim/check-history.lisp`, `check-recovery.lisp` (**owed**), `check-reclaim.lisp` | B3-B6 |
| acceptance | `fn2/tests/sim-layer-b.lisp` (+ driver `.lsp`, **owed**) | B3-B7 |

## 2. Decisions inside the contract
- **B-HASH-ATTACHED.** Every 64 KiB payload block is hashed and content-named;
  BLAKE3 composes its subtree CVs into object hashes and range checks. Served hash-mode
  paths attach the vendored C BLAKE3. `blake3-spec.lisp`, `blake3-pool-spec.lisp` and the
  incremental ACL2 implementation remain the specification, differential oracle and
  fallback. The target is device throughput. Each process must qualify its native
  primitives before installing them; `A-CRYPTO-NATIVE` explicitly assumes their
  correspondence to BLAKE3. Finite vectors and differential tests qualify that assumption,
  rather than proving it. Keyed and derive modes retain the ACL2 implementation.
  Padding scans use the separately qualified `A-NATIVE-SPAN` first-nonzero primitive;
  ACL2 still decides admission, refusal order and consumed-byte charges.
- **B-DIGEST-ROWS (remedy 16).** A digest is an index into the B-owned, profile-sized
  `defcolumns fn2-digests` table of eight u32 columns. BLAKE3, Merkle proofs and format
  expectations share this representation. Named workspace regions replace word offsets;
  guarded indexes and widths replace absorbing reads and writes (B8).
- **B-BLOCK-DEVICE.** The crash model is a block-device model, not a POSIX one: fn2 has one
  preallocated data file or a raw device and no directories, rename, unlink or fsync(dirfd)
  (ENVELOPE §2.3 "What is absent"). The quarry's `books/byte-store.lisp` contributes its outcome
  vocabulary (every operation takes an environment-chosen outcome), its tear rule (a landing write
  cut into write units that land as written, as zeros, or as garbage) and its fsyncgate rule (a failed
  fence lands a torn selection and discards the rest); its inode and directory tables do not carry.
  The file backend is an implementation of the device (ENVELOPE §2.4 row "storage"); file growth is
  absent because the file is preallocated and zero-filled at format.
- **B-MODEL-IS-PREDICATE.** The crash model is ACL2 logic over lists (the list view exists only in
  the logic and in test/checker code; nothing on a served path executes it). It is stated as an
  *allowed-outcome predicate* (`given the trace so far, is this observed image / read result /
  completion allowed?`) rather than as an enumerator, so the simulator's concrete choice is checked
  by membership, trace by trace (ENVELOPE §2.6: "checked against it trace by trace").
- **B-ASSUMPTIONS-AS-PARAMETERS.** `A-PERSISTENCE-FENCE`, `A-INTEGRITY-EVIDENCE` and
  `A-INDEPENDENT-FRONTIER` (ROUND2 §E.5) are explicit fields of the fault profile passed to the
  model and to recovery; recovery's permitted conclusions are a function of them. The format checker states collision freedom of its two covered openings directly;
  it does not decorate that premise with an unreachable integrity-evidence disjunct.
- **B-IDENTITY-EXACT** (ember, 2026-10-28, via the coordinator): exact Message-ID octets are kept
  permanently in the identity metadata with content identity, acceptance binding and conflict
  state; erasure of identities is the operator's matter outside the node's contract; no digest-only
  identity and no aging window (STORAGE-DESIGN §4.6 updated). For this layer: the journal's identity
  records and the identity commitment of the checkpoint claim carry and commit to the exact octets.
- **B-ONE-DSL-OWNER** (coordinator, from the 2026-10-28 review, finding 5/10): layer A owns
  `defcolumns` and `defmachine`; the commit-batch, checkpoint, cleaner and recovery machines are
  declared through A's `defmachine` (A4b) and wait for it. BR1 explicitly assigns the
  on-disk `deflayout` codec compiler to layer B; it does not replace either A generator.
- **B-DEFLAYOUT.** `deflayout` compiles a named declaration into per-layout encoders,
  resumable decoders, field indexes, enum constants and an ACL2 world-table entry. Kind
  dispatch and fixed offsets are resolved at expansion time. The list interpreter is the
  specification, not the served implementation. The flat form is the generated functions;
  these are the subject of a future ATC qualification or extraction, not a cons-list
  descriptor. Layer A retains ownership of `defcolumns` and `defmachine`; `deflayout` is
  the on-disk codec compiler explicitly authorized by BR1.
- **B-COMPLETION-ONLY** (coordinator, storage ABI): the core observes an I/O effect only at its
  completion; the simulator's completion-time, reorderable semantics is the contract. The commit
  machine's dependencies -> log-write -> fence phases advance on completions only.
- **B-WIDTHS.** As A-WIDTHS: in-memory counters are `u60`; persistent integers use the canonical
  unsigned base-128 encoding of §A (shortest form, numeric order, resumable decode), so no resident
  bignum and no fixed-width namespace ceiling.
- **B-GEOMETRY.** Format parameters, not ceilings: sector `S = 4096` (append and damage-isolation
  unit), tear unit 512 inside it, payload/page block `P = 65536`; the device's write-damage radius is
  a declared profile field of the crash model (default: a torn write damages only units of its own
  sectors; the broad profile admits damage to durable units within the radius of an in-flight
  write, papers table row 6).

## 3. Simulator gaps

B1 compares the same storage entry points that A's adapter calls with the list oracle. A already
implements arbitrary short-write prefixes, misdirected completed writes followed by torn crash
landing, both failed-barrier reopen views, and sticky device death. These are not gaps.

| Papers-table row | Model behaviour | What A's simulator would need |
|---|---|---|
| 6 | A crash damages clean tear units within the declared sector radius of a physical in-flight write. | A collateral-damage choice over neighboring clean units; `crash-unit` currently requires pending bytes in that unit. |
| 3, 11 | An in-flight request is physically redirected before any completion, then tears or is lost at crash. | Record its physical destination before completion and use it in `sim-crash-flight-one`; that path currently uses fault 26 and the intended address. Completed miswrites can already tear later. |
| 5 | A lying successful fence loses selected covered units, retaining others; a lying FUA completion may lose its own bytes. | A per-unit landing selection at fence completion and a lying-FUA outcome; `lie` currently skips the whole fence snapshot, while successful FUA always persists its own bytes. |
| 8, 10 | A failed fence lands a torn selection, with the remaining cache retained or discarded on reopen. | Invoke tear landing during failed completion; current `fail` leaves the entire durable image unchanged. Both basic reopen views already exist; add `:cached-lost` to retain readable cached bytes after discarding their dirty status, so a later fence cannot resurrect lost writeback. |
| 14, 15 | Preflush followed by own-request FUA, including death between the phases and a short final write after successful preflush. | A separate preflush stage and snapshot on the request; the current FUA flag persists only its own bytes. |
| 10 | Each landing tear unit may contain an arbitrary octet string. | A per-byte garbage selector for one tear; current crash landing repeats one chosen byte per unit. Separate `corrupt-byte` calls can compose more varieties. |
| 22 | An `:io` or `:no-space` write leaves the entire request uncertain, including possible unreported physical progress. | Fault choices that modify storage before returning these errors; currently the byte operation fails before modifying a byte. Short known progress is already implemented. |
| 10, 14 | A live torn landing is not evidence that an honest later fence persisted the covered bytes. | Repair the interaction between `storage-land-bytes` and `storage-fence-bytes`: landing garbage currently copies the pending completion stamp into the durable stamp, so a subsequent fence can skip the required write. The B1 differential driver contains a fixed regression and reports seeded occurrences separately. |
| 8, 11, 14 | A stale cached version cannot undo a newer durable fence snapshot at crash. | Require a strictly newer pending stamp before treating a unit as dirty. The simulator currently uses unequal stamps, so reopening before an outstanding fence completes can make old bytes or garbage overwrite the new durable version. First seeded counterexample: `20261329`; the driver includes a fixed regression. |

Fail-slow (row 19) is latency. It changes scheduling in A but has no observation in the untimed
crash or log safety models. Row 9's multiple-descriptor error delivery is outside the one-device,
one-descriptor interface; raw flash, persistent memory, and tenant confidentiality (16–18) are
outside this model. Real-kernel trace replay (21) remains a separate validation obligation.

## 4. The crash model and log model

Seat repair at review (2026-10-28): `fn2-lm-recovery-allowedp` required `:intact` when corruption
or rollback had occurred but the profile's assumptions gave recovery no means to detect it; a
recovery that noticed it by other evidence would have been refused. Now such traces permit
`:intact`, `:damaged` or `:unknown` (no detection claim either way); `log-model-unit` asserts it.

`books/tuple.lisp` shares `fn2-cm-defreaders` across the crash, log and history
models. It generates named readers and `update-READER` updaters for each declared
logical tuple; positional `nth` remains only where a sequence position is the meaning.
These list representations belong to logic and test checkers, not served storage.

`books/crash-model.lisp` represents one block device. A geometry is
`(sector-size tear-unit sector-count radius)`; the development geometry uses 4,096-byte sectors
and 512-byte tear units. Radius is measured in sectors and capped by both geometry and profile.
Images are lists of tear-unit octet lists. State holds durable and visible images, their per-byte
completion stamps, completed-write records in completion order, submitted writes, per-fence
submission snapshots and covered write sets, sticky death, the u60 completion serial, spent
at-rest corruption budget, and a failed-barrier flag. Stamps order overlapping versions; they
are not a durability theorem. No served operation executes this list representation.

`fn2-cm-profile(kind, persistence-fence, integrity-evidence, independent-frontier, radius,
corruption-budget)` names `:crash-only`, `:broad`, or `:lying` and the three separate assumption
bits. The at-rest corruption budget counts explicit affected tear units. Collateral crash damage
is bounded by the declared radius; torn bytes inside a pending write are not at-rest budget use.
The profile does not assert the assumptions about hardware. Layer A's constrained
`fn2-a-integrity-evidence` supplies the named checksum premise for refinement.

The central oracle interfaces are:

- `fn2-cm-read-allowedp(state, byte-address, outcome, bytes, profile)`.
- `fn2-cm-crash-image-allowedp(state, image, profile)`.
- `fn2-cm-fence-allowedp(state, op, outcome, image, profile)`.

Writes are submitted with `(op, byte-address, bytes, fua)` and completed with an environment
outcome: `:ok`, `:io`, `:no-space`, `(:ok physical-address)`, or
`(:short known-progress physical-address)`. Failures retain uncertainty over the request; short
progress changes the visible prefix. `fn2-cm-redirect-write` selects a physical destination before
completion. Plain FUA persists its own known progress. On a profile without the fence assumption,
`(:ok physical-address :lose-fua)` explicitly selects a lying FUA result; ordinary success may
still persist. `:preflush-fua` is a distinct request mode. `fn2-cm-complete-preflush` exposes its
internal barrier cut; submission freezes the covered completed-write set as well as byte/stamp
snapshots, including earlier ambiguous zero-progress failures. The final request starts after
that phase, including when its own completion
is short. A full successful completion also has a convenience transition performing both phases.

Fences cover completed writes at submission. Completion accepts `:ok` or `:io`, plus explicit
`(:ok :persist)` and `(:ok :lie)` choices: a device permitted to lie may execute an honest fence
on one request. An honest fence installs its covered snapshot without replacing newer persisted
versions. A failed or lying fence admits a torn selection of covered units. `fn2-cm-reopen` chooses
cached (`nil`) or reverted (`t`) visibility; after failure, `:cached-lost` keeps cached
bytes readable but discards their dirty tracking. It is a storage-view operation, not process
cancellation.
`fn2-cm-crash` drops all outstanding operations, resets visibility to the allowed durable image,
and retains sticky device death. `fn2-cm-land-live` models A's live tear injection without treating
that landing as successful persistence. `fn2-cm-corrupt` explicitly changes an at-rest unit and
spends budget. Reads return the visible bytes, `:io`, or `(:misdirect physical-address)` data.

Callers carry `fn2-cm-statep` from initialization through the model transitions; the
membership predicates do not revalidate the whole state. The crash predicate traverses tear
units. An affected unit admits any unit-sized octet list because
the quarry's garbage choice ranges over every such list; other units must equal their durable
contents. This admits every subset and ordering of in-flight and volatile landing writes without
enumerating subsets. At-rest faults are explicit transitions, so a corruption budget cannot excuse
an unexplained mutation of a clean unit in an observed crash image.

`books/log-model.lisp` defines sealed batches `(number predecessor records dependency-set)` and a
validated event trace for one history incarnation. `:submit-batch`, `:batch-writes-complete` with
the complete dependency set, `:fence-ok`, `:acknowledge`, and `:crash` separate submission,
completion, persistence, and the client's success. Acknowledgement requires the batch's own fence
and every predecessor's fence. B3 and B5 call exactly
`fn2-lm-recovery-allowedp(trace, profile, classification, recovered-history)` for HISTORY/RECOVERY.

Recovery histories are prefixes of the submitted batches. Complete unacknowledged batches may be
adopted; `:survives` records complete landing even without a completion observation. The observation
events `:corrupt-required`, `:bad-tail`, `:rollback`, and `:present-frontier` identify actual
post-write faults and available evidence. Honest fences without subsequent destruction require
all acknowledged batches in every permitted recovery. Integrity-backed required corruption yields
`:damaged` or `:unknown`, never a shorter `:intact` history. An unexplained bad final batch is
`:unknown` under broad profiles; the harmless `:torn-tail` conclusion needs the crash-only profile.

Rollback detection requires both `A-INDEPENDENT-FRONTIER` and a presented, named witness;
`fn2-lm-conflicting-witness` returns that name. Without both, an older consistent prefix is permitted
and no rollback-detection claim is made. Repeated read-only recovery crashes retain actual damage
and require witness observations to be presented again. `fn2-lm-integrity-premise` connects the
profile's integrity bit to A's constrained predicate for B5's eventual refinement. Abstract batches
are not counted as corrupt storage units: one damaged shared dependency can affect several batches.

The four B1 keystones are recorded by `defthm-owed`, with evaluated positive and hypothesis-removal
witnesses in the unit books. They remain unproved; certification establishes admission and execution
of the tests, not a completed durability/refinement proof. Their statements and scope are in
`OWED.md` under Layer B.

## 5. Layouts

`(deflayout NAME LAYOUT-EXPRESSION)` evaluates the declaration at book expansion time.
`NAME` is an unstarred symbol, for example `fn2-format-frame-header`; its logical
layout is `*fn2-format-frame-header*`. Composition with `append` and
`fn2-format-prefix` happens only during expansion. The compiler records a `fn2-layouts`
world-table row keyed by NAME. It emits `*NAME-NUM-FIELDS*`, `*NAME-MAX-SIZE*`,
`*NAME-FIELD-<field>*` indexes and `*NAME-PHASE-<field>*` / `*NAME-PHASE-DONE*`
continuation constants; enum fields also emit their declared enum's named constants.
The encoder, size calculation and value checks use statically named field steps
(`NAME-emit-<field>`, `NAME-size-<field>`, `NAME-check-<field>`). Each step has a small
proof boundary and calls its fixed successor; this avoids expanding a whole layout's
nested return checks during proofs. No runtime operation walks the declaration or
recomputes a field's kind. Field names must not collide after keyword normalization,
and `DONE` is reserved for the terminal phase.

The generated interfaces (final arguments are stobjs) are:

- `NAME-size(base, fields)` returns the encoded byte count from named field positions.
- `NAME-start(base, fields)` clears the continuation belonging to this decode.
- `NAME-encode(base, slot, gen, off, okind, oslot, ogen, fields, pool)` returns
  `(mv code end pool)`. Fixed fields use expansion-time offsets up to the first variable
  field; subsequent offsets add the generated preceding field sizes.
- `NAME-decode-step(base, slot, gen, off, end, okind, oslot, ogen, budget, fields, pool)`
  returns `(mv code next fields)`. `budget` is 1..4096 byte transitions; `:more` preserves
  its generated phase and partial field. `NAME-decode` has the same arguments without
  budget and starts a new decode with budget 4096.

`base` is the first field row in an exclusively owned contiguous range of
`*NAME-NUM-FIELDS*` rows. Fields are addressed as `base + *NAME-FIELD-<field>*`.
The continuation occupies named columns of the base row, so concurrent decoders use
independent base rows and disjoint field ranges. They never stash one another's state.
`fn2-fields-init` allocates profile capacity once. Field columns are `value:u60`,
`ref-slot:u32`, `ref-gen:u60`, `ref-off:u32`, `ref-len:u32`, `status:u8`.
Keep source handles and already consumed bytes immutable across `:more`.

| Kind | Encoding | Destination / refusal |
|---|---|---|
| `:u8`, `:u16`, `:u32` | fixed little-endian | value; encode `:value` for out-of-width |
| `:u64` | eight little-endian bytes | value; currently `:wide` above its u60 destination |
| `:varint`, `:u60`, `(:id NS)` | shortest unsigned base-128, low groups first | value; `:noncanonical`, `:wide` |
| `:bool`, `(:enum NAME (keywords))` | one declared code | value; `:unknown-tag` |
| `:digest` | BLAKE3-256 tag 1 then 32 bytes | value tag and source reference |
| `(:octets MAX)` | canonical length then payload | source reference; `:length` |
| `(:zero N)` | N zero bytes | `:nonzero-padding` |

A-WIDTH-PER-COLUMN governs refusal: decoded integers are refused only when they exceed
an explicitly declared destination width. Native `:u64` columns are pending in layer A;
until they land, `:u64` wire values use the existing u60 destination and refuse above
that width. This is a representation limitation, not a u60 on-disk format definition.
Varints scan through their terminal group before reporting `:wide`. Truncation reports
`:truncated`; canonicality concerns the consumed prefix, not trailing bytes.

`fn2-layout-copy` remains the single payload-copy seam until A supplies its range
primitives. The generated encoder invokes it for a payload field, not for each byte.
Sources and destination are checked before encoding; overlap is refused. The list
functions `fn2-layout-octets`, `fn2-layout-parse` and the old generic codec are
specification/test oracles only. Differential drivers compare generated encodings and
decodings against that specification. Each declaration also registers
`NAME-roundtrip` and `NAME-canonical` obligations about its actual generated exports.
`NAME-roundtrip-hyps` names the complete one-shot precondition, including the 4096
transition budget. Those general correspondence proofs remain owed; unit teeth and
random differential drivers are executable evidence, not proofs.

## 6. Format

The catalog in `books/format.lisp` joins independently certified declarations in
`format-physical.lisp`, `format-events.lisp` and `format-storage.lisp`, sharing
`format-base.lisp`. The declarations and generated codecs describe field encoding only. The readers in
`books/format-check.lisp` check framing, expected physical identities and integrity hashes.
Neither establishes semantic folding, query completeness, availability, freshness, authority,
or the predecessor-cut restriction (STORAGE-DESIGN §4.4).

### Integrity readers and sealing

`fn2-fc-init(n, fc)` and `fn2-fc-context-init(n, context)` allocate checker
continuations and expected-context rows. Each active checker owns its numbered row in
both tables and in the separately initialized BLAKE3 table. The `base` argument names
its disjoint range of decoded field rows; reserve at least
`*fn2-format-sealed-batch-num-fields*` rows per active checker. The decoder keeps its
own continuation in that range. No cursor or decoded value is saved and restored by
the checker.

The export is
`fn2-format-run(kind, sealp, row, slot, gen, off, len, base, okind, oslot, ogen, budget,
fc, context, b3, fields, pool, digests)`, returning `(mv code fc b3 fields pool digests)`.
`kind` is `:frame`, `:page`, `:anchor` or `:seal`; `sealp` selects writing the final
hash instead of checking it. Page names live in their parent: `fn2-format-seal-page`
uses the same continuation and writes the result into the digest row referenced by
`context.hash`. `budget` is 1..4096 byte transitions. `:more` retains the continuation; every terminal result resets it.
`fn2-fc-reset` explicitly abandons an unfinished operation. The internal driver uses
`fn2-format-fuel(len)` rather than duplicating a fuel formula across wrappers.

The expected-context row has named columns: `location`, `allocation`, `history`,
`incarnation`, `writer-epoch`, `commit`, `page-kind`, `encoded-length`,
`extent-writer-epoch`, `extent`, `previous-commit`, and the u32 digest-row references
`hash`, `geometry`, `previous-seal`. Other expectations are u60. The checker result is
in its named `*fn2-fc-result*` digest region. Populate references with generated
`fn2-fc-context-set-NAME` setters and words with the digest table's generated setters.
Each checker also owns its numbered BLAKE3 row and digest workspace stripe. Keep expectations, input handles and input bytes immutable across `:more`;
a sealer exclusively owns its output range. Decoded field accesses use the
`deflayout` generated field-index constants.

Frame hashing is `BLAKE3("fn2/journal-frame/v1" || LE64(location) ||
LE64(extent-writer-epoch) || LE64(allocation) || exact-frame-with-hash-zeroed)`.
Frames are 4096 bytes. Only the final 32 hash bytes are zeroed; the algorithm tag stays
covered. The header must match expected history, incarnation, batch writer epoch,
commit, extent and extent allocation pair, and padding must be zero.

Page hashing is `BLAKE3("fn2/physical-page/v1" || exact-encoded-page)`. The checker
matches physical unit, allocation pair, kind, encoded length and parent-held hash,
plus history and incarnation. Header/payload bounds and zero padding are checked.
The page/frame bulk path admits a whole readable span, scans padding for its first
nonzero byte, and hashes only the valid prefix. Frames stop the bulk region before
the algorithm tag and final digest, retaining their ordered byte checks.
`fn2-fc-zero-prefix(absolute-offset, length, pool)` is an ACL2-defined, guard-verified
read-only scan; its stateless native attachment reads at most 4096 admitted bytes
and returns the exact first-nonzero offset, including a zero-length span. A failed span admission takes the original
byte path, preserving refusal priority and the exact consumed prefix. Each successful
span is charged by its consumed byte count; it never turns 4096 bytes of hashing into
one budget unit. Device storage-domain binding belongs to the caller; the page header
has no such field.

Anchors use `fn2/anchor/v1`, their final 32 bytes zero while hashing. The checker
matches slot, history, incarnation and all geometry digest bytes.

Seals use `fn2/sealed-batch/v1` followed by LE64 encodings of expected history,
incarnation, extent, extent writer epoch and allocation counter, then the canonical
sealed-batch bytes with the final 32 bytes zeroed. The layout carries these five
identity fields, which must also match the expectations. The checker requires the
expected commit and previous commit and compares all 32 previous-seal bytes against
the expected predecessor. It covers record-stream commitments, dependencies and root
recipes. A valid seal establishes neither external dependency availability nor a
successful persistence fence; those remain composition obligations.

Refusals include `:wrong-history`, `:wrong-incarnation`, `:wrong-extent`,
`:wrong-allocation`, `:wrong-commit`, `:wrong-previous-commit` and
`:wrong-previous-seal`, alongside framing, hash, padding, page-parent and anchor
geometry errors. Layout and pool refusals propagate unchanged.

The three binding keystones remain owed, with executable positive and
hypothesis-removal witnesses through the actual pool-backed checker. Collision
freedom is stated directly for the two covered byte sequences. The seal statement
binds identity, expected predecessor and exact covered content; it makes no real-world
hash-security or disk-persistence claim.

The checker preservation proofs share typed prefix selection, a read-only ordered
byte check and a single span-size bounds theorem through the existing shape
proof template. This reduces repeated case splits without changing any theorem
formula, guard or teeth. The follow-up certificate takes 38.35 ACL2 seconds (previously
93.90), or 39.00 seconds including the launcher; the independent format declaration books take 2.11, 10.45, 35.08
and 24.07 seconds, and their public catalog 1.59 seconds. These are author-machine
certification wall times; event/persistence profiles and the complete scope are in
`build/REPORT.md`.

### Layout vocabulary

Magic bytes: bootstrap `46 32 47 44` (F2GD), structured pages `46 32 50 47` (F2PG), journal
frames `46 32 4a 52` (F2JR); version/schema-version 1. Initial sector/page geometry is
4096/65536. Digest tag 1 is BLAKE3-256 followed by 32 bytes. Namespace names carry no wire
bytes; all IDs and counts are canonical base-128 integers. Size maxima below describe the
codec’s inline u60 domain, not an extensible-integer namespace ceiling.

Page kinds, codes 0 through 14 in order: `:run-data :run-index :partitioned-filter :manifest
:allocation-map :source-manifest :range-proof :checkpoint-descriptor :merkle-node :raw-source
:key-list :recovery-arena :dependency-manifest :membership-list :obligation-list`.

Record kinds, codes 0 through 15 in order: `:article-acceptance :cursor-advance
:registration-change :configuration-change :withdrawal :obligation-create :obligation-release
:keyed-mutation :allocation :relocation :run-replacement :retirement :release-allocation
:checkpoint-installation :begin-writer-epoch :checkpoint-statement`.

All enum codes are zero-based list positions. Frame codes: records=0, seal=1, continuation=2.
Allocation states: FREE=0, RESERVED=1, ALLOCATED=2, RETIRE_PENDING=3. Unused allocation-map
fields must be zero: FREE has zero owner-kind/owner/allocation identity/retirement commit;
RESERVED and ALLOCATED have zero retirement commit; RETIRE_PENDING retains owner and allocation
identity. Enforcement belongs to allocation validation, not the layout codec.

Article acceptance, cursor advancement, registration/configuration changes, withdrawal, and
obligation create/release concatenate record-header, operation-header, and body. Keyed-mutation
concatenates record-header and body, which already contains principal/operation.
Checkpoint-statement concatenates record-header and body without operation-header. Maintenance
kinds (allocation through begin-writer-epoch) concatenate maintenance-header and body under
journal commit framing; they do not consume an event number. Checkpoint statements describe an
already determined predecessor cut, logged at k+1; neither descriptor nor statement includes the
enclosing event root or seal. Operation outcomes are inline canonical codes (seat review: an isolated ack must not cost a
Ref); charges, configurations, memberships, keys, manifests, arena and frontier sequences are
external pages referenced by Ref. Source-manifest subtree CV is
algorithm-tagged like other digests; its intended subtree spans 64 KiB.

Ref fields are defined once and prefixed when embedded. Frame headers include physical extent
identity as well as its allocation pair, binding the physical context required by §E.

| Layout | Fields | Inline bytes min–max | Fields in wire order |
|---|---:|---:|---|
| ref | 7 | 39–79 | storage-domain, physical-unit, writer-epoch, allocation, page-kind, encoded-length, expected-hash |
| bootstrap | 10 | 45–101 | magic, version, sector-size, page-size, anchor-0, anchor-1, anchor-2, anchor-3, storage-domain, geometry-hash |
| anchor | 15 | 175–247 | slot, history, incarnation, checkpoint, checkpoint-batch, descriptor-storage-domain, descriptor-physical-unit, descriptor-writer-epoch, descriptor-allocation, descriptor-page-kind, descriptor-encoded-length, descriptor-expected-hash, previous-checkpoint, geometry, anchor-hash |
| page-header | 10 | 13–69 | magic, version, page-kind, history, incarnation, physical-unit, writer-epoch, allocation, header-length, payload-length |
| raw-source-context | 8 | 8–72 | storage-domain, history, incarnation, physical-unit, writer-epoch, allocation, actual-length, logical-source-offset |
| frame-header | 12 | 15–95 | magic, frame-kind, history, incarnation, writer-epoch, commit, extent, extent-writer-epoch, extent-allocation, ordinal, fragment-offset, payload-length |
| frame-trailer | 1 | 33–33 | frame-hash |
| maintenance-header | 2 | 2–2 | record-kind, schema-version |
| record-header | 3 | 3–11 | record-kind, schema-version, event |
| operation-header | 2 | 2–18 | principal, operation |
| article-acceptance | 55 | 311–874 | article, message-id, source-identity, source-length, source-storage-domain, source-physical-unit, source-writer-epoch, source-allocation, source-page-kind, source-encoded-length, source-expected-hash, projection-storage-domain, projection-physical-unit, projection-writer-epoch, projection-allocation, projection-page-kind, projection-encoded-length, projection-expected-hash, memberships-storage-domain, memberships-physical-unit, memberships-writer-epoch, memberships-allocation, memberships-page-kind, memberships-encoded-length, memberships-expected-hash, membership-count, acceptance-storage-domain, acceptance-physical-unit, acceptance-writer-epoch, acceptance-allocation, acceptance-page-kind, acceptance-encoded-length, acceptance-expected-hash, configuration-storage-domain, configuration-physical-unit, configuration-writer-epoch, configuration-allocation, configuration-page-kind, configuration-encoded-length, configuration-expected-hash, charges-storage-domain, charges-physical-unit, charges-writer-epoch, charges-allocation, charges-page-kind, charges-encoded-length, charges-expected-hash, created-obligations-storage-domain, created-obligations-physical-unit, created-obligations-writer-epoch, created-obligations-allocation, created-obligations-page-kind, created-obligations-encoded-length, created-obligations-expected-hash, outcome |
| cursor-advance | 11 | 43–115 | registration, previous-event, next-event, selection-storage-domain, selection-physical-unit, selection-writer-epoch, selection-allocation, selection-page-kind, selection-encoded-length, selection-expected-hash, outcome |
| registration-change | 10 | 42–106 | registration, previous-version, contract-storage-domain, contract-physical-unit, contract-writer-epoch, contract-allocation, contract-page-kind, contract-encoded-length, contract-expected-hash, outcome |
| configuration-change | 10 | 42–106 | configuration, previous-generation, value-storage-domain, value-physical-unit, value-writer-epoch, value-allocation, value-page-kind, value-encoded-length, value-expected-hash, outcome |
| withdrawal | 9 | 41–97 | article, authorization-storage-domain, authorization-physical-unit, authorization-writer-epoch, authorization-allocation, authorization-page-kind, authorization-encoded-length, authorization-expected-hash, outcome |
| obligation-create | 17 | 81–185 | obligation, owner, article, terms-storage-domain, terms-physical-unit, terms-writer-epoch, terms-allocation, terms-page-kind, terms-encoded-length, terms-expected-hash, charges-storage-domain, charges-physical-unit, charges-writer-epoch, charges-allocation, charges-page-kind, charges-encoded-length, charges-expected-hash |
| obligation-release | 8 | 40–88 | obligation, release-evidence-storage-domain, release-evidence-physical-unit, release-evidence-writer-epoch, release-evidence-allocation, release-evidence-page-kind, release-evidence-encoded-length, release-evidence-expected-hash |
| keyed-mutation | 14 | 78–166 | table, object, principal, operation, binding, expected-prior-version, new-value-storage-domain, new-value-physical-unit, new-value-writer-epoch, new-value-allocation, new-value-page-kind, new-value-encoded-length, new-value-expected-hash, outcome |
| allocation | 5 | 5–37 | extent, owner-kind, owner, writer-epoch, allocation |
| relocation | 15 | 79–167 | object, old-storage-domain, old-physical-unit, old-writer-epoch, old-allocation, old-page-kind, old-encoded-length, old-expected-hash, new-storage-domain, new-physical-unit, new-writer-epoch, new-allocation, new-page-kind, new-encoded-length, new-expected-hash |
| run-replacement | 15 | 79–167 | schema, old-runs-storage-domain, old-runs-physical-unit, old-runs-writer-epoch, old-runs-allocation, old-runs-page-kind, old-runs-encoded-length, old-runs-expected-hash, new-runs-storage-domain, new-runs-physical-unit, new-runs-writer-epoch, new-runs-allocation, new-runs-page-kind, new-runs-encoded-length, new-runs-expected-hash |
| retirement | 4 | 4–36 | extent, writer-epoch, allocation, retirement-commit |
| release-allocation | 12 | 44–124 | extent, writer-epoch, allocation, retirement-commit, promoted-checkpoint, release-evidence-storage-domain, release-evidence-physical-unit, release-evidence-writer-epoch, release-evidence-allocation, release-evidence-page-kind, release-evidence-encoded-length, release-evidence-expected-hash |
| checkpoint-installation | 8 | 40–88 | checkpoint, descriptor-storage-domain, descriptor-physical-unit, descriptor-writer-epoch, descriptor-allocation, descriptor-page-kind, descriptor-encoded-length, descriptor-expected-hash |
| begin-writer-epoch | 4 | 4–36 | history, incarnation, previous-writer-epoch, writer-epoch |
| checkpoint-statement | 21 | 181–293 | history, incarnation, event-cut, event-root, fold-schema, summary-commitment, exact-identity-commitment, descriptor-storage-domain, descriptor-physical-unit, descriptor-writer-epoch, descriptor-allocation, descriptor-page-kind, descriptor-encoded-length, descriptor-expected-hash, authorized-keys-storage-domain, authorized-keys-physical-unit, authorized-keys-writer-epoch, authorized-keys-allocation, authorized-keys-page-kind, authorized-keys-encoded-length, authorized-keys-expected-hash |
| root-recipe | 37 | 197–413 | checkpoint-base-storage-domain, checkpoint-base-physical-unit, checkpoint-base-writer-epoch, checkpoint-base-allocation, checkpoint-base-page-kind, checkpoint-base-encoded-length, checkpoint-base-expected-hash, suffix-first, suffix-last, physical-manifest-storage-domain, physical-manifest-physical-unit, physical-manifest-writer-epoch, physical-manifest-allocation, physical-manifest-page-kind, physical-manifest-encoded-length, physical-manifest-expected-hash, allocation-changes-storage-domain, allocation-changes-physical-unit, allocation-changes-writer-epoch, allocation-changes-allocation, allocation-changes-page-kind, allocation-changes-encoded-length, allocation-changes-expected-hash, event-frontier-storage-domain, event-frontier-physical-unit, event-frontier-writer-epoch, event-frontier-allocation, event-frontier-page-kind, event-frontier-encoded-length, event-frontier-expected-hash, configuration-generations-storage-domain, configuration-generations-physical-unit, configuration-generations-writer-epoch, configuration-generations-allocation, configuration-generations-page-kind, configuration-generations-encoded-length, configuration-generations-expected-hash |
| sealed-batch | 78 | 494–942 | history, incarnation, extent, extent-writer-epoch, extent-allocation, commit, previous-commit, previous-seal, input-root, event-first, event-last, record-stream, dependencies-storage-domain, dependencies-physical-unit, dependencies-writer-epoch, dependencies-allocation, dependencies-page-kind, dependencies-encoded-length, dependencies-expected-hash, allocation-retirement-storage-domain, allocation-retirement-physical-unit, allocation-retirement-writer-epoch, allocation-retirement-allocation, allocation-retirement-page-kind, allocation-retirement-encoded-length, allocation-retirement-expected-hash, metadata-edits-storage-domain, metadata-edits-physical-unit, metadata-edits-writer-epoch, metadata-edits-allocation, metadata-edits-page-kind, metadata-edits-encoded-length, metadata-edits-expected-hash, output-checkpoint-base-storage-domain, output-checkpoint-base-physical-unit, output-checkpoint-base-writer-epoch, output-checkpoint-base-allocation, output-checkpoint-base-page-kind, output-checkpoint-base-encoded-length, output-checkpoint-base-expected-hash, output-suffix-first, output-suffix-last, output-physical-manifest-storage-domain, output-physical-manifest-physical-unit, output-physical-manifest-writer-epoch, output-physical-manifest-allocation, output-physical-manifest-page-kind, output-physical-manifest-encoded-length, output-physical-manifest-expected-hash, output-allocation-changes-storage-domain, output-allocation-changes-physical-unit, output-allocation-changes-writer-epoch, output-allocation-changes-allocation, output-allocation-changes-page-kind, output-allocation-changes-encoded-length, output-allocation-changes-expected-hash, output-event-frontier-storage-domain, output-event-frontier-physical-unit, output-event-frontier-writer-epoch, output-event-frontier-allocation, output-event-frontier-page-kind, output-event-frontier-encoded-length, output-event-frontier-expected-hash, output-configuration-generations-storage-domain, output-configuration-generations-physical-unit, output-configuration-generations-writer-epoch, output-configuration-generations-allocation, output-configuration-generations-page-kind, output-configuration-generations-encoded-length, output-configuration-generations-expected-hash, event-frontier-storage-domain, event-frontier-physical-unit, event-frontier-writer-epoch, event-frontier-allocation, event-frontier-page-kind, event-frontier-encoded-length, event-frontier-expected-hash, final-seal |
| dependency-entry | 9 | 73–121 | target-storage-domain, target-physical-unit, target-writer-epoch, target-allocation, target-page-kind, target-encoded-length, target-expected-hash, length, digest |
| source-manifest-header | 3 | 35–51 | source-length, block-size, source-identity |
| source-manifest-entry | 10 | 74–130 | logical-offset, length, block-storage-domain, block-physical-unit, block-writer-epoch, block-allocation, block-page-kind, block-encoded-length, block-expected-hash, subtree-cv |
| allocation-map-entry | 7 | 7–47 | extent, state, owner-kind, owner, writer-epoch, allocation, retirement-commit |
| checkpoint-descriptor | 38 | 198–422 | checkpoint, cut-commit, cut-event, metadata-manifest-storage-domain, metadata-manifest-physical-unit, metadata-manifest-writer-epoch, metadata-manifest-allocation, metadata-manifest-page-kind, metadata-manifest-encoded-length, metadata-manifest-expected-hash, allocation-state-storage-domain, allocation-state-physical-unit, allocation-state-writer-epoch, allocation-state-allocation, allocation-state-page-kind, allocation-state-encoded-length, allocation-state-expected-hash, event-proof-directory-storage-domain, event-proof-directory-physical-unit, event-proof-directory-writer-epoch, event-proof-directory-allocation, event-proof-directory-page-kind, event-proof-directory-encoded-length, event-proof-directory-expected-hash, event-frontier-storage-domain, event-frontier-physical-unit, event-frontier-writer-epoch, event-frontier-allocation, event-frontier-page-kind, event-frontier-encoded-length, event-frontier-expected-hash, recovery-arena-storage-domain, recovery-arena-physical-unit, recovery-arena-writer-epoch, recovery-arena-allocation, recovery-arena-page-kind, recovery-arena-encoded-length, recovery-arena-expected-hash |
| recovery-arena-entry | 3 | 3–27 | extent-physical-unit, writer-epoch, allocation |
| membership-entry | 3 | 3–27 | group, group-number, article |
| key-entry | 1 | 1–9 | key |
| configuration-generation-entry | 1 | 1–9 | configuration |

Allocation owner-kind is an opaque u8 machine/object category; owner is a typed `owner` ID
matching the allocator’s owner-kind/owner-id fields.

## 7. Allocator

`books/alloc.lisp` declares profile-sized extent and edge tables through `defcolumns`.
Extent state uses the generated `*fn2-extent-state-{free,reserved,allocated,retire-pending}*`
constants; pressure accounting uses the declared `fn2-alloc-reason-code` enum. Extents
carry opaque owner kind/id, writer-epoch/allocation-counter pair, retirement commit,
free/retirement links and ten cached u32 protection counts. `*fn2-alloc-none*` is the
link sentinel. All resident identities and cuts are u60.

`fn2-alloc-edges` has named columns `state`, `kind`, `holder`, `extent`, `epoch`,
`counter`. Each live row represents one holder's protection of one exact allocation.
Many holders may protect the same extent with the same kind. An edge handle is its
row index, and the holder is its operation reference. Reserve's internal reservation
is owned by the allocation's epoch/counter pair and can only be discharged by
commit or cancellation; it is not an externally droppable row.

The edge APIs are:

- `fn2-alloc-edges-init(edge-capacity, edges)` provisions the supported profile's rows.
- `fn2-alloc-edge-add(edge, holder, extent, epoch, counter, kind, extents, edges)`
  claims a free row and increments that kind's cached count.
- `fn2-alloc-edge-drop(edge, holder, extent, epoch, counter, kind, extents, edges)`
  requires the entire ownership tuple to match. A different holder returns
  `:edge-holder` with both stores unchanged.
- `fn2-alloc-relocate(edge, holder, source, epoch, counter, destination, new-epoch,
  new-counter, durable, extents, edges)` transfers exactly one named
  `:installed-root` or `:prepared-successor` edge after durable replacement.

The three mutating edge APIs return `(mv code extents edges)`. Each call does
constant work. Relocation's composing machine enumerates its owned handles and
yields between transfers; there is no whole-table scan or implicit bulk movement.
Other edge kinds are physical protections and return `:physical-edge` on relocation.
The holder survives relocation and can discharge the edge at the destination's new
allocation identity. Edge admission adds `:edge-bounds` and `:edge-live` refusals.

Installed-root protects current placement; selectable-checkpoint protects every
selectable checkpoint; recovery-base protects replay infrastructure;
prepared-successor protects an uninstalled successor; obligation protects durable
custody; promised-read protects a BODY/object lease; borrow protects an externally
held physical range; outstanding-io protects a submitted operation through completion
or backend exclusion; recovery-candidate quarantines unresolved candidates.
Identity references are not payload-retention edges. Identity-metadata storage is
protected through root/dependency edges. Physical reader, checkpoint, recovery,
obligation and I/O protections remain at their old locations through relocation.

Reserve requires a completed writer epoch, consumes a fresh allocation counter, and
creates its internal reservation. Commit installs ownership and discharges it.
Retire records a completed retirement commit. Release requires RETIRE-PENDING, no
protecting edges, and retirement at or below the installed checkpoint cut. Its
composing machine must establish RELEASE_ALLOCATION persistence before invoking
FREE. Cancellation calls the same `fn2-alloc-protector` with `:reservation` excepted;
there is one list of protecting kinds. Epoch advance and process death never erase
an old I/O edge. Counter exhaustion requests a new durable epoch and never wraps.

`fn2-alloc-adjust` is exact arithmetic with a guard requiring its result to fit u60.
`fn2-alloc-account` asserts those local guard facts before updating cached totals;
an impossible underflow/overflow raises a hard error. A live edge with a zero count
also raises a hard error instead of being absorbed. No served operation scans the
whole allocation state to validate its invariant.

Checkpoint advancement remains a resumable retirement FIFO: at most the supplied
budget (1..32) retirements are covered per call. A requested cut becomes installed
only when all preceding retirements are covered; `:more` requires the caller to
resume. Covered rows remain linked until release; unlinking is constant work.

`sim/check-reclaim.lisp` independently interprets exact owned-edge rows, reports
wrong-holder drops, and checks unsafe release, destructive write and repeated
allocation IDs. Its event/extent/edge tuples use named generated readers.
`fn2-alloc-ownership-invp` is a logical/test predicate connecting every live edge's
allocation identity and every cached count. Unit fixtures evaluate it with concurrent
holders and after relocation. The proved theorem
`fn2-alloc-edge-drop-requires-matching-holder` covers the actual drop export and has
positive and hypothesis-removal witnesses. General preservation of the ownership
invariant and the existing allocator durability/ID obligations remain unproved;
certification does not establish persistence or the composing machine's evidence.

## 8. BLAKE3

`books/digests.lisp` declares the eight u32 digest columns, IV and empty-root
constants, and named workspace regions. A profile allocates `136*n` workspace rows
plus caller-owned keys, outputs and proof nodes for `n` continuations. Within each
stripe, BLAKE3 owns its CV, key, 54 frontier rows, scratch and result; Merkle owns
60 frontier rows and proof/frozen-argument rows; the format checker owns its result
and expectation rows. Capacity is supplied at initialization. These are continuation
resources, not a bound on stored objects. The only remaining BLAKE3 word buffer is
16 u32 message words per hasher row. Guards check physical indexes and word widths;
there are no out-of-range writes discarded or word reads replaced by zero.

- Initialize `fn2-digests-init(capacity, digests)` and `fn2-b3-table-init(n, b3)`.
  `fn2-b3-init(row, mode, key-row, digests, b3)` returns `(mv digests b3)`.
  Modes 0/16/32/64 retain hash/keyed/context/material semantics; context/material
  derivation passes its key as a digest-row index.
- `fn2-b3-update(row, slot, gen, off, len, okind, oslot, ogen, digests, b3, pool)`
  returns `(mv code consumed digests b3)` and consumes at most 4096 bytes. Pool
  refusal retains the exact successfully consumed prefix. `update-const` takes
  `(row, string, off, len, digests, b3)` with `len <= 4096` and the same returns.
- `fn2-b3-finalize(dst, row, digests, b3)` and `fn2-b3-subtree-cv` write digest row
  `dst`, returning `digests`. Finalization preserves the resumable hasher state;
  its destination must be outside that row's live CV/key/frontier region.
  `fn2-b3-start-subtree(row, counter, b3)` still sets an empty row's absolute
  counter aligned to a 64-chunk payload block.
- `fn2-b3-parent-cv(dst, left, right, key, flags, digests)` and `parent-root`
  take four row indexes and write one digest row. Aliased input/output rows work:
  compression reads its inputs before writing any result column.
- `fn2-b3-verify-range(row, base, source-len, block, block-len, expected-row,
  digests, b3)` returns `(mv code digests b3)`. First hash the candidate at
  `64*block`. Proof CVs occupy consecutive digest rows starting at `base`, outside
  continuation workspace. Each call consumes at most one CV. Keep arguments,
  expected digest and proof rows immutable across `:more`.

The replaceable subtree boundary is
`fn2-b3-subtree-cv-into(dst, absolute-pool-offset, len, counter, digests, pool)`.
It is guard-verified and defined by ACL2 compression over the pool array. Length is
1024 times a power of two, at most 65536; the counter is absolute and the span must
fit the pool's byte storage. Admission remains in ACL2: the caller validates handle,
generation, owner and readability before passing the absolute offset. The primitive
does not decide ownership or content identity.

The incremental bulk path passes complete 1 KiB chunks through this boundary.
A second entry, `fn2-b3-chunk-output-into(row, off, counter, digests, b3, pool)`,
retains the rightmost chunk's CV before its final block and its 64 buffered bytes.
A non-root CV alone cannot support a later ROOT decision or continued updates.
`fn2-b3-fragment-into(row, absolute-offset, length, digests, b3, pool)` handles
an admitted partial chunk through the same ACL2 byte semantics in one stateless
call. Its native domain stays within the current 1 KiB chunk in hash mode; it
preserves every digest and hasher column, including dirty unused message words and
the last compression's scratch digest. Nonadmitted spans retain byte admission.
`fn2-b3-output` and the two parent entries are also attached, covering remaining
tails and format prefixes; the
65-byte RFC Merkle node has its own attached `fn2-mk-node` entry. No C hasher state
survives a call. The declared quantum stays 4096 bytes, including bulk input.
Page and frame hashing yield at chunk boundaries when possible; partial chunks
use the fragment boundary. Short domain prefixes, tag checks and zeroed digest
bytes retain byte transitions. Charging uses actual
consumed bytes, and an unreadable bulk span falls back to byte admission so that
the refusal status, position and hashed prefix remain exact.

`host/b3-native.lisp` is raw SBCL code loaded after the certified books, never by a
book. Build `build/lib/libfn-blake3` with `sh fn2/host/build-blake3.sh build/lib`.
The lifted C adapter exports the quarry's formerly static subtree function and
small compression/Output/node/fragment wrappers over vendored BLAKE3 1.8.7, plus
the bounded zero-prefix scan. Pool storage
must be a specialized `(simple-array (unsigned-byte 8) (*))`, checked at attach time;
input is pinned and read in place. Fixed stack arrays marshal only message/digest
words. Every replacement is reached through its submitted function symbol.

Before installation, start-up compares all 35 official hash vectors, subtree
lengths 1..64 chunks at six counters, partial and full chunk Outputs, parents and
Merkle nodes with distinct children against saved ACL2 definitions. It also checks
ten partial-chunk states with all-column effect comparisons, and zero-prefix scans
at byte/word/4096-byte edges with first, middle, last and absent nonzero bytes.
Missing libraries/symbols, wrong version,
wrong pool specialization or any disagreement signal `fn2-b3-native-refused`, with
reference definitions retained. SBCL save hooks restore reference functions; image
init hooks run `fn2-b3-native-startup` again in each new process. Explicit reset also
restores the reference functions. Fast domains are guarded hash-mode inputs;
keyed/derive modes and arguments outside the native domain call the saved reference.
The named correspondence assumption is `fn2-a-crypto-native` in
`assumptions-integrity.lisp`, distinct from accidental-fault collision assumptions.
`fn2-a-native-span` in `assumptions-native-span.lisp` names correspondence of the
noncryptographic padding scan and its unchanged-pool effect.

Range checking retains byte count, counter, position, partial-final-chunk and ROOT
checks. For sources up to 64 KiB it finalizes the complete source, including empty
input. Source length must come from an authenticated descriptor; an opaque sibling
CV cannot authenticate its byte length. The current verifier folds every source
block CV: candidate hashing plus `ceil(source-len/65536)-1` parent compressions and
one digest row per block. Logarithmic sibling paths remain future work. The two
ACL2 equivalence keystones remain owed; native attachment does not discharge them.

Matched-session BH1 measurements (wall time; CPU times, before/after comparisons,
profiles and verbatim acceptance in `build/REPORT.md`). No other BH1 job ran during
the final measured session.

Apple M2 Max, arm64 (`uname -m`), SBCL 2.6.8. Profile: one BLAKE3 and one
checker continuation; 160/144 digest rows; 80 decoded fields; 300000/65536-byte
pools; 4096-byte quantum; 65536-byte blocks; range source 196608 bytes / three CV
rows. Each operation allocated **0 bytes** after warmup, in both modes.

| Operation | ACL2 MiB/s | C-attached MiB/s | ACL2 µs/op | C-attached µs/op |
|---|---:|---:|---:|---:|
| Incremental, 64 KiB | 56.700 | 261.097 | 1102.293 | 239.375 |
| Page seal, 64 KiB | 33.312 | 351.424 | 1876.215 | 177.848 |
| Page seal + check, 64 KiB | 15.765 | 132.628 | 3964.535 | 471.242 |
| Range: 64 KiB block in 192 KiB source | 69.468 | 301.511 | 899.691 | 207.289 |
| Merkle node, 65 bytes | 40.593 | 163.129 | 1.527 | 0.380 |
| Subtree primitive, 4 KiB | 81.065 | 1227.370 | 48.187 | 3.183 |
| Frame seal + check, 4 KiB | 6.926 | 33.631 | 564.025 | 116.149 |

A 4096-byte native subtree primitive takes 3.183 µs. Incremental hashing
amortizes 239.375 µs over sixteen windows, or 14.961 µs/window. The
11.778 µs difference includes admission, separate 1 KiB calls, frontier/Output
maintenance, call/return and finalization; it is not a measurement of A's scheduler.
At 1 GiB/s the 4096-byte cap requires 262144 resumptions/yields per second. This is
the finding for A; neither its files nor the declared cap changed. The complete
checker remains below the device-speed target. The page fixture has a 32-byte
header area, three payload bytes and zero padding; range timing includes candidate
hashing and verification in a three-block source. Seal+check counts each unit once.

Before the follow-up, C-attached frame seal+check was 2.329 MiB/s (1676.988 µs)
and page seal+check 23.703 MiB/s (2636.797 µs). Frame checked pool reads fell from
8254 to 150 per cycle; page reads from 1037 to 33 per check. Padding scans and
partial-chunk byte admission were the dominant local costs. The remaining page
profile spends 56.9% of CPU samples in C's portable single-chunk compression;
checked pool reads are no longer the bottleneck. Short prefix/tag/digest and header
transitions remain; complete checker throughput is still below device speed.

Acceptance: 105/105 official vectors, 2000 original differential cases, 10000/10000
random subtree cases, 10000/10000 zero-prefix cases (pool unchanged), 10000/10000
partial-fragment cases (all digest/hasher columns equal), unchanged range counts
(306 accepted; 305 flip, 306 counter, 83 moved and 109 truncated refusals), and
66 bulk/byte exact-prefix agreements across frame/page/anchor/seal and budgets
1,7,4096. Missing-library and corrupted subtree/zero-prefix/fragment startup checks
refuse attachment and retain every reference definition. Standalone ACL2-only
BLAKE3, format and Merkle controls pass with unchanged driver counts: format retains
224580 XOR1 mutants, 21 misplacements and 10206 budget agreements; Merkle retains
2000 roots and 40000 each inclusion/tampered/shifted/resized-height checks.
The earlier oracle measured 6.774 MiB/s incremental and 6.821 MiB/s list BLAKE3;
BR1's frame seal+check measured 2.712 checked MiB/s. Pool-backed aligned hashing,
digest rows and bulk checking account for the different oracle speeds above.

## 9. Event log

`books/merkle.lisp` implements the RFC 6962 append-only binary-tree shape with
BLAKE3-256 as the declared fn2 hash profile. Leaves are `H(0x00 || canonical semantic
record bytes)`; internal nodes are `H(0x01 || left || right)`; the empty root is
`H(empty)`. There is no additional leaf domain string. This retains the standard
prefix rules while selecting BLAKE3 explicitly; SHA-256 interoperability is later work.
Physical pool location is not hashed into a leaf. Callers supply canonical semantic
encodings; this primitive does not validate their semantic schema.

`fn2-mk-table-init(n, log)` allocates a profile-sized `defcolumns` table. Each row
carries u60 size and proof continuation columns. Its 60 frontier digests and proof
workspace occupy the named digest-table regions described in §8. `fn2-mk-init(row, log)` resets the frontier and proof continuation.
`fn2-mk-append(row, digest-row, digests, log)` returns `(mv code digests log)` and performs one full node hash
per binary carry, at most 60. `fn2-mk-root(dst, row, digests, log)` writes the destination digest row, folding
occupied levels small to large with each larger subtree on the left. Append refuses
`:exhausted` at the resident u60 limit rather than wrapping. The 65-byte node hash uses
two reference compressions with CHUNK_START and CHUNK_END|ROOT, or its checked native
attachment; it is a complete
BLAKE3 hash, not BLAKE3's internal parent-CV operation.

`fn2-mk-leaf-start(b3row, digests, b3)` initializes the hasher and feeds the leaf prefix (the caller owns the pairing of hasher row and log row; seat review removed a reuse of the BLAKE3 row's verify-target column for it).
`fn2-mk-leaf(slot, gen, off, len, okind, oslot, ogen, b3row, digests, b3, pool)` returns
`(mv code digests b3)`, consuming at most 4096 record bytes per call. Repeat identical arguments
and unchanged input bytes on `:more`; after `:ok`, `fn2-b3-finalize(dst, b3row, digests, b3)` writes
the leaf digest row. The active leaf owns that BLAKE3 row.

Proof verification follows [RFC 9162 §§2.1.3.2 and 2.1.4.2](https://www.rfc-editor.org/rfc/rfc9162.html#section-2.1.3.2).
The APIs are `fn2-mk-verify-inclusion(row, index, size, leaf-row, base, count, root-row,
digests, log)` and `fn2-mk-verify-consistency(row, old, new, base, count, old-root-row,
new-root-row, digests, log)`, returning `(mv code digests log)`. Proof nodes occupy
consecutive digest rows from `base`, outside continuation workspace. One call consumes at most one sibling and two
node hashes. Fixed arguments are checked on resume; proof rows stay immutable.
`:more` retains continuation, and `fn2-mk-proof-reset(row, log)` cancels it without
changing the frontier. `:state` preserves the active continuation; ordinary completion
and proof refusal clear it. Refusals include `:index`, `:size`, `:proof-length`,
`:root-mismatch` and `:state`; leaf input also passes pool refusals through.
Empty-old consistency extends the RFC algorithm and requires the canonical empty root;
same-size consistency requires equal roots and no proof nodes.

Authenticate `(size, root)` together. An RFC inclusion path does not bind every possible
change of size: the three-leaf index-0 proof also verifies as size 4 under the same root
because its final sibling is opaque. Tests retain that counterexample and separately
check size changes that must alter the path.

The driver compares 2000 random prefix sizes up to 5000 leaves against an independent
list oracle, checks 40000 inclusion proofs and 2000 consistency proofs and their tested
corruptions, and exercises 40-node continuations. All passed; 100000 appends allocated
zero bytes after initialization. All public runtime exports are guard-verified.

Merkle authentication establishes neither correct application folding, authorization,
freshness, availability nor query completeness. Runtime-to-MTH and content-level
consistency soundness remain owed. The latter names `fn2-a-integrity-evidence` for
equal hashes of unequal opening encodings from both trees and every actual verifier
node input. It is not a concrete hash-security claim. Persistent frontier/proof paging
and recovery composition remain later work.

## 10. Commit batch

B3 is not yet a composed machine. The R4 declaration seam admits a new kind,
its scalar columns, dispatch and core accessors, but not the existing persistent
B2/B4 workspaces needed by its continuations. `fn2-format-seal-frame` and
`fn2-format-seal-batch` require `fn2-fc`, `fn2-b3` and `fn2-fields` alongside
the pool; `fn2-alloc-reserve` requires `fn2-extents`. None is a child of
`fn2-core`. Recreating them with `with-local-stobj` at each yield would discard
hashing/allocation state and allocate on the served path. Implementing copies
inside the commit columns would duplicate the existing B2/B4 implementations.

**B-MACHINE-SEAM, prerequisite.** A must expose persistent auxiliary-table
registration, initialization and reference copy/comparison before B can compose
these APIs through `(id budget fn2-core)`. Core child registration alone is
insufficient: `reference-state.lisp` enumerates the fixed tables and machine
kinds separately when generating congruent copy/difference functions. The
observation router must dispatch the B observer's `(mv wake fn2-core)` after
kind/generation validation and before A's generic pending decrement; its
current single-value `cond` arm and `ignore reason` declaration do not match
that interface. No A seam has been changed by B3.

The intended transition conditions remain those of ROUND2 §E.2:

| Phase | Completion required before leaving |
|---|---|
| collect | Ready members and their reserved resources captured; unfinished uploads excluded |
| seal | Immutable membership, dependency manifest, B2 seal and complete successor root prepared within resumable budgets |
| dependencies | Every expected dependency write completed with its exact issued length |
| log-write | Every batch frame write completed with its exact issued length |
| fence | Successful covering barrier, or preflush completion followed by successful final FUA sealing write |
| durable | Exact dependency-set durability evidence retained |
| install / publish | Prepared root handle installed and published in bounded transitions, without passing an unresolved predecessor |
| notify | Incremental outcomes; one client's success does not wait for other replies |
| draining | Notification and borrow obligations transferred or discharged |
| uncertain | Recovery alone resolves the row; a late generic success does not leave this state |

Two slots prepare successive roots `RA = Apply(R0,A)` and `RB = Apply(RA,B)`.
The follower cannot decide against `R0`. A fence-in-flight flag must remain
set through timeout until the outstanding fence completion is harvested;
checking only whether the partner's phase equals `fence` would incorrectly
allow a second fence after the partner enters `uncertain`. Uncertainty fences
new mutation across the storage domain. The simulator control must count
actual outstanding fences and reject a count above one, independent of the
adapter's fence-slot backpressure.

Baseline mode completes dependency and log writes before submitting Fence.
A separate Fence followed by the final FUA write can expose the preflush/FUA
sequence using A's existing actions; FUA alone persists only its own bytes.
Death between these stages remains a crash cut. Neither mode is implemented
by B3 yet. Scheduling is also unconnected: protected service 0 would require
matching semantics in the independent reference service runner; principal-0
scheduling is the currently authorized fallback that already shares machine
dispatch on both sides. The choice will be recorded when the machine is wired.

### HISTORY translation boundary

The independent checker API is `fn2-history-translate(events)` returning
`(mv code log-trace)`, and `fn2-check-history(events, profile, classification,
recovered-history)` calling B1's exact `fn2-lm-recovery-allowedp` interface.
Its input contract requires test/checker data projected from real issue, harvest,
publication, reply, fault and crash boundaries; it is not executable machine state.
Baseline event records name the batch's exact dependency/log manifest, each
issued op token and length, terminal results, fence issue/result, timeout,
publication, acknowledgement, refusal and crash. Successful exact write-set
completion yields `:batch-writes-complete`; actual successful fence completion
yields `:fence-ok`; acknowledgement yields `:acknowledge`. Physical recovery
evidence has a separate allowlist and cannot inject a synthetic fence or ack.
Member/refusal records are opaque identities compared by exact equality; the
producer must use stable operation identities, not arbitrary request bodies.
This translator does not establish semantic request binding or IDENTITY.
It currently requires globally distinct write identities rather than shared
dependencies, and uses B1's deferred guard-verification convention.

The simulator projection and recovery stand-in are outstanding. The stand-in
must read the simulator's durable image through B2d frame/seal checkers and
validate the required dependency prefix. A supplied expected history or a
machine's completed counter cannot substitute for that readback. Checker unit
fixtures alone establish neither scenario 13/14 nor HISTORY on simulator runs.
