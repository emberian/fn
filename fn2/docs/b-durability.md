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
| recovery | `fn2/books/recovery.lisp` (table level), `recovery-machine.lisp` (continuations), the `fn2-recovery-machine` declaration in `machines-b.lisp`; keystones `recovery-proof.lisp` | B5 |
| checkpoint and cleaner machines | `fn2/books/checkpoint.lisp`, `fn2/books/cleaner.lisp` (**owed**) | B6 |
| HISTORY, RECOVERY, RECLAIM checkers | `fn2/sim/check-history.lisp`, `check-recovery.lisp`, `check-reclaim.lisp` | B3-B6 |
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
`*NAME-FIELD-<field>*` indexes and `*NAME-PHASE-FIELD-<field>*` / `*NAME-PHASE-DONE*`
continuation constants. The enum machinery owns these phase constants and
`*NAME-PHASE-COUNT*`; field tags use `:FIELD-<field>` so a field named `count`
cannot collide with the cardinality. Enum fields also emit their declared enum's named constants.
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
| record-header | 11 | 11–83 | record-kind, schema-version, event, revision, occurrence, lineage, domain, incarnation, author, payer, grant (the event envelope; event = position) |
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

`machines-b.lisp` declares `fn2-commit` with two rows, the 4096-byte / 32-step /
4-descriptor run budget and `:observes` handlers for write and fence results.
`commit.lisp` supplies `fn2-commit-events`; its continuations and observer are
`defmachine-callback` functions over A’s scalar row snapshot. `defmachine-run`
generates dispatch. Initial generation is a named initializer; declarations
contain function names rather than executable forms. DM0b arms use ordinary
`if`/`cond`, `let`/`let*` and `mv-let`; no early-exit `b*` binders or positional
callback forwarding remain. A refreshes `row-` reads after each `fn2-core`
rebinding. Explicit locals such as the seal stage and issued count capture the
pre-transition value where the protocol needs it. All eleven callbacks are
checked against the registered calling conventions in `commit-resource-unit`;
an injected unsupported binder is refused. B currently has no callback-to-callback
calls; any such call uses A's `fn2-call` form.
`commit-format.lisp` packs
using the B2 generated layout encoders. The test transaction is a keyed mutation: a
consecutive range of distinct object/operation/event keys names one immutable
manifest node. Its generated 73-byte layout binds the predecessor seal and
batch, first key, member count, extent, writer epoch and allocation counter.
The keyed value is this immutable structured node. Admission requires a fresh
monotonically increasing key range; the frontier survives row reuse. The fixture's
ready-transaction contract also requires fresh operation IDs after a terminal
refusal. Capacity/profile backpressure may be retried. B3 has no persistent
refused-operation/idempotency ledger. Enforcing that input contract at layer C
is an outstanding integration requirement, not an implemented seam.

**B-MACHINE-SEAM.** The A edits are `(include-book "machines-b")` before
registry consumption in `assembly-index.lisp`, and `(fn2-commit-events)` in
`assembly-callbacks.lisp` before `fn2-resolve :callbacks`. Layer A's own
continuations (`fn2-scribe-events`, `fn2-machine-a-events`) moved into the
section book `assembly-callbacks-a.lisp`, which `assembly-callbacks` includes.
With both in one book the section exceeded the one-minute rule (86.7 s at laptop
load average 160); split, the sections measured 38.4 s and 51.6 s at load 108. DM0b seals machine
and child inputs through `fn2-input-seals`; evidence remains open until the
production `owed-export.lsp` includes all B unit roots and resolves/seals
`:coverage`. Callback/staging fixture units certify separately from that export.
The remaining assembly sections
are A-owned. B registers allocator extents and holder edges, checker/context,
BLAKE3, digest rows, layout fields, resource rows and root descriptors through
`defcorechild`.
The reference model includes these children automatically. The streaming codec's
saved reference cursor is named `fn2-fields-resume-ref`; this avoids a collision
with A's generated congruent `fn2-fields-ref` stobj. Profile readers
with defaults live in B: 16 extent rows, 38 edge rows, two checker/hash rows,
256 layout-field rows, 289 digest rows, baseline barrier mode. Digest capacity
defaults to `136 * format-slots + extent-slots + 1`; an explicit `:digest-slots`
must cover that minimum. A's original profiles remain valid. Scheduling uses principal 0; A still owns protected service 0.

The kind has 24 declared fields plus A's eight common/phase fields, exactly the
32 scalar values allowed by ACL2's snapshot return convention. The packing
cursor becomes the seal offset after record packing finishes; the old saved
record offset was unused. Named checked-update helpers retain `put-core`'s
commit-kind and atomic width validation while exporting shape contracts. This
keeps the observer proof from repeatedly expanding nested update branches.
The exported proof boundary names the **complete** assembled invariant as
`fn2-commit-core-invariant`. Its exact projection, variable-input rewrite,
constructed-output bridge and forward type bridge are a temporary implementation
of A's DSL-METATHEORY §4 projection kit, not a weaker invariant. Child type,
WFP and update facts are generated from the registry's B-layer children plus
pool/scheduler/control; their type/WFP forwarding is disabled after B's proofs.
B globally disables `fn2-layoutp-head`: a current-base full echo certification
with this setting local took 65.841 s. Outbox opacity is local. B's redundant
`fn2-core-wfp` disable is removed; A already disables it in assembly-access.
All thirty child row/reader disables are local: the enabled-reader core-init
probe completed in 49.149 s including loading. The eighteen redundant child
P/WFP disables were removed from the declaration book. The remaining global
cross-book layout rule disable is `fn2-layoutp-head`; B also exports the exact invariant
interface above and disables its own generated type/WFP forwarding after its
guard proofs. Full ablation scopes and times are in `build/REPORT.md`.

### Row validity (R5e2)

A's R5e2 made every machine field reader require its read code `:ok` in the
guard. `fn2-commit-idp` is the kind's generated snapshot read code, and one
lemma per declared commit column (generated from the declaration) states that it
implies the field's read code is `:ok`. Each internal helper that takes a row id
checks `fn2-commit-idp` at entry and otherwise stops the core with
`*fn2-stop-reason-machine-phase*`, which is A's own R5e2 pattern. The external
`fn2-commit-start` refuses with `:admission` when either id is not a commit row.
Every continuation first reads `fn2-commit-partner-state`: `:invalid` stops the
core, `:failed` stops the follower, and otherwise the partner row is known valid.
Two continuations were restructured so that no row field is read after a core
rebinding: seal's cursor reset moved into `fn2-commit-seal-advance`, and the
observer reads `cb-bytes` and `cb-failed` up front. No intervening write changes
either field. Each post-rebinding read made DM0b insert a fresh checked snapshot,
which cost the observer 62 s; it now takes 4.5 s. `fn2-commit-now` reads the
scalar `fn2-control-now`. A's `fn2-exec-now` is defined after assembly, so a
continuation cannot call it (seam note to A). B's byte-copy loop is
`fn2-commit-copy-bytes`, and the outcome writer is `fn2-commit-note-outcome`,
because `fn2-commit-copy` and `fn2-commit-record-outcome` are now generated
names. Step charges 16 and 32 have no name in A's `fn2-work` family; B still
passes bare charges (owed remedy B-CHARGES).

### Phases and resources

| Phase | Work and condition for advancing |
|---|---|
| collect | Attach the prepared-successor edge to the extent reserved at admission |
| seal | Resume fills, generated codecs and BLAKE3/checker work; construct the immutable successor descriptor before any I/O |
| dependencies | Issue the dependency page; require an exact successful harvested 4096-byte result |
| log-write | Issue records and seal frames, allowing both in flight; require both exact successful harvested results |
| fence | Baseline: successful covering fence after all writes. Alternate: successful dependency preflush before FUA log writes |
| durable | Require retained dependency, log and barrier evidence; commit the allocation |
| install | Swap the prepared root handle, only after its predecessor is published |
| publish | One bounded publication transition |
| notify | Expose one member acknowledgement per run |
| draining | After all pending operations and the fence leave, release one workspace per run; return the slot to free |
| uncertain | Persistent failure state, including fence timeout; only recovery may replace it |

Admission reserves all four workspaces, then an extent, before assigning a batch
number or publishing a proposed root. A failed reservation unwinds its workspaces
and consumes no sequence number. The test kind admits 1–16 members per batch.
An extent spans three 4 KiB units: dependency page, records frame, seal frame. The two journal
frames have 3900-byte payload areas; unused payload bytes are zero and the
stand-in parser checks them. The seal binds the actual record-frame digest,
dependency digest/allocation, predecessor seal and output root recipe. The input
root is the predecessor seal; the genesis checkpoint plus suffix 1..batch retains
all preceding mutations. The node supplies the physical manifest, metadata,
allocation-change and event-frontier references. Configuration and checkpoint
references remain genesis values because this fixture changes neither. These
references describe this test kind's suffix-derived state; the node does not
implement a production event-Merkle frontier. Checker
contexts and layout ranges are disjoint between batch rows. No runtime byte
lists or per-run allocation of local checker stobjs are used.

The follower's successor names the leader's proposed root. It waits for the
leader's final seal before encoding its predecessor link, but need not wait
for the leader's fence to prepare or write. Root descriptors retain predecessor,
extent and member range; each batch’s seal occupies digest row
`136 * format-slots + batch`. The preceding row is the immutable predecessor,
with batch zero reserved for genesis. Stage 17 copies the inner-seal result into
that directory before stage 18 hashes the outer frame. `install` changes a handle.
The directory lies beyond every checker/hash workspace stripe, so a successor
can link after its predecessor drains without retaining eight hash limbs in its
root descriptor.

A directory row is indexed by batch number and capacity is extent capacity plus
one. Each admitted batch consumes one unreclaimed extent, so this capacity is
resource-derived. Installation adds the installed-root edge before dropping the
prepared-successor edge; ancestors remain protected by their root edges. B6 must
provide directory reclamation when it introduces extent reuse. A drained machine
row can be admitted again with a fresh generation; generation exhaustion refuses
admission. Uncertain rows cannot rearm. The begun allocator writer epoch is the
incarnation of the batch sequence.

Completion routing is generated by A. B additionally checks the expected phase
and event class, exact write length, and completed count below issued count.
It accumulates completed counts/bytes and a sticky failure outcome/reason.
Wrong-class or excess results enter uncertainty. A successful late fence clears
only its in-flight flag; it cannot leave uncertainty or publish an outcome.

Each resource row records the issuing operation slot and generation. Its B4
`:outstanding-io` edge has a distinct edge row and the op generation as holder.
Because A's callback omits operation identity, log edges are conservatively
retained until all issued results of their class are harvested; no edge is
assigned to an arbitrary completion. Exact per-operation immediate release
would require A to expose the harvested token. Pool loans remain A-owned until
harvest.

### Barrier contract

A fence-in-flight flag is set on successful issue and cleared only by its
matched harvested completion, including after timeout. The fence continuation
checks both batch rows before issuing. The simulator independently counts
queued, submitted and posted-but-unharvested fence operations and rejects a
count above one; a deliberate double-issue control tests that counter. A fence
issue installs a deadline 1024 monotonic ticks after the core's current clock.
While waiting, the row remains runnable and checks clock observations harvested
through A's mailbox. Expiry enters uncertainty without clearing the flag; the
late success scenario uses that actual clock/dispatch path. A deadline that
cannot fit the declared width enters uncertainty before issuing, without wrap.

Baseline mode writes the dependency and both frames, harvests every exact
result, then issues Fence. `:commit-barrier-mode 1` selects the stronger
preflush/FUA contract: complete the dependency, harvest a successful preflush,
then issue **both** journal frames with FUA. Their exact successful completions
constitute the composed persistence boundary. This does not assume that an
ordinary earlier write is covered by a later FUA write. An unresolved predecessor
fences the follower.

### HISTORY

`fn2-history-translate` consumes projected manifest, issue, completion,
publication, acknowledgement, timeout and crash events. Successful admission
requests retain their key ranges independently of mutable machine rows; actual
busy-row `:admission` results are projected as terminal refusals with their
requested identities. Profile/capacity
backpressure is not projected as a terminal client reply. Operations carry their
actual slot/generation tokens; FUA bits come from descriptors. Reply counts
are bounded by immutable admitted membership; an extra reply or same-batch
counter regression is a named projection error. The scenario
runner snapshots the outbox before adapter admission and the posted FIFO before
`fn2-exec-harvest`, then executes the real scheduler continuation and router.
For baseline, exact dependency/log completion emits B1's
`:batch-writes-complete`, and successful FenceResult emits `:fence-ok`. For the
alternate mode, dependency preflush followed by all exact FUA log completions
emits that same abstract persistence boundary. Neither uncertainty nor an
acknowledgement is inferred from readable cached bytes. Full HISTORY assumes
that a terminal-refused operation identity is never reused. A retained real
busy-refusal/retry counterexample violates refusal consistency even though all
three acknowledged batches recover. This is separate from physical durability;
the durability obligation checks writes, completions, barriers and recovery
without adding that freshness premise.

Recovery after each death is B5's machine (§11); `fn2/sim/commit-history.lisp`
keeps only the projection and `fn2-b-recover-images`, the harness's independent
reader of what each submitted batch meant to write (the RECOVERY checker's ground
truth, never a recovery). The B3 stand-in `fn2-b-recover` is deleted.

Scenarios 13/14 enumerate every microstep death cut of their tiny-profile
pilot schedules: one schedule per barrier mode for 13, and five fault classes
per mode for 14, with dependency and journal targets for write failures.
This exhausts those schedules' cuts, not every interleaving.
Concrete 13 samples one cut per seeded schedule; concrete 14 completes each
seeded fault schedule and then crashes. B's tiny profile adds eight 4 KiB buffers. The two-batch sweeps supply eight
simulated 4 KiB units; reuse controls use the fixture's sixteen-unit default.
Extent capacity follows this geometry. Explicit resource-exhaustion controls
override the relevant capacity.
The transient write-EIO injection uses A's terminal-result adapter because A's
existing write fault kills the device permanently. The driver prints measured
bytes per acknowledgement and encoded record payload per journal byte, and
requires every named fault class and the fence-count control to be exercised.

### Resource threads and notification debt (B3c)

R7 `:holds` is absent on this base. `*fn2-commit-holds*` beside `defmachine`
is the phase-entry potential; the registry checks its state coverage.
`*fn2-commit-transitions*` names the graph. Phase alone is insufficient: operation
lifecycle, drain cursor and retained failure state refine the potential.

| Phase entries | Batch / pool | Allocation and edges |
|---|---|---|
| free | 0 / 0 | Previously installed ownership remains with roots |
| collect | 1 / 4 | One extent and root/member-record reservation |
| seal, dependencies, log-write, fence, durable, install | 1 / 4 | Same reservation plus prepared-successor edge |
| publish, notify | 1 / 4 | Installed-root edge replaces prepared edge; extent stays allocated |
| draining | 1 / `4 - cb-stage` | Root ownership is retained while workspaces leave |
| uncertain | Retained actual inventory | No new acquisitions; completion can discharge IO; recovery owns resolution |

Each write adds an op, queued action credit and an operation-owned IO edge.
Adapter take releases the queued credit; harvest releases the op. Both log ops
can overlap, and their allocator edges can remain until the completed class is
harvested. A commit gate G (capacity 1, between partners) spans fence issue to
harvest. Physical F (profile `:fence-slots`) is acquired by adapter take **before**
outbox release and released by physical completion, independently of outbox or
op availability. The scribe uses F, not G. A scribe fence can therefore cause
head-of-line blocking of a queued commit fence; it does not prevent the active
fence's completion. The scenario's max-fences control counts all outstanding
commit fences; it is not a claim that the scribe shares the commit-only gate.

`commit-resources.lisp` generates P/V words from differences of refined
potentials. A word acquires batch/pool/extent/root reservations, prepares,
performs dependency, overlapping log and barrier lifecycles in the selected
mode, installs, publishes, notifies and drains. Acquisition precedes release
when a transition does both. The installed extent, root descriptor and edge
remain explicit terminal holdings: **no fictitious retirement V** is inserted.
The scribe likewise retains its workspace. Capacity is batch=2, pool=the chosen
4 KiB class, O=`:o`, Q=`:qa`, IO=6, prepared=2, G=1, F=`:fence-slots`;
extent/root/installed capacities subtract `:commit-existing-roots` (default 0).
Root reservations include this test kind's bounded member records and
notification source. Private layout/hash arrays have no competing acquire.

There are two commit words, one scribe iteration, `:c + :accept-credits`
outbox-only A projections, and `:c` abstract recipients. Recipient send capacity
is B's `:recipient-send-slots` (default one) per recipient. This deliberately
models the requested A outbox projection, not full echo buffer ownership.
Admission must have reserved the two batches' buffers first; failed admission
unwinds rather than becoming a blocking PV acquire. Predecessor seal/publication
waits are separately acyclic: the predecessor seals with reserved workspaces,
and publication waits hold no op or fence resource. Bounded device completion
and fair harvesting are assumptions of this finite healthy-wave model.

`fn2-commit-notification-range(batch,cursor,core)` reads the immutable published
key interval, clamping a recipient-owned cursor. Notification debt therefore
leaves the batch through its published root; `notify` never waits for Send.
Both rows can drain and be reused while two recipients remain at cursor zero.
The reuse control checks those old intervals after four actual commits, plus an
empty interval at a caught-up cursor. Actual transport, durable recipient
cursors, exactly-once delivery and B6's root-retention policy are separate
integration work; this is a replayable notification source, not implemented Send.

The unit audit follows actual callback/helper phase writes, rejecting a
counterfactual notify→free arm. Shared callbacks are audited against their source
union; scenarios check the exact source/destination edge on **every** microstep.
Independent pool/operation/allocator reads check phase holdings, issuance,
adapter credit release, completion, edge transfer, draining and non-acquisition
in uncertainty. Generic potential telescoping proves every closed potential
path has zero delta. An independent P/V prefix inventory checks the generated
words against their retained root holdings; a missing pool release is refused
with cycle name `:baseline-missing-vpool`. This is tested implementation
correspondence, not a universal machine-to-PV refinement theorem.

`check-deadlock.lisp` implements the finite Algorithm 5.13 boundary test: capacity
violations become open rectangles; candidate lower-face coordinates plus
finished coordinates are checked for feasibility and blockage in every active
direction. Maximum-demand pruning removes only resources that cannot overflow.
Explicit terminal holdings remain inside rectangles. There is no schedule
sampling, silent search cap, or topology. A geometric witness need not be
reachable; zero geometric deadlocks is the conservative result used here.
Both modes report tiny 13 threads / 2,066 rectangles / 24,576 candidates / 0
deadlocks and concrete 523 / 4 / 18 / 0. The reversed fence/batch and held-send
controls each report three threads, four rectangles, one deadlock, witness
`((2 2 2))`. Exhaustive independent prefix/BFS comparisons cover 8,568 small
program/capacity cases. Persistent uncertainty and absent recovery are named
terminal obligations, not normal successful releases; the zero result is not
fault liveness, starvation freedom, or a B5 recovery result.

### Validation scope

The twelve durability teeth remain executed zero-argument evaluators. The B
scenario driver includes the resource unit and runs real and counterfactual PV
checks before scenarios 13/14. Tiny exhausts 316/1882 cuts of the stated schedules;
concrete runs 10,000 seeds per scenario. Every fault class must be hit. Final
current-closure certification times, verbatim acceptance and any remaining red
are recorded in `build/REPORT.md`; an earlier checkpoint's green is not current
acceptance. B5 discovery and B6 reclamation remain separate quests.

## 11. Recovery (B5)

### Machine
`fn2-recovery-machine` (declared in `machines-b.lisp`, continuations in `recovery-machine.lisp`,
expanded by `assembly-callbacks-s`, `-t` and `assembly-callbacks` after the commit continuations) is one row with phases
`free read read-result verify search install done`, the 4096-byte / 32-step / 4-descriptor run
budget, and holds the recovery bundle (`:storage-job :storage-window`, resources.lisp's
`(:recovery :start)`) from `:read` through `:install`; the arm that reaches `:done` releases it.
Each run reads or verifies at most one 4 KiB unit (ROUND2 §B.3). Its scratch state is the core
child `fn2-core-rec-cand` (one row per arena position: status `unread empty invalid unreadable
candidate chained`, the claimed commit, writer epoch, allocation counter, event interval, seal
offset and length) and a digest region after the commit directory (per position: final seal,
previous seal, record-stream commitment, dependency hash; then the chain's previous seal, the
presented witness, one scratch row). It verifies through B2d's `fn2-format-run` on its own checker
continuation (format row 2; `:format-slots` now defaults to 3, `:format-field-slots` to 384).

Every arm is in the checked arm language with its full contract (cost, own-field writes, core
children, successors, uses; no `:language :unchecked`): the arm reads its own fields, moves its
phase and writes its row; the table work is a set of defcost'd operations of
`recovery-machine.lisp` (`fn2-recovery-discover-unit`, `-chain-unit`, `-cand-mark`, `-link`,
`-scan`, `-dirty-scan`, `-witness-match`, `-adopt`, `-finish`) that take the row's owner triple
explicitly and report a refused bound as `:bounds`. A refused bound stops the core with the named
reason `:recovery-bounds`, a refused release of the bundle with `:recovery-release` (both appended
to `fn2-stop-reason`); nothing in recovery absorbs.

API: `fn2-recovery-present-witness-word i word fn2-core` (before start; eight words of a receipt's
seal), `fn2-recovery-start id assume witness fn2-core -> (mv code fn2-core)` (`assume` is the
profile's assumption bits, `witness` the receipt's commit, 0 for none). Results are the row's
`rc-class` (`*fn2-rec-classes*`), `rc-witness-outcome` (`*fn2-rec-witness-outcomes*`) and
`rc-chain`; the commit root rows name each recovered batch's extent.

### Algorithm (STORAGE-DESIGN-ASTRA parts G, H, I over the genesis arena)
1. **Discovery.** Every position of the arena (the allocator's extent table) is read at its seal
   unit, and, when that unit is all zero, at its records frame and dependency page too: a position is
   `empty` only when all three units are zero, and debris in either other unit beside an empty seal
   unit is `invalid` (dirt). A nonzero seal unit's frame header is decoded and must name this position,
   the genesis lineage (history 1, incarnation 1) and a seal frame; the frame hash is checked with
   the header's own identity; the sealed batch is decoded and must repeat that identity, and its
   previous seal, final seal, record-stream commitment and dependency hash are loaded. A failed
   check is `invalid`; a failed read is `unreadable`. No length or next pointer from an unchecked
   frame is trusted, and discovery never stops at the first bad position.
2. **Chain.** Starting from the zero genesis seal, the unique candidate whose commit is the next
   number and whose previous seal equals the chain's is verified whole: the seal checker with the
   chain's previous seal, the records frame and its exact equality with the seal's record-stream
   commitment, the dependency page under the seal's hash. Two such candidates are a branch
   (`ambiguous`); a failed unit or read ends the chain.
3. **Classification** with the assumption bits as inputs (B-ASSUMPTIONS-AS-PARAMETERS):
   `damaged` when a credited witness contradicts the chain; `unknown` when the chain branched or a
   read could not be established, or the arena is dirty (a position that is neither empty nor
   chained) under a profile that is not crash-only with honest fences; `torn-tail` for a dirty arena
   under crash-only with A-PERSISTENCE-FENCE; `intact` otherwise. Checksums alone never yield
   `damaged`: the commit fixture lets the follower write before its leader's fence, so a valid
   successor beside an invalid predecessor is also an ordinary torn tail (a departure from part E's
   step 6, recorded here).
4. **Witness** (scholar ch. 4 item 10): a presented receipt is `uncredited` without
   A-INDEPENDENT-FRONTIER; with it, `rollback-detected` beyond the chain, `consistent` when the
   chain's seal at that commit matches, `discontinuity` otherwise.
5. **Install once**, only for `intact` and `torn-tail`: the allocator adopts every position below
   the high water in arena order with its recorded identity (`fn2-alloc-adopt`, new in alloc.lisp):
   chained extents become ALLOCATED to their commit with an installed-root edge, every other one
   is quarantined with a recovery-candidate edge and never reused; the commit directory, root
   recipe rows and admission frontier are restored; the writer epoch begins above every adopted
   identity. `damaged` and `unknown` install nothing: the allocator's epoch stays unbegun, so every
   mutation is refused until repair.

### Departures and owed items
- **B-RECOVERY-GENESIS.** No anchor bank or checkpoint descriptor exists until B6 writes them, so
  root selection (part I steps 1-3) reduces to the genesis base and its arena is the whole extent
  table; allocator adoption assumes the genesis allocation order. B6 replaces both with the
  promoted checkpoint's arena and allocation map.
- The journaled BEGIN_WRITER_EPOCH batch (part H) is owed: recovery begins the epoch in memory.
- Read misdirection (scenario 15's "misdirect a read") is not covered: a misdirected read is
  indistinguishable from damage without a re-read, and the row has no field left for a retry
  (24 of 24 used). Write misdirection is covered.
- GC2 (`:run-replacement`, `fn2-runs-install`, following one level of `:dependency-manifest`
  pages) is the next B5 commit.

### Death is a fresh process
B5 found that `fn2-sim-crash`'s `fn2-core-init` did not give a fresh process: defcolumns'
generated init resized each column, which keeps earlier rows, so pre-crash allocator edges
survived and blocked adoption (and A's outbox generations and the control's stop reason survived
in extra fields). The generated init now resizes each column to 0 and then to n, empties resizable
extra arrays, resets scalar extras to their declared initial values and clears hash-table extras;
fixed arrays and nested stobj fields keep their own init (`columns.lisp`, agreed with the DSL seat). Every RECOVERY case first compares the post-death core
with a newly created core (`fn2-b-death-difference`, the reference model's comparison); the
planted-survivor control (`fn2-b-death-control`) leaves one live edge row and must be reported.

### RECOVERY and the ground truth
`sim/check-recovery.lisp` drives the row through the executor, the simulated adapter and the
router (`fn2-b-rec-run`), applies post-death faults to the durable image (`:corrupt`,
`:corrupt-last`, `:misdirect`, `:rollback`, `:witness`), and computes the harness's ground truth
from the manifests captured before death: every batch whose bytes landed exactly `:survives`; a
fenced batch damaged after its fence is `:corrupt-required`; a dirty arena names its first
defective, non-injected batch as `:bad-tail`. B1's `:bad-tail` therefore names the first defective
batch of a dirty tail, at most the last submitted (log-model change; a follower may land before
its torn leader). The recovered history is rebuilt by the harness from the chained extents and the
durable bytes, so a chained extent the harness cannot confirm fails HISTORY.
`fn2-check-recovery` is `fn2-lm-recovery-allowedp` plus the witness outcome: detection exactly when
a credited presented witness lies beyond the recovered history, `none` exactly without a witness,
`uncredited` exactly without A-INDEPENDENT-FRONTIER.

### Acceptance (tiny gate, forge, 2026-10-30)
`FN2_B_PROFILE=tiny sh fn2/tools/forge-driver.sh sim-layer-b`, both barrier modes, every case through
the real recovery and RECOVERY:
- death control: fresh after init, planted survivor reported.
- scenario 15: 336 cases, classes `corrupt-middle -> unknown` 12, `corrupt-tail` (every death cut of
  the pilot, then one byte in the last batch's seal unit) `intact` 134 / `unknown` 182,
  `misdirect-write -> unknown` 4, `older-image -> intact` 4; RECOVERY pass.
- scenario 16: 12 cases; witnessed rollback detected and `damaged`, unwitnessed and uncredited make
  no claim, covered witnesses `consistent`.
- scenarios 13/14 (now with the real recovery): 316 and 1,882 death cuts, HISTORY/RECOVERY pass;
  the whole tiny gate in 22.8 s.
- recovery time: 0.78 s per MiB of scanned arena (simulator and ACL2 hashing: the difference of an
  intact recovery over 64 and 5 extents, 5-run means 0.215 s and 0.036 s). Not a device number.
The concrete 10,000-seed sweep stays the nightly row (scenarios 13/14; 15/16 concrete seeds owed).

Certify times on forge (closure at -j 8 on 84e6bb293, load 3-6): the commit kind's second section
is its own book `assembly-callbacks-r` (34 s); recovery's table-level operations are
`assembly-callbacks-s` (31 s), its first arms (refusals, observation, read, result, verify)
`assembly-callbacks-t` (40 s), the rest of the arms and the dispatch resolution
`assembly-callbacks` (29 s); `recovery.lisp` 5 s, `recovery-machine.lisp` 2 s. The one wall on the
way (113 s) was the install arm's classification proofs case-splitting through the inlined
classification and witness rules: the arm now sees them only through their type facts, and
install is four forwarded callbacks (scan, classify, adopt, finish).

### Keystones (owed, `books/recovery-proof.lisp`, teeth in `tests/recovery-proof-unit.lisp`)
- `fn2-recovery-never-shortens-intact`: honest fences and no later destruction ⇒ every acknowledged
  batch is in the recovered history. Teeth: baseline and preflush/FUA positives; a lying flush
  (fence removal) and an at-rest corruption (destruction removal) each lose an acknowledged batch.
- `fn2-recovery-broad-bad-tail-unknown`: not crash-only and a ground-truth bad tail ⇒ `unknown` or
  `damaged`. Teeth: a death after the leader's writes and before its fence with one byte of dirt is
  `unknown` under broad and `torn-tail` under crash-only.
- `fn2-recovery-rollback-needs-witness`: detection ⇒ A-INDEPENDENT-FRONTIER and a presented witness
  beyond the recovered history. Teeth: witnessed rollback detected and `damaged`; unwitnessed
  rollback recovered `intact` with no claim; uncredited receipt; covered witness `consistent`.

## 11a. The commit kind's members (B5-4: GC2's run member, B-S2's transaction member)

Statement first (2026-10-30; read once by Astra, build/coordinator/fn2/lanes/b-quests/b54-astra.md).
B5-4a (this commit) builds M1-M4 and M6 for the keyed fixture: the member and settled tables, admission
through `fn2-commit-admit-keyed`, the suffix abort and `:dropping`, the four hooks, and settlement with
`fn2-commit-take`; its controls are tests/commit-member-unit.lisp. M5, M7 (B5-4b), the commit port (M9)
and M8 (B-S2) follow in that order.

### 0. What exists
The batch is B3's fixture: the harness calls `fn2-commit-start (id members first-key mode partner)`;
seal synthesizes N keyed mutations (object = first + index); the dependency page is a page header plus
`fn2-commit-manifest-node`. No member, workspace, admission or refusal exists: every failure is
`:uncertain`.

### 1. Decisions

**M1. Member table and settled outcomes, two core children.** `fn2-core-commit-members` (defcolumns
`fn2-commit-member`, books/commit-members.lisp): `2 x 16` rows, member `m` of batch row `r` at `16r+m`;
columns `kind` (`:none :keyed-mutation :run-replacement :txn`), `slot gen len` (workspace),
`okind oslot ogen` (owner: reads are under it; it is told the outcome), `entries entry-bytes`, `schema`,
`event`. `fn2-core-commit-settled` (defcolumns `fn2-commit-settled`, 64 rows, a free list): `okind oslot
ogen batch event outcome` (`:accepted :uncertain :refused`) plus the settlement evidence (`phase` the
batch reached, `published` root at settlement). Admission reserves one settled row per owned member, so
settlement never fails; notify moves the outcome there; the batch row's reuse never waits for a client.
The batch row gains `cb-wrote :bool` (a journal write was ever issued; never reset within a batch),
`dep-bytes :u32`, `rec-bytes :u32`, `cb-open :bool` (collection open). `:keyed-mutation` is the
harness's kind (records synthesized at seal as today; no workspace, no owner, no settled row).

**M2. One open collector; events in admission order.** Admission picks the row: a row in `:collect`
with `cb-open` takes the member when the member rows, the records room and the dependency room have
space, else `:exhausted`. With no open collector, a `:free` row opens a batch (today's start body:
pools, extent, batch `proposed + 1`, proposal published) when its partner is not `:collect` with
`cb-open`, not aborting (M3) and not `:uncertain`; otherwise `:exhausted`. The member's event is the
global next event (`fn2-commit-root` row 0 `first-key`), advanced by one per member. Collection closes
when the batch row's `:collect` arm runs (the scheduler's next visit after the opening admission made
it runnable: group commit by construction). The keyed fixture `(fn2-commit-admit-keyed n mode fn2-core)
-> (mv code id batch event fn2-core)` admits n members and closes at once, so the harness's two
back-to-back batches stay two batches. Events of the members of any one batch are contiguous, and a
follower opens only after its leader closed, so events increase in admission order across batches
(C-S3 (a)); an aborted suffix's positions are reissued (M3), so the claim is over published batches.

**M3. Refusal is a suffix abort.** A batch is *refused* exactly when it fails while `cb-wrote` is 0
(in `:collect`, `:seal`, or the first issue of `:dependencies`), or it has `cb-wrote` 0 when its
predecessor becomes uncertain or refused. A follower may not issue its first journal write until its
leader has `cb-wrote` 1 (one condition in `fn2-commit-writes`), so a refused leader's follower has
written nothing to the journal and is refused with it (C-S3 (b), no exception). Protocol: the first
refused batch `k` records `aborting = k` and its first event in root row 0 (admission answers
`:exhausted` while `aborting` is set); each refused batch moves to `:dropping`, whose arm, in
increasing batch order (a follower waits while its leader is still `:dropping`), calls
`(fn2-successor-drop batch fn2-core)` once, settles its members `:refused`, clears the batch's root
row, seal digest and seal-ready, and releases through the drain path; the last batch of the suffix (the
one whose number is `proposed`) restores `proposed := k - 1` and the next event, then clears
`aborting`. From `cb-wrote` 1 on, a failure is `:uncertain` (persistent, as today); an uncertain batch
calls neither drop nor publish, so its private overlays stay in C's tip (C-S3 (c)). The uncertain arm
settles its members `:uncertain` before it waits for pending completions (the outcome is known; a lost
completion must not hide it). *Pages C wrote before a refused admission* are C's: they lie in
extents C reserved, are referenced by no chained entry, and recovery treats them as M7's unreferenced
well-formed pages (quarantined, not dirt). *HISTORY:* `fn2-history-request` forbids a repeated batch
number and `fn2-history-step` a refusal of requested members, so an abort needs an explicit abort-attempt
transition (attempt identity distinct from the reusable batch number and events); the harness's keyed
batches never refuse today (no scenario injects a pre-write failure), so the transition lands with the
first scenario that does, and the refusal path is covered by the unit's controls until then.
*Positions:* Astra would move settled outcomes into the owner's row; B keeps them in its own settled
table (M1), because B writing a D row crosses the seam, and the bounded table gives the same property
(batch rows reuse without waiting for a client).

**M4. Hooks: constrained functions, refusing default attachments, frame constraints.** B's first commit
section moves to directly after A's (the chain a -> b -> c -> d -> r -> s -> t: one include line each
in `-b`, `-c`, `-d`, `-r`), so admission, take and the hooks precede C's and D's sections. `-b` expands
`(fn2-commit-hook-events)`: one `encapsulate` per hook, guard `(fn2-core-wfp fn2-core)`, and constraints
(i) valid input gives valid output (`fn2-corep` and `fn2-core-wfp` under `(and (fn2-corep fn2-core)
(fn2-core-wfp fn2-core))`), (ii) **frame:** the machine table and every B child (`fn2-core-commit-io`,
`-commit-root`, `-commit-members`, `-commit-settled`, `-extents`, `-alloc-edges`, `-rec-cand`, `-digests`,
`-fc`, `-fc-context`, `-b3`) are unchanged, and the pool is unchanged at the workspace handle; then a
default attachment answering `(mv :unregistered fn2-core)` (the attachment is outside the encapsulate):
- `(fn2-runs-install schema batch slot gen okind oslot ogen fn2-core) -> (mv code fn2-core)` (GC2);
- `(fn2-successor-publish batch fn2-core)`, `(fn2-successor-drop batch fn2-core)` -> `(mv code fn2-core)` (C-S3);
- `(fn2-member-replay batch event slot gen len okind oslot ogen fn2-core) -> (mv code fn2-core)` (M7).
**C's change (for C's yes through main, in the same foundation commit):** C's wrappers in
`fn2-successor-core-events` are renamed `fn2-succ-core-publish` / `-drop`, C proves the two frame
constraints for them, and `-c` attaches them (`(defattach fn2-successor-publish fn2-succ-core-publish)`,
drop likewise); C's defcosts keep the hook names; C attaches `fn2-runs-install` with C1c and
`fn2-member-replay` with D5 2/n. Existing callers (identity-core-unit) are unchanged. Proofs use only
the constraints (attachments give no equations), so keystones about hook calls are evaluated over
attached runs, never proved from an attachment. The hooks' defcosts name the attacher's tables (a
declaration; the frame constraint is what is proved); asked of the DSL seat: a layer group
`:tables (:layers :c :d)` so a lower layer never spells an upper layer's child names.

**M5. GC2's member as agreed.** `(fn2-commit-admit-runs schema slot gen body-len entry-bytes
entry-count okind oslot ogen fn2-core) -> (mv code batch fn2-core)`: one 4 KiB workspace under
`(okind oslot ogen)`, the `fn2-format-run-replacement` body at 0 (`body-len <= 167`), `entry-count`
(1..31) contiguous dependency entries from 256 totalling `entry-bytes`. Admission decodes the body and
each entry with their generated decode steps: exact lengths, the body's `schema` equal to the
argument, entries contiguous; else `:admission`, nothing changed. Room per M2.
- *Records:* M7's member envelope, then a record header (`:run-replacement`, version 1, the event)
  and the body copied verbatim.
- *Dependencies:* after the manifest node, per run member in member order, exactly one group
  `fn2-commit-dependency-group` (`(event (:id event)) (count :u8) (bytes :varint)`) and the entries
  verbatim; page payload length `73 + dep-bytes`; the page hash (and so the seal) covers it. Room:
  `4096 - 96 - 73 = 3927` bytes (one 31-entry member: at most 3,751 + 21).
- *Barrier:* C harvested every listed write `:ok` before admission, and both barrier modes issue their
  flush after admission, so the batch's barrier covers them (completion-time ABI).
- *Install:* after the `:install` root swap, one run member per run in member order,
  `fn2-runs-install`; a code other than `:ok` makes the batch `:uncertain`, new reason `:install`
  (code 7: durable, possibly partly installed; recovery replays it whole).

**M6. Publish, then settle; the owner takes.** `:publish` swaps the published root and calls
`fn2-successor-publish` once, before any outcome; a code other than `:ok` stops the core with the new
named reason `:commit-publish`. `:notify` settles one member per run (`:accepted`, the batch, the phase
and published root as evidence), then wakes the owner row (`fn2-sched-make-runnable` with its
`principal-slot`) when its generation still equals `ogen`. The owner reads `(fn2-commit-take okind
oslot ogen fn2-core) -> (mv code batch event outcome fn2-core)`: `:ok` (and frees the settled row),
`:pending`, `:none`. Settled rows of an owner whose generation moved are freed by the next admission's
scan (one row per admission). The consumer-progress assumption, stated: D's woken arm takes and saves
the outcome before any connection or output wait, on every path including disconnect; otherwise its
settled row stays (bounded: admission answers `:exhausted` only for want of a settled row).

**M7. Recovery: verify dependencies one level; replay every chained member in order.**
- *Envelope:* every member's records are preceded in the records frame by a member envelope, a new
  record kind `:member` appended to `record-kind` (codes unchanged): `fn2-format-member-envelope`
  (`(kind (:enum fn2-commit-member-kind ...)) (count :u8) (length :varint) (schema (:id schema))`); a
  batch has exactly `event-last - event-first + 1` envelopes, so the stream ends without trusting
  padding.
- *Verify:* every dependency entry's target unit is read and its BLAKE3 compared with the entry's
  digest; a `:dependency-manifest` target is verified and each of its entries' targets too, exactly one
  level (a second-level `:dependency-manifest` fails). A failed target ends the chain at that batch.
  The row keeps the parent traversal state across reads (`rc-dep` cursor, `rc-level`, the parent's
  entry offset in its scratch digest rows).
- *Dirt:* a position referenced by a chained entry is chained data; an unreferenced position whose
  unit is a well-formed page naming its own position and the lineage is quarantined and is not dirt;
  everything else is as B5-3 classifies.
- *Replay:* classification first (a hook never changes the class); then, for every chained batch in
  order and every member in member order, recovery rebuilds the member's workspace in its window,
  equal to the admitted one on the defined slices (run: `[0, body-len)` and `[256, 256 +
  entry-bytes)`; txn: `[0, len)`), and calls `fn2-runs-install` or `fn2-member-replay`, then
  `fn2-successor-publish` for the batch. A code other than `:ok` stops the core with the named reason
  `:recovery-replay` after a replayed prefix (the default attachment stops recovery of any history
  holding a served member; the keyed fixture replays nothing). Replay is O(chain) and bounded by C's
  overlay capacity until B6's checkpoint records C's installed roots and replay starts after it
  (recorded departure B-REPLAY-WHOLE-CHAIN; C's `:full` from a replay hook is a stop, not a yield).

**M8. B-S2's transaction member (lands after the commit port).** `(fn2-commit-admit-txn slot gen len
okind oslot ogen fn2-core) -> (mv code batch event fn2-core)`: the workspace holds `count >= 1` records,
each `fn2-commit-member-record` (`(record-kind (:enum record-kind ...)) (length :varint)`) then its
body; kinds in `*fn2-commit-txn-record-kinds*`; each body decoded by its kind's decode step to exactly
`length`, the whole to exactly `len`. Seal writes the envelope, then per record a record header (its
kind, the member's event) and the body verbatim; replay rebuilds the wrappers from the headers and
envelope (canonical: the decoders accept exactly one encoding of each length). The frame's records room
is its 3,900-byte payload; an article acceptance is at most 885 bytes with its header, so four
transactions fill a batch until D4 3/n moves bodies to payload blocks. What a replayed stream means
(identity facts, memberships, outcomes, C's assigned fold values; references in an article acceptance
resolved through their durable targets) is the attacher's specification, owed by C and D with the
attachment; B guarantees the stream's identity and order.

**M9. The commit port follows at once.** B5-4a's new and changed arm bodies stay in `:language
:unchecked` beside their eleven siblings (one language per kind until the port, so no arm half-checks
against an unchecked forwarded callback); the commit port (ruling 3) is the next commit and converts
all twelve arms with their full contracts and turns every `assert$?` in commit.lisp and alloc.lisp into
`fn2-core-stop` with a named reason and a control, before M8 lands. (Revised from "rides along".)

### 1a. As built in B5-4a (beside M1-M9)
- **Events start at 1.** Root row 0's `first-key` is 1 at genesis (`fn2-commit-root-init-for`), so 0,
  every member and settled row's initial event, names no event; an empty-chain recovery keeps it.
- **The format rows are derived.** `fn2-b-upload-windows` (`:large-upload-windows`, default 16, the
  round-2 bound of resources.lisp) is the one window count: B's `:format-slots` floor and default are
  `4 + w` (rows 0-1 commit, 2 recovery, 3..2+w D's upload windows, 3+w C's sealer), D's
  `fn2-upload-capacity` is `min(u, 16, w)` and C's sealer row is `3 + w`. A profile naming fewer
  slots is refused, so the sealer's row exists in every profile (C-SEAL-NO-ROW's case is unreachable).
  Since 2026-10-31 the floor is `4 + w + c`: `fn2-b-ctl-rows` (`:control-connections`, default 2, the
  tiny profile's) gives E's control connections rows `4+w .. 3+w+c`. `fn2-b-ctl-slot s` is control
  connection S's slot: its b3 row hashes the FNCT trailer, and its 128-row field stripe (at
  `128 * slot`, B's per-slot stripes from row 0) holds the generated codec's FNCT decode and encode.
  That is E's ask in amended form: the slot's own stripe already gives 128 rows, more than the 64
  asked for, so no separate stripe sits below the read stripes. E's `fn2-ctl-capacity` reads
  `fn2-b-ctl-rows`.
- **Section books under the one-minute rule.** The commit kind's events are four section books:
  `-b` (hooks, admission), `-b2` (root edges, refusal, collect, seal), `-r` (observe, writes, fence,
  durable), `-r2` (install, publish, settlement, drop, notify, drain, the run); settlement is three
  one-child helpers (`fn2-commit-member-owner`, `-settle-row`, `-wake-owner`) and the follower gate is
  `fn2-commit-follower-waits`.
- **The harness runs the served turn.** `fn2-b-rounds` and `fn2-b-rec-drive` step `fn2-turn` (through
  `fn2-b-turn`, which records every result the turn harvests) on an executor-initialized core
  (`fn2-init-executor ... :null`), so Q1's TRACE sees B's transitions; `fn2-b-admit` is the
  harness's admission plus the row's wake, and the q1 case hook re-reads its reference after
  `fn2-b-start` / `fn2-b-admit` as after `fn2-recovery-start`. The keystones' command language
  (`fn2-commit-proof-step`: explicit `:run` row, `:harvest`, `:complete`) keeps its explicit
  interleavings: it is the adversary over orders the turn's calendar never chooses, and it runs the
  same generated arm dispatch (`fn2-commit-run`).

### 2. Keystones (owed; `books/commit-proof.lisp`, teeth evaluated in `tests/commit-member-unit.lisp`)
- `fn2-commit-published-events-ordered`: over a run, the events of the members of published batches,
  read in admission-attempt order, are strictly increasing and contiguous from the first. Teeth:
  leader + follower; a refused leader with its follower aborted and both positions reissued; a planted
  swap of two events fails.
- `fn2-commit-abort-suffix`: every dropped batch has `cb-wrote` 0 throughout; within each abort the
  drops are the suffix `k..proposed` in increasing order; after it `proposed = k - 1` and the next
  event is `k`'s first; no batch below `k` changes. Teeth: refused leader with a sealing follower;
  refused follower alone; an uncertain leader drops nothing; a planted early follower write is caught.
- `fn2-commit-hooks-before-outcomes`: for every published batch, `fn2-runs-install` returned `:ok`
  once per run member in member order after the root swap, and `fn2-successor-publish` returned `:ok`
  before any of its outcomes was settled; B's children are unchanged across each hook call. Teeth: an
  attachment refusing the second member leaves the batch uncertain with outcomes `:uncertain` only; the
  default attachment makes every run batch uncertain; an attachment that writes the commit root is
  refused by the frame constraint at `defattach`.
- `fn2-recovery-replays-prefix`: after recovery of class intact or torn-tail, the hook calls are a
  prefix of the ordered fold (each chained batch: its members in order, then its publish), complete
  unless a hook refused, in which case the core stopped `:recovery-replay` right after it; each call's
  workspace equals the admitted one on the defined slices. Teeth: a three-batch chain of mixed members
  against a recording attachment; a corrupted dependency target ends the chain before its batch and
  replays nothing of it; a second-level `:dependency-manifest` fails verification; a refusing
  attachment stops after the prefix.
- Plus evaluated controls: delayed take, a vanished owner, a missing completion on an uncertain batch
  (outcomes still settled), malformed member boundaries (each refused `:admission`).

### 3. Commits (each under the whole-tree gate; every book under 60 s)
1. B5-4a: M1 tables, M2 with `fn2-commit-admit-keyed`, M3 suffix abort and `:dropping`, M4 hook section
   with publish/drop (C's rename and attachment in the same commit after C's yes), M6 settlement and
   take; harness on admission; S13/S14 re-measured (collection closing on a run changes the cuts).
2. B5-4b: M5 run member, M7 envelope, dependency verification, dirt rule and replay; a run-member
   scenario in sim-layer-b with a recording test attachment.
3. Commit port (ruling 3), then B-S2 (M8) with D.

## 11b. B-S2: the transaction member (statement first, 2026-10-31)

Status: statement, before code. It refines §11a M7/M8 against the seam D states (d-machines-nntp.md
14.4.4 and the B-S2 bullet), C's asks (c-ordered-runs.md §8 C-S3 (a)-(c), already met by B5-4a), and
IDENTITY-ACROSS-PEERS ruling 2 (the origin fields). The twelve arms' port waits for MACHINE-FORM.
None of this needs the port: the new code is admission, a record kind, seal stages and a grant
source, and the arms they touch stay in the language they are in until the form arrives.

**S1. The call.** `(fn2-commit-admit-txn slot gen len okind oslot ogen fn2-core) -> (mv code batch
event fn2-core)`. D's interim of that name is deleted (the twin). D passes a workspace it owns
(`slot gen` under `okind oslot ogen`, read-only to B from admission to settlement) holding
`[0, len)` of member records (S2). Codes:
- `:ok`: the member is in the open collector. `batch` is its batch number and `event` its commit
  position (the global next event, C-S3 (a)). A settled row is reserved for the owner.
- `:exhausted`: backpressure. There is no open or free row, the records or dependency room is short,
  the batch is at 16 members, no settled row is free, or an abort is in progress. Nothing changed,
  and the owner may park on `:batch-membership` (S6).
- `:admission`: the workspace does not decode (S2). Nothing changed. D refuses the POST by its own
  word.
An abort or an uncertain predecessor never changes a member that was already admitted; B5-4a's suffix
abort settles it `:refused`, and a batch whose first journal write happened settles `:uncertain`.

**S2. The member records.** The workspace is a sequence of `count >= 1` records. Each one is
`fn2-format-member-record` (`(record-kind (:enum record-kind ...)) (length :varint)`) followed by
`length` body octets, and the whole is exactly `len` octets. The kinds are
`*fn2-commit-txn-record-kinds*`, D's four from 14.4.4: `:article-acceptance` (the existing
`fn2-format-article-acceptance`: the stored octets by reference, the content and source digests, the
stored length), `:identity-fact`, `:membership` and `:operation-outcome`. Each body is decoded by its
kind's generated decode step to exactly `length`. The decoders accept one encoding per value, so
replay can rebuild the stream byte for byte. Admission decodes and checks everything; seal trusts it.
Room: the frame's records payload is 3,900 bytes, which holds about four POSTs per batch until D4 3/n
moves bodies into payload blocks. The article octets themselves stay in D's window: the
acceptance record references them, and until D4 3/n the reference is the window's durable extent
written by the upload (B-S1).

**S3. The envelope and its origin (ruling 2).** Every member's records are preceded in the frame by
`fn2-format-member-envelope`, which B5-4b lands for the run member. It is extended now, while
adding a field is cheap: `(kind (:enum fn2-commit-member-kind ...)) (count :u8) (length :varint)
(schema (:id schema)) (lineage (:id lineage)) (domain (:id domain)) (incarnation (:id incarnation))
(position (:id event))`. For a member committed here, the origin is this node's lineage, its single
commit domain (ruling 13), the history incarnation from the anchor (STORAGE §3 identities), and
the member's event. A peer-imported acceptance (E4) carries its originating values instead. That is
why the origin sits in the member envelope and not in the batch seal. Record headers keep `event`
only. The revision stamp C's records carry sits beside it in the record bodies, untouched. Recovery
checks that `position` equals the member's event in the chain, so a reordered or spliced member is
damage.

**S4. Seal, verbatim.** For each `:txn` member in member order, the seal's records stage writes the
envelope, then for each record a record header (`record-kind`, version 1, the member's event) and
the body copied from the workspace. The copy goes through `fn2-commit-copy-bytes`, the per-octet
loop the 10-30 review names, until A's pool range copy exists (owed ask A-S8; a recorded departure,
B-TXN-COPY). The records hash and the seal cover every byte, as for keyed members.

**S5. The outcome.** It is settled per member (B5-4a M6). `:accepted` comes after publish: the batch
is durable, `fn2-runs-install` and `fn2-successor-publish` both returned `:ok`, and the settled row
carries the published root as evidence. `:uncertain` means the journal write was reached and the
fate is unknown; the uncertain drain settles it before waiting for completions. `:refused` means
the batch was dropped before any journal write. A member that is known durable but not yet
published is never `:refused`: it stays pending until publish or until recovery replays it (B5-4b).
The owner reads the outcome with `(fn2-commit-take okind oslot ogen fn2-core)`; D's arm takes it
before any connection or output wait (the consumer-progress assumption of M6). The settling arm
wakes the owner row only through `fn2-sched-make-runnable`, with the owner's generation checked.
This is the outcome wake, distinct from S6.

**S6. The `:exhausted` waiter through the grant service.** A sixth grant source is asked of A
(machines-a-access, the sealer's pattern): `fn2-batchable-ready-p` / `fn2-batchable-grant-one`,
default nothing. B attaches them in `-b2`: the source is ready when `fn2-commit-pick` would not
answer `:exhausted` and a settled row is free, and a grant wakes the oldest row parked on wait
reason `:batch-membership`. D's `:ready`, on `:exhausted`, parks with that wait reason and stays
`:ready` instead of busy-retrying. No arm writes another row's wake id.

**S7. Fencing.** An unresolved (`:uncertain`) batch keeps its storage scope fenced. Admission answers
`:exhausted` while the pick finds the partner uncertain (B5-4a), so no later member can commit past
an unresolved one. Recovery resolves it by classification and replay, never by waiting.

**S8. The format floor.** `:format-slots` defaults to `4 + w`, and that is also its floor, with
`w = fn2-b-upload-windows` (landed in B5-4a). Every profile therefore has the sealer's checker row.
A profile that names fewer slots is refused.

**D's amendments (accepted 2026-10-31).**
- (1) D's `:ready` runs in this order: resolve, stage, `fn2-successor-out`, write the member records into
  D's workspace, C-S3a fill-octets after the last stage, `fn2-commit-admit-txn`, then bind with the
  returned event. On `:exhausted` D parks on `:batch-membership` while staged, and the re-stage on
  wake rewrites both the records and the fill. B never caches a workspace's records across a park:
  admission decodes the workspace when it is called.
- (2) Ruling 6: `:article-acceptance` is optional. A `:txn` member made only of identity records
  plus `:operation-outcome`, with no acceptance and no `:membership`, is admissible: it is the
  evidence-only commit. D's reply reports the article refusal and the evidence commit's outcome (S5)
  separately.
- (3) Rulings 3 and 7, and C's §4a (219184b5d): D's `:identity-fact` is replaced by one B kind,
  `:identity`, whose body is a §4a record. The body leads with C's record tag (schema and version),
  and B decodes it with C's generated decoder for that tag. B does not freeze a shape of its own.
- (4) Ruling 1: the `:article-acceptance` record names two digests distinctly. The content digest
  is the identity subject's (D25's authored source). The source digest is the stored projection's.
- The `defcost` of `fn2-commit-admit-txn` declares `:answers (:ok :exhausted :admission)`, and that
  of `fn2-commit-take` declares `:answers (:ok :pending :none)`. The arm language routes every answer
  code, so D's `:ready` cannot absorb one. D adds `:batch-membership` to `resources.lisp` at the
  txn's port.

**S9. S-ARTICLE-LOCATION: the member result names where the article's octets are.** An
`:article-acceptance` member's `:accepted` settlement carries the article's source references as
`fn2-format-ref` values, the layout the acceptance record already holds (`SOURCE-` and
`PROJECTION-`): storage domain, physical unit, writer epoch, allocation, page kind, encoded length,
expected hash. Until D4 3/n moves bodies into content-named payload blocks, the source reference is
the upload window's durable extent (B-S1), with the article's offset and length inside it. After D4
3/n it is the payload block (B-HASH-ATTACHED: each 64 KiB block is hashed and content-named).
`fn2-commit-take` returns the event, and the references are read from the settled row's acceptance
record. The txn binds them into C's `fn2-article` location field (C adds the field). A reference
holds an allocator `:promised-read` edge from the time it is published until the article is
retired, so the extent cannot be reclaimed while it is named.

**S10. The block read, for D6 3/n (ARTICLE, HEAD, BODY).** There are two operations. Each has a
defcost that names `fn2-core-extents`, `fn2-core-alloc-edges` and the issuing kind's lease, and
declares `:answers`.
- `(fn2-block-read ref-row lease-slot lease-gen off len okind oslot ogen fn2-core) -> (mv code
  fn2-core)`, with `:answers (:ok :exhausted :stale :bounds)`. It checks the reference's allocation
  handle against the allocator (`:stale` when the epoch or counter has moved) and takes a `:borrow`
  edge on the extent for the read's lifetime. It then issues `fn2-issue-read` (the
  `(:storage-job :read)` hold) of `[off, off+len)` into the caller's lease. The read result arrives
  as the caller's `:read-result` observation.
- `(fn2-block-read-done ref-row lease-slot lease-gen fn2-core) -> (mv code fn2-core)`, with
  `:answers (:ok :hash :io)`. It runs after the result. For a whole block it verifies the block's
  expected hash with the BLAKE3 hasher row (`:hash` is damage, never served). It drops the
  `:borrow` edge.
A cursor's `:need-page` issues the same pair. The caller owns the lease, so B writes no other kind's
row.

**Keystones (owed, `commit-proof.lisp`; teeth in `tests/commit-txn-unit.lisp`).** Each is stated
over `fn2-commit-txn-proof-run (workspaces commands mode plant)`: the real core and executor with the
simulated adapter on the tiny profile, members owned by `(9, 3+i, 5)`, the stepper's commands plus
`(:admit i)`. Evidence is read at the boundaries: journal writes from the outbox (counted per batch),
publication from the visibility rows, the sealed records frame from the pool image after the seal and
before the pools are released. The statements take `plant` nil; the teeth plant one mutation each.
- `fn2-commit-txn-outcome-evidence`: every settled outcome matches its batch's evidence: `:accepted`
  ⇒ the batch was published; `:uncertain` ⇒ the batch issued its first journal write; `:refused` ⇒
  it issued none. ("Journal write" is any write of the batch, the dependency unit first: that is
  when `cb-wrote` makes refusal impossible.) Teeth: one batch of two members, clean completions, both
  `:accepted`; one member whose writes fail (`:no-space`), `:uncertain`; two batches where the
  leader's write fails before the follower writes, `:uncertain` and `:refused`; and member 0's
  outcome planted `:refused` after its batch wrote, which fails.
- `fn2-commit-txn-records-verbatim`: each sealed records frame is its members' admitted records in
  event order, each a record header at the member's event (occurrence = event) and the body
  verbatim, and only the frame's zero padding after. Only `:article-acceptance` is admitted until its siblings land with
  their producers, so the two members carry different acceptance bodies (three records). Teeth: the
  two-member batch; a body octet of member 0's workspace flipped after admission, which fails.
- `fn2-commit-txn-admission-total`: `:ok` changes exactly one member row, which holds the admitted
  workspace and owner; `:exhausted` / `:admission` change nothing in the member and settled tables,
  the two rows' admission columns, the frontier or the stop reason. Teeth: a frame longer than its
  workspace, an unknown kind, a body one octet short (`:admission` each), then members until the
  batch's records room runs out (`:exhausted`); and a refusal planted to reserve a settled row, which
  fails.

**As built (one-minute rule).** The B-S2 code is its own section book, `assembly-callbacks-bt`
(admission, the source reference, the block read, the seal's verbatim copy), between `-b` and `-b2`.
Admission's two endings (`fn2-commit-txn-open`, `fn2-commit-txn-join`), the seal's per-member,
records and frame-header stages, refusal's root write (`fn2-commit-mark-abort`) and the reserve
loop's two steps are functions of their own, so each caller's proofs see preserved calls instead of
their case splits. Forge: `-b` 45 s, `-bt` 41 s, `-b2` 48 s.

**Order.** (1) The `assert$?` to named-stop commit (it touches helper bodies, not the arms'
language). (2) B-S2 itself, landed with D's switch from the interim and A's grant source as one
seam: the record kinds, admission, seal stages, envelope with origin, and the controls. (3) B5-4b
replay, which re-runs install and publish for a batch that is durable but unpublished. (4) The port,
in MACHINE-FORM.

## 14. Delivery record: the B3b slip review (2026-10-29)

§9 is the event log, so the slip finding lives here. Section 11 is recovery; 12-13 stay reserved for
checkpoint/cleaner and acceptance.

**Finding: the main cause was integration and base churn. Scope was a secondary cause. No design
wall caused the slip.** B's accepted library (B1, B2a-f, B4a/b, BR1, BH1, BR2: about 11,500 lines
that touch no A file except one owed-export include block) sat on `fn2/b-durability` without
reaching fn2/main. The B seat reported READY only at layer milestones, never for an accepted
library prefix. Every A change to the declaration forms therefore landed as a B rebase plus a
conversion, inside a quest that was already running. While B3b and B3c were open, the base moved
eight times: d90b821b3, 957b018c1 (R5a pass 3: named callbacks), 1fa1fe24b (W1: section books),
4cf85c4a8 (DM0a), 9cc09f2bf (DM1: obligation store, layer stamps), d8ec35855 (DM0b: restricted
callback arms, `fn2-call`), 26570c101 (coverage seal moved) and 0cad033b0/9eb370594. Three of
those moves changed forms that B3b's code calls.

Each move cost one Codex resume plus the full acceptance. That acceptance includes a 20,000-case
concrete sweep of 2,400-2,600 s, which has run five times so far. The tiny exhaustive sweep is the
real gate: 2,198 death cuts in 11 s.

**Scope.** B3b produced 3,310 lines against a 1,200-line target. The machine, its allocator and
format glue, the HISTORY projection, the recovery stand-in, the keystone proof book and the
scenario driver were in one quest, so the diff could not be read in one sitting and every
acceptance coupled the machine to the slowest driver.

**The design walls each closed within one session.**
- The 60 s rule on machines-b (229 s) and the assembly (294 s) was fixed in B3b part 2 by named
  checked updates and an exact opaque invariant interface. Now machines-b takes 11.9 s and the
  slowest section takes 50.5 s.
- The DM0b refusal of `b*` binders inside callbacks was a mechanical conversion to `cond` and
  `mv-let`, with no change to the language (ember's decision 2).
- The obligation seal inside sim/check was moved by A to the top of owed-export within the hour.

**What changes.**
1. B's accepted library merges to main now, as its own fast-forward, ahead of the commit machine.
2. The commit machine lands split. B3b-1 is the machine and its books (machines-b, commit,
   commit-alloc, commit-format; commit-resources, check-deadlock; the HISTORY,
   resource and deadlock units, and the tiny exhaustive sweep as its gate). B3b-2 is the
   keystone book commit-proof, the scenario driver sim-layer-b and the concrete sweep.
3. The concrete 10,000-seed sweep becomes a nightly row, not a per-quest gate.
4. From now on, every accepted B quest whose files touch no A seam is reported READY for merge.

**Landed (2026-10-29).** The library merged to dev as 12cd1031f. The converged commit
machine (B3b + B3c + B3c part 2) lands as B3b-1 and B3b-2, split by files rather
than by quest: B3c rewrote commit.lisp, and the DM0b, R5e1 and R5e2 ports apply
to the whole. B3b's historic state alone would need each conversion done twice.
`fn2/sim/commit-proof-step.lisp` is the real stepper, carved out of commit-proof.
The scenario driver includes the stepper, not the keystone book, so the tiny
exhaustive sweep gates B3b-1 without commit-proof.

**B3b-2.** The keystone book `commit-proof.lisp` (fn2-commit-ack-implies-durable and
fn2-commit-uncertain-persists, OWED with 12 executed teeth) and `commit-proof-unit` now sit
on top of the stepper, and owed-export includes the unit. The concrete sweep (scenarios 13
and 14, 10,000 cases each) is a nightly row on dregg-forge: `SECS=7200 sh
fn2/tools/forge-driver.sh sim-layer-b`. It is not a per-commit gate; the tiny exhaustive sweep
(`FN2_B_PROFILE=tiny`) is.
