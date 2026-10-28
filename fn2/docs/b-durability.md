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
| log model (abstract history, acknowledgement, allowed recoveries) | `fn2/books/log-model.lisp` | B1 |
| layout codec (layouts as data, one generic codec) | `fn2/books/layout.lisp` | B2a |
| incremental BLAKE3 over the pool | `fn2/books/blake3.lisp` | B2b |
| the on-disk format as layouts | `fn2/books/format.lisp` | B2c |
| format integrity readers and sealing | `fn2/books/format-check.lisp` | B2d |
| semantic Merkle event frontier and proof verification | `fn2/books/merkle.lisp` | B2e |
| commit-batch machine (declared through layer A's `defmachine`) | `fn2/books/commit.lisp` | B3 |
| allocator with typed edges | `fn2/books/alloc.lisp` | B4 |
| recovery | `fn2/books/recovery.lisp` | B5 |
| checkpoint and cleaner machines | `fn2/books/checkpoint.lisp`, `fn2/books/cleaner.lisp` | B6 |
| HISTORY, RECOVERY, RECLAIM checkers | `fn2/sim/check-history.lisp`, `check-recovery.lisp`, `check-reclaim.lisp` | B3-B6 |
| acceptance | `fn2/tests/sim-layer-b.lisp` (+ driver `.lsp`) | B3-B7 |

## 2. Decisions inside the contract
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
  model and to recovery; recovery's permitted conclusions are a function of them. Layer A's
  `fn2-a-integrity-evidence` (books/assumptions-integrity.lisp) is reused for the checksum premise.
- **B-IDENTITY-EXACT** (ember, 2026-10-28, via the coordinator): exact Message-ID octets are kept
  permanently in the identity metadata with content identity, acceptance binding and conflict
  state; erasure of identities is the operator's matter outside the node's contract; no digest-only
  identity and no aging window (STORAGE-DESIGN §4.6 updated). For this layer: the journal's identity
  records and the identity commitment of the checkpoint claim carry and commit to the exact octets.
- **B-ONE-DSL-OWNER** (coordinator, from the 2026-10-28 review, finding 5/10): layer A owns
  `defcolumns` and `defmachine`; the commit-batch, checkpoint, cleaner and recovery machines are
  declared through A's `defmachine` (A4b) and wait for it; this layer adds no declaration macro.
- **B-LAYOUT-AS-DATA.** On-disk encodings are declared once as constant layouts, lists of
  `(name kind)` in the field-kind vocabulary of A's columns DSL extended with on-disk kinds
  (fixed little-endian, canonical varint, typed identity namespaces, enums, length-prefixed octets,
  digests, zero padding). One generic guard-verified encoder/decoder interprets any layout over a
  pool range; decoded values live in a `defcolumns` fields row; the flat descriptor the ATC lowering
  consumes is the layout constant itself; the list specification `fn2-layout-octets` exists only in
  the logic. Reason: one declaration per encoding without a third DSL; one codec to test and later
  to prove, instead of one generated codec per kind.
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

B2a declares layouts as constant lists of `(name kind)`, interpreted by
`books/layout.lisp`; no declaration macro is added. Enum codes are zero-based
positions in their declared keyword list. Namespace names are part of the
layout descriptor, not extra wire tags; bytes require their enclosing schema
for interpretation. `allocation` is the allocation-counter component; B2c
pairs it with a separately typed `writer-epoch` field.

| Kind | Bytes | Decoded fields row | Format failures |
|---|---|---|---|
| `:u8`, `:u16`, `:u32` | 1, 2, 4 little-endian bytes | `value` | `:truncated`; encode `:value` |
| `:u64` | 8 little-endian bytes, bits 60..63 zero (A-WORD-U60: an on-disk encoding of a u60) | u60 `value` | `:wide`, `:truncated`; encode `:value` |
| `:varint`, `:u60` | shortest unsigned base-128, low groups first | u60 `value` | `:noncanonical`, `:wide`, `:truncated` |
| `(:id NS)` | same canonical varint | u60 `value`; namespace retained in layout | same as varint |
| `:bool` | 0 or 1 | `value` | `:unknown-tag`, `:truncated` |
| `(:enum NAME (kws))` | one declared code byte | numeric `value` | `:unknown-tag`, `:truncated` |
| `(:octets MAX)` | canonical length then exact octets | source handle `ref-slot/ref-gen/ref-off/ref-len` | `:length`, `:noncanonical`, `:truncated` |
| `:digest` | algorithm tag 1 (BLAKE3-256), then 32 bytes | `value=1`, reference to 32 bytes | `:unknown-tag`, `:length`, `:truncated` |
| `(:zero N)` | N zero bytes | zero value, no payload | `:nonzero-padding`, `:truncated` |

Identity namespaces: `history incarnation writer-epoch commit event article
group-number checkpoint allocation storage-domain physical-unit anchor-slot principal
operation table object extent group obligation registration configuration schema key owner`.
A canonical integer exceeding u60 is
scanned through its terminal group and returns `:wide`, retaining its source
bytes. It is not truncated or treated as an unknown field. Its eventual
extension consumer belongs to later storage work. `fn2-layout-max-size` is the
maximum **inline u60 encoding** size, not a bound on extensible persistent
integers. `fn2-layout-fixed-offsets` returns `(name kind-code offset kind)` per
field: the first variable-width field retains its known starting offset;
subsequent offsets are nil.

`fn2-fields-init(n, fields)` allocates the profile's field-position rows.
Columns are `value:u60`, `ref-slot:u32`, `ref-gen:u60`, `ref-off:u32`,
`ref-len:u32`, `status:u8`. Successful fields have status zero; refusal status
is the function's keyword. The extra scalars hold field index, byte position,
partial accumulator, sticky wide-varint flag, payload size/reference, phase and
next offset. `fn2-layout-start(fields)` resets only that continuation.

APIs (the final arguments are stobjs):

- `fn2-layout-encode(layout, slot, gen, off, okind, oslot, ogen, fields, pool)`
  returns `(mv code end pool)`.
- `fn2-layout-decode(layout, slot, gen, off, end, okind, oslot, ogen, fields, pool)`
  returns `(mv code next fields)`.
- `fn2-layout-encode-step` inserts `budget` before `fields, pool` and returns
  `(mv code next fields pool)`; `fn2-layout-decode-step` inserts `budget` there
  and returns `(mv code next fields)`. Budgets are 1..4096. `:more` retains the
  continuation. Keep the layout, source handles and previously read bytes
  unchanged until completion; input `end` may grow as fragments arrive in
  the same readable pool range. A final incomplete range returns `:truncated`.
- `fn2-layout-copy(src-slot, src-gen, src-off, dst-slot, dst-gen, dst-off, len,
  okind, oslot, ogen, pool)` returns `(mv code pool)`. Layer A is adding measured
  range primitives (copy, compare, scan over a handle's range); this shim is
  replaced by them when they merge.
- Logic/test only: `fn2-layout-octets(layout, values)` and
  `fn2-layout-parse(layout, octets)` → `(mv code values rest)`.

One-shot calls admit layouts whose inline maximum is at most 4096, otherwise
`:budget`. A wide integer needing more than 4096 bytes returns `:more`
even from the one-shot decoder; continue with `decode-step` to classify its
terminal group. Decode consumes a prefix and returns its end; canonicality concerns
that consumed prefix. Bounds/stale/state/owner failures retain inputs. Encoding
validates all values, sources and destination before writing, and refuses
source/destination overlap as `:overlap`. Decode retains old row values in
scalar stack bindings and restores them on a late refusal; one byte is read
per transition. Successful zero-copy references retain exact source octets,
including Message-ID octets; physical integrity checking and sealing belong to B2d.

## 6. Format

The layouts in `books/format.lisp` describe field encoding only. The readers in
`books/format-check.lisp` check framing, expected physical identities and integrity hashes.
Neither establishes semantic folding, query completeness, availability, freshness, authority,
or the predecessor-cut restriction (STORAGE-DESIGN §4.4).

### Integrity readers and sealing

`fn2-fc-init(n, fc)` allocates the profile's checker slots. Each row has six continuation
columns and 32 packed u60 words. Initialize at least as many BLAKE3 rows with
`fn2-b3-table-init`, and initialize the required `fn2-fields` capacity once.

The six step exports are `fn2-format-check-frame`, `fn2-format-check-page`,
`fn2-format-check-anchor`, `fn2-format-check-seal`, `fn2-format-seal-frame` and
`fn2-format-seal-batch`. Their shared signature is
`(row slot gen off len base okind oslot ogen budget fc b3 fields pool)`;
they return `(mv code fc b3 fields pool)`. Each has a `-once` form without `budget`,
driving the same machine to completion at budget 4096. All twelve exports are guard-verified.

A step consumes at most `budget` byte transitions, with budgets 1..4096. Decoding,
domain/context input, hashing, padding/geometry checks and digest writes are bounded.
`:more` retains the continuation; terminal statuses reset it. `fn2-fc-reset` abandons it.
The same-numbered BLAKE3 row belongs exclusively to the active checker. Fields rows 0..95
are scratch; decoder state and needed values are saved per checker slot, permitting
interleaving. Each active checker has a distinct immutable expected-context range at
`base >= 96`. Keep arguments, expected values and leased input bytes fixed across `:more`;
a sealer exclusively owns its output range.

| Context offset from base | Expected value |
|---|---|
| 0 | Absolute physical frame/page unit, or anchor slot |
| 1 | Allocation counter |
| 2, 3 | History, incarnation |
| 4, 5 | Writer epoch, commit number |
| 6, 7 | Parent page kind, encoded length |
| 8..15 | Parent expected digest: eight little-endian u32 words |
| 16..23 | Anchor geometry digest: eight little-endian u32 words |
| 24 | Frame extent-allocation writer epoch |

Unused entries still occupy the 25-row context. Oversized digest words refuse `:value`.
Frame hashing is `BLAKE3("fn2/journal-frame/v1" || LE64(physical-frame-unit) ||
LE64(extent-writer-epoch) || LE64(allocation-counter) || exact-frame-with-hash-zeroed)`.
Frames are 4096 bytes. Only the final 32 hash bytes are zeroed; the algorithm tag stays
covered. Header history, incarnation, batch writer epoch, commit and extent-allocation
pair must match; padding must be zero. Moving the frame changes its covered context and
refuses `:bad-hash`. No image is copied to zero a hash field: B2b's scalar byte kernel
receives the preceding bytes, a constant zero run, and subsequent bytes.

Page hashing is `BLAKE3("fn2/physical-page/v1" || exact-encoded-page)`. The checker matches
physical unit, allocation epoch/counter, kind, length and parent hash, plus expected
history/incarnation; it checks header/payload bounds and zero padding. **Storage-domain
binding belongs to the caller's device binding**: B2c's page header has no storage-domain
field, and the page keystone makes no claim about it.

Anchor and sealed-batch domains are `fn2/anchor/v1` and `fn2/sealed-batch/v1`, with their
own final 32 hash bytes zero while hashing. The anchor checker validates slot, geometry,
history/incarnation and canonical framing. The seal covers the entire canonical
`sealed-batch` encoding, including record-stream commitment, dependency references and
root-recipe fields. External referenced bytes require separate commitment checks;
a passing seal alone establishes neither complete-batch availability nor durability.

Success is `:ok`. Refusals include `:bad-magic`, `:bad-hash`, `:wrong-history`,
`:wrong-incarnation`, `:wrong-epoch`, `:wrong-commit`, `:wrong-allocation`,
`:wrong-location`, `:wrong-kind`, `:wrong-length`, `:wrong-slot`, `:wrong-geometry`,
`:nonzero-padding`, `:version`, `:length`, `:value`, `:bounds`, `:state` and `:exhausted`.
Layout/pool refusals, including `:truncated`, `:noncanonical`, `:wide`, `:unknown-tag`
and handle/owner errors, pass through unchanged.

The three binding keystones in `OWED.md` remain unproved. Unit tests evaluate whole
premises and hypothesis-removal witnesses through actual pool operations. Their local
test-only attachment proves the constraint of A's equality witness; it supplies concrete
test values, not evidence about real devices or hash security.

The mutation corpus changes every byte position by XOR 1 in 50 4096-byte frames,
50 128-byte pages, 20 anchors and 20 seals: 224480 refusals and zero accepted mutants.
It does not enumerate all 255 substitutions per position. A separate 65536-byte page
checks budgets 1, 7 and 4096 and corruption beyond the first 4096 bytes and at the last byte.
The parent acceptance measured zero allocation over 10000 seal/check pairs and 3.955
checked MiB/s; that throughput's elapsed time includes both sealing and checking.

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
| sealed-batch | 73 | 489–897 | commit, previous-commit, previous-seal, input-root, event-first, event-last, record-stream, dependencies-storage-domain, dependencies-physical-unit, dependencies-writer-epoch, dependencies-allocation, dependencies-page-kind, dependencies-encoded-length, dependencies-expected-hash, allocation-retirement-storage-domain, allocation-retirement-physical-unit, allocation-retirement-writer-epoch, allocation-retirement-allocation, allocation-retirement-page-kind, allocation-retirement-encoded-length, allocation-retirement-expected-hash, metadata-edits-storage-domain, metadata-edits-physical-unit, metadata-edits-writer-epoch, metadata-edits-allocation, metadata-edits-page-kind, metadata-edits-encoded-length, metadata-edits-expected-hash, output-checkpoint-base-storage-domain, output-checkpoint-base-physical-unit, output-checkpoint-base-writer-epoch, output-checkpoint-base-allocation, output-checkpoint-base-page-kind, output-checkpoint-base-encoded-length, output-checkpoint-base-expected-hash, output-suffix-first, output-suffix-last, output-physical-manifest-storage-domain, output-physical-manifest-physical-unit, output-physical-manifest-writer-epoch, output-physical-manifest-allocation, output-physical-manifest-page-kind, output-physical-manifest-encoded-length, output-physical-manifest-expected-hash, output-allocation-changes-storage-domain, output-allocation-changes-physical-unit, output-allocation-changes-writer-epoch, output-allocation-changes-allocation, output-allocation-changes-page-kind, output-allocation-changes-encoded-length, output-allocation-changes-expected-hash, output-event-frontier-storage-domain, output-event-frontier-physical-unit, output-event-frontier-writer-epoch, output-event-frontier-allocation, output-event-frontier-page-kind, output-event-frontier-encoded-length, output-event-frontier-expected-hash, output-configuration-generations-storage-domain, output-configuration-generations-physical-unit, output-configuration-generations-writer-epoch, output-configuration-generations-allocation, output-configuration-generations-page-kind, output-configuration-generations-encoded-length, output-configuration-generations-expected-hash, event-frontier-storage-domain, event-frontier-physical-unit, event-frontier-writer-epoch, event-frontier-allocation, event-frontier-page-kind, event-frontier-encoded-length, event-frontier-expected-hash, final-seal |
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

`books/alloc.lisp` declares profile-sized extents with FREE/RESERVED/ALLOCATED/RETIRE-PENDING
states (codes 0..3), opaque owner kind/id, writer-epoch/allocation-counter pair, retirement
commit, free-list link, and ten u32 protection counts. Identity references deliberately are not
payload-retention edges; identity-metadata storage is itself protected through its
root/dependency edges. All resident identities/cuts are u60.

Installed-root protects current placement; selectable-checkpoint protects any selectable
checkpoint; recovery-base protects replay infrastructure; prepared-successor protects
uninstalled successors; reservation protects in-progress ownership; obligation protects durable
custody; promised-read protects a BODY/object lease; borrow protects an externally held physical
range; outstanding-io protects a submitted operation until completion or backend exclusion;
recovery-candidate quarantines unresolved recovery candidates. Relocation moves only
installed-root and prepared-successor counts after durable replacement, preserving
promised-read/obligation/borrow and all checkpoint/recovery/I/O/quarantine edges on old physical
locations until explicitly discharged. It neither retires nor frees the old extent.

Reserve requires the completed-epoch flag, consumes a fresh counter and creates its reservation
edge; commit installs the owner and discharges that edge. Retire records a completed retirement
commit. Release requires RETIRE-PENDING, zero counts, and retirement <= installed checkpoint
cut; invoke the FREE transition only when RELEASE_ALLOCATION persistence is established by the
composing machine. Cancellation may discharge its own reservation only after every other
protection ends. Process death/epoch advance never silently removes old I/O edges; backend
evidence is required before dropping them. FREE ownership/id/retirement fields are canonical
zero.

Named refusals are :epoch-not-begun, :epoch-order, :counter-exhausted, :no-space (separate
pressure result), :bounds, :stale, :state, :edge-kind, :reservation-owned, :edge-overflow,
:edge-underflow, :retirement-order, :budget, :checkpoint-order, :checkpoint-blocked,
:replacement-not-durable, :owner, or the first protecting edge keyword. Refusals do not mutate
state. Counter exhaustion requests a new durable epoch; it never wraps.

Maintained state totals and disjoint reason totals make pressure O(1): :ok when FREE or already
release-ready space exists, :checkpoint-blocked when edge-free retired space awaits the
checkpoint, :quarantine when unresolved candidates hold space, otherwise :all-live. With
multiple reasons the priority is that order. :ok release-ready space still needs the release
transaction before reserve succeeds.

Checkpoint publication (B4b, replacing B4a's freezing row walk) processes only the retirement
FIFO's pending suffix, at most 32 extents per call. Retirements must have nondecreasing commit
numbers; a lower commit is refused `:retirement-order`. `fn2-alloc-checkpoint-advance(cut,
budget, table)` returns `:more` with its continuation in the table while covered retirements
remain; reservations, retirement, release and edge updates interleave freely. Processed
edge-free extents move from blocked to ready; protecting edges keep their reason. The published
cut advances only once the pending head exceeds the requested cut or the suffix is empty, so
release still requires retirement <= published cut and no protecting edge (ready accounting
during a continuation is not release authorization). A doubly linked retirement list holds
exactly the RETIRE_PENDING extents and unlinks a released row in O(1). Recovery/machine
orchestration owns continuation after a crash. Measured: a 1,000,000-extent table with 500,000
retirements publishes in 15,625 calls of budget 32 with 1,000 reserve/edge operations
interleaved, none refused.

`sim/check-reclaim.lisp` independently interprets allocation events and reports the first
unsafe release, destructive write, or repeated allocation ID. Initial writes to a matching
RESERVED allocation may carry reservation/outstanding-I/O edges; they are not reuse. Its
list model is test/checker code. The two allocator obligations remain unproved in `OWED.md`;
these functions do not establish persistence or the composing machine’s evidence.

## 8. BLAKE3

`books/blake3.lisp` is the incremental executable reference. `defcolumns` owns
profile-sized hasher rows; each row has scalar continuation columns and 464
u32 words: CV[8], key[8], buffered block[16], frontier[54][8]. The block's 64
bytes are packed little-endian. Only table initialization resizes storage.
The served path shares the scalar compression of `books/blake3-spec.lisp` (the quarry's
`books/blake3.lisp` lifted whole with its two helpers made local, so fn2 has no quarry
dependency); the spec's list functions are the keystones' and tests' reference only.

- `fn2-b3-table-init(n, b3)` allocates; `fn2-b3-init(row, mode, k0..k7, b3)`
  resets a row. Modes are 0 (hash), 16 (keyed), 32 (derive context), 64
  (derive material). Hash/context use the IV; keyed/material use eight key
  words. Derivation hashes the context in mode 32, then uses its eight output
  words as the mode-64 key.
- `fn2-b3-update(row, slot, gen, off, len, okind, oslot, ogen, b3, pool)`
  returns `(mv code consumed b3)`, consuming at most 4096 bytes; `:more`
  means the caller yields and resumes at the returned prefix length. A pool
  refusal retains the successfully consumed prefix. `fn2-b3-read` is the
  single checked byte-access shim for A's future range primitive.
- `fn2-b3-update-const(row, string, off, len, b3)` has the same result for
  constant byte strings, with `len <= 4096`. Physical pages feed
  `"fn2/physical-page/v1"` then their exact encoded bytes, including identity
  context and padding; B2c owns that encoding.
- `fn2-b3-finalize(row, b3)` returns eight u32 multiple values without changing
  the row; later updates remain valid. `fn2-b3-start-subtree(row, counter, b3)`
  sets an empty initialized row's absolute chunk counter, aligned to 64 chunks.
  Feed the block and call `fn2-b3-subtree-cv(row, b3)` for eight non-root words.
- `fn2-b3-parent-cv(l0..l7, r0..r7, k0..k7, flags)` and `fn2-b3-parent-root`
  with the same arguments return eight words using PARENT or PARENT|ROOT.
- `fn2-b3-verify-range(row, base, source-len, block, block-len, d0..d7, b3,
  fields)` returns `(mv code b3)`. Hash the candidate at absolute counter
  `64*block` first. Each source block's eight CV words occupy consecutive
  `fields.value` rows from `base`; fields capacity is a profile resource.
  Verification starts the continuation, then consumes one CV per call until
  `:ok` or refusal. Keep arguments and fields unchanged across `:more`.

Range verification checks the candidate's actual byte count, absolute counter,
position, partial last chunk and expected ROOT digest. A source of at most
65536 bytes uses whole-source finalization, including empty input. Source
length must come from the authenticated descriptor: a sibling CV alone cannot
reveal its byte length. Truncating the candidate or the declared length of its
final block refuses. The verifier uses hash mode; generic hash/parent APIs
also support keyed and derive modes. Both equivalence keystones remain owed.

Cost (seat review): the verifier folds every block CV of the source, so one block's check
costs the block's own hashing plus `ceil(len/65536)-1` parent compressions, and the source's
CVs occupy `8*nblocks` fields rows. A logarithmic sibling path (the subtree CVs along the
block's path in the left-balanced tree) is the later improvement; the manifest's per-block CVs
are sufficient material for either.

Measured in this arm64 ACL2/SBCL executable: 6.774 MiB/s incremental versus
6.821 MiB/s for quarry `fn-blake3`, each hashing the same 300000-byte input
20 times (CPU time). After warmup, 100000 init/update(1025 bytes)/finalize
iterations allocated 0 bytes; this exercises chunk completion and parent ROOT.
All 105 official digests, 2000 random-length/random-split differential cases,
and 306 true range checks passed, with the tested corruptions rejected.

## 9. Event log

`books/merkle.lisp` implements the RFC 6962 append-only binary-tree shape with
BLAKE3-256 as the declared fn2 hash profile. Leaves are `H(0x00 || canonical semantic
record bytes)`; internal nodes are `H(0x01 || left || right)`; the empty root is
`H(empty)`. There is no additional leaf domain string. This retains the standard
prefix rules while selecting BLAKE3 explicitly; SHA-256 interoperability is later work.
Physical pool location is not hashed into a leaf. Callers supply canonical semantic
encodings; this primitive does not validate their semantic schema.

`fn2-mk-table-init(n, log)` allocates a profile-sized `defcolumns` table. Each row
carries u60 size, proof continuation columns and 520 u32 words: 60 frontier roots and
proof workspace. `fn2-mk-init(row, log)` resets the frontier and proof continuation.
`fn2-mk-append(row, d0..d7, log)` returns `(mv code log)` and performs one full node hash
per binary carry, at most 60. `fn2-mk-root(row, log)` returns eight digest words, folding
occupied levels small to large with each larger subtree on the left. Append refuses
`:exhausted` at the resident u60 limit rather than wrapping. The 65-byte node hash uses
B2b's scalar compression twice with CHUNK_START and CHUNK_END|ROOT; it is a complete
BLAKE3 hash, not BLAKE3's internal parent-CV operation.

`fn2-mk-leaf-start(b3row, b3)` initializes the hasher and feeds the leaf prefix (the caller owns the pairing of hasher row and log row; seat review removed a reuse of the BLAKE3 row's verify-target column for it).
`fn2-mk-leaf(slot, gen, off, len, okind, oslot, ogen, b3row, b3, pool)` returns
`(mv code b3)`, consuming at most 4096 record bytes per call. Repeat identical arguments
and unchanged input bytes on `:more`; after `:ok`, `fn2-b3-finalize(b3row, b3)` returns
the leaf's eight words. The active leaf owns that BLAKE3 row.

Proof verification follows [RFC 9162 §§2.1.3.2 and 2.1.4.2](https://www.rfc-editor.org/rfc/rfc9162.html#section-2.1.3.2).
The APIs are `fn2-mk-verify-inclusion(row, index, size, d0..d7, base, count, r0..r7,
log, fields)` and `fn2-mk-verify-consistency(row, old, new, base, count, o0..o7,
n0..n7, log, fields)`, returning `(mv code log)`. Proof nodes occupy eight consecutive
`fields.value` rows each, from `base`. One call consumes at most one sibling and two
node hashes. Fixed arguments are checked on resume; proof fields stay immutable.
`:more` retains continuation, and `fn2-mk-proof-reset(row, log)` cancels it without
changing the frontier. `:state` preserves the active continuation; ordinary completion
and proof refusal clear it. Refusals include `:index`, `:size`, `:proof-length`,
`:proof-word`, `:root-mismatch` and `:state`; leaf input also passes pool refusals through.
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
