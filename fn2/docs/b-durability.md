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
| the on-disk format as layouts; Merkle event log | `fn2/books/format.lisp` | B2c |
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
| `:u64` | 8 little-endian bytes | low u32 `value`, upper u32 `hi` | `:truncated`; encode `:value` |
| `:varint`, `:u60` | shortest unsigned base-128, low groups first | u60 `value` | `:noncanonical`, `:wide`, `:truncated` |
| `(:id NS)` | same canonical varint | u60 `value`; namespace retained in layout | same as varint |
| `:bool` | 0 or 1 | `value` | `:unknown-tag`, `:truncated` |
| `(:enum NAME (kws))` | one declared code byte | numeric `value` | `:unknown-tag`, `:truncated` |
| `(:octets MAX)` | canonical length then exact octets | source handle `ref-slot/ref-gen/ref-off/ref-len` | `:length`, `:noncanonical`, `:truncated` |
| `:digest` | algorithm tag 1 (BLAKE3-256), then 32 bytes | `value=1`, reference to 32 bytes | `:unknown-tag`, `:length`, `:truncated` |
| `(:zero N)` | N zero bytes | zero value, no payload | `:nonzero-padding`, `:truncated` |

Identity namespaces: `history incarnation writer-epoch commit event article
group-number checkpoint allocation`. A canonical integer exceeding u60 is
scanned through its terminal group and returns `:wide`, retaining its source
bytes. It is not truncated or treated as an unknown field. Its eventual
extension consumer belongs to later storage work. `fn2-layout-max-size` is the
maximum **inline u60 encoding** size, not a bound on extensible persistent
integers. `fn2-layout-fixed-offsets` returns `(name kind-code offset kind)` per
field: the first variable-width field retains its known starting offset;
subsequent offsets are nil.

`fn2-fields-init(n, fields)` allocates the profile's field-position rows.
Columns are `value:u60`, `hi:u32`, `ref-slot:u32`, `ref-gen:u60`, `ref-off:u32`,
`ref-len:u32`, `status:u8`. Successful fields have status zero; refusal status
is the function's keyword. The extra scalars hold field index, byte position,
partial accumulator, high half/wide flag, payload size/reference, phase and
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
including Message-ID octets; integrity verification remains B2b/B2c work.
