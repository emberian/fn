# caps-to-profile: the three data caps become profile capacities or work bounds (2026-09-26)

Lane `caps-to-profile` (wave 4), branch `lane/caps-to-profile` from dev
`deb68237` (friends-accounts merged: the tenth configuration slot). PRF-171,
STO-023, SCN-101, PKT-451 (PKT-452 unused: no format bump). D27: bound work,
never data.

## 1. The decision table

| Cap | Today | Class after | Governed by | Format bump? | Rollback consequence |
| --- | --- | --- | --- | --- | --- |
| (A) `*fn-cpp-max-generations*` 4096, checkpoint-publish.lisp:323; packs checkpoint-pack-retire.lisp:8-32 | a LIFETIME cap on generation numbers: nothing reclaims a number, so a store gets 4,096 checkpoint (or pack/compaction) publications | the number is the u32 codec width (iii), as the frontier's; the RETAINED names are a capacity of the profile's T | field 2 `max-transactions` (existing): the next generation exists while fewer than T+1 names are retained and the number is below 2^32-1; the host's listing bound is T+2 (names plus the selection marker) | **no**: generation names are already decimal u32 (`fn-cpp-generation-name-chars` takes any `fn-record-uint32p`), the selection marker is already one CBOR uint32 | an older image reads every directory this lane writes while it holds at most 4,096 names below 4096; a store that has published generation 4096 or above refuses to open under an older image (its namespace plan refuses the name `:bound`/exhausted): the same class as PKT-440 |
| (B) `*fn-cfg-max-rows*` 1024 through `:set-peer`, config.lisp:51/:724 | DATA: `:set-peer` replaces the whole row group, carriage grows it, so one peer holds at most 1,024 rows / 65,538 octets | WORK: 1,024 rows per delta, 64 deltas and 65,538 octets per record, a per-publication bound; the peer's total grows by records | the record count by field 11 (`fn-cvec-config-generations`, `fn-cvec-config-publication-keeps-the-release-generation`), octets by H | **no** (config delta codes 17 and 18, as friends-accounts added 15 and 16; schema-0 records decode unchanged: they are their own translation) | an older image refuses a store whose configuration log holds code 17 or 18 (PKT-440's class); a store that never extended a peer past its first request is unaffected |
| (C) the group-name width: field 7 has no reader; `*fn-record-max-group-name*` / `*fn-cfg-max-label*` 256 | a hidden constant: a profile with field 7 = 100 admits a 256-octet name | DATA governed by field 7; the codec widths rise to the wire's 460 (RFC 3977 section 3.1, a protocol bound, iii) | field 7 `max-group-name-octets` (existing), read by `group create` (`:max-group-name-octets`) | **no**: community-bounds' design (section 3): the ceiling takes field 7, validity only weakens, the format-7 translation keeps 256 | none for a store whose names are at most 256; a name above 256 is refused by an older image's record codec |

Rejected for (A): reclaiming retired numbers. `fn-cprt-next-after-retirement-is-above-selected`
(checkpoint-pack-retire.lisp:184) makes the selected generation a durable
high-water mark, the crash model (`fn-cprt-crash-survivors`) lets an issued
unlink of an older name survive a crash before the directory barrier, so a
reused number could meet a surviving file of the same name; and the ordinary
checkpoint allocator's gap-free contract (`fn-cpp-next-generation-from`) has
no gaps to reuse. Monotone numbering is load-bearing; widening it to the u32
width is not.

Rejected for (B): a profile field for rows per peer (PKT-436's rejected
alternative: a format change that still keeps one peer inside one record).

Rejected for all: a store format 9. Every quantity this lane needs is either
an existing field (T for A, field 7 for C) or a work bound (B). PKT-452 is
therefore not written; the deploy step gains nothing and ember hears nothing.

## 2. (B) A peer's rows: the work bound per delta (PRF-171)

Commit `9755f664`. books/config.lisp: `:add-peer-rows` (code 17) and
`:remove-peer-rows` (code 18), constructors `fn-cfg-add-peer-rows` /
`fn-cfg-remove-peer-rows`, the row arithmetic `fn-cfg-rows-without-members`
and `fn-cfg-rows-within`. `fn-cfg-delta-reason` names every refusal:
`:peer-rows-empty`, `:peer-rows-unkeyed`, `:no-such-peer`, `:peer-row-absent`
(a removal of a row the group does not hold), `:peer-rows-emptied` (a removal
may not empty a peer; that is `:remove-peer`). `fn-cfg-apply-delta`: an add
leaves the group less the repeated rows followed by the new ones; a removal
drops exactly the listed rows. books/peer-carriage-rows.lisp:
`fn-pcb-extend-deltas NAME NEW PEERS` = the add of NEW, then the removal of
the rows a single-valued slot of NEW supersedes (`fn-pcb-slot-superseded-rows`),
only when there are any. books/native-admin.lisp
`fn-native-admin-plan-deltas-over` emits it.

Theorems (books/peer-carriage-rows.lisp):

- `fn-pcb-extend-deltas-apply-as-the-extend-delta`: `(implies (and
  (true-listp new) (fn-cfg-rows-keyed-p new name)) (equal (fn-cfg-apply v gen
  stamp (fn-pcb-extend-deltas name new (fn-cfg-peers v))) (fn-cfg-apply-delta
  v gen stamp (fn-pcb-extend-delta name new (fn-cfg-peers v)))))`. The
  published record applies as the old whole-group `:set-peer`, so PRF-099's
  `fn-pcb-peer-budget-after-extend-delta` holds of it. (A third hypothesis,
  that the peer exists, was removed after the weakened theorem was proved:
  both sides are the value unchanged when it does not.)
- `fn-cfg-add-peer-rows-refuses-exactly-past-the-work-bound`: for a label
  NAME, a row list ROWS that is non-empty and keyed on NAME, and a peer that
  exists, `(fn-cfg-delta-reason v gen stamp reserved ceiling
  (fn-cfg-add-peer-rows name rows))` is `(if (< *fn-cfg-max-rows* (len rows))
  :malformed-delta nil)`.
- `fn-cfg-add-peer-rows-extends-the-group`: with ROWS a true list keyed on
  NAME, the group after the delta is `(append (fn-cfg-rows-without-members
  existing rows) rows)`: no bound but the records that built it.
- `fn-cfg-apply-delta-adds-at-most-the-work-bound` (linear): every
  `fn-cfg-deltap` delta grows the peers slot by at most 1,024 rows;
  `fn-cfg-apply-adds-at-most-the-work-bound`: a delta list by at most 1,024
  times its length (a record holds at most `*fn-cfg-max-deltas*`; the record
  count is `max-config-generations`, `fn-cvec-config-publication-keeps-the-
  release-generation`, cited).

Host lines: `fn-native-admin-plan-deltas-over` is called by
host/native-admin-host.lisp `fn-native-admin-host-apply` (offline, the
replayed table) and `fn-native-admin-host-owner-reconfigure` (the live
owner's table); the record is admitted by `fn-store-cfg-peer-delta-record`
(host/store-node-host.lisp) through `fn-cnode-record-acceptablep`, and
replayed at open by `fn-cfg-record-acceptablep` / `fn-cfg-apply-record`, the
same `fn-cfg-delta-reason` and `fn-cfg-apply-delta`.

Teeth (tests/acl2/peer-carriage-tests.lisp, PRF-171 section): a peer of 1,025
rows takes one more (1,026, every earlier row kept); a 1,024-row delta is
admitted and a 1,025-row one is `:malformed-delta`; one refusal per
hypothesis of the exact-bound keystone (a 257-octet name, a non-uint32 row, no
rows, unkeyed rows, no such peer); must-fails for the keyed and true-list
hypotheses of the extension keystone and of the refinement keystone (rows
keyed on another peer apply in another order; an improper row list); the
work bound reached by exactly 1,024 rows and passed by a malformed 1,025;
the budget request's two deltas (add, then remove the two old budget rows),
admitted, equal to the whole-group extension, budget (5 3); the two new
refusals; codes 17 and 18 round-trip and a record holding both encodes and
decodes to itself. tests/acl2/native-admin-tests.lisp: the `peer budget` and
`peer carries` plans publish the incremental deltas, and applied give the
answers the whole-group delta gave.

Replay and translation: codes 1 to 16 decode exactly as before (the decoder
is unchanged on them; friends-accounts' 279-octet literal test keeps checking
the old kinds byte-identically), so a schema-0 `:set-peer` record is its own
translation; nothing at open rewrites anything.

Assurance chain: native entry `operator CONFIG peer carries|budget` ->
`fn-native-admin-plan` -> `fn-native-admin-plan-deltas-over` ->
`fn-pcb-extend-deltas` -> refinement `fn-pcb-extend-deltas-apply-as-the-
extend-delta` -> the admitted record (`fn-cfg-delta-reason`, exact bound) ->
`fn-cfg-add-peer-rows-extends-the-group` -> observed: `peer list` after a
fresh open (SCN-101). The maintained relation is `fn-cfg-valuep` (the peers
slot a row list): `fn-cfg-apply-delta-preserves-valuep`
(books/config-invariants.lisp) covers both new arms.

## 3. (A) Checkpoint generations: uint32 numbering, profile capacity (PRF-171)

Commit `e10e4530`. books/checkpoint-publish.lisp: `*fn-cpp-max-generations*`
and the constant observation limit are gone; `fn-cpp-generation-capacity T` =
T + 1; `fn-cpp-namespace-observation-limit CAPACITY` = CAPACITY + 1 (the
selection marker); `fn-cpp-next-generation(-from)`, `fn-cpp-namespace-plan`
and `fn-cpp-publication-initial` take CAPACITY.
books/checkpoint-pack-retire.lisp: `fn-cprt-generationsp` is the strictly
increasing uint32 shape (no length cap); `fn-cprt-next-generation GENERATIONS
CAPACITY` refuses `:exhausted` at CAPACITY retained names; `fn-cprt-next-from`
numbers to the uint32 maximum. Host: host/checkpoint-host.lisp
`fn-store-checkpoint-generation-capacity VALUES` (the opened profile's T + 1)
and every namespace wrapper take the profile; host/native/checkpoint.lisp
passes `(fnn-store-config store)` and refuses by name ("checkpoint
generations at the profile's capacity (max-transactions + 1)", and for packs
"retire older generations or raise it"); tools/checkpoint.py passes
`store.config["profile"]`.

Theorems:

- `fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`:
  `(implies (and (not (equal (fn-cpp-next-generation names capacity) :bad))
  (<= (nfix capacity) (+ 1 *fn-cbor-max-uint*))) (equal
  (fn-cpp-next-generation names capacity) (if (<= (nfix capacity) (len
  names)) :exhausted (len names))))`. Host: `fnn-checkpoint-publish` ->
  `fn-store-checkpoint-next-generation` and
  `fn-store-checkpoint-publication-initial`.
- `fn-cprt-next-generation-refuses-exactly-at-the-profile-capacity`: on
  `fn-cprt-generationsp`, `:exhausted` exactly at CAPACITY retained names or
  a highest name at the uint32 maximum, else the highest plus one. Host:
  `fnn-pack-publish-generation` -> `fn-store-checkpoint-pack-next-generation`
  and `-pack-publication-initial`.
- Carried unchanged in statement: `fn-cprt-next-after-retirement-is-above-
  selected` (now with the CAPACITY argument), the durable high-water mark.
  PRF-085's chain keystones (books/checkpoint-pack-chain.lisp) are untouched.

Teeth: 4,097 retained names under T 8191 give 4097; the old figure is the
instance T 4095 (capacity 4096: 4,096 names exhausted, 4,095 names give
4095); a gapped namespace is `:bad` (must-fail for that hypothesis); the
uint32 width (must-fail past it); packs: `(70000)` under capacity 2 gives
70001, two names exhausted, `(4294967294)` gives 4294967295, the maximum is
exhausted, an unordered list is `:invalid` (must-fail).

Rollback: an older image refuses a checkpoint or pack directory holding a
name at or above 4096 (its generations-after-p / next-from) or more than
4,097 entries (its observation limit). Nothing is written at open.

## 4. (C) The group-name width: NOT touched

This lane did not edit books/records-shape.lisp or books/byte-store-frame.lisp.
The design stands as community-bounds section 3 wrote it and is PKT-451, a
freeze batch the deputy schedules.
