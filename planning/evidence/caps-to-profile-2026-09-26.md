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
