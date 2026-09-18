# Store corruption and namespace matrix

Status: executable malformed-image test inventory for
`tests/test_store_corruption.py`. It closes concrete detection coverage around
the immutable-file adapter's recovery scan. It does not turn an arbitrary disk
image into a valid crash outcome, prove the physical adapter correspondence, or
qualify a filesystem, device, or power-failure profile. The recovery contract is
in [store-refinement.md](store-refinement.md#existing-and-missing-adapter-traces)
and the syscall-result matrix is [store-fault-matrix.md](store-fault-matrix.md).

## Method and result classes

Each case creates a real temporary store and accepts real two-group articles
through `tools/run_store.py` and the `Acl2Store` bridge. Corruption is then
applied directly to the local image. A corrupt image is intentionally outside
the normal old-or-new crash choices: the desired result is a detected
`StoreFault`/CLI status 2, not recovery of a diagnostic prefix.

For every malformed-image row, the test invokes `recover`, reader `status` and
`inspect`, and writer `post`. All must fail with the recorded diagnostic, so a
valid prefix cannot be advertised to readers or reused for mutation. Where an
existing final record is relevant, its bytes are compared before and after the
refusal; the adapter does not overwrite or repair it. The tests use ACL2 for
all record decode/replay and article/pin reconstruction. Python only constructs
the intentionally malformed bytes or namespace entry.

The valid uncertain-tail row is different. It uses the adapter's actual
post-publication injected outcome, then a new bridge replays the observed final
files. It proves the exact complete record is retained beside two earlier
accepted crossposts; it does not treat malformed images as crash choices.

## Finite matrix

| Image boundary | Cases | Required result |
| --- | --- | --- |
| Allocation frontier bytes | truncated JSON; checksum mismatch; checksummed boolean `next_txid`; symlink; directory; 4,097-byte oversize file | acquisition refuses before a reader or writer can open; original final article bytes remain unchanged |
| Configuration/history consistency | config checksum mismatch; correctly checksummed but unsupported profile; frontier 1 behind two committed records | reader and writer refuse; the history is not silently replayed as a shorter usable prefix |
| Framed final record | declared frame length one octet too large; integrity trailer mismatch; complete frame containing unknown schema bytes | ACL2/adapter decode path faults; no reader or writer opens the prefix |
| Final namespace | a contiguous filename whose decoded record sequence differs; collision at the intended next final name | recovery faults on the mismatch; `publish` returns `StoreIndeterminate` without changing the colliding file |
| Valid multiple-commit uncertainty | two acknowledged two-group crossposts followed by `postpublish` uncertainty | fresh ACL2 replay contains all three articles, three pins, six reserved units, both group counters at 4, and frontier 3 |
| Metadata-to-read change | frontier is changed to truncated JSON after `check_regular` has observed it but before the bounded read | acquire faults and releases its writer lock; later reader and writer calls still refuse the corrupt image |

There are 16 finite malformed/uncertain rows: six frontier, three
configuration/history, three frame, two namespace, one valid uncertain-tail,
and one metadata-to-read change. They complement, rather than replace, the
earlier basic truncation/checksum/schema/symlink and frontier-boundary checks in
`tests/test_store.py` by requiring all public reader and writer entry points to
refuse every malformed image and by exercising the previously missing collision,
decoded-sequence, multi-prior-tail, and metadata-to-read cases.

## Adapter recovery inventory

| Recovery observation in `tools/run_store.py` | Matrix coverage | Deliberately not claimed |
| --- | --- | --- |
| `_load_config`: regular-path check, bounded JSON read, checksum and exact-profile check | checksum and exact-profile refusal | every JSON type/value mutation and configuration migration |
| `_load_frontier`: regular-path check, 4,096-byte bound, JSON/checksum/range validation | truncation, checksum, boolean/range, symlink, nonregular, oversize, and history-behind-frontier relation | every integer boundary and a durable allocator-replacement proof |
| `transaction_files`: exact names, non-symlink regular entries, contiguous sequence names | collision creates a second exact name; decoded sequence mismatch remains unusable | `scandir` I/O and every unexpected-name/non-file form, which have separate basic coverage |
| `durable_records`: bounded final read, frame check, ACL2 record sequence | length, digest, schema, and filename/decoded-sequence mismatch | all byte corruptions, checksum-collision attacks, or a proof of frame canonicality |
| `recover`: ACL2 replay plus frontier advance | frontier behind two committed records and valid replay of two prior commits plus an uncertain tail | freshness against replacement by an older wholly valid store |
| metadata check followed by content use | forced check-then-corrupt frontier change refuses and releases ownership | a TOCTOU proof, hostile local filesystem model, or concurrent administrator safety |

## Limits

These are deliberate bad-image tests and one process-visible uncertainty test.
They do not establish that a completed barrier survives loss of power, that a
partially written file has any particular contents after a crash, that checksums
authenticate hostile storage, or that an old entirely valid store is detected.
They also do not cover hardware/media loss, filesystem rollback, storage
compaction/checkpoints, all concurrent namespace races, or a general trace
theorem. Passing this matrix is testing evidence, not an ACL2 proof or a
freshness/durability claim.
