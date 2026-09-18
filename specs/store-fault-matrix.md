# Real-file storage fault matrix

Status: executable adapter test inventory. This document records what
`tests/test_store_fault_matrix.py` injects against `tools/run_store.py`; it is
not a proof of the storage refinement and it does not qualify a filesystem,
device, or power-failure profile. It supplements the experiment's existing
fault evidence rather than changing the adapter contract in
[store-experiment.md](store-experiment.md) or the refinement obligations in
[store-refinement.md](store-refinement.md).

## Test method

Every row starts with a real temporary store containing one already acknowledged
two-group article (`PRIOR`), opened through the real `Acl2Store` bridge. The
test then reserves a new transaction ID with the real allocator, prepares a
new two-group record in ACL2, and injects exactly one host failure. It checks
the raised public host result, the live `Store.fenced` mutation gate, and the
same host object where recovery is legal. It finally reopens from the directory
and invokes ACL2 replay again.

For every recovered image, the test asserts that `PRIOR` has the same payload,
one archive pin, and both group allocations. Where a new final record is
visible, it asserts the complete two-group record, one additional pin, and both
group counters together. The tests decode only the ACL2-produced records to
observe their txids; they do not reproduce acceptance or replay in Python.

`after` means the wrapper invokes the real syscall/helper first and then raises.
`before` raises first. A staging `create-after` wrapper closes the newly created
descriptor before it raises, leaving only an ignored staging orphan. The adapter
has no distinct buffered `flush` operation: `write_all` uses `os.write`, and its
file durability boundary is `fsync_file`/`os.fsync`. Recovery's existing files
are rebarriered through `fsync_regular`/`os.fsync`.

## Enumerated matrix

| Boundary | Injected cases | Public result and immediate fence | Observed recovered state |
| --- | --- | --- | --- |
| Transaction staging create (`os.open`) | before, after | `StoreError`; gate remains open because no final-name attempt occurred | only `PRIOR`; frontier advances from 1 to 2 after the already completed allocator reservation |
| Transaction staging write helper (`write_all`) | before, after | `StoreError`; gate remains open | only `PRIOR`; a later real post gets txid 2, so the aborted txid 1 is not reused |
| Transaction staging short/failed `os.write` | partial then `EIO`; partial then `ENOSPC`; zero progress | `StoreError`; gate remains open | only `PRIOR`, with the reserved txid consumed by the known abort |
| Transaction staging file fsync/flush boundary (`fsync_file`) | before, after | `StoreError`; gate remains open | only `PRIOR`; same nonreuse assertion, including the after-file-fsync staging orphan case |
| Transaction staging close (`os.close`) | actual close then `EIO` | `StoreError`; gate remains open | only `PRIOR`; a close after staging data still precedes final-name authority |
| Final hard link (`os.link`) | before, after | `StoreIndeterminate`; gate closes and rejects `advance_frontier` | before: only `PRIOR`; after: `PRIOR` plus exactly the new crosspost, both groups and both pins present |
| Transaction directory barrier (`fsync_dir(transactions)`) | before, after | `StoreIndeterminate`; gate closes | complete new crosspost replays in both cases because the hard link was already performed; recovery re-establishes barriers before use |
| Post-barrier staging cleanup | `os.unlink` error; staging-directory fsync error after actual call | returns `durable`; gate stays open | final crosspost and `PRIOR` replay; cleanup cannot revoke a final record |
| Allocator staging create (`os.open`) | before, after | `StoreError`; gate remains open | frontier remains 1, then an actual retry consumes txid 1 and advances frontier to 2 |
| Allocator staging short/failed `os.write` | partial then `EIO`; partial then `ENOSPC`; zero progress | `StoreError`; gate remains open | same retry result; incomplete replacement staging is not allocator authority |
| Allocator staging file fsync/flush (`fsync_file`) | before, after | `StoreError`; gate remains open | same retry result; no replacement was attempted |
| Allocator staging close (`os.close`) | actual close then `EIO` | `StoreError`; gate remains open | same retry result; no replacement was attempted |
| Allocator replacement (`os.replace`) | before, after | `StoreIndeterminate`; gate closes | before: frontier remains 1; after: actual replacement is reread as frontier 2 through the same object and after reopen |
| Allocator directory barrier (`fsync_dir(root)`) | before, after | `StoreIndeterminate`; gate closes | replacement was already visible, so recovered frontier is 2 in both rows; `PRIOR` remains unchanged |
| Recovery transaction read (`read_regular_bounded`) | before, after | raw `OSError`; recovery leaves an already live object fenced | a later same-object recovery succeeds, then a fresh ACL2 bridge sees exactly `PRIOR` and frontier 1 |
| Recovery config and frontier file barriers | `fsync_regular` before and after each file's real call | `StoreIndeterminate`; recovery leaves the object fenced | later same-object recovery and a fresh reopen both see exactly `PRIOR` and frontier 1 |
| Recovery transactions/root/parent directory barriers | `fsync_dir` before and after each real call | `StoreIndeterminate`; recovery leaves the object fenced | later same-object recovery and a fresh reopen both see exactly `PRIOR` and frontier 1 |
| Recovery helper closes | actual `os.close` then `EIO` for transaction read, config regular-file barrier, and transactions directory barrier | read close gives raw `OSError`; barrier closes give `StoreIndeterminate`; every case fences | later same-object recovery and a fresh reopen both see exactly `PRIOR` and frontier 1 |
| Completion return | durable completion returns `fault` | `StoreIndeterminate`; host is fenced and emits no success; its closed owner later rejects mutation as `StoreError` | published new crosspost is replayed with `PRIOR`, two articles/two pins, and frontier 2 |
| Completion loss | real ACL2 durable completion occurs, wrapper then raises | `StoreIndeterminate`; host is fenced and emits no success; its closed owner later rejects mutation as `StoreError` | the same replay result as completion return; loss of a reply does not revoke the final record |
| Store lock close after a completed command | actual writer or reader `os.close(lock_fd)` then `EIO` | direct `command_post` or `command_status` caller receives `OSError` after its normal output was produced | a fresh reopen sees the durable state: `PRIOR` plus the writer crosspost, or `PRIOR` alone for the reader |

The test has 47 injected rows: ten transaction-staging rows, four publication
attempt/barrier rows, two cleanup rows, twelve allocator rows, twelve recovery
read/rebarrier rows, three recovery-helper-close rows, two completion rows, and
two store-lock-close rows. The
publication-attempt rows exercise recovery through the same `Store`/ACL2 bridge
and then a fresh reopen. Known prepublication failures exercise their same-object
known-abort path before the reopen; they do not claim that recovery was needed.
Existing
`tests/test_store.py` retains separate coverage for initialization/configuration
barriers, no-visible-name link EIO, frontiers ahead/behind committed history,
corruption and namespace rejection, lock contention, and CLI pre/post-publication
injection. This matrix intentionally concentrates on the previously separate
before/after effect cases, write-progress failures, and all five recovery
rebarriers.

## Adapter callsite ledger

The following is a source-level inventory of the current file adapter's direct
syscall/helper boundaries. “Matrix” means this file injects that branch;
“existing” names coverage retained in `tests/test_store.py`; “uncovered” means
neither claim is made here.

| Callsites in `tools/run_store.py` | Status in this matrix | Explicitly skipped branch or qualification |
| --- | --- | --- |
| `fsync_dir`: its own `os.open`/`os.fsync`/`os.close` helper body | Matrix exercises errors returned by the helper at publication, allocator, cleanup, and each recovery directory target; it directly injects a post-effect close for the recovery transactions directory | Descriptor-open and kernel-fsync substeps are not independently injected; one direct close representative is used because every recovery directory error has the same fenced result class |
| `fsync_file`: `os.fsync` for newly staged config/frontier/allocator/transaction files | Matrix: transaction and allocator staging before/after helper results | Initialization config/frontier file staging remains existing coverage; no claim about a device completing fsync then reporting an error |
| `write_all`: repeated `os.write` | Matrix: helper-level transaction failures and partial `EIO`, partial `ENOSPC`, and zero-progress writes for both transaction and allocator staging | No exhaustive short-write length schedule; the chosen positive partial write is enough to execute the retry branch before failure |
| `read_regular_bounded`: no-follow `os.open`, repeated `os.read`, final `os.close` | Matrix: recovery helper result before/after a transaction read plus a direct post-effect transaction-read close error | Descriptor-open and individual read-chunk failures are not independently separated; this is not a TOCTOU or kernel read-semantics test |
| `fsync_regular`: no-follow `os.open`, `os.fsync`, final `os.close` | Matrix: before/after helper results for config and frontier recovery files plus a direct post-effect config-barrier close error | Descriptor-open and kernel-fsync substeps are not individually faulted; recovery uses the same fence on any helper error |
| `_safe_directory`: `lstat`, `mkdir`, parent directory barrier | Existing initialization/configuration coverage only | Root/transactions/staging creation and `mkdir` failures are outside the bounded post/recovery matrix |
| `_open_lock`: lock `os.open`, `fstat`, `flock`, close-on-refusal | Existing lock-contention coverage; matrix covers final successful writer and reader lock `os.close` errors | Lock creation/open/fstat/flock and error cleanup combinations remain uncovered |
| `initialize`: exclusive config/frontier `os.open`, write, file barrier, close, root and final five barriers | Existing failed-config-file-barrier coverage | Frontier initialization branches, directory creation/barrier substeps, and initialization lock-close errors remain uncovered |
| `advance_frontier`: staging create/write/fsync/close, `os.replace`, root barrier | Matrix covers every listed operation's caller-visible failure branch before/at/after replacement | Staging-orphan cleanup is intentionally absent from this method; allocator stage names remain non-authoritative |
| `publish`: staging create/write/fsync/close, optional injected prepublish unlink/barrier, link, transactions barrier, best-effort staging unlink/barrier | Matrix covers create/write/fsync/close, link, transaction barrier, and both cleanup operations | The CLI-only `prepublish` synthetic branch is existing coverage; final-name collision and actual `unlink` success durability are not separately injected here |
| `_require_writer`: writable mode plus a live exclusive lock before `advance_frontier`/`publish` | Completion rows observe a closed owner refusing further mutation | Read-only and independently closed mutator cases are covered by `tests/test_store_lifecycle.py` |
| `recover`: final namespace scan/read and config/frontier plus transactions/root/parent rebarriers | Matrix covers one final-record read and all five rebarrier targets before/after helper results | `scandir`, filename validation, frame/ACL2 decode/replay refusal, and malformed namespace inputs remain existing corruption/bounds coverage |
| command payload `read_regular_bounded`, ACL2 process I/O and `Acl2Store.close` | Uncovered here | These are host input/process failures, not storage-adapter mutation boundaries; completion return/loss remains covered at the bridge result boundary |
| `Store.close`: unlock then lock `os.close` | Matrix covers after-effect writer close after a committed post and reader close after a status result | Unlock failure remains uncovered; a close result cannot establish or revoke the already published record |

## Interpretation and limits

These observations exercise process-visible outcomes under one injected call at
a time. They establish neither the old-or-new namespace hypothesis nor the
durability of a completed barrier. In particular, they do not cover torn or
reordered unsynced writes, power loss, kernel/filesystem crash behavior,
hardware write caches, concurrent out-of-band modification, hard-link/rename
semantics on platforms other than this development profile, corruption that
preserves the checksum, whole-store rollback to an older valid snapshot, full
disk accounting, segment packing/checkpoints/compaction, or arbitrary multi-step
fault traces. Abrupt child-process kill cases are deliberately outside this file
and belong to their dedicated test owner.

The `after` cases model an exception after a call returns to the wrapper, not a
claim that the operating system actually performed the effect before reporting
an error. The physical correspondence, platform assumptions, and required
general trace theorems remain the open work listed in
[store-refinement.md](store-refinement.md#existing-and-missing-adapter-traces).
