# fn2 storage design: the angles (2026-10-28)

The storage study the execution model leaves open (`fn2/EXECUTION-MODEL.md` §7.1 and §7.4). Brief:
`build/coordinator/briefs/STORAGE-DESIGN-20261028.md`. Ember, verbatim: "we need to be very careful and think importantly now about
how we can achieve an efficient storage design, using lessons of postgres, tahoe-lafs, and other data layers. ... No compile-time
ceilings. Yah immutable log-structured is a good idea but is it really the BEST idea? let's analyze a few angles on it." And:
platforms are never refused; fn2 documents what it requires of a filesystem or device.

This file gives arguments and tables. It does not vote. Figures follow `fn2/ENVELOPE-AND-HOST.md`'s tags: **[M]** measured (the
measurement is cited), **[D]** derived here by arithmetic from stated inputs, **[A]** an assumption with its basis. Nothing was
built or run for this study. Papers are cited by `~/paperbin/` filename. fn documents are cited by path under
`~/dev/fn/build/coordinator/` unless the path says otherwise. Specs are cited at `origin/dev` (`git show origin/dev:specs/storage.md`).

Layout: §0 states the workload and the designs; sections A-L are the brief's twelve angles, each with a table across the
designs; §12 is the scorecard, §13 the recommendation with its two strongest objections and the hybrid, §14 the measurements that
would decide between the top two and the five decisions left to ember.

Fetched into `~/paperbin` for this study (downloads are data; the Tahoe paper's publisher PDF was refused, so its text was taken
from the Scry academic corpus record `academic:10.1145/1456469.1456474`): `wilcoxohearn2008-tahoe-least-authority-filesystem.txt`,
`tahoelafs2026-docs-{architecture,mutable,file-encoding,uri,dirnodes,outline}.rst`, `postgresql2026-docs-*.txt` (twelve chapters:
page layout, TOAST, visibility map, free-space map, HOT, file layout, WAL intro/reliability/internals/configuration, MVCC intro,
routine vacuuming), `sqlite2026-docs-{wal,atomiccommit,fileformat2,psow}.txt`, `kafka2026-docs-design.md`,
`sheehy2010-bitcask-log-structured-hash-table.{pdf,txt}`, `zhou2021-foundationdb-unbundled-transactional-kv-store.{pdf,txt}`,
`rosenblum1992-design-implementation-log-structured-file-system.{pdf,txt}`. Already present and used: `chu2012-lmdb-*`,
`mohan1992-aries-*`, `oneil1996-*`, `lu2016-wisckey-*`, `dong2021-rocksdb-*`, `tigerbeetle2026-*`, `crotty2022-*`,
`rebello2020-*`, `zheng2014-*`, `alagappan2018-*`, `haas2023-*`, `chajed2021-*`, `chajed2022-*`.

The constraints every design must meet come from the execution model, and they are not reargued here. Rule 6: persistent
references name extents and blocks, never addresses, and the core owns every lease. Rule 8: one ordered commit stream per storage
domain, the commit machine `collect → seal → dependencies → log-write → fence → durable → install → publish → notify → draining`,
`uncertain` as a persistent state, the recovery classes `intact / torn tail / damaged / unknown`, the three assumptions
`A-PERSISTENCE-FENCE`, `A-INTEGRITY-EVIDENCE`, `A-INDEPENDENT-FRONTIER`, and cleaning and checkpoints going through the same
protocol. Rule 9: persistent namespaces are paged through bounded caches, and resident capacity bounds active execution state only.
The authority rule is STO-001 (`specs/storage.md`): "committed journal/checkpoint state is authoritative. Lookup indexes are
derived from it."

## 0. The workload, and the designs

### 0.1 What fn2 stores and how it is used (the facts carried into every angle)

| object | size, rate, count | access | mutation | source |
|---|---|---|---|---|
| article (record: 64 B header + ~70 B Message-ID and groups + ~200 B injected headers + body) | typical POST 2 KiB, so a ~2.4 KiB record [D]; up to 16 MiB (default ceiling 1 MiB); 100-1,000 POSTs/s design range; 1M articles the sizing case | ARTICLE/HEAD/BODY/STAT by (group, number) and by Message-ID; 16 concurrent readers is the gauntlet case | never changed; withdrawal is an appended event (CNS-008) | ENVELOPE §1.3, §1.6; CLIENTS §1.1 |
| overview entry | ~300 B per article [A] | XOVER/OVER ranges within one group; `XOVER 1-1000000000` is a resumable cursor over a pinned selection | written once | ENVELOPE §1.4; EXECUTION-MODEL §2 |
| Message-ID binding | 1 per article; mean 40 B ID, 250 B max | insert-if-absent with three answers (stored, duplicate, conflict; D25); an absent probe is the common peering case (IHAVE/CHECK) | insert only | ENVELOPE §1.6; CLIENTS §2.2 item 3 |
| group membership and numbers | ~1.5 groups per article [A]; numbers are never reused | number→article, low/high/count per group | append per group | ENVELOPE §1.6; STO-010 table |
| consumer cursor and ack | 32 B row; 4,096 consumers in the default preset; akapug's fleet is ~30 seats on 4 boxes | read per poll; written per ack, forward only, idempotent on equal | small, hot, frequent | CLIENTS §1.1, §1.2; ENVELOPE §1.8 |
| accounts, principals, limits, subscriptions, per-principal charges | small rows | read on every admission | charges change on every admitted operation (rule 5: reserve before issuing, settle on completion) | EXECUTION-MODEL rule 5 |
| retention pins (`:archive`, `:forward`, proposed `:checkpoint`) | per object or per range | checked by reclamation | released only by evidence | CLIENTS §2.2 item 6; issue #17 |
| statements, keyring evidence | small; "kept forever" today | lookup by (issuer, subject, kind) wanted | append; supersession | STO-010 table; CLIENTS §2.2 item 5 |
| replicated streams | peers pull by stream; BP carries portable batches | sequential per stream | append | CLIENTS §1.5 |

Four workload facts shape every angle below:

1. **Writes are append-mostly and immutable.** Articles, statements, withdrawals, releases and acceptance evidence are written
   once. The only in-place state is the small hot set (cursors, accounts, charges, subscriptions, limits, per-signer heads).
2. **Reads are point reads plus short ranges.** Point reads come by number within a group and by Message-ID. Ranges are
   per-group (XOVER) or per-stream (consumer poll, peer pull). There is no ad-hoc query.
3. **Versions must be pinnable cheaply and for a long time.** A connection reads at a pinned version (F_node's
   `fn-ideal-pinned-archive`, CLIENTS §3.1). A 16 MiB BODY at the stall floor of 4,096 B/s (ENVELOPE §1.8, `send stall`)
   streams for up to **4,096 s, about 68 minutes** [D: 16 MiB / 4,096 B/s]. A resumable XOVER cursor spans many turns. So "how
   much does a stalled reader hold" is a first-order question, not a corner case.
4. **Expiry retires whole ranges, but range boundaries differ by group.** Retention is per group and settable live (STO-038;
   akapug's need #1 in CLIENTS §1.2). Release is evidence-gated: a pinned article outlives its group's expiry.

The rates, in the four resources (ENVELOPE §1.1, §1.5): a flush is 4.0 ms on client NVMe and 8.35 ms on hbox ZFS-on-HDD [M].
Group commit keeps flushes at or below 1/t_f, whatever the POST rate. At 1,000 POSTs/s the payload is ~2.4 MB/s. **The device
pays in flushes and IOPS, not bytes.** akapug's fleet is 0.08 rows/s on average [D], so it is the λ → 0 row, where every commit
is a batch of one. A design must be good at b = 1 (latency, write amplification of a lone small commit) and at b = 8-64
(throughput). Many designs are good at only one of the two.

### 0.2 The designs

Each design is named by a letter. The table below names the reference implementation each draws on.

| | design | in one sentence | references |
|---|---|---|---|
| **L** | append-only log with derived indexes | the log of records is the only authority; every index is a fold over it, rebuilt at open or checkpointed; space comes back by dropping or cleaning segments | fn1's record log (`fn2/INTERFACES-TODAY.md` §2: FNLG frames, 32-octet chained trailers); Bitcask (`sheehy2010-bitcask-log-structured-hash-table.pdf`: a resident "keydir", "hint files", "merge"); Kafka segments (`kafka2026-docs-design.md`); Sprite LFS cleaning (`rosenblum1992-design-implementation-log-structured-file-system.pdf`) |
| **G** | log-structured, with an LSM over a grid | one data file of fixed-size grid blocks addressed by (index, checksum); a superblock with 4 copies; a WAL ring of prepares; LSM trees whose tables are grid blocks; incremental compaction paced per beat; blocks freed only at a checkpoint and only when no snapshot sees them | `tigerbeetle2026-internals-data-file.md`, `tigerbeetle2026-internals-lsm.md`, `tigerbeetle2026-architecture.md`; O'Neil (`oneil1996-log-structured-merge-tree.pdf`); WiscKey value separation (`lu2016-wisckey-separating-keys-values.pdf`); RocksDB (`dong2021-rocksdb-evolution-development-priorities.pdf`) |
| **P** | heap pages plus WAL with MVCC | in-place 8 KiB pages holding tuple versions stamped with transaction IDs; a WAL written first; checkpoints; full-page images against torn pages; vacuum; a visibility map; TOAST for wide values | `postgresql2026-docs-storage-page-layout.txt`, `-storage-toast.txt`, `-storage-vm.txt`, `-storage-hot.txt`, `-wal-intro.txt`, `-wal-reliability.txt`, `-wal-configuration.txt`, `-mvcc-intro.txt`, `-routine-vacuuming.txt`; ARIES (`mohan1992-aries-recovery-method.pdf`) |
| **C** | copy-on-write B+tree with two root slots | every commit copies the root-to-leaf paths it changes into free pages and then switches one of two meta pages; a single writer; readers never block; no WAL, no compaction; freed pages are reused once no reader can see them | LMDB (`chu2012-lmdb-memory-mapped-database-openldap.pdf`); fn1's page store `pgs-` (`fn2/INTERFACES-TODAY.md` §3a, with keystones `pgs-open-after-commit`, `pgs-open-after-crash`, `pgs-fork-isolation`) |
| **T** | content-addressed immutable objects with capabilities | objects named by a hash of their content; a verify-cap (check integrity without reading), a read-cap (read), and for mutable slots a write-cap; signed, sequence-numbered versions; Merkle trees over segments; erasure-coded shares across servers; servers delete shares whose leases have all lapsed | Tahoe-LAFS (`wilcoxohearn2008-tahoe-least-authority-filesystem.txt`, `tahoelafs2026-docs-architecture.rst`, `-mutable.rst`, `-file-encoding.rst`, `-uri.rst`) |
| **V** | event log plus materialized views | the log is the truth; mutable keyed state (cursors, accounts) is a fold over the log, materialized and checkpointed; keyed logs are compacted to the last value per key | Kafka compacted topics (`kafka2026-docs-design.md`, "Log Compaction"); FoundationDB's log servers + storage servers (`zhou2021-foundationdb-unbundled-transactional-kv-store.pdf`); issue #17's "the log overrides" |
| **H1** | log for articles, page store for the hot state | L (or V) for everything immutable; C or P for the small mutable tables | FDB's storage server: "an unversioned SQLite B-tree and in-memory multi-versioned redo log data" (zhou2021, §2.4) |
| **H2** | per-group (or per-retention-class) segments | each group's records go to that group's own extent chain, so expiry drops whole extents | Kafka partitions; Postgres partition DETACH/DROP (`postgresql2026-docs-routine-vacuuming.txt` discusses the per-row alternative) |
| **H3** | SQLite-style WAL with checkpoint-into-main | commits append page images to a WAL; readers consult a WAL index and then the main file; a checkpoint copies WAL pages into the main file in place, stopping at any active reader's end mark | `sqlite2026-docs-wal.txt`, `sqlite2026-docs-atomiccommit.txt`, `sqlite2026-docs-psow.txt` |

Two of these are not storage engines. **T** is a naming, integrity and authority discipline. Something else (one of L, G, C, P)
still has to say where the bytes for a hash live and how a (group, number) finds that hash. **V** is a semantics for mutable
state over a log. Its physical form is L for the log plus one of C, P or G for the materialized view. Both are analysed as the
layer they are, and section 13 composes them.

## A. Write, read and space amplification for the actual workload

Common inputs: 4 KiB sectors; a ~2.4 KiB record for a 2 KiB POST; ~390 B of derived index per article (64 B row + ~12 B of
per-group number entries + 12 B membership + ~300 B overview) [D, ENVELOPE §1.6]; 1M articles, 1.5 groups each; b is the
group-commit batch (b = 1 at akapug's rate and at one closed-loop poster; b ≈ 4.5-9 at 1,000/s, ENVELOPE §1.5). "Write amp"
counts device bytes per byte of record, at steady state, including everything the design will eventually write for that record
(log, home location, index pages, page images, compaction). B-tree page counts assume a depth-3 tree with cached internals [A].

### A.1 Write amplification per 2 KiB POST

| design | b = 1 | b = 8 | where the bytes go | the mechanism that dominates |
|---|---|---|---|---|
| **L** | ~1.9x | ~1.3x | the record once (4 KiB sector at b = 1, ~2.65 KiB at b = 8: the tail pad is paid once per batch), plus ~390 B of append-only columns at checkpoint (only tail blocks are dirty); the Message-ID table is rebuilt at open and never written | the tail pad at b = 1. Cleaning adds `u/(1-u)` bytes copied per byte freed when expiry is not time-ordered (LFS, rosenblum1992 §3.4: write cost `2/(1-u)`) and **0** when whole segments retire |
| **G** (TigerBeetle shape) | ~2.8-4.4x | ~2.2-3.4x | the prepare into the WAL ring (1.1-1.7x), the record again into the grid when the WAL is checkpointed (~1x), plus the index trees' compaction: a random-keyed Message-ID tree of ~24 B entries at a leveled write amp of ~10-16 [A: growth factor 8, 3-4 populated levels] is ~0.2x, an overview tree keyed by (group, number) moves ~300 B per level, ~0.5-1x | the double write (WAL ring is not the permanent home) and overview compaction. If bodies sit inside LSM tables rather than separated blob blocks, the body is rewritten at every level: ~10x. **Value separation is not optional for G** (lu2016 §3). A G variant whose blob blocks are written directly to the grid in the commit's dependency phase, with the WAL carrying references only (ENVELOPE §1.3), removes the body's second write and lands near L |
| **P** (Postgres shape) | ~3-5x | ~2.5-4x | WAL (~1x, but Postgres rewrites a partly filled 8 KiB WAL page at each group commit, which fn2's "never overwrite a still-required sector" forbids); the heap at checkpoint (~1x; a 2.4 KiB row exceeds `TOAST_TUPLE_THRESHOLD` "normally 2 kB", so the body is compressed or moved to ~2,000 B TOAST chunks, `postgresql2026-docs-storage-toast.txt` §66.2.1); a full-page image of 8 KiB at the first change of each index leaf after a checkpoint (`postgresql2026-docs-wal-configuration.txt`: "the first modification of a data page after each checkpoint results in logging the entire page content"), then the leaf itself; one more heap rewrite by the anti-wraparound freeze (`postgresql2026-docs-routine-vacuuming.txt` §24.1.5) | random Message-ID B-tree inserts: at 1M articles the ID index is ~7k leaves [D: 1M × ~40 B / (8 KiB × 0.7)]; at 100 POSTs/s and a 5-minute checkpoint, 30k inserts dirty nearly every leaf, so ~56 MiB of page images plus ~56 MiB of leaf writes per 30k articles, ~3.8 KiB per article [D]. At 1,000/s the same leaves amortize to ~0.4 KiB |
| **C** (LMDB shape) | ~18x | ~7x | per commit: the body as an overflow page (2.4 KiB rounds up to 4 KiB; LMDB stores values over about half a page out of line [A]), the copied right spine of the sequence tree (3 pages), a copied path in the Message-ID tree per insert (b distinct leaves plus shared internals), a copied path per touched group in the (group, number) tree, and a 4 KiB meta page | path copying for random keys; at b = 1, ~44 KiB written for a 2.4 KiB record [D]. LMDB also issues **two** syncs per commit (data pages, then the meta page) [A: the documented LMDB commit order]. fn1's `pgs-` page store uses 16 KiB pages (`INTERFACES-TODAY` §3a), four times worse per copied page |
| **T** | substrate + ~0.1x | substrate + ~0.1x | a Merkle tree over 64 KiB segments (32 B per segment) and a ~200 B extension block per object; on a peer group with K-of-N erasure coding, `N/K` (3.3x at Tahoe's default 3-of-10, wilcoxohearn2008 §1) | the substrate it sits on |
| **V** | as L, plus ~40 B per keyed update | as L | the log; a keyed delta record (~40 B) per cursor or account change; the materialized table at checkpoint (whole small tables are cheaper to rewrite than to diff) | the checkpoint interval, for the view |
| **H1** | ~1.9x | ~1.3x | L for articles; the hot state's own pages at checkpoint | as L |
| **H2** | ~1.9-3.3x | ~1.3-1.5x | L, but a batch touching g lanes pays g tail pads | the extra tail pads when a batch spans several segment chains; at b = 1 with the article in one lane and its commit record in the shared journal, ~8 KiB for 2.4 KiB (3.3x) unless the journal is the default lane (then 1.9x) |
| **H3** (SQLite WAL) | ~7-13x | ~4-6x | each commit appends every modified page (body overflow + the leaf of each tree) to the WAL, ~16 KiB at b = 1, and the checkpoint writes them again into the main file, minus pages changed twice between checkpoints (the right-most leaves) | whole-page WAL frames for sub-page changes, then the second write |

Reading the table: **for immutable small records, every page-oriented design pays for the page, and every log-oriented design
pays only for the record.** The gap is largest exactly where fn2's first clients live (b = 1). C's gap closes only when commits
are large and keys are sequential (LMDB's `MDB_APPEND` case), which is the article sequence tree but not the Message-ID tree.

### A.2 Read amplification

Reads are counted in device operations, because NVMe pays per IOPS before it pays per byte (a 64 KiB read and a 4 KiB read cost
about the same ~80-100 µs at QD1 [A, `haas2023-modern-nvme-storage-exploit.pdf`]). "Warm" means index blocks are cached and the
payload is not; "cold" means nothing is cached.

| design | ARTICLE by number, warm / cold | ARTICLE by Message-ID, warm / cold | XOVER 1-1000 in a group that gets 0.1% of traffic | 16 MiB BODY |
|---|---|---|---|---|
| **L** | 1 / 3 (per-group number block, row block, record sector) | 1 / 2 (resident hash, row block, record) | **up to ~1,000 reads** if overview entries are kept in global commit order: the group's 1,000 entries are spread across ~300 MB of other groups' overview [D: 1,000 × 1,000 articles × 300 B]. ~5 reads with a per-group overview layout | 256 sequential 64 KiB reads of a contiguous blob extent (1x) |
| **G** | 1 / 2-3 (manifest resident; one value block per probed level, ~1 with disjoint monotone ranges) | 1 + filter false positives / 2-3 | ~5 reads once compacted (the tree is keyed by (group, number)); the recent part is in the mutable/immutable tables | 1x with value separation; without it, the body sits inside tables and is read whole |
| **P** | 1-2 / 3-4 (index leaf, heap page, TOAST index leaf, TOAST page) | same | ~1,000 heap pages: heap order is insertion order and the (group, number) index has low correlation, unless the table is `CLUSTER`ed (a one-time rewrite) | ~8,400 TOAST chunk rows of ~2,000 B, ~2,100 page fetches, near 1x in bytes |
| **C** | 1 / 2 (leaf, overflow pages) | 1-2 / 3 (ID-tree leaf, then the sequence tree leaf, then overflow) | ~5 leaves if the (group, number) tree holds overview values inline (300 B fits) | one contiguous overflow run of 4,096 pages, 1x, if the free list can supply a contiguous run (LMDB scans its free list for one [A]) |
| **T** | the substrate's, plus the hash-tree path once per object | (the hash is the name: one index probe) | the substrate's | 1x with streaming verification: each 64 KiB segment is verified against the tree as it arrives (wilcoxohearn2008 §4.3: "the reader can verify the correctness of part of the file without downloading the entire file") |
| **H3** | C's, plus a WAL-index probe in memory | C's | C's | C's; SQLite warns that WAL "does not work well for very large transactions" (`sqlite2026-docs-wal.txt`) |

**Finding A-1 (new against ENVELOPE §1.4).** The envelope's "OVER-40 touches 1-2 blocks" holds only for a busy group, or when
overview entries are clustered by group. A per-group range in a global commit-order pool costs one block per entry for a sparse
group, the same correlation problem Postgres has between heap order and index order. Every design that answers XOVER well
clusters overview by (group, number) somewhere: G by compaction, C by key order, H2 by placement. In L this is the one place where
"append in commit order and derive" is not enough by itself (§13 resolves it with a one-step re-clustering of aged overview).

### A.3 Space amplification

| design | steady state | transient | what it costs to get space back |
|---|---|---|---|
| **L** | ~1.0x of records plus permanent tail pads (1.7x for lone 2.4 KiB commits, since a sector holding acknowledged data is never rewritten, ENVELOPE §1.3) | withdrawn and expired records stay until their segment is dropped or cleaned | free when retirement is time-ordered (drop the oldest segments, Kafka's `retention.ms` deletion); `u/(1-u)` copying otherwise |
| **G** | ~1.1x for leveled index trees [A]; blobs as in L; a fixed WAL ring | compaction's inputs and outputs coexist until the inputs are invisible to every snapshot | compaction, paced per beat (tigerbeetle2026-internals-lsm.md, "Compaction") |
| **P** | ~1.2-1.5x (page fill factor, tuple headers, TOAST and index overhead) [A] | dead tuples until vacuum; for append-only articles there are almost none; for hot state, one per update | vacuum; space returns to the free-space map, not to the file system, except by `VACUUM FULL` |
| **C** | ~1.0x for append-ordered trees, ~1.4-2x for random-keyed ones (half-full leaves) [A]; overflow values round up to whole pages | pages freed after the oldest live reader's snapshot cannot be reused (section C) | free-list reuse; the file never shrinks |
| **T** | 1x on one node; `N/K` across a peer group | none | per-object deletion when every lease has lapsed (`tahoelafs2026-docs-architecture.rst`, "Leases, Refreshing, Garbage Collection") |
| **H3** | C's, plus the WAL | the WAL grows while a reader pins an old end mark (section C) | checkpoint, then WAL reset |

## B. Crash recovery: cost at open, the tougher fault model, and how damage is detected

The tougher fault model is ENVELOPE §2.5's 22 rows, drawn from the crash-model table in `~/paperbin/README-fn2-20261028.md`.
The rows that separate the designs are corruption at rest (1, 6), misdirected writes and reads (3, 4), a write that is lost after
the flush reported `:ok` (5), tearing inside the unit (10), and in-flight writes that complete in any order under direct I/O (11).
Rule 8's recovery classes are `intact / torn tail / damaged / unknown`. Rule 8 also requires that recovery "never silently
chooses a shorter history".

### B.1 Cost at open

| design | what open does | cost at 1M articles [D] | grows with |
|---|---|---|---|
| **L** | read the superblock (4 copies, quorum 2); load the checkpointed columns; replay the log tail since the checkpoint; rebuild the Message-ID table from the rows (EXECUTION-MODEL §6 ruling: start with rebuild-at-open) | tail ≤ 64 MiB at ~2 GB/s ≈ 30 ms; rebuild ~0.1 s (ENVELOPE §1.6) | the checkpoint interval (bounded) and **the store size** (the rebuild: ~1 s at 10M, ~10 s at 100M) |
| **G** | read the superblock quorum, then the manifest and free set through the checksummed references; replay the WAL ring's prepares since the checkpoint (`tigerbeetle2026-internals-data-file.md`) | WAL ring replay (bounded by the ring); manifest load | the ring and the manifest (O(tables)) |
| **P** | ARIES redo from the last checkpoint's redo point (`mohan1992-aries-recovery-method.pdf`; `postgresql2026-docs-wal-intro.txt`) | WAL since the checkpoint; Postgres has no undo pass because old tuple versions stay in the heap | `max_wal_size` / `checkpoint_timeout` |
| **C** | pick the newer valid meta page; nothing to replay | one or two page reads: **constant** | nothing |
| **T** | nothing for the objects; the naming index is the substrate's | the substrate's | the substrate's |
| **V** | load the checkpointed views; replay deltas since the checkpoint | as L, minus the rebuild if the views include the ID index | the interval |
| **H3** | scan the WAL frames from the header, accept frames up to the last valid commit frame (cumulative checksums with the header's salts), rebuild the WAL index (`sqlite2026-docs-wal.txt`) | the WAL, bounded by the autocheckpoint at 1,000 pages | the WAL |

### B.2 What the tougher fault model does to each, and how each detects damage

| design | checksum placement | torn write (row 10) | misdirected write or read (rows 3, 4) | lost write after `:ok` flush (row 5) | out-of-order completion (row 11) | telling a torn tail from mid-log damage (row 20) |
|---|---|---|---|---|---|---|
| **L** (fn1 today) | per-entry chained 32-octet trailer over the previous trailer (`INTERFACES-TODAY` §2); in fn2, also a per-record checksum held in its row, outside the record (ENVELOPE §1.6) | detected by the trailer; only the unacknowledged batch can tear, because acknowledged sectors are never rewritten | detected when the reference carries the checksum (row → record); the chain alone detects it only at scan time | **a lost batch in the middle is detected** (its successor's chain link fails); **a lost tail is not**, unless an independent witness names the frontier (`A-INDEPENDENT-FRONTIER`) | harmless: commit is gated on all completions, then one flush (ENVELOPE §2.5, "The commit rule") | possible: a mid-log failure followed by a valid later batch whose chain names a predecessor is `damaged`, not `torn tail` |
| **G** | every block's checksum is held by its parent (block reference = (index u64, checksum u128)); the superblock carries its own checksum, read with a 4-copy quorum of 2 because "a misdirected read can hide the single latest copy" (tigerbeetle2026-internals-data-file.md) | detected | **detected** by the parent's checksum and the block's own address in its header | detected for any block reached through a parent (a stale block fails the parent's checksum); a lost superblock write falls back to the previous quorum | harmless: the superblock is written only after the blocks it names are durable | yes: TigerBeetle's repair distinguishes and repairs from replicas (`alagappan2018-protocol-aware-recovery-consensus-storage.pdf`) |
| **P** | a checksum inside each data page (default on; `postgresql2026-docs-wal-reliability.txt`: "Data pages are checksummed by default, and full page images recorded in WAL records are always checksum protected"); WAL records carry CRCs | **repaired** from the full-page image in WAL (that is what FPW is for, same file); without FPW a torn page is unrecoverable | partly: the page checksum mixes in the block number [A: Postgres's checksum algorithm], so a page read from another block of the same relation fails; a page from another relation or file may not | **not detected**: a stale page has a valid checksum. Postgres's post-fsyncgate rule is to PANIC on fsync failure (Rebello, `rebello2020-can-applications-recover-fsync-failures.pdf`), which handles reported failures, not silent ones | handled by ordering WAL before data (pageLSN), not by checksums | WAL records are chained by LSN with CRCs; a bad record ends redo, and Postgres treats it as the end of WAL |
| **C** (LMDB) | **none** (LMDB trusts the file system) [A: LMDB has no page checksums] | the meta-page switch is the atomic step; a torn data page under the new root is silent corruption unless the meta write was ordered after the data sync (hence two syncs) | silent | silent | needs the two-sync order: data pages durable before the meta page | n/a |
| **C with checksummed pointers** (ZFS shape; what fn2 would build) | each page's checksum held in its parent; the root's in the meta slot | detected; fall back to the other meta slot | detected | **detected for every block on the path from the root** (the parent holds the expected checksum, so a stale child fails) | **one flush suffices**: if the new root landed and a child did not, the child fails its checksum and open falls back to the older slot; the commit was not acknowledged | n/a (no log) |
| **T** | the name is the hash; every byte verified against it | detected | detected (wrong content fails its name) | detected when referenced; a whole lost object is "unavailable", repairable from any holder of the same content | harmless | n/a |
| **H3** | cumulative checksums over WAL frames, salted per WAL generation; **main-file pages have none** | WAL: detected; main file: the checkpoint overwrites pages in place, so SQLite depends on the device's powersafe-overwrite property (`sqlite2026-docs-psow.txt`) or a journal | silent in the main file | silent in the main file | needs WAL sync before checkpoint and main-file sync before WAL reset (`sqlite2026-docs-wal.txt`) | ends the WAL at the first bad frame |

What the table says:

- **The decisive property is where the checksum lives, not which structure is used.** A checksum inside a block detects only
  tearing and bit rot. A checksum held by the block's parent also detects misdirection and stale (lost) writes, for every block
  reached through that parent. TigerBeetle's grid and ZFS's block pointers do this; fn1's chained trailers do it for the log's
  order; LMDB, SQLite's main file and Postgres's heap do not. fn2 can put parent-held checksums on any of L, G, C, V, and should,
  whatever else it picks.
- **Open cost separates C from everyone else, but only up to a constant.** C opens in two page reads; L and V pay a bounded tail
  replay plus whatever is not checkpointed. The one unbounded term in the whole table is L's rebuild-at-open of the Message-ID
  table, which grows with the store. The EXECUTION-MODEL §6 ruling accepts it as the starting point and the repair path; rule 9
  and angle L below put a size on when it stops being acceptable.
- **A lost tail batch is undetectable by any single-node structure** without an independent witness: the newest valid state
  always looks like a plausible shorter history. G's quorum of superblock copies helps against misdirected reads, not against a
  device that lost the last flush. This is `A-INDEPENDENT-FRONTIER` (rule 8), and the only real witnesses are outside the
  device: a peer's receipt, a client's signed receipt (Mini's receipts, CLIENTS §1.1), a second device. Section G's Merkle log
  is what makes those witnesses cheap to check.

## C. Pinned-version reads under concurrent commits and under cleaning

Two things hide under the word "pin", and the designs differ mainly in whether they keep them apart:

- a **visibility pin**: the version a connection reads at, so its answers are a function of its own octets and that version
  (F_node's connection isolation, CLIENTS §3.4). In fn1 it is `(id, wire, session, version)` with `version ≤ generation`;
- a **byte lease**: the specific extents a reply is reading or sending (rule 6: "sends and writes lend immutable bytes whose reuse
  waits for every external borrow to end").

The stall case for every row: one reader streams a 16 MiB BODY at the stall floor of 4,096 B/s, so it holds its pin and leases for
**4,096 s** [D]. Concurrent load: 1,000 POSTs/s plus 100 hot-state commits/s (acks, charges) [A, the top of the design range].

| design | who pins what | what cleaning or reuse must wait for | worst-case space held by the stalled reader [D] |
|---|---|---|---|
| **L** | a visibility pin is a number: rows with `seq ≥ count(v)` are invisible, and a withdrawal is an appended event stamped with its version, so `visible-at(seq, v)` is a column check (fn1's `fn-cat-visible-at`, INTERFACES-TODAY §4). Leases name extents | (a) **lease-only**: an extent is reusable when no lease names it; (b) **epoch**: payload released at version w is reusable when no visibility pin is older than w | (a) the one article: ≤ A (16 MiB at the ceiling), so ≤ C × A in total (1 GiB at C = 1,024 and A = 1 MiB). (b) everything released since the pin: with time-ordered expiry at 1,000 POSTs/s, ~2.4 MB/s × 4,096 s ≈ **9.8 GB**; at akapug's 14 MB/day, ~0.7 MB |
| **G** | a snapshot number; a table is visible to S when `snapshot_min ≤ S ≤ snapshot_max`; compaction copies, never modifies (tigerbeetle2026-internals-lsm.md, "Snapshots and Compaction") | input tables are removed only when "invisible to all current and persisted snapshots" | every compaction input written during the stall: ~1 KiB of index compaction per POST × 1,000/s × 4,096 s ≈ **4 GB**, plus blobs as in L. TigerBeetle's queries are short and its persistent snapshots are a "TODO" in that document, so long pinned reads are outside its design |
| **P** | a snapshot's `xmin` horizon | vacuum cannot remove any tuple dead after the oldest snapshot, in any table | the hot state's dead versions: 100 updates/s × 4,096 s × ~100 B ≈ **40 MB** plus index bloat. Append-only articles create no dead tuples, so Postgres's horizon costs little here |
| **C** (LMDB) | a reader transaction pins its root | no page freed after the reader's snapshot can be reused ("Older versions can be held open longer by reader transactions", chu2012) | every page every later commit copied: ~17 KiB per article at b = 8 (A.1) × 1,000/s × 4,096 s ≈ **70 GB**, plus ~1.2 MB/s of hot-state paths (another ~4.9 GB). **The file grows by the whole write stream for as long as the reader lives.** This is LMDB's known long-reader growth |
| **C, split** (separate trees per class; a reply leases its overflow pages and drops its root after selection) | the selection is read under the root; the bytes under leases | reuse waits for leases, and for roots only as long as selections take | as L (a) |
| **T** | references to objects; Tahoe servers delete only shares whose leases have all lapsed | leases | the object |
| **V** | views (cursors, accounts) are read at latest, not at a pinned version; FoundationDB makes the same choice with "a 5-second MVCC window to limit the memory usage" (zhou2021 §6.4) | nothing, for the views | 0 for the views; the log as L |
| **H3** | a reader's WAL end mark | "the checkpoint must stop when it reaches a page in the WAL that is past the end mark of any current reader" (sqlite2026-docs-wal.txt) | the whole WAL written during the stall: ~16 KiB per commit × 1,000/s × 4,096 s ≈ **64 GB**, and every reader's lookup slows as the WAL grows |

What the table says:

1. **Append-only data with version-stamped events makes visibility pins free.** A pinned version is a number compared against
   columns that never change meaning. This is why L, V and T pay nothing for pinning, and why P pays little for its append-only
   tables. C and H3 pay for pins in space because their pages are rewritten. G pays because compaction rewrites.
2. **Byte leases are the only thing that must hold space, and they are bounded by the reply.** A reply leases the extents it is
   sending. With L's option (a), a stalled reader costs at most its article. With option (b), every pin holds back all
   reclamation since that pin. Option (b) is simpler to state ("reclaim only below the oldest pin"), but its worst case is set by
   the slowest reader on the node.
3. **The semantic choice under (a) has to be made explicitly.** If the reader at version v has not yet begun to read article r, and
   r's payload is reclaimed after its release at a version w > v, then the reader's pinned view still lists r, but r's bytes
   are gone. That is the same situation as the consumer's "explicit `unavailable` gap" (CNS rules, CLIENTS §2.1), and it can be stated
   the same way: a pinned version guarantees visibility decisions and identity, and guarantees payload bytes only for what the
   connection has leased. The alternative is (b) with a **bounded pin age**: a version pin older than a profile value is rebased
   with a named outcome, as FoundationDB bounds its window and as fn1's consumers rebase on a view change. Both are bounded;
   §13 recommends (a) for payloads, with (b) kept for the metadata that visibility decisions read.
4. **The hot state should not be readable at old versions.** Cursors and accounts are read at latest by the machines that change
   them. Keeping them versioned (P, C) is what makes long readers expensive in those designs. Keeping them unversioned and
   checkpointed (V) costs nothing.

## D. Retention and expiry

What fn2 must do (STO-010's lifetime table, `specs/storage.md`; issue #17; CLIENTS §2.2 items 6 and 8):

- retire payloads whose retention has passed, per group, with retention settable on a running node;
- never retire a payload that a pin holds (`:archive`, `:forward`, and #17's proposed `:checkpoint`): "release only by an explicit
  predicate over committed evidence; independent pins survive one another's release";
- keep identities after bodies are gone: the Message-ID binding, content identity, each group's number high-water (numbers are never
  reused), and the D13 anti-resurrection summary, which STO-010 makes the precondition of both history compaction (H) and content
  reclamation (C);
- give a crossposted article the lifetime of its longest-lived membership.

So the reclamation predicate, whatever the design, is: **a payload is releasable when every membership's retention has passed,
no pin covers it, and no lease names its extent.** A storage unit (segment, extent, table, page) is reusable when every payload in
it is releasable, or has been moved.

| design | a whole time range of one group | mixed retention in the same storage unit | pins | identities after the body | operator cost model |
|---|---|---|---|---|---|
| **L** (one journal) | a cheap drop **only if** the oldest segments hold nothing else: true when every group shares one retention | the unit holds records with different lifetimes, so it waits for the longest or is **cleaned** (copy the survivors forward, as an ordinary committed move record): Sprite LFS's cost-benefit policy, cleaning the segment that maximises `(1-u) × age / (1+u)` (rosenblum1992 §3.6). A 1-day group interleaved with a 30-day group holds ~30x the 1-day group's volume unless cleaned [D] | a pinned record is one more survivor to move | rows and Message-ID bindings stay (~100 B per article [D: 64 B row + ~40 B of ID]); the payload locator becomes "reclaimed" by an appended event | cleaning cost `u/(1-u)` per byte freed; zero when expiry is uniform |
| **H2** (segments per retention class) | a drop of whole extents in that class's chain | does not arise inside a class. A crosspost is placed in the class of its longest-lived group; the shorter group's expiry removes only its membership entries. A live retention change leaves old records in the old class, where they become survivors to move when that class's oldest extent drops | survivors moved, cost proportional to the pinned bytes | as L | cost proportional to pinned or reclassified bytes, not to the store |
| **G** | a range tombstone over (group, number), reclaimed when compaction reaches the bottom level [A: RocksDB-style range deletes]; separated blobs need their own collection (WiscKey's value-log GC, lu2016 §3.3), which is L's cleaning again. TigerBeetle has no bulk expiry (a ledger keeps everything) | as the blobs' collection | as L | tombstones and identities must persist below every level | compaction plus blob collection |
| **P** | per-row `DELETE`: one WAL record per row, a dead tuple per row, index cleanup by vacuum: O(rows) | same, per row | per row | the row stays; the TOAST value can be dropped | O(rows) WAL and vacuum. Time-range **partitions** make expiry a `DROP`, which is H2 inside Postgres |
| **C** | per-key delete: a copied path per key: O(rows × depth) | same | per key | the key stays with a "reclaimed" value | O(rows) page copies; no range drop, but freed pages are reused without compaction |
| **T** | per object: Tahoe servers delete a share once every lease on it has lapsed (`tahoelafs2026-docs-architecture.rst`) | per object | a pin is a lease that only evidence can cancel (Tahoe's leases lapse by time; fn's pins do not) | the hash outlives the object as a name; "unavailable" is a first-class answer | per object, metadata only |
| **V** (Kafka) | `retention.ms` deletes whole segments of a partition, oldest first: L's cheap case, which works because a partition's retention is uniform and time-ordered | keyed topics are compacted to "at least the last update for each primary key" (kafka2026-docs-design.md, "Log Compaction") | none | **Kafka drops tombstones** after `delete.retention.ms` ("the default is 24 hours"), so "it is possible for a consumer to miss delete markers if it lags". fn2 must not copy this: a withdrawal and the anti-resurrection summary are kept for as long as anything could re-offer the identity | segment deletion plus per-key compaction |

What the table says:

1. **Every design that makes expiry cheap does it the same way: it places together what dies together.** Kafka's partitions,
   Postgres's partitions, H2's class chains and L's "oldest segments first" are one idea. Designs that interleave lifetimes in a
   storage unit (L with mixed groups, C, P without partitions) pay per row or per byte moved.
2. **The axis is retention class, not group.** Per-group chains (one per group) would give 4,096-65,536 chains, each with a
   partly filled tail block resident or dirty: 4,096 × 64 KiB = 256 MiB of tails [D], and a batch spanning many groups pays a tail
   pad per chain. Per-class chains keep the count to the number of distinct retention policies an operator configures (a handful),
   and the default deployment (one policy) has exactly one chain, which is L.
3. **Identity survives in all designs at ~100 B per article** [D]. That is 100 MB per 1M articles, forever, unless D13's summary
   compresses it (a sorted run of Message-ID digests is 16-32 B per identity, or a filter if "probably seen" answers are
   acceptable for a re-offer, which they are not for exact identity, P2). This term, not the payloads, is what grows without
   bound in a long-running node with expiry, and it is a paged structure (angle L), not a resident one.
4. **Pins are cheap in every design only if they are ranges.** A per-article `:archive` pin for 1M articles is a 1M-entry table;
   a pin over (group, low..high) or a sequence range is one row. #17's checkpoint pins are prefix-shaped already
   (`prefix-head, prefix-sequence`). The pin table belongs to the hot state (angle E), keyed by range, with exceptions per object.

## E. The small hot mutable state: where it lives and what one ack costs

The hot set: consumer cursors and registrations (a 32 B row each; 4,096 in the default preset, ENVELOPE §1.8), accounts and
principals, durable charges (rule 5), live limits and configuration generations (STO-038), retention pins (angle D), per-signer
heads for helm's signed records ("an op id, the signing key and the previous head", CLIENTS §1.2), and an operation-identity index
so a retry is answered `replayed` (CLIENTS §2.2 item 3; helm need #2). Wake lists and parked waits are **not** stored: they are
execution state, "state bits or reserved links, never a message queue" (rule 7).

The rate that matters: akapug's fleet at 3-7k rows/day with ~30 seats, each seat acking what it reads, is up to ~210k acks/day,
~2.4/s on average [D: 30 × 7,000 / 86,400], against 0.08 article commits/s. **Acks outnumber articles about 30 to 1 in the
first real client's workload.** At a 2 KiB record per ack, the acks alone would write ~430 MB/day, about 30x the articles'
~14 MB/day [D]. The answer the brief rules out is therefore not a detail; it would make the hot state the dominant cost of the node.

| design | where a cursor lives | what one ack writes | flushes per ack | how a read finds it |
|---|---|---|---|---|
| **L** (pure: an ack is a Store record, fn1's shape) | as `:consumer` events in the history, folded at open (STO-010 table, "Consumer positions") | one framed record: ~2 KiB with fn1's record envelope and pad [A: an fn1-shaped record] | one per commit batch, shared | a fold; in practice a resident projection (fn1's `consumer-projection` in `fn-sn`, INTERFACES-TODAY §1b), which is already a view |
| **G** | a key in a cursors tree | a WAL prepare (~64-128 B) plus the mutable table entry; repeated overwrites of one key coalesce before any table is written | shared | the mutable table, then the levels |
| **P** | a heap row, updated in place as a new tuple version (a HOT update when the page has room, `postgresql2026-docs-storage-hot.txt`) | ~100 B of WAL; an 8 KiB page image on the first change of each page after a checkpoint (the cursor table is 16 pages, so 128 KiB per checkpoint, small); one dead tuple for vacuum | shared | an index probe, then the heap page |
| **C** | a key in a tree | a copied leaf and path: ~12 KiB per commit, shared by the batch's acks | shared, but two syncs per commit in LMDB's order | a tree descent |
| **T** | not a fit for server-owned state. For **client-owned** progress it is exact: a Tahoe mutable slot is a signed version with a sequence number that "supercedes the previous one" (wilcoxohearn2008 §4.4), which is a forward-only cursor the client signs. Mini's receipts are this shape (CLIENTS §1.1) | a signed statement per ack: ~200 B with Ed25519, several KiB with the hybrid ML-DSA-65 profile [A: ML-DSA-65 signatures are 3,309 B]: right for an occasional checkpoint of a consumer's progress, wrong for every ack | shared | by (signer, stream) |
| **V** | a row of a materialized table (struct of arrays, rule 1), paged through the cache if the table is large (rule 9) | **a ~40 B delta in the next commit batch**: (kind, table, slot, generation, new position, op id) [D]; two acks of the same cursor in one batch coalesce to one delta | shared; one whole flush only when the ack is the only thing committing, which is the irreducible cost of a durable ack | a column read, constant time |
| **H3** | a B-tree row | a whole 4 KiB WAL frame for a 32 B change, then the page again at checkpoint | shared | a WAL-index probe, then the page |

**The right answer** is V's row. Kafka's argument for its own consumer offsets is the same one: the position "is just a single
integer ... This makes the state about what has been consumed very small, just one number for each partition. This state can be
periodically checkpointed. This makes the equivalent of message acknowledgements very cheap" (`kafka2026-docs-design.md`,
"Consumer Position"). For fn2:

- **An ack is a typed delta of ~40 B in the shared commit stream**, not a record of its own kind with a record's envelope. It rides
  the same batch, the same flush, the same chain and the same recovery as everything else (rule 8: one ordered commit stream per
  storage domain). At ~2.4 acks/s that is ~8 MB/day [D], about half the articles' bytes, and almost all of it is the
  transaction-identity and chain overhead that every committed fact pays.
- **The cursor table is a fold over those deltas, materialized in place** in the core's state (rule 1) and checkpointed as whole
  blocks: 4,096 × 32 B is 128 KiB, two 64 KiB grid blocks, so the checkpoint rewrites the table rather than tracking which rows
  changed [D]. A larger table (rule 9: consumers are a persistent namespace, not a resident array) is paged, and the checkpoint
  writes its dirty blocks.
- **Durable charges ride the record they pay for.** A POST's charge is a field of the POST's commit record; it needs no
  separate delta. Only charges without a record of their own (a read quota, a wait's reservation that must survive a crash) need
  a delta, and most of rule 5's accounting (scheduling shares, in-flight reservations) is execution state that a crash may erase,
  because the operations it accounts for die with it.
- **Derived hot state costs nothing to write.** A per-signer head is the newest signed record's own fields; the head table is a
  view over records that are written anyway. The same holds for group high-water marks and the Message-ID binding.
- **The operation-identity index is not small.** A `replayed` answer needs (principal, op id) → receipt for as long as a retry
  could arrive. That is an insert-only keyed index like the Message-ID binding (angle L), with its own retention window per
  principal (a retention class for operation identities, STO-010's open "identity history has no lifetime policy",
  CLIENTS §1.5).

So the brief's question 1 in CLIENTS §5 ("is a key's current value a fold over that key's log entries") gets a yes from the
storage side: a fold is the cheapest durable form of mutable keyed state, and "the log overrides" (#17) holds by construction,
since the materialized table is checkpointed state derived from the log (STO-001), not a second authority.

## F. Large values: tens of MiB in and out without residency

The requirement: a 16 MiB article streams in from a socket and out to a socket through bounded buffers (two 256 KiB chunk
buffers per in-flight upload, a 64 KiB reply window per connection; ENVELOPE §1.3 and §1.8), its head is parsed and its
Message-ID checked before the body is accepted, and nothing holds the whole value in memory. The commit batch is capped at 4 MiB
(ENVELOPE §1.8), so a value larger than the cap cannot sit inside a batch at all.

| placement | used by | streamed in | streamed out | effect on small commits | leftovers after a refusal or a crash mid-upload | integrity granularity |
|---|---|---|---|---|---|---|
| **inline in the commit record** | L in its naive form; fn1 (the record log carries the payload, `INTERFACES-TODAY` §2) | no: the record must be complete before it is sealed and chained | yes, by range | **head-of-line blocking**: the batch's flush waits for the whole value: ~8 ms at 2 GB/s, ~160 ms at an HDD's ~100 MB/s [A]; and the 4 MiB batch cap is exceeded | none (nothing was written) | one checksum for the whole record: a reader verifies 16 MiB to serve 64 KiB |
| **blob blocks in the grid, referenced by the commit record** (value separation) | G with WiscKey separation (lu2016); ENVELOPE §1.3's proposal; TigerBeetle's grid | yes: each 64 KiB block is written as it arrives, before the commit | yes: block by block under leases | none: the commit record carries one reference to a blob-index block and joins the ordinary batch | allocated blocks that no durable commit references: free again at recovery (the free set is checkpointed state; blocks allocated after the checkpoint and not reachable from a replayed commit are free, `tigerbeetle2026-internals-data-file.md`) | per block, held in the blob-index block, whose checksum is in the commit record: a two-level Merkle tree |
| **TOAST** (chunked rows in a side table) | P (`postgresql2026-docs-storage-toast.txt`: chunks of "about 2000 bytes", a unique index on (chunk_id, chunk_seq), an 18-byte pointer in the row) | as rows, each WAL-logged | by an index range scan | each chunk is a WAL record in the same stream as small commits | aborted rows, removed by vacuum | per page (data checksums) |
| **one file per value** | fn1's earlier per-file layout (`fn-store-8`, STO-028); Bitcask's data files are append-only instead | yes | yes | none for the data; but publishing the file costs a create, an fsync of the file and an fsync of the directory | orphan files, swept (fn1's `store-sweep`) | the file system's |
| **overflow page run** | C (LMDB) | needs the whole run allocated contiguously up front from the free list | yes | the run is part of the commit's dirty set | free pages | none (LMDB) |
| **segmented, with a Merkle tree** | T (Tahoe: immutable files as segments with a Merkle tree over the ciphertext and one over the shares; MDMF uses "individual 128-KiB" segments, `tahoelafs2026-docs-mutable.rst`) | yes | yes, with each segment verified on the way out ("streaming download", wilcoxohearn2008 §4.3) | none | unreferenced shares, removed when leases lapse | per segment, against the root carried by the capability |

What the table says: **blob blocks referenced by the commit record, with per-block checksums in a blob-index block, are the only
placement that streams in, streams out, keeps small commits unblocked, and verifies a range without reading the whole value.**
That is the G-style placement whatever the rest of the design is, and it fits L, V and C equally (C would store the blob-index
reference as a value).

**One tree instead of two.** BLAKE3, which fn already uses for content identity (OBJ-001) and for the log's trailers, is itself a
Merkle tree over 1 KiB chunks, and a 64 KiB block is a complete subtree of 64 chunks. If each block's stored checksum is that
subtree's chaining value, then the blob-index block (a list of 256 chaining values for 16 MiB) and the article's content digest
are the same tree: the storage integrity check and the identity check coincide, a peer can verify any 64 KiB of a body it pulls
against the Message-ID's content digest, and a block placed at the wrong offset fails because BLAKE3 binds each chunk's position
through its chunk counter [A: the BLAKE3 specification's chunk-counter input; to confirm against the reference implementation
before the format is frozen]. The cost is ~8 KiB of chaining values per 16 MiB (256 × 32 B) and no extra hashing, since the body
is hashed once on ingest anyway.

Deduplication by content is worth little here and should not drive the layout: a crosspost is one record with several memberships
already, and a second copy of the same article from a peer is the same Message-ID, refused as a duplicate before its body streams
(IHAVE/CHECK). Content addressing earns its place by verification and repair (angles G and I), not by space.

## G. Verification and integrity: what each structure lets recovery, a reader and a third party prove

| structure | used by | recovery can prove | a reader can prove | a third party (peer, client, auditor) can prove | write cost | read cost |
|---|---|---|---|---|---|---|
| **checksum inside the block** | Postgres data pages; SQLite's WAL frames | the block is not torn and not rotted | the same | nothing | one hash per block written | one hash per block read |
| **checksum held by the parent** (block reference = (index, checksum)) | TigerBeetle's grid; ZFS block pointers; fn2's row → record checksum (ENVELOPE §1.6) | the block is exactly the one its parent committed: tearing, rot, misdirection and stale (lost) writes are all detected for every block reachable from a quorum-read superblock | the same, transitively from the superblock | nothing beyond its own copy | one hash per block, stored in the parent | verified once when the block enters the cache (~2 µs per 4 KiB, ~32 µs per 64 KiB block [A]); never again while cached, since O_DIRECT means a cache hit is our own memory (ENVELOPE §1.7) |
| **chained trailers** (each entry carries a hash over its predecessor's trailer) | fn1's record log (`INTERFACES-TODAY` §2); SQLite's cumulative WAL checksums | the log prefix up to the last valid link is exactly what was written, in that order; a gap in the middle is `damaged`, not a shorter history | the order of what it read | a peer holding a trailer value can check that a later log extends it, but only by reading every entry in between | one hash per entry | none on a random read (a reader of one record uses the row's checksum); a full scan at recovery |
| **Merkle tree over the state** (COW pages with checksummed pointers) | ZFS; a C design with parent-held checksums | the current state is exactly the one the root names | that a value is in the current state | given the root, a value's presence in the state, with a path of O(depth) hashes | O(depth) hashes per changed leaf, per commit | as parent-held |
| **Merkle tree per object** | Tahoe's ciphertext and share trees; BLAKE3's own tree (angle F) | each object's bytes | any segment of an object, without reading the rest | that a segment belongs to the object a capability names | none beyond hashing the object once | per segment |
| **Merkle log** (an append-only tree over record digests: RFC 6962-style or a Merkle mountain range [A]) | Certificate Transparency's logs; not yet in any fn design | everything the chained trailers prove | that one record is in the log at a position | **inclusion** of one record in O(log n) hashes (~20 × 32 B = 640 B at 1M records [D]); **consistency**: that a log of size m is a prefix of a log of size n, in O(log n) hashes. A peer or client holding an old (size, root) detects rollback or a forked history | ~2 hashes per appended record on average, plus O(log n) to recompute the root once per batch [A]; ~1-2 µs per record [D at ~1 µs per BLAKE3 call on 64 B]; the interior hashes are an append-only column of 32 B per record (32 MiB per 1M) | none on a read; a proof is built only when asked |

What the table says:

1. **Parent-held checksums are the floor** for fn2 under the tougher fault model: they are the only placement that turns rows 3,
   4 and 5 of the fault table into detected faults, and they cost one hash per block, verified once per cache fill. Every design in
   §0.2 can carry them; LMDB, SQLite's main file and Postgres's heap do not.
2. **Chained trailers are what fn1 has, and they prove order but not presence to anyone outside.** A peer that wants to know
   "is article X in your log, and is your log today an extension of the one you showed me yesterday" has to read the whole log in
   between. A Merkle log answers both questions in a few hundred bytes. It subsumes the chain (the root at each batch commits to the
   whole prefix), so it replaces the chain rather than sitting beside it.
3. **A checksum is not an integrity claim against an adversary.** Anyone who can write the disk can recompute an unkeyed
   checksum. What makes the log's state a claim is a **signed root**: the node signs (size, root) at each checkpoint, or at a
   cadence. That signed root is exactly issue #17's checkpoint as a claim, `(history, prefix-head, prefix-sequence, fold-id,
   summary-digest, identity-commitment)`, with `prefix-head` a Merkle root rather than a trailer. It is also what Mini's receipts
   and helm's premises would cite, and what makes `A-INDEPENDENT-FRONTIER` checkable: a client or peer that kept a signed (size,
   root) is the independent witness rule 8 asks for, and it can prove a rollback by presenting it (§B.2's last point).
4. **Cost per read is the same for all of them** once verification happens at cache fill: the integrity structure chosen changes
   what can be proved, not how fast an ARTICLE is.

## H. Capabilities and signed records: can narrowed rights be a property of the data?

Tahoe's model (wilcoxohearn2008 §2, §4): three powers in a strict order, **verify ⊂ read ⊂ write**, each derivable from the one
above and not the reverse ("diminishing a capability"). An immutable file's verify-cap is a hash of its Capability Extension
Block (which holds the Merkle roots); its read-cap is the verify-cap plus the decryption key. A mutable file has a key pair: the
verify-cap is `H(VK)`, the read-cap adds a read key, the write-cap holds a write key that unlocks the signing key; each version is
signed together with "a sequence number indicating that this version of the file contents supercedes the previous one". Servers
can deny service or attempt rollback, and nothing else.

What the clients ask that is the same shape (CLIENTS §1.2, §2.2 items 4 and 7, §4): helm wants signed records carrying "an op
id, the signing key and the previous head", identity as a key with "roles ... narrowable delegated rights", and an agent inbox
that does not need the operator socket; Robigalia (inferred) wants "capability-scoped (attenuable) access rather than login
accounts"; peers move portable objects whose authorship must survive relaying.

| power | Tahoe's form | fn2's form | can it be a property of the data on one node? | storage cost | per-request cost |
|---|---|---|---|---|---|
| **verify** | the hash of the extension block (immutable); `H(VK)` (mutable) | the article's content digest (OBJ-001, already kept) and, for a signed stream, the hash of the signer's key | **yes, fully**: anyone holding the digest checks the bytes from any source (angle F's BLAKE3 tree); anyone holding the key hash checks a signed record without trusting the node that relayed it | 32 B per object (exists); a key hash per stream or signer | a hash at cache fill (exists); a signature check once per record at admission (exists for signed posts) |
| **append / write** | holding the signing key for a mutable slot | holding a signer key S with the right to append to stream G: each record signed by S carries S's previous head (Tahoe's sequence number, helm's previous head) | **yes**: the record proves its writer; the node checks the signature and the previous head at admission, and a peer can re-check after import. A fork (two records naming the same previous head) is evidence, which fn already detects for statements (`fn-sn-equivocatorp`, CLIENTS §2.2 item 4) | the signature in the record (Ed25519 64 B; the hybrid profile adds ML-DSA-65's 3,309 B [A]); a per-signer head table, which is a view over the records (angle E) | one verification per record at admission (Ed25519 ~77.5 µs per 1 KiB row, CLIENTS §1.2) |
| **delegated, narrowed right** | handing over a diminished cap | a **delegation statement**: K1 grants K2 right R over stream G, narrowed (a prefix of groups, an expiry, a rate), signed by K1; revocation is a later statement. Stored as ordinary statements (`specs/objects.md`'s Statement record) | **yes, as evidence**: the chain of statements is data any node can check; the decision to honour it is the node's admission rule | statements (append-only); a view from subject to current delegations (hot state) | verify the delegation chain once per authenticated session and cache the resulting rights in the connection's state; ~0 per command after that |
| **read** | the decryption key: the server cannot read | for ordinary groups, **no**: the node must read bodies to serve NNTP, build overview and run XPAT. Read authority stays the node's decision over principals (row-level visibility, CLIENTS §2.2 item 7), which delegation statements can feed | only for **sealed streams**: groups whose bodies the client encrypts before signing, which the node stores, indexes by envelope (Message-ID, size, signer, time) and serves opaquely. This is already fn's stance ("it keeps no secrets (encrypt before signing)", CLIENTS §1.1) | none beyond the ciphertext | none; the cost is functional: no overview fields, no search inside a sealed stream |
| **check without reading** | the verify-cap given to a checker or repairer ("the repairer process does not get the full capability ... merely ... the 'repairer capability' subset", `tahoelafs2026-docs-architecture.rst`) | a peer or a small donated device holding sealed or plaintext blobs plus their digests | **yes**: a scrubber, a backup peer or a ClockDAG device verifies and repairs blobs it may not read | none extra | per blob scrubbed |

What the table says:

1. **Verify and append authority become properties of the data at almost no cost**, because fn already keeps content digests and
   client signatures. What is missing is structural, not cryptographic: a previous-head field in signed records, a per-signer head
   view, and delegation statements with a view over them. All of it is append-only records plus derived hot state, which the
   design in §13 already has.
2. **Read authority cannot be cryptographic for the streams fn2 indexes.** Tahoe can make read a cryptographic power because a
   Tahoe server does nothing with the bytes but store them. An NNTP node renders overview, threads and search from them. So read
   stays an admission decision for ordinary streams, and becomes cryptographic only for sealed streams, at the price of the node
   knowing only their envelope. This is a choice per stream, not per node (§14, decision 5).
3. **Per-object capabilities are the wrong granularity for streams.** A Tahoe mutable file is one object with one key pair (and
   RSA key generation took "between 0.8 seconds and 3.2 seconds", wilcoxohearn2008 §6.1). fn2's unit of authority is the stream and
   the signer; the unit of verification is the object. Keeping those apart gives per-object verification with per-stream keys.
4. **On Robigalia**, node-local authority is a kernel capability (a `(slot, generation)` handle the kernel makes unforgeable),
   so the storage layer never stores authority itself; it stores the statements that justify minting it, and the cryptographic
   form is needed only across nodes.

## I. Replication and peers: what a pulling peer gets, and what BP/DTN carriage needs

fn's peers are **not replicas**. Each node assigns its own numbers, keeps its own stored projection (`Path`, `Xref` and injection
records are outside the authored source, OBJ-003), and convergence is "on validated fact sets, not identical local variants"
(OBJ-004, CLIENTS §2.1 "Peers"). So the physical replication schemes (TigerBeetle's VSR with grid repair by block, Postgres's
physical WAL streaming, copying an LMDB file) apply only to replicas of one node, which fn2 does not build now (EXECUTION-MODEL §2
defers partitioning; VSR-style replication is further still). Between peers what moves is portable objects and statements.

| design | what a pulling peer is given | dedup and convergence | repair of a damaged local block | what the peer can verify | BP/DTN fit |
|---|---|---|---|---|---|
| **L** | records after a stream position (the source's local sequence: an offset, Kafka's model; "The offset for a message never changes", kafka2026-docs-design.md) | by Message-ID and content digest at import (D25's three answers) | only from a peer holding byte-identical content | with chained trailers, continuity only by reading every entry in between | a portable batch is a run of records; custody is a `:forward` pin |
| **L + Merkle log** | the same, plus the source's signed (size, root) and on request a consistency proof from the peer's last (size, root) | as L | as L | **that the source did not roll back or fork** between pulls, and that each record is in the log the source signed (inclusion proofs). Tahoe gets freshness by reading K + E servers and trusting the highest sequence with K shares (wilcoxohearn2008 §5); a signed Merkle log gets it from one source plus the peer's own memory | a receipt can cite (size, root): "I hold your log through here", which is grounded evidence for releasing the `:forward` pin (F_dtn's `fn-sys-release-is-grounded-end-to-end`, CLIENTS §3.6) |
| **G** | records, and block-level repair by (index, checksum) | as L | from a **replica** with an identical grid; not from a peer, whose grid layout differs | blocks, between replicas | as L |
| **content-addressed blobs** (T's naming applied to bodies) | the authored source by its digest | identical bodies are identical blobs on every peer | **from any peer that has the article**, by digest, block by block (angle F's BLAKE3 subtree chaining values verify each block on arrival) | each block of a body, against the Message-ID's digest | **a bundle fragment can be verified on its own**, before reassembly, if fragment boundaries fall on 64 KiB blocks |
| **T across a peer group** | erasure-coded shares: K of N needed (`N/K` space; 3-of-10 in Tahoe) | by verify-cap | the repairer regenerates missing shares from any K (`tahoelafs2026-docs-architecture.rst`, "File Repairer") | shares and objects | the ClockDAG case (CLIENTS §1.3: "community-credit ledgers on donated devices with small disks"): a small device keeps shares of old bodies rather than whole bodies, so the group survives N - K device losses at `N/K` space. This is a peer-group service above the node, not a node storage layout |
| **P** | logical decoding of the WAL (row changes) for peers; physical streaming for replicas | application-level | from a replica | none intrinsic | none intrinsic |
| **C** | a whole-file copy | none | none | none | none |
| **V** | peers replicate the log; each rebuilds its own views (Kafka's consumers rebuild state from topics) | as L | as L | as L | as L |

What the table says:

1. **For peers, the useful replication unit is the portable record plus its content-addressed body**, and the useful evidence is a
   signed log root. Block-level repair (G) needs identical layouts and therefore replicas; it does not help a peer group.
2. **Content addressing requires separating the authored source from the node's projection in the layout.** The body blob should
   be the authored source's bytes exactly (identical on every peer, named by its digest), and the node's injected headers (`Path`,
   `Xref`, `Injection-Info`) belong in the node's own commit record. ENVELOPE §1.3's record puts ~200 B of injected headers before
   the article as received; for repair across peers, the order is: commit record (node-local, including injected headers and the
   reference) → blob (portable, digest-named). ARTICLE then sends the injected headers from the record and the body from the
   blob, as two ranges of one reply (the stored form is still the wire form, split at a known offset). A small article keeps its
   authored source inline in the commit record, as its own digest-named range; repairing it re-fetches that range by digest from
   a peer and rebuilds the node-local part from the node's own columns (memberships give `Xref`; the record's head gives the rest
   only if it survived, so the node-local head is the one thing a peer cannot restore).
3. **What BP/DTN carriage needs from storage** is four things, and all four are in the design of §13: stable content identity
   (the digest), idempotent and out-of-order import (the Message-ID binding's three answers), custody as an evidence-released pin
   (angle D's pin table, `:forward` kind), and receipts that cite something checkable (a digest for one object, a signed (size,
   root) for a prefix). The one BP-specific storage cost is that forward pins on a delay-tolerant link may last days, so the
   space they hold is a profile budget with a named exhaustion (the sender stops accepting new forward obligations; ENVELOPE's
   `436` "try later" is the NNTP form of the same thing).

## J. Filesystem and device soundness: the requirements each design places on the platform

Ember's ruling (EXECUTION-MODEL §7.2): "its our job to make software that is capable of being correct. if someone wants to deploy
it in a way that is fundamentally unsound, that's on them, not us. we shouldn't go out of our way to 'refuse' things though." So
each design's requirements are stated below as documentation, with the consequence of violating each. The host **observes and
reports** what it can (file system type, whether direct I/O was honoured, logical and physical sector size, ZFS `recordsize`,
whether the device reports a volatile write cache and FUA), in `health` and at start, and refuses nothing. This replaces
ENVELOPE §2.4's "The host refuses to start on a copy-on-write file system unless the operator says the page-cache backend is
acceptable" and ENVELOPE §2.8's second decision, and it turns fn1's STO-031 (a store "opens only on the filesystem its record
names") into an observation reported by name rather than a refusal.

### J.1 What each design requires

| requirement | L, V, G, and T as a naming layer (never overwrite a still-required sector; checksums held by parents; one completion-gated flush per batch) | P (in-place pages + WAL) | C (COW tree, two meta slots) | H3 (SQLite WAL, checkpoint into main) | consequence if violated |
|---|---|---|---|---|---|
| **R1. an honest flush**: once the barrier reports done, every write completed before it is durable (`A-PERSISTENCE-FENCE`) | required | required | required | required | acknowledged commits can be lost. Detection: a lost middle batch by the chain or the Merkle log; a lost tail only by an independent witness (§B.2) |
| **R2. sector atomicity**: a write of the device's logical sector lands whole or not at all | **not required**: a torn sector is a checksum failure in an unacknowledged batch | required for the page size, **or** full-page images in WAL (Postgres: "If you have file-system software that prevents partial page writes (e.g., ZFS), you can turn off this page imaging", `postgresql2026-docs-wal-reliability.txt`) | required for the meta page, or the meta page checksummed with fallback to the other slot | required for the main file at checkpoint unless powersafe overwrite holds (`sqlite2026-docs-psow.txt`) | silent corruption of a page that was already acknowledged |
| **R3. ordering between writes** | **not required**: commit is gated on completions, then one barrier (ENVELOPE §2.5) | WAL before data, enforced by flushes | data before meta (LMDB: two syncs); not required with parent-held checksums and slot fallback | WAL synced before checkpoint; main synced before WAL reset | a durable reference to data that is not durable |
| **R4. reads return the written bytes, or an error, or garbage** (never another block's valid bytes undetected) | not required: parent checksums detect misdirection | required (in-page checksums miss cross-file misdirection) | required in LMDB (no checksums); not with checksummed pointers | required for the main file | wrong data served as right |
| **R5. direct-I/O alignment** (offset, length and buffer address multiples of the logical block size) | required when O_DIRECT is used; the format pads to 4 KiB sectors | same if direct I/O is used; Postgres normally uses buffered I/O | LMDB uses `mmap`, so its I/O is the page cache's (and Crotty et al. argue a DBMS should not, `crotty2022-mmap-in-your-dbms.pdf`) | buffered | `EINVAL` at the first misaligned write: an `Io` outcome, not a crash |
| **R6. overwrite in place** | **never used** after a sector holds required data; space is reused only after release and a checkpoint | used for every page | used for free pages and the meta slots | used by every checkpoint | n/a |
| **R7. exclusive access** (one writer process) | required (`flock`/`O_EXCL` on Linux; structural on Robigalia, ENVELOPE §2.4) | required (postmaster lock) | single writer by lock | file locks, and a `-shm` shared-memory index readers must share, so "the WAL implementation will not work on a network filesystem" (`sqlite2026-docs-wal.txt`) | two writers interleave commit streams |

The append-and-reference designs need two properties (R1, and R5 when using direct I/O). The page-oriented designs need R1-R4 and
R6. **The fewer platform properties a design relies on, the more deployments are sound without anyone having to know**, which is
the practical meaning of "never refuse": a design that depends only on an honest flush is sound on almost everything, and the
documentation has one important sentence to say.

### J.2 Platform notes for the operator documentation (L/V/G-shaped design)

| platform | sound? | what to document |
|---|---|---|
| ext4, XFS on a device with a volatile cache | yes, given R1 | preallocate the data file by **writing zeros once**, not `posix_fallocate`: unwritten extents make each first write commit the journal, measured at ~23 KB and 2.85 device writes per POST (ENVELOPE §1.3, DESIGN-RESOURCE-MODEL §3) [M] |
| ZFS | yes, given R1 | ZFS never tears a record and checksums every block itself, so fn2's checksums are a second layer (harmless). ZFS is copy-on-write: each fn2 append allocates new ZFS space, so `NoSpace` can arrive on any write, including into a "preallocated" file; it is an ordinary `Io` outcome and the batch is not acknowledged. Set `recordsize` to the grid block (64 KiB) or smaller: a 4 KiB write into a 128 KiB record that is not cached forces ZFS to read the record to rewrite it [A: ZFS's partial-record read-modify-write; measure, §14 M7]. Direct I/O on ZFS (OpenZFS 2.3 and later [A]) is honoured only for suitably aligned writes. Flush latency is the ZIL's; hbox's ZFS-on-HDD without a SLOG measured 8.35 ms per `fdatasync` [M], and a SLOG is the latency lever (ENVELOPE §1.5) |
| Btrfs | yes, given R1 | copy-on-write by default, as ZFS; `chattr +C` (nodatacow) on the data file makes writes in place and **also turns off Btrfs's data checksums**, leaving fn2's own. After a failed `fsync`, Btrfs reverts the in-memory view to the old data (Rebello, `rebello2020-can-applications-recover-fsync-failures.pdf`); fn2 treats any failed flush as a crash and recovers from the log, so it never reads that view |
| tmpfs | **not durable** | R1 is false (an `fdatasync` returns in 0.0006 ms [M] and persists nothing past a reboot); sound for tests and the simulator's twin only. The host reports it by name |
| darwin (development) | only with `F_FULLFSYNC` | `fsync` on darwin does not flush the device cache; the darwin backend uses `F_NOCACHE` and `F_FULLFSYNC` and does not claim the direct-I/O fault model (ENVELOPE §1.7) |
| network file systems | depends on the server | R1 and R7 hold only if the server's commit semantics and locking are honest; fn2 cannot observe either. Document as "the server's guarantees are fn2's guarantees" |
| raw block device (Linux), and **Robigalia** | yes, given R1 and the device's flush | no file system at all: the superblock copies, the log and the grid are fn2's own format ("unchanged, because Linux already had them in one file", ENVELOPE §2.4). R1 is the device's FLUSH (NVMe FLUSH, `VIRTIO_BLK_T_FLUSH`) or FUA; the sector size comes from the device. A device with power-loss protection makes the flush nearly free (~0.02-0.1 ms [A]). A device that acknowledges FLUSH without doing it (`zheng2014-torturing-databases-power-faults.pdf`'s "durability lies") violates R1; fn2 detects it only as §B.2 says |

On Robigalia, the append-and-reference shape is also the one that maps directly onto a block-device queue: every write is a new
sector, every barrier is the device's flush, and nothing depends on an ordering the device does not promise. A page-oriented
design on a raw device would need R2 from the device's atomic write unit [A: NVMe's AWUPF], which varies by device, or would carry
full-page images as Postgres does.

## K. Simplicity and verifiability

The refinement obligation (EXECUTION-MODEL §4) relates the concrete core to a reference semantics in which, per F_node,
"history and generation are projections of the log" (CLIENTS §3, "What fn2 should keep"). A storage design is simpler to verify
the closer its durable state is to that abstract state, and the fewer background machines it runs that change durable state
without a client operation. The paperbin README's route 1 (`chajed2022-daisynfs-verifying-nfs-server.pdf` over
`chajed2021-gojournal-verified-concurrent-journaling.pdf`) is the precedent: prove one transaction layer against the tough
model once, and write everything above it as sequential transactions.

| design | moving parts that change durable state | invariants a proof must carry (the main ones) | what the refinement says | how it maps onto rule 8's commit machine and recovery classes |
|---|---|---|---|---|
| **L** | the log writer; the checkpointer (column tails, superblock); the cleaner (only if expiry is not time-ordered); the index rebuild at open | (1) the committed log is a chained (or Merkle) prefix; (2) every row's checksum is its record's; (3) every derived index equals the fold of the committed prefix; (4) the free set is disjoint from every referenced extent; (5) no extent is reused while a lease or pin needs it | **abstract state = the committed prefix**; every other structure is a function of it. This is F_node's own statement, so the abstraction function is nearly the identity | collect (records into the batch buffer) → seal (checksums, chain or Merkle append) → dependencies (blob blocks) → log-write (the batch's sectors) → fence → durable → install (append to columns, apply to indexes) → publish (advance the visible count) → notify → draining. A checkpoint is a commit whose dependencies are the dirty column blocks and whose log-write is the superblock. Recovery: `intact` (chain verifies to the tail), `torn tail` (the final batch fails, nothing valid after it), `damaged` (a failure followed by a valid later batch, or a referenced block failing its parent's checksum), `unknown` (no superblock quorum, or an independent witness names a longer history) |
| **G** | the WAL ring writer; the grid writer; the compaction scheduler (per beat); the manifest log; the free set and its reservations | L's, plus: tables in a level are sorted and disjoint per snapshot; compaction preserves the map at every live snapshot; snapshot visibility of tables; reservations cover every block a compaction may write; the manifest describes exactly the live tables | abstract state = a map per tree; compaction is a stutter step that changes representation and not the map | compaction is maintenance work that must also go through the commit protocol (rule 8: "cleaning and checkpoints go through the same commit protocol"): each beat's outputs are dependencies of a later checkpoint commit. Recovery classes as L, over the WAL ring |
| **P** | the WAL writer; the background writer and checkpointer; vacuum; the freezer; the visibility-map and free-space-map maintainers; TOAST | write-ahead (pageLSN ≤ flushed LSN); tuple visibility rules over transaction status; the xmin horizon; freeze before wraparound; HOT chains; TOAST pointer validity; full-page-image correctness | abstract state = a set of relations under snapshot isolation, plus ARIES's repeating-history argument | recovery is ARIES redo; vacuum and freeze are background mutations of durable pages with their own WAL. The most moving parts of any row |
| **C** | the single writer; the free list | (1) every reachable page is the one its parent names (with checksummed pointers); (2) the meta slot with the higher valid transaction is the state; (3) free pages are unreachable from every live root; (4) a reader's root stays valid while it reads | abstract state = a map; commit = an atomic root switch; crash = old root or new root. **fn1 already has these keystones** for its page store: `pgs-open-after-commit`, `pgs-open-after-crash`, `pgs-fork-isolation` (INTERFACES-TODAY §3a), and the paged checkpoint's `fn-pck-crash-recovers-from-old-or-new` (§8) | collect → seal → dependencies (all copied pages) → log-write (the meta slot) → fence → durable → install → publish. Recovery: the newer valid slot is `intact`; a newer slot whose children fail is `torn tail` and falls back; `damaged` when the older slot's tree also fails |
| **T** | none of its own on one node (a naming discipline); leases and the repairer across a peer group | a name is the hash of its content (under collision resistance, fn's `A-CRYPTO`); a mutable slot's versions are signed and sequence-numbered | abstract state = a set of named immutable objects plus signed slot heads | as its substrate's |
| **V** | L's, plus the view materializer | L's, plus **each view equals the fold of the log up to the checkpoint's position**: issue #17's "the log overrides" as an invariant | abstract state = the log; views are cached folds, so a refinement proof states one fold equation per view | install applies the batch's deltas to the views; a checkpoint writes view blocks as dependencies |
| **H3** | the WAL writer; the checkpointer that overwrites the main file; the WAL-index | WAL frames' cumulative checksums; a page's newest frame before a reader's end mark is its value; the checkpoint never passes an active end mark | abstract state = a B-tree database file at each commit | a checkpoint overwrites pages in place, so it is the one design whose maintenance step is not a new-sector write, and its crash cases include a torn main-file page |

What the table says:

1. **L and V have the smallest distance between durable state and F_node's abstract state.** Their refinement is "the log is the
   state; the rest is folds". C has the fewest moving parts and keystones that fn1 already proved, but its abstract state (a map)
   is one step further from F_node's (a history), so a refinement over C would state "the map equals the fold of the history",
   which is V's view invariant applied to the whole store.
2. **Background mutators are where the proof work is.** P has five of them; G has compaction, which TigerBeetle paces
   deterministically per beat precisely so that its cost and its interleavings are bounded; L has a cleaner only when expiry is not
   time-ordered; C and V have none beyond the checkpoint. H2's role in this angle is to make L's cleaner rarely run.
3. **Every design maps onto rule 8's commit machine**, because each has a "write everything new, then one durable step" core.
   The difference is the number of distinct kinds of commit the machine must carry: L and V have two (a batch, a checkpoint), G
   has three (batch, checkpoint, compaction beat), P has more.

## L. Namespaces without compile-time ceilings

Ember: "No compile-time ceilings." Rule 9: "resident capacity limits active execution state (connections, uploads, cursors,
parked waits, subscription edges), never how many objects the store retains; data limits are the operator's profile (D27), with
explicit exhaustion transitions." Two consequences for the format, whatever design is chosen:

- **ENVELOPE §1.8's ceilings column goes.** A u32 article sequence (`max_articles` 2^32 - 1), a u16 group id (`max_groups`
  65,536) and a 65,536-consumer ceiling are compile-time widths that some node will reach. Persistent identifiers are u64
  (sequence, group id, consumer id, principal id, statement id); a u64 at one million commits per second lasts ~585,000 years
  [D], so it bounds nothing. The block size and sector size are **format parameters** recorded in the superblock at `format`, not
  constants in the code. What remains constant is protocol bounds that are not fn2's to choose (RFC 3977's 512-octet command line,
  RFC 5536's 250-octet Message-ID).
- **Anything that grows with the store is paged**, and resident memory holds only what the profile sizes at start: the block
  cache, connection and upload slots, in-flight I/O, dirty-block budget, and the active state rule 9 names. The cache never "fills"
  as an error: it evicts. What runs out is in-flight capacity, and each has a named, resumable outcome.

| design | articles (rows by sequence) | groups and number → article | Message-ID binding | consumers, accounts, pins | history | exhaustion transitions |
|---|---|---|---|---|---|---|
| **L** | append-only column blocks; block `seq / rows_per_block` found through a column directory that is itself append-only (a radix of block references, three levels of 4,096 references reach 2^36 blocks [D]) | per-group chains of u64-sequence blocks, each with its own directory; a group table paged by id; a name index | **resident hash rebuilt at open (the first slice's ruling)**: 16 B per article resident, so resident memory grows with the store, **which rule 9 forbids beyond the profile**. The paged form is needed for rule 9 to hold at all | tables of fixed rows, paged | the log itself | a cold read waits for one of the in-flight read slots (64 by default) as an ordinary continuation; a full dirty-block budget forces a checkpoint and backpressures commits; disk full is a named store-full outcome by policy |
| **G** | a tree keyed by sequence, paged by construction | a tree keyed by (group, number) | a tree keyed by ID (TigerBeetle's id tree, ENVELOPE §1.6); filters per table (~10 bits per key [A]) are the only per-key resident cost, and they can be paged | trees | the WAL ring plus the trees | as L, plus compaction reservations: a beat that cannot reserve its blocks waits |
| **P** | heap pages, paged through the buffer pool | B-tree indexes | a B-tree | heap tables | WAL segments, recycled | buffer pool eviction; xid wraparound is the one hard ceiling, and Postgres's answer is a refusal: "database is not accepting commands that assign new transaction IDs to avoid wraparound data loss" (`postgresql2026-docs-routine-vacuuming.txt`), the exact failure ember's rule rules out, caused by a 32-bit identifier |
| **C** | a B+tree | a B+tree | a B+tree | B+trees | none kept (only the current state) | the map size: LMDB fixes the maximum database size when the environment opens [A: `mdb_env_set_mapsize`], a ceiling set at open |
| **T** | objects by hash, through the substrate | the substrate | the hash is the name | the substrate | the substrate | the substrate |
| **V** | as L | as L | as L, or as a view | views, paged | the log | as L |
| **Bitcask** (for contrast) | data files | n/a | the "keydir", "simply a hash table" of every key **in memory** (sheehy2010), rebuilt from hint files at start | n/a | data files | none: the keydir must fit in RAM. This is L's resident-hash choice taken to its end, and the reason it does not satisfy rule 9 |

What the table says:

1. **The Message-ID binding is the one namespace where L's simplest choice (a resident hash, rebuilt) conflicts with rule 9.**
   Everything else in L pages naturally because it is append-only and addressed by position. The ID binding is addressed by a
   random key, so it needs a paged keyed structure: a B-tree (P, C), an LSM tree (G), or, for an insert-only binding, the simplest
   LSM: **sorted runs of (tag, sequence) pairs**, 16 B each, 4,096 per 64 KiB block; a resident fence per block (8 B per 4,096
   entries, ~2 KiB at 1M [D]); a filter per run for absent probes (the common peering case); runs merged k at a time as
   maintenance commits. At 1M entries that is ~16 MiB of runs on disk and ~1.3 merge passes per entry at k = 8 [D]; at 100M it
   needs no rebuild at open (the runs are checkpointed state), where the resident hash needs ~1.6 GB of memory and ~10 s of rebuild
   [D, ENVELOPE §1.6 scaled].
2. **The resident hash then becomes what it should be: a cache.** The first slice can start with the rebuilt hash (EXECUTION-MODEL
   §6's ruling), on the understanding that the paged runs replace it as the index and the hash, if kept at all, is the hot part of
   the runs held in the block cache. One structure, not two (EMBER-ARCHITECTURE-WORDS §11: "replace, delete the twin").
3. **The two worked examples of a ceiling are both fixed-width identifiers**: Postgres's 32-bit transaction IDs, which force a
   whole-database freeze discipline and finally a refusal, and fn1's transaction budget, where "reclaim never returns transactions"
   (CLIENTS §1.3: "a node you run would set the budget near 2^32"). With u64 identifiers neither exists, and expiry no longer has to
   return a budget, because there is none to return.

## 12. The scorecard: every pure design fails at least one angle

"Good" means the design meets the angle for fn2's workload as it is; "costly" means it meets it at a price the angle's table
quantifies; "fails" means it does not meet the angle without becoming a different design. T is scored only where it is more than
its substrate.

| | A amp. | B recovery | C pins | D expiry | E hot state | F large | G integrity | H caps | I peers | J platform | K verify | L namespaces |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **L** | good (1.9x / 1.3x) | good, except the rebuild grows with the store | good | costly with mixed retention (cleaning) | costly as pure records (~2 KiB per ack) | good with blob blocks | chain only: costly to prove anything to a third party | neutral | good | good (R1 only) | good | **fails** (resident ID hash) |
| **G** | costly (WAL + grid + compaction) | good | costly (snapshots pin compaction inputs: ~4 GB in the stall case) | costly (tombstones + blob GC) | good | good with separation | good (parent checksums) | neutral | good between replicas only | good | costly (compaction) | good |
| **P** | costly (FPW, TOAST, freeze) | good, but lost writes are silent | good | **fails** per row, unless partitioned | good | costly (TOAST) | costly (in-page checksums) | neutral | costly | costly (R2-R4, R6) | **fails** (five background mutators) | **fails** (32-bit xids) |
| **C** | **fails** at b = 1 (~18x) | good (constant) | **fails** (~70 GB stall growth) | costly (per key) | costly (a copied path per commit) | costly (contiguous runs) | good with checksummed pointers | neutral | **fails** (no history to pull) | costly (two syncs or checksums) | good (fn1's keystones) | costly (map size at open) |
| **T** | substrate | substrate | good | good per object | not a fit | good (streaming verify) | good | **good** | **good** | good | good | substrate |
| **V** | as L | as L | good | as L | **good** (~40 B delta) | as L | as L | neutral | as L | good | good | as L |
| **H3** | **fails** (~7-13x) | good | **fails** (WAL growth) | costly | costly (whole frames) | costly | costly | neutral | costly | costly (R2) | costly | costly |

No row is "good" throughout. The pattern in the failures is consistent: **page-oriented designs fail on amplification and long
readers because fn2's records are small and immutable and its readers are slow; the pure log fails on the keyed namespaces and on
proving things to others.** So the answer to ember's question ("is it really the BEST idea?") is: immutable log-structured is the
best idea for the **authority and the bulk data**, and it is not by itself the best idea for the keyed indexes, the hot mutable
state or the integrity claim. Each of those has a better answer in another design, and they compose.

## 13. Recommendation: the committed log with folded views over a checksummed grid

### 13.1 The design

1. **One data file or one raw device** (ENVELOPE §1.7, §2.4): a superblock in 4 copies read with a quorum of 2, holding the format
   parameters (sector size, block size), the checkpoint root and the Merkle log's signed (size, root); a grid of fixed blocks (64 KiB
   by default, chosen at `format`); a free set that is checkpointed state. From G (`tigerbeetle2026-internals-data-file.md`).
2. **The journal is the one ordered commit stream and the only authority** (STO-001; rule 8). A batch is sector-padded entries in
   journal extents: commit records (each article's node-local head with its injected headers, its memberships, its charge, and
   either its authored source inline, when small, or a reference to its blob-index block), typed deltas of ~40 B for the hot state,
   statements, releases and pins. The batch header carries the Merkle log's (size, root) after the batch, which replaces fn1's
   chained trailer and subsumes it (angle G). From L and V.
3. **Large authored sources are streamed blob blocks** referenced by the commit record (value separation, lu2016; ENVELOPE §1.3).
   The blob-index block lists each 64 KiB block's BLAKE3 subtree chaining value, so the storage checksum and the content digest are
   one tree (angle F), and the authored source is byte-identical on every peer and repairable from any of them by digest
   (angle I). From G's placement and T's naming.
4. **Derived columns, append-only and paged**: article rows, the membership pool, per-group number chains, and overview entries.
   Overview is written once in commit order (the hot, recent range of every group is in the cached tail) and re-clustered by
   (group, number) when it ages out of the tail, by a maintenance commit (finding A-1; +~0.12x write amp [D: 300 B per 2.4 KiB]).
   Columns are checkpointed by their dirty tail blocks (ENVELOPE §1.6's "persist only append-only data"). From L.
5. **Keyed derived indexes are sorted runs**, one LSM implementation for every keyed index fn2 grows, used first for the
   Message-ID binding (angle L, point 1): runs of fixed-width (key, sequence) entries, resident fences, per-run filters, k-way merges
   as maintenance commits paced per batch. The first slice may start with the rebuilt resident hash (EXECUTION-MODEL §6), which the
   runs then replace. Later secondary indexes (by References for threads, by issuer and subject for statements; CLIENTS §2.2 items 5
   and 12) are more trees of the same kind. From G, restricted to what an insert-only binding needs.
6. **The hot mutable state is a set of folds** (cursors, registrations, accounts, durable charges without a record of their own,
   pins as ranges, per-signer heads, the operation-identity index's recent window, live limits): struct-of-arrays tables in the
   core's state (rule 1), paged by block when large (rule 9), changed only by the batch's deltas at `install`, read at latest and
   never at a pinned version, and checkpointed by writing their dirty blocks to fresh grid blocks whose references go into the
   next superblock: C's copy-on-write and root switch, applied to the views only, once per checkpoint rather than once per commit.
   From V, with C's checkpoint.
7. **Visibility pins are numbers; only byte leases hold space** (angle C, option a). A pinned version guarantees visibility
   decisions and identities; a payload reclaimed after its release is answered `unavailable` to a connection that had not leased
   it, as consumers already are (CLIENTS §2.1). Reclamation of a storage unit waits for retention, pins and leases; never for the
   oldest version pin.
8. **Expiry places together what dies together** (angle D). With one retention policy (the default), the journal's oldest
   extents retire whole and the cleaner moves only pinned or long-lived survivors. With several policies, each retention class
   has its own payload extent chain (H2 by class, not by group), so a class's expiry is a drop of its oldest extents.
9. **Checksums are held by parents everywhere** (row → record, blob index → block, superblock → checkpoint root → column and view
   blocks), verified once at cache fill. The checkpoint signs (size, root): issue #17's checkpoint claim, and the independent
   witness peers and clients can keep (`A-INDEPENDENT-FRONTIER`).
10. **The platform requirement is R1, plus R5 under direct I/O** (angle J). Nothing is refused; the host reports what it observed.

### 13.2 How it runs on rule 8's machine

There are **two commit kinds**. A *batch* goes collect (records and deltas into the batch buffer; coalesce deltas per slot) →
seal (record checksums; Merkle appends; the batch header) → dependencies (blob blocks of large uploads, already streaming) →
log-write (the journal sectors) → fence → durable → install (append to columns and runs' mutable parts; apply deltas to views) →
publish (advance the visible count) → notify (waiters of the streams the batch touched) → draining. A *checkpoint* is the same
machine with dependencies = the dirty column, run and view blocks and the free set, and log-write = the superblock copies. Merges of
sorted runs, overview re-clustering and cleaning produce new blocks as dependencies of a later checkpoint and change no client-visible
fact, so they are stutter steps of the abstract state. Recovery: superblock quorum → checkpoint root → replay the journal from the
checkpoint's position (bounded by the checkpoint interval: ~64 MiB, ~30 ms [D]) → classify `intact / torn tail / damaged / unknown`
as in angle K's L row, using the Merkle log for the batch chain and parent checksums for every referenced block.

### 13.3 What it costs, against the angles

| angle | this design | from |
|---|---|---|
| A | ~1.9x at b = 1, ~1.3x at b = 8, +0.12x for overview re-clustering, + the runs' merges on ~16 B per article | L |
| B | constant superblock read + bounded journal tail; no rebuild once the runs are in | G, L |
| C | 0 for version pins; ≤ the leased article per stalled reader | L, V |
| D | whole-extent drops per retention class; cleaning bounded by pinned survivors | H2, Kafka |
| E | ~40 B per ack in a shared flush; whole-table checkpoints for small tables | V, Kafka |
| F | streamed blob blocks, per-block verification against the content digest | G, T |
| G | parent-held checksums + a signed Merkle log root | G, T, CT |
| H | verify and append authority in the data (digests, signer chains, delegation statements); read authority by admission, or sealed streams | T |
| I | portable records + digest-named authored sources + consistency proofs | T, Kafka |
| J | R1 (+ R5) | L, G |
| K | two commit kinds; abstract state = the committed prefix; one fold equation per view; one LSM implementation for keyed indexes | L, V |
| L | u64 identifiers; everything that grows is paged; resident memory is the profile's | G |

### 13.4 Its two strongest objections

**Objection 1: it is several structures where one would do.** A copy-on-write B+tree with checksummed pointers (C, ZFS-shaped)
is one structure: it opens in two reads, needs no index rebuild and no replay, pages every namespace, is a Merkle tree of the
state for free, and fn1 already proved its crash keystones (`pgs-open-after-crash`, `fn-pck-crash-recovers-from-old-or-new`).
The recommended design has a journal, columns, runs, views and a grid. The answer is in the numbers, not in taste: C writes ~18x
per small commit at b = 1, where fn2's first clients live; a stalled reader grows it by the whole write stream (~70 GB in the
stall case); its random-key paths are copied per commit; and F_node's abstract state is a history, which C does not keep, so a
C-based fn2 would still need a log for peers, consumers and #17's checkpoints. The design takes C's best idea (the root switch)
for exactly the part where it is cheap, the checkpoint of small mutable tables. **What remains true in the objection**: the
recommended design has more kinds of block, and its proof has a fold equation per view where C's has one tree invariant.

**Objection 2: a uniform LSM would do it with one mechanism.** G puts rows, Message-IDs, overview by (group, number), cursors
and range expiry into trees under one compaction scheduler, and TigerBeetle has made that deterministic and bounded per beat.
The recommended design has three special cases of the same idea (sorted runs for IDs, re-clustered overview, retention-class
extents), and special cases are where bugs live. The answer: G as TigerBeetle builds it writes everything twice (WAL ring, then
grid), rewrites index entries of immutable articles on every level they descend, pins compaction inputs under long snapshots
(~4 GB in the stall case, with persistent snapshots still a "TODO" in its own document), and has no bulk expiry. **What remains
true in the objection**: as fn2 grows secondary indexes (threads, statements, search; CLIENTS §2.2 item 12), it will need a
general keyed-index mechanism, and that is an LSM. This is why §13.1 point 5 builds the Message-ID runs as the first tree of one
general LSM implementation, rather than as a one-off. If the measurements of §14 show overview re-clustering and retention-class
extents behaving like compaction anyway, they should become trees of that same LSM.

### 13.5 The hybrid, stated as the rule it follows

If the pure designs each fail an angle, the hybrid is the one that gives **each kind of state the structure its access pattern
asks for, under one commit stream and one recovery**:

| kind of state | access pattern | structure | from |
|---|---|---|---|
| history (records, statements, releases, pins, deltas) | append; replay; pull by position | the journal, chained by a Merkle log | L, V, CT |
| bulk immutable bytes (authored sources) | write once; stream; verify a range; repair from peers | digest-named blob blocks in the grid | G, T, WiscKey |
| positional derived indexes (rows, memberships, number chains, overview) | append; read by position or short range | append-only column blocks; overview re-clustered once | L |
| keyed derived indexes (Message-ID, later References, issuer/subject) | insert-only; point and absent probes | sorted runs: one LSM implementation | G |
| small hot mutable state (cursors, accounts, pins, heads) | read and write at latest; tiny updates | folds of ~40 B deltas, materialized, checkpointed copy-on-write | V, C |
| the claim about all of it | prove to others | a signed (size, root) at each checkpoint | T, CT, #17 |

## 14. What would decide, and what is ember's

### 14.1 The measurements that would decide between the top two

The top two are §13's design and a uniform G (TigerBeetle's shape, with value separation). Each measurement runs in the
deterministic simulator first (byte and operation counters are exact there) and then on the laptop's NVMe and hbox's ZFS, as
ENVELOPE §2.8's floor rows are run. Performance is reported, never a gate.

| # | measurement | decides |
|---|---|---|
| M1 | device bytes and flushes per committed POST at λ = 1, 100, 1,000/s, 2 KiB and 64 KiB bodies, for both designs | A: whether G's double write and compaction matter at fn2's rates or vanish under group commit |
| M2 | cold XOVER 1-1,000 in a group with 0.1%, 1% and 10% of traffic: reads, bytes and latency; commit-order overview, re-clustered overview, and G's (group, number) tree | finding A-1, and whether re-clustering is needed or a tree is simpler |
| M3 | Message-ID absent and present probes at 1M, 10M, 100M entries: resident hash vs sorted runs with filters vs G's id tree; open time for each | L angle: when the rebuilt hash stops being acceptable; whether runs and G's tree differ at all |
| M4 | a 16 MiB BODY at 4,096 B/s while 1,000 POSTs/s commit and expiry runs: blocks held at the end of the stream | C: lease-only pins vs snapshot pins, measured |
| M5 | 30 consumers acking every article of a 7,000-row/day stream interleaved with POSTs: bytes and flushes per ack | E: the ~40 B delta claim |
| M6 | open after a crash at 1M articles with a 64 MiB checkpoint interval, including the crash-during-recovery schedule (row 13) | B |
| M7 | 4 KiB direct-I/O appends on ZFS at `recordsize` 4 KiB, 64 KiB and 128 KiB, and on ext4 with zero-filled vs `posix_fallocate`d extents | J: the operator documentation's ZFS and ext4 sentences |

### 14.2 The five decisions the storage layer leaves to ember

Each is put with the recommendation; the arguments are the angles named.

1. **The unit of state.** Recommendation: the immutable committed log is the only authority, and every mutable keyed object is
   a fold over it, materialized and checkpointed (angles E and K; CLIENTS §5 question 1). The alternative is a second authority
   for mutable state (a mutable store beside the log), which the angles find more expensive and harder to verify.
2. **What a pinned version promises about payload bytes.** Recommendation: a pin guarantees visibility and identity, and bytes
   only for what the connection has leased; a payload reclaimed after its release answers `unavailable`, as consumers already see
   gaps (angle C, option a). The alternative is epoch reclamation with a bounded pin age and a named rebase when a pin expires
   (option b): a stronger promise to readers at the price of the slowest reader setting how much space is held.
3. **Retention placement.** Recommendation: one journal by default (expiry retires its oldest extents; the cleaner moves
   survivors), with operator-defined retention classes as a profile option that gives each class its own payload extent chain
   (angle D). The alternative is classes always (more streams per batch, more tail pads at b = 1), or never (cleaning cost
   `u/(1-u)` under mixed retention).
4. **The integrity commitment in the format.** Recommendation: a Merkle log over committed records from the first format, with
   the node signing (size, root) at each checkpoint, so that inclusion and consistency proofs exist for peers, consumers and #17's
   checkpoint claims, and `A-INDEPENDENT-FRONTIER` has a checkable witness (angles B, G, I). The cost is ~1-2 µs and ~32 B per
   record [D]. The alternative is fn1's chained trailers, which prove order to the node itself and nothing cheaply to anyone else.
5. **Sealed streams.** Recommendation: allow streams whose bodies are client-encrypted, stored and served opaquely and indexed only
   by envelope (Message-ID, size, signer, time), as a per-stream choice; ordinary streams keep read authority as an admission
   decision (angle H). This is the one place Tahoe's least-authority model can apply to a single node, and it costs those streams
   overview, threading by content and search.
