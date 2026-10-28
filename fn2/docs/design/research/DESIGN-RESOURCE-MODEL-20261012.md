# Resource model and the design that reaches the floors (Design seat, 2026-10-12)

Present state; rewritten whole when it changes. Counts are the model and milliseconds only validate them.

## 0. The point

Two structural choices set fn's resource use. Local fixes cannot reach either, and both have measured costs:

1. **Every publication rewrites the whole store, payloads included, every K/2 records.**
   - A publication writes 196-217 MB at 50k and reads about 550 MB.
   - It also fires straight after an open whose suffix is at least K/2.
   - Over a store's life that is Θ(n²/K) bytes.
   - Peer catch-up at K=128 writes **198 KB to the device for each 2 KiB article (about 97x)** and does 1.35 flushes per article.
   - This one mechanism explains three open questions: the 21 s of CPU at rest after a 50k open, POST's doubling from 10k to 50k, and catch-up's late rise.
2. **Indexes are heap trees decoded on every access, and payloads are re-hashed on every read.**
   - The catalog takes about 8 KB of anon heap per article (the slope from 10k to 50k).
   - One OVER line costs 8 full-row reconstructions and 16 tree decodes.
   - A random 2 KiB ARTICLE reads 13-24 KB.
   - NEWNEWS scans all n.

The floor layout is one append-only log that holds every payload once, in wire form, plus fixed-width column pages checkpointed by dirty page. It lands as three large landings (§4). It subsumes D1-D8, W2, W3, W5 and W6 and deletes the .fnsc checkpoint writer, the per-row tree codec, the per-read digest and the NEWNEWS scan.

## 1. Runs and conventions

- **M** means measured.
  - The runs are labels under `<box>:/tank/fn/scratch/load-harness/runs/`, with local copies in `build/lanes/design-model/build/runs/`.
  - Every run used the C7 402b65786 image, `fn-host`, the curve fixtures (K = 65536, built without a checkpoint) and work on the real filesystem.

  | label | box and filesystem | load (1-min) |
  |---|---|---|
  | design-p-floor | persvati, ext4 on a Micron client NVMe (write-back cache, FUA) | 0.2 |
  | design-p-io10k | persvati | 0.5 |
  | design-p-io50k | persvati | 1.1 |
  | design-p-w6q10k | persvati (peers preset, K = 128) | 0.8 |
  | design-h-io10k | hbox, ZFS: 2× HDD mirror, NVMe special vdev, no SLOG | 3.1 (5-min 13.7) |
  | design-h-io50k | hbox | 5.8 |
  | design-h-floor | hbox ZFS | 1.8 |

  - The cell is DESIGN-IO in this worktree's `tools/load` (unpushed). Each phase records:
    - the owner's `/proc/<pid>/io` deltas;
    - box-wide `/sys/block/*/stat` deltas (reads, writes, sectors, flushes);
    - `/proc/spl/kstat/zfs/zil` deltas;
    - the store files' growth.
  - Device counts are box-wide. A 20 s idle-control phase gives the background rate, and per-op device figures are net of it.
  - Earlier figures cite PERF-MEASUREMENTS-20261012.md (hbox tmpfs, quiet).
- **D** means derived from code at cdd1fb27e. The full traces, with every file:line, are `build/lanes/design-model/build/codex/write-trace/REPORT.md` and `read-trace/REPORT.md`; short citations appear here.
- **Variables.**
  - n articles; s article octets; b records per committed batch; k lines or ids requested; G groups.
  - E is the protected log entry that holds an article. The fixtures pack 8 records per entry, so E is about 19 KB.

## 2. Per operation: TODAY, FLOOR, gap

| op | TODAY | FLOOR (data plus durability contract) | gap |
|---|---|---|---|
| **POST 2 KiB, one connection** | **Syscalls**: 8 read, 13 write, 1 fdatasync, 1 lseek, 1 clone3, about 89 futex, 75 rt_sigprocmask, 5 tgkill (M, OPPROF).<br>**Log bytes**: 4096 per POST, from the U = 4096 batch pad (D: store-log.lisp:274,283; io.lisp:8080).<br>**Every command**: +176 B to decisions.fnj (M).<br>**Device, ext4**: 2.85 writes, about 23 KB and 1.0 flush per POST (M p-io10k/50k).<br>**Device, ZFS**: 1 ZIL commit, 8.2 KB ZIL per disk, 1.04 writes per disk (M h-io10k).<br>**Allocation**: 3.1 MB (M); a 3 MiB article costs about 17 whole-article list copies (D, l4-trace).<br>**Latency (validation)**: p50 8.0 ms (ext4) and 24.3 ms (ZFS) against flush floors of 4.0 and 8.35 ms. | **Per batch**: 1 `write` of Σ(s+~80) and 1 fdatasync.<br>**Per POST**: about 3 syscalls (read, reply, wake) + 2/b.<br>**Device**: 1 write IO + 1 flush per batch.<br>**Allocation**: O(1); buffers are reused. | Syscalls about 7x; flushes 1 → 1/b; bytes 2x → 1.04x; allocation 10³x+ |
| **POST at 8 connections** | 4.4 POSTs per flush (ext4, M p-io50k), 300/s, CPU-bound at 3.0 ms CPU per POST.<br>ZFS: 4.65 per ZIL commit, 128/s, p50 54 ms (M). | Throughput = b/t_flush, with b = everything queued during the previous flush. | CPU, then flush latency |
| **POST while a publication runs (50k)** | +426 KB read and +49 KB written per POST; p50 9.6 ms (ext4) and 30 ms (ZFS) (M) | Same as POST | All publication (§2, publication row) |
| **ARTICLE, random 2 KiB** | Syscalls: 3.7-4.2 reads, 3 writes. Reads 12.8-24.5 KB per command, 6-12x (M, all four io runs). CPU 1.7-2.2 ms (M).<br>A cold window reads all of E plus 32 and BLAKE3-hashes it (D: extent.lisp:345,372; extent-window-span.lisp:120).<br>The preflight scans all s; there is 1 row reconstruction with 2 decodes and 1 decisions line. | Index → (segment, off, len), 1 `pread` of s (0 when page-cached), 1 `write`; no hash. | Bytes 6-12x; CPU about 100x |
| **HEAD** | 3 preads and 19 KB for a head of about 500 B (M OPPROF); whole-E digest (D) | 1 pread of h, with h stored in the row | About 40x bytes |
| **STAT** | Builds s payload conses (D: nntp-responses.lisp:107,140) | Index only, 0 reads | s conses → 0 |
| **OVER-40** | Syscalls: 42 writes (one per line), 1 read, 0 preads once publication is idle (M p-io50k; so OPPROF@50k's 18 preads fit publication, INFERRED).<br>40 cursor quanta.<br>Per line: 8 row reconstructions and 16 tree decodes, plus 2 msgid tag-page scans of 1024-2048 slots (D: served-columns.lisp:115,255,278; catalog-paged.lisp:645,304).<br>12.5 MB consed; 5.9 ms CPU at 10k and 8.0 at 50k (M persvati). | k fixed rows plus about 300k overview bytes; 1 `write`; 2 syscalls | About 20x syscalls; about 10³x CPU |
| **GROUP** | 4 full rows and 8 decodes from two summaries (D: served-catalog-view.lisp:214,1003); 1 read and 2 writes (M) | 1 group-summary row (count, low, high), kept at commit | Decodes 8 → 0 |
| **LISTGROUP k** | 2k+4 rows and 4k+8 decodes; builds the whole reply list (D: served-available-commands.lisp:34) | k numbers from the group's number array | About 10³x |
| **LIST, G groups** | 2G rows and 4G decodes; 23 writes and 43 ioctls (SIOCOUTQ and SIOCOUTQNSD probes, mux.lisp:276,294) (M, D)<br>LIST NEWSGROUPS is Θ(G²) alist lookups (D: nntp-responses.lisp:2463). | G summary rows; 1 write per 64 KiB | About 20x syscalls |
| **NEWNEWS** | A full scan of n with 3(n+k) row reconstructions (D: newnews-stream-cursor.lisp:78,480); about 0.6 s at 10k (M C6) | Binary search on the arrival column (monotone in sequence), then k rows filtered by group: O(log n + k) | >10⁴x |
| **Catch-up ingest (B, 10k, K = 128)** | 30.45 articles/s.<br>Device per article: 1.35 flushes, 5.8 writes, **198 KB written** (M p-w6q10k).<br>B's CPU per 1000 articles rises 14.5 → 25 → 34 → ... → 43 s (M). B's checkpoint sequence advances every 1-2 s, so publication runs back to back (M; the per-publication thread is INFERRED from the changing tid).<br>Spool: a 512-B window write, ceil(x/64) 64-B digest preads, replay preads (D: catchup-spool.lisp:16-42).<br>Cursor journal: 1 fsync per publication (D: pull-service.lisp:239-262). | As POST, with b equal to the round window: 1 write and 1 flush per window; the cursor rides in the same entry. | Bytes about 97x; flushes about 1.35b x |
| **Publication** | **Trigger**: 2(count−S) ≥ K, profile max-open-suffix (D: owner-checkpoint-open.lisp:253). This includes straight after an open.<br>**Writes**: a whole new .fnsc of P 16 KiB history pages (power-of-two reserve) + H + arena (every payload) + F/P/E/R runs. Then fsync, rename and dir fsync, and a readback of C (D: io.lisp:3194-3356,3977,4009).<br>**At 50k**: 196-217 MB written and about 550 MB read (process-wide), 35 s CPU (M p-io50k). On ZFS, its fsyncs push 13-37 MB through the ZIL as copies (M h-io*). | Dirty column pages + root: about K/2 × 64 B = 2 MB at K = 65536, 1 fsync + 1 root write; payload bytes 0. | Bytes about 100x per publication; the lifetime total goes from Θ(n²/K) to Θ(n) |
| **Open** | Replays the whole log, reading Σ(e_j+10) with 2 lseeks per entry, and copies the active segment (D: io.lisp:7817,7985).<br>Rebuilds a heap of 115 MB anon at 10k and 432 MB at 50k (M).<br>4.5/5.1 s at 10k and 21.6/28.0 s at 50k (M, persvati/hbox), then a whole publication. | Root pages + replay of the tail since S (≤ K/2 records); columns are paged in on demand | O(n) → O(K) |
| **Reclaim** | Three passes over all N rows plus a full checkpoint C_f write and readback (D: owner.lisp:8743-8965; owner-reclaim.lisp:61) | Segment cleaning: read the live records of the victim segments and append them at the head. Bytes ≈ live/(1−u). | Θ(n) → Θ(live in victims) |
| **Resident memory** | About 8 KB anon per article, the slope from 10k to 50k (M) | About 100 B per article of columns + 16 B of msgid hash; payloads stay in the page cache | About 80x |

Every command also appends 66-68 B to `decisions/decisions.fnj` with its own write (M; owner.lisp:9101, io.lisp:1229). The floor for that is 0 per command, or one line per batch.

## 3. The filesystem layer

**Measured cost of the durability unit:**

| site | 1 append + fdatasync | 8 appends | 64 appends | what one commit is on the device |
|---|---|---|---|---|
| hbox tmpfs | 0.0006 ms | - | - | nothing |
| persvati ext4, client NVMe | 4.0 ms p50 | 4.0 ms per batch | 4.1 ms per batch | about 2.85 writes and 1 flush (M) |
| hbox ZFS, HDD mirror | 8.35 ms p50 | 8.45 ms per batch | 9.2 ms per batch | 1 ZIL commit: the 4 KiB itx is copied into an 8 KB ZIL block, written to both HDDs (M) |

The ZFS row is M design-h-floor at load 1.8; there, 100 MB write+fsync takes 91 ms and rename+dir fsync 9.5 ms. POST p50 on ZFS is 24 ms at one connection (about 3x its flush floor) and 54 ms at 8 connections (M h-io10k).

**ext4 on persvati.**
- The flush, not the bytes, is the cost: 64× 2 KiB costs the same 4 ms as one. So the right unit is a batch of everything queued during the previous flush, and throughput is b/4 ms.
- Today's log extends by `posix_fallocate` (io.lisp:7572, 9484). The first write into an unwritten extent changes extent metadata, so each fdatasync also commits the jbd2 journal: about 23 KB and 2.85 IOs per 4 KiB POST (M).
- Floor: segments written to zero once and recycled. An overwrite of initialized blocks needs only the data write and one cache flush (D, ext4 semantics; the measurement is owed, §6).

**ZFS on hbox** (recordsize 128K, lz4, sync=standard, logbias=latency, txg 5 s, `zfs_immediate_write_sz` 32K, no SLOG).
- Each fdatasync is a ZIL commit. Itxs of 32K or less are **copied** into the ZIL, so the data is written twice (ZIL, then txg) and mirrored: 4 device copies (M: needcopy 4,099,520 B over 1001 commits).
- Itxs over 32K go **indirect**: they are written once in place, and the ZIL logs a pointer (M: publication indirect 29-43 MB).
- Without a SLOG, every commit is an HDD write: 8.4 ms at the floor, 20-35 ms as fn issues them (M).
- A txg rewrites the log's 128K tail record copy-on-write each time it holds appends. So at fewer than 32 appends per txg, txg-level amplification is 128K/(appends × 4K) (D, ZFS semantics).
- 16 KiB page writes into 128K records are read-modify-write: up to 8x (D).
- lz4 shrinks the synthetic fixtures 10x (M: 2.5 MB on ZFS against 26 MB logical, n10000).

**Layout rules that follow:**
- The log is appended in batches; a batch over 32K goes indirect on ZFS (written once).
- Column pages go in a dataset whose recordsize equals the page size, 16K.
- Either a SLOG on NVMe, or the store on an NVMe pool, decides the ZFS commit cost. This is a box decision, ember's (§6).
- hbox's ZFS row is no proxy for NVMe durability timing; its counts (ZIL commits per batch, copies) are what transfer.

## 4. The design: one log of wire-ready payloads, fixed-width columns, checkpoint by dirty page

**The log** is the only payload store and the commit point.
- Segments are fixed size, written to zero once and recycled.
- An entry keeps today's frame: header, predecessor digest, records, BLAKE3 trailer (A-CRYPTO-TRAILER stays).
- A record is a fixed 64-B header:
  - sequence, txid, arrival stamp, msgid hash;
  - head and body lengths;
  - group count.

  Then the Message-ID and group/number list, then the article **in wire form**: CRLF and dot-stuffed, without its terminator. ARTICLE, HEAD and BODY are then a byte range of a stored record.
- One long-lived flusher writes each batch with one `write` and one `fdatasync`, where the batch is what arrived during the previous flush.
- POST, transit, feed, catch-up records with their cursor, configuration (P8's ruling) and resolutions all ride the same batch, so one flush covers an article and every journal fact about it.
- No per-batch thread, no spool file and no separate journal fsync.
- Integrity is checked once:
  - the digest is computed at ingest;
  - an entry read after open is verified once and marked in a per-segment bitmap, an invariant under the single writer (D3).

**The columns** are stobj u64 arrays, and they are the catalog's executable representation (D2):

| column | holds |
|---|---|
| article row, by sequence | locator (segment, offset, len, head len), stamp, txid, msgid hash, withdrawal, flags |
| per group | a number → sequence array and a summary row (count, low, high, next), kept at commit |
| msgid table | open-addressed, hash → sequence |
| overview pool | append-only, holding the NOV fields cut at ingest |

- OVER is k row reads plus pool slices.
- NEWNEWS binary-searches the stamp column.
- No read decodes a tree, and no read touches a payload it does not send.
- Replies are assembled in the pool lease: O's landing 2, and C's window generator.

**Checkpoint** is the column pages that changed, plus a root holding the log position S.
- It uses the page store with its proved crash theorems and def-representation `:pages`. Payloads are never copied.
- Cost per publication is O(K/2 × row width). Over a store's life it is Θ(n).

**Open** adopts the root, pages columns in on demand, and replays the log from S.
- Bytes read are at most root + tail, with no n term.
- No publication follows an open.

**Reclaim** is segment cleaning.
- The live records of low-utilization segments are re-appended through the flusher, and their locators are updated.
- A segment is unlinked only when neither root slot and no lease references it.

**Subsumes:**

| item | how |
|---|---|
| D1 | Payloads never leave byte arrays; the CBOR/list codec stays only on 64-B headers |
| D2 | The columns |
| D3 | Verify once |
| D4 | Dirty pages |
| D5 | Adopt + tail |
| D6 | Allocation per command goes to about 0, which deletes the nursery problem rather than tuning it |
| D7 | Becomes cheap once data work is gone; the 0.2 ms chunk-span floor is then the next target |
| D8 | Its late rise was publication |
| W2 | No decode exists |
| W3 | Kept as the reply path |
| W5, W6 | The flusher |

**Deletes, by path:**

| part | what goes |
|---|---|
| the .fnsc writer and reader | `fnn-state-checkpoint-*` (io.lisp:3182-3356); `fnn-history-image-*` (:3898-4004); `fnn-checkpoint-write-*` (:3827, :4009); books store-checkpoint-arena*, -codec*, -tables*, history-image-* |
| the per-row tree codec on catalog rows | `fn-cp-held`, `fn-cp-decoded` (catalog-paged.lisp:298-304); `fn-scc-*` |
| the msgid tag-page scan | msgid-linear-exec.lisp:936 |
| per-read verification | extent-window-span; `fnn-extent-window-run`; the 8-entry entry cache (extent.lisp:372, 1342, 1480) |
| the NEWNEWS article-list scan | newnews-stream-cursor.lisp:480 |
| the catch-up spool | catchup-spool.lisp |
| the per-batch syncer | owner.lisp:2075, 5092 |
| per-command journal writes | decisions.fnj's per-command write |
| the exports | all of the publication and reclaim PAYLOAD-EXPORT sites (store-checkpoint-arena-writer.lisp:396; store-checkpoint-arena.lisp:646; owner-reclaim.lisp:63; reclaim-chunked-walk.lisp:374; store-node-host.lisp:933, 993) |

**Rests on** (existing keystones):
- the page store: `pgs-open-after-commit`, `pgs-open-after-crash`, `pgs-crash-isolates-other-roots` (pagestore-keystones.lisp:2347, 2493, 2531);
- paged-checkpoint: `fn-pck-dirty-is-the-delta`, `fn-pck-dirty-bound` (:327), `fn-pck-open-after-commit-is-full-recover`, `fn-pck-crash-recovers-from-old-or-new`. These are proved and on no executable path today: write-trace §3 found no fn-pck call in host/;
- `adt-tp-*`;
- `fn-owner-recover-from-checkpoint-equals-full-recover`;
- A-CRYPTO-TRAILER and the torn-prefix keystone;
- the POST machine's AckEligible ⇒ DurableCommitEvidence;
- the lease contract (HL*, KL1-KL12).

**Retires:**
- the fn-sct-*, fn-scka-* and fn-sccr-* keystones;
- the catalog-row tree-codec round-trip keystones;
- the extent-window-span keystones;
- the history-image keystones.

**Restates:**
- the fn-cat-paged correspondence obligations (catalog-paged.lisp:2803-3313), over columns; fn-cat$a stays the abstraction;
- fn-pck-* over column rows that carry a locator, not a payload (D41-STAGE5);
- extent-verify as the verified-segment invariant;
- the spans-newnews keystone, over the stamp column;
- M's per-record heap terms and K-BOUND.

### Landings, each a whole path replaced, statement-first

**LA, one log writer** (P, with L and A).
- POST landing 2 already is its core: span writer, G10(b) single writer, P8's configuration fold. LA widens it to transit, feed, catch-up records with cursors, and resolutions, and adds group commit (W6).
- Deletes:
  - the POST list pipeline (body-chunks.lisp:494; nntp-post.lisp:218,479; the packed take; `fn-octets-list`; the io.lisp:264 coercions; capture lists at store-log-kernel-concrete.lisp:334-343);
  - the syncer per batch, the spool, and the cursor and feed journal fsyncs.
- Keystones:
  - **LA1**: a batch's log effect is the concatenation of its records' encodings (PRE ++ article ++ SUF).
  - **LA2**: an ack implies its batch's fdatasync completed.
  - **LA3**: one fdatasync per batch, and the entries extend a prefix-closed log (P4/E over a batch).
  - **LA4**: a cursor is durable iff the articles it covers are.
  - **LA5**: bytes appended ≤ ΣR_i + frame + pad(U), as a cost row.
  - **LA6**: the stored wire form is a bijection with the article octets.

**LB, columns and reads** (C, with A for the served machine).
- The column stobjs become the catalog's attached representation. ARTICLE, HEAD, BODY, STAT, OVER, GROUP, LISTGROUP, LIST and NEWNEWS read them, and payload bytes come by `pread` of the stored range into the lease.
- Columns are rebuilt from the log at open until LC lands.
- Deletes the decode, tag-scan, per-read digest and NEWNEWS-scan paths above.
- Keystones:
  - **LB1**: the column row at i equals fn-cat$a's row.
  - **LB2**: the kept group summary equals the recomputed one, under commit and withdraw.
  - **LB3**: with a monotone stamp column, NEWNEWS over the range equals the filter of the full scan.
  - **LB4**: verified-entry invariant: a set bit implies the trailer digest holds.
  - **LB5**: the ARTICLE reply bytes are the stored range, which refines F_node's response.
  - **LB6**: cost: OVER does exactly k row reads; ARTICLE does at most 1 pread of s.

**LC, checkpoint, open and reclaim over columns** (L).
- The proved fn-pck machine goes on the host in place of .fnsc. Payloads stay in segments, open is adopt + tail, and reclaim is segment cleaning.
- Deletes the .fnsc writer and reader, whole-store publication, publication after open, the re-intern at open, and reclaim's three passes.
- Keystones:
  - fn-pck-* restated over locator rows;
  - **LC1**: a segment is unlinked only when unreferenced by both root slots and every lease;
  - **LC2**: a cleaned record equals the record it moved, with only its locator changed;
  - **LC3**: bytes read at open ≤ root pages + tail entries;
  - **LC4**: bytes written per publication ≤ dirty pages + root.

**Order.** LA is in flight. LB needs no LA. LC needs LB's columns. D7 follows LB.

**No interim fix.** Raising K would hide the Θ(n²/K) cost, not remove it.

## 5. Triage of current work

| item | verdict | why |
|---|---|---|
| P9 POST landing 2 (lane/post; K1, A1/G-BOUND, A4, R) | **Finish, widen to LA** | It is LA's core |
| L17 lane/log-seq (record refusals, the open identity check) | **Finish** | Correctness; codec bounds survive |
| L17 lane/log-l4 (probe F1/F2) | **Finish** | Correctness |
| L capture-framing restatement for the span writer | **Finish, in LA** | |
| D14 d-bprl-pin (CHECK-C5-HOT-PATH-BPRL) | **Finish** | BP pin walk, not store layout |
| D web-compression RED | **Finish** | Correctness |
| M22 memory-run-launch | **Finish** | Launch sizing, not store layout |
| O5 OVER landing 2 (lease render, W'=1 family deleted) | **Finish** | The reply path survives; it deletes the window-fit family |
| C spans-window READY; fn-ovr-records-parse-or-reclaimedp | **Finish** | O's generator and premise |
| A vertical-post-heap (C11) | **Finish** | Already READY; removes a live export |
| A21 owner-retain | **Split** | K1, the owner-state carry, finishes. K2, the checkpoint route at io.lisp:3040, 3074 and fn-ssr-intern, **stops**: LC deletes that route (rule 6.7) |
| C21 W2 decode-once (lane/spans-decode-once) | **Stop** | LB deletes `fn-cp-held`; K-W2a/b's counts become LB6 |
| PAYLOAD-EXPORT-* L rows: checkpoint ×4, reclaim ×2, state-digest; A's shared-pending (owner-host.lisp:2840) | **Stop** | Deleted by LC; owner-host.lisp:2840 by LA |
| PAYLOAD-EXPORT-* A rows: keyring (store-intern.lisp:128,131), consumer poll (history-fold-refinement.lisp:293), BP ×3, offline pending (store-node-host.lisp:1612) | **Keep queued** | Not on LA, LB or LC's paths; re-scope as locator reads after LB |
| D1, D6 | **Do not start** | Subsumed |
| D2, D3, D4, D5 | **Do not start as items** | Become LB and LC |
| W4 judged persvati A/B; OPPROF judged reruns | **Stop** | Within noise; the target paths go |
| A RECLAIM-COUNTERPART-SELECTOR | **Hold** | Retires with LC unless a non-reclaim entry reproduces it |
| A candidate: transit relayed-header rebuild | **Into LA** | |

## 6. Owed and decisions

**Owed (measurement), as ONE Codex run (SEAT-COMMON, big steps).**
- One brief takes the whole remaining campaign, so the worker owns the counts table end to end:
  - the DESIGN-IO cell, for every operation in §2: add HEAD, STAT, GROUP, LISTGROUP, LIST and NEWNEWS phases, plus a reclaim phase;
  - the ext4 overwrite-against-fallocate floor variant in floor.c;
  - one script that turns both boxes' runs into §2's table.
- The seat launches the box jobs (Codex launches none), interleaved on both boxes the same day, then rewrites §2 whole.
- The DESIGN-IO instrumentation is in build/lanes/design-model (unpushed); it goes to Perf's harness lane with that run.

**Each landing is one large Codex run after its statements are approved.**
- LA, LB and LC each get one brief: the approved keystones, the real signatures, every path it deletes (the lists in §4), the test sweep for the retired behaviour (SEAT-COMMON), and the lane gates.
- The owner seat writes and searches the statements first. Then one worker proves and implements the whole landing, and a fresh worker reviews it.

**Decisions for ember:**
1. D3's claim change: "every served byte was verified at ingest, or once after open", instead of on every read.
2. Whether hbox gets an NVMe SLOG, or a store dataset with recordsize 16K for column pages. A ZFS commit costs an HDD write today.
3. Whether this design replaces D1-D8 in the plan, so the coordinator can stop W2 and the export items above.
