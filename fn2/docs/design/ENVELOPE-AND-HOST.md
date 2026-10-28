# fn2: the performance envelope and the host model (2026-10-28)

Read-only exploration for fn2, the TigerStyle rebuild of fn. Sources are cited inline. Every figure is tagged:
**[M]** measured (cited run or document), **[D]** derived here by arithmetic from stated inputs, **[A]** an assumption about
hardware or a library, with its basis. origin/dev at the time of reading: `6521f18c4`. Nothing here was built or run; the
arithmetic is the envelope, and every [A] is a thing a FLOOR run should confirm before a bound is frozen.

Part 1 follows TigerStyle's order (tiger-style.md, "Performance": network, disk, memory, CPU, each by bandwidth and latency,
"optimize for the slowest resources first ... after compensating for the frequency of usage"). Part 2 is the host: what it must
provide and nothing more.

---

# Part 1. The performance envelope

## 1.1 Hardware assumptions (the four resources)

| resource | bandwidth | latency | basis |
|---|---|---|---|
| network, public node (Hetzner 1 GbE) | ~117 MB/s | WAN RTT 10-100 ms | [A] line rate less framing |
| network, LAN / 10 GbE | ~1.17 GB/s | RTT 0.05-0.5 ms | [A] |
| network, loopback (the gauntlet's transport) | several GB/s | 2 KiB request + preformatted `write()` reply: p50 0.0079 ms, CPU 0.0091 ms (client and server together); 40 lines (6 KB) 0.0103 ms CPU; 128 KiB 0.031 ms CPU | [M] PERF-MEASUREMENTS-20261012 FLOOR |
| disk, client NVMe with volatile write cache (persvati, ext4) | ~2 GB/s sequential write [A] | append + fdatasync p50 **4.0 ms**, the same for 1, 8 or 64 appends (4.0 / 4.0 / 4.1 ms per batch) | [M] DESIGN-RESOURCE-MODEL §3 |
| disk, ZFS on an HDD mirror, no SLOG (hbox) | 100 MB write + fsync in 91 ms | fdatasync p50 **8.35 ms** (8.45 at 8 appends, 9.2 at 64) | [M] DESIGN-RESOURCE-MODEL §3 |
| disk, enterprise NVMe with power-loss protection | ~2-3 GB/s | flush or FUA write ~0.02-0.1 ms (the cache is non-volatile, so a flush is nearly free) | [A] vendor class; owed as a FLOOR row |
| disk, NVMe random 4 KiB read | 400k-1M IOPS at queue depth 32-64 | ~80-100 µs at QD1 | [A] (Haas and Leis, VLDB 23: millions of IOPS only with async I/O and many outstanding requests) |
| tmpfs | memory speed | fdatasync 0.0006 ms | [M] |
| memory | ~10 GB/s single-core memcpy | ~80-100 ns per DRAM miss (one 64 B line) | [A] |
| CPU, BLAKE3 | ~2 GB/s per core for KiB-sized inputs (more with SIMD on large inputs) | 2.4 KiB in ~1 µs | [A] |
| CPU, a byte scan (CRLF, dot-lines, header colon) | ~5 GB/s | 2 KiB in ~0.4 µs | [A] memchr-class |
| CPU, AES-GCM (TLS record crypto) | 2-4 GB/s per core with AES-NI | | [A] |
| CPU, TLS handshake | | ~0.5-2 ms of CPU per full handshake (ECDHE + signature), ~0.1 ms resumed | [A] |

The ordering this gives fn2: **the flush is the only expensive thing in a POST** (4 ms against microseconds of everything else),
**the network is the only expensive thing in a large transfer** (3 MiB at 1 GbE is 25 ms), and **CPU and memory matter only through
frequency**: they are microseconds per operation, multiplied by every operation. Today fn inverts this: CPU is 3.0 ms per POST and
5 ms per ARTICLE ([M] PERF-MEASUREMENTS), so CPU dominates even the flush.

## 1.2 The target workloads

| workload | what it asks | source |
|---|---|---|
| **The gauntlet bars** (fn's public product bars) | ARTICLE 2 KiB at 16 readers beside one poster at 5 POSTs/s: p50 <= 5 ms, p99 <= 50 ms, p99(16)/p99(1) <= 2. POST durable p50 <= 20 ms, p99 <= 250 ms, CPU <= 16 ms per POST, >= 10 POSTs/s on ZFS and >= 50 on tmpfs. Every command's p99 <= 50 ms with growth exponent in store size <= 0.2. ARTICLE time linear in size. Publication stall <= 2 s. Catch-up >= 35 articles/s at 1k, 10k and 100k. Open from checkpoint <= 10 s at 40k. Whole-process peak <= 128 MB (relaxed to a 249 MB guardrail by ember, GOALS G7). Slow-reader owner growth <= readers x reply size. | GAUNTLET.md; PRODUCT-DRAFT-20261009 |
| **What fn measures today** | R16 ARTICLE p50 82.6 ms, p99 131.6 ms, 203 reads/s (about 4.9 ms of server time per read, serialized); R1 p99 35.2 ms. POST c1 85.1/s at p50 9.35 ms and 11.68 ms CPU; c8 149.6/s, CPU-bound at about 3 ms per POST. VmHWM 135.5 / 177.9 MiB on the small preset. Slow-reader owner growth +107.9 MiB against a 2 MiB bound. Publication writes the whole store (exponent 0.95). | GAUNTLET.md (drain-20261009) |
| **G6: 10-100x** | OVER-40: 7.20 ms CPU and 645 syscalls (futex 146, rt_sigprocmask 261) against a 0.0103 ms floor (~700x). POST 2 KiB: 3.00 ms CPU and 227 syscalls (futex 89, rt_sigprocmask 75, write 13, read 8, poll 6, tgkill 5, clone3 1, fdatasync 1) against a floor of about 4. POST CPU doubles from 10k to 50k. | GOALS.md G6; PERF-MEASUREMENTS |
| **Representation** | POST changes whole-article representation 18 times between the socket and the log, 16 under the owner mutex, at least 14 of them cons-list passes at 16 B per octet. ARTICLE is 3 buffer-to-buffer copies. | REPRESENTATION-HISTORY-20261028 §2.3 |
| **akapug's fleet** (the first outside consumer) | about 30 seats on 4 boxes, 3-7k rows a day; today a 2.0 s file poll wakes at 0.34-2.16 s. Wants served remote `wait`/`ack` over TLS, a waiter bound above the 12-waiter cap, per-group wake, an inbox spanning a room, DMs and mentions. Acceptance: wake p50/p95 and crash/redelivery. | emberian/fn#19 |
| **fn2's own ambition** | "a high performance database node" (a generalized redis/postgres for ember's data models), the persistent event log of the robigalia distributed OS. | briefs/PAPERS-20261028.md; EMBER.md:508 |

akapug's demand in the four resources [D]: 7,000 rows/day is **0.081 rows/s** on average; a 100x burst is 8 rows/s. At 2 KiB a row,
storage grows 14 MB/day, about **5 GB/year**. That is three orders of magnitude below what one group-committed flush serves. The
fleet does not ask for throughput: it asks for **wake latency** (a commit is published at the flush's completion, so the floor is
t_flush + one send + one network RTT: about 4-5 ms on client NVMe plus the WAN RTT, against today's 0.34-2.16 s) and for
**connection and waiter counts** (30 seats x up to 4 boxes = 120 parked waiters at most; the 12-waiter cap is the binding limit, and
a waiter must be a state of a connection, bounded by the connection cap, not a separate resource with its own cap).

The design target, therefore: meet the gauntlet bars with two orders of magnitude of headroom on one core, so that fn2's "database
node" ambition (10^4-10^5 small commits/s, 10^5 reads/s) is the same machine at a larger configuration, not a different design.
TigerBeetle's argument applies (concepts-performance.md, "Performance = Flexibility"): a system that runs at one tenth of capacity has
headroom for the unexpected.

## 1.3 POST: the minimum copies, syscalls and flushes

**Assumptions.** Plaintext NNTP (TLS adds one encrypt/decrypt pass per direction, §1.7). The stored form is the wire form
(DESIGN-RESOURCE-MODEL §4: CRLF line ends and dot-stuffing kept, terminator dropped), so the body bytes received are the body bytes
stored. A record is a fixed 64 B header, the Message-ID and group list (~70 B), the injected header lines fn adds (Path, Date,
Xref, Injection-Info: ~200 B [A]), then the article as received. So a 2 KiB article is a **~2.4 KiB record** [D]. The log is
appended in sector-aligned units of 4 KiB (§1.8 says why 4 KiB), and **a sector holding acknowledged data is never rewritten**
(rewriting it risks tearing data already acknowledged: crash-model row 10, a 4 KiB write on a 512e device tears at 512 B), so every
batch begins at a fresh sector and pays its tail pad once.

NNTP's POST is two-phase: the client sends `POST`, waits for `340`, sends the article, waits for `240`. The 340 round trip is part
of the protocol, not of fn; IHAVE/TAKETHIS streaming (RFC 4644) removes it for peers.

### POST 2 KiB

| quantity | minimum | why |
|---|---|---|
| CPU copies of the article | **2** | kernel socket buffer -> the connection's receive buffer (1), receive buffer -> the batch buffer at the record's offset (1). The second is unavoidable under O_DIRECT, since a gathered write needs every iovec sector-aligned in address and length, and a 2.4 KiB record from several connections cannot be. With buffered I/O the user copy can become a `writev` gather, but the kernel then copies into the page cache, so the count is still 2. The device reads the batch buffer by DMA. |
| passes over the article | **2 reads, fused** | one scan (terminator, dot-lines, header boundaries, line limits) and one BLAKE3 over the record, both while the 2.4 KiB is in L1 [A]: ~0.4 + ~1 µs |
| syscalls, classic sockets | **4 + 2/b** | `recv` POST, `send` 340, `recv` the article (2 KiB fits one segment), `send` 240; per batch of b records one `write` (or `pwrite`) and one `fdatasync`. DESIGN-RESOURCE-MODEL's "about 3 + 2/b" folds the 340 into the next read. Today: **227** [M]. |
| syscalls, io_uring | **~(4 + 2/b) / k** | the same operations are ring entries; one `io_uring_enter` submits and reaps k of them. At k = 16 that is ~0.3 syscalls per POST; with SQPOLL, 0 (and a core spent polling). |
| flushes | **1/b** | one `fdatasync` (or one FUA commit write, §1.7) per batch, b the records queued during the previous flush (§1.5). At one connection in a closed loop b = 1. |
| bytes written | **~2.4 KiB + pad** | a batch of one record writes one 4 KiB sector (1.7x); the pad is paid once per batch, so at b = 8 it is ~1.1x. Today: 4,096 B per POST from the U = 4096 pad, plus ~23 KB and 2.85 device writes per POST on ext4 because `posix_fallocate` leaves unwritten extents whose first write commits the jbd2 journal ([M] DESIGN-RESOURCE-MODEL §3). A segment **zero-filled once by real writes and recycled** costs one data write and one cache flush per batch. |
| latency floor | **t_flush + 2 RTT + ~10 µs** | 4.0 ms on client NVMe (today p50 9.35 ms judged, 11.5 ms at C2), 8.35 ms on hbox ZFS (today 24.3 ms), ~0.1 ms on PLP NVMe |
| CPU floor | **~10-15 µs** [D] | parse head 0.5 µs, scan 0.4, hash 1, Message-ID probe 0.2, row and group-array insert 0.3, batch copy 0.1, plus ~4 socket operations at ~2 µs of kernel time each. Today 3.00 ms at 10k and 6.40 ms at 50k [M]: 200-600x. |
| allocation | **0** | every buffer is a slot of a pool sized at start. Today 3.1 MB consed per POST [M]. |

### POST 3 MiB

A 3 MiB article does not fit a connection's receive buffer and must not be made to: the head (at most `max-header-octets`, 16 KiB,
fn's default) is parsed and the Message-ID checked for a duplicate before the body is accepted, and the body is **streamed**.

- **Layout: value separation.** The body goes to **blob blocks** in the data file's grid (fixed blocks, §1.8), written as it arrives;
  the log record carries only the head, the list of block references `(index u64, checksum u128)` and the body length (WiscKey's
  key/value separation, Lu FAST 16; TigerBeetle's external checksums: a block's checksum lives in its parent, so a misdirected write
  or read is detected). The commit record stays small and joins the ordinary batch, so a large POST does not stall the log head
  behind 3 MiB of writes.
- **Copies: 1.** Receive straight into a sector-aligned chunk buffer (256 KiB [A]) that is itself the O_DIRECT write source: kernel ->
  user is the only CPU copy; the device reads the chunk by DMA. Because the stored form is the wire form, no transformation copy
  exists. The scan and BLAKE3 run over each chunk while it is in L2.
- **Passes**: scan + hash over 3 MiB: ~0.6 + ~1.5 ms of CPU [D].
- **Syscalls, classic**: 3 MiB / 256 KiB = **12 `recv`** (more if the socket hands back less; at a 64 KiB socket read, 48), **12 `pwrite`**,
  the commit record in the batch's one `write`, and 1/b `fdatasync`. **io_uring**: the same 24-25 operations, in a handful of `enter`s.
- **Flushes: 1/b**, the same as a small POST: one flush makes the blob blocks and the commit record durable together (§2.5 gives the
  ordering rule: the commit record is written after the blob writes complete, and it carries their checksums).
- **Memory**: two chunk buffers per in-flight large upload (one filling from the socket, one writing), **512 KiB, independent of A**.
  The bound on A (`max_article_octets`) bounds only the length of the article's block-reference list (16 MiB / 64 KiB blocks =
  256 references of 24 B, one 64 KiB blob-index block), so the commit record carries a single reference whatever A is.
- **Latency floor**: the network. 3 MiB at 1 GbE is **~25 ms** of transfer [D] (plus TCP slow start on a cold connection); at 10 GbE
  2.5 ms; on loopback ~1 ms. Disk: 3 MiB at ~2 GB/s is 1.5 ms, overlapped with the transfer. The flush is then t_flush after the last
  chunk.
- **Today**: about 17 whole-article cons-list copies at 16 B per octet ([D] DESIGN-RESOURCE-MODEL §2 "l4-trace"): ~800 MB of
  allocation for one 3 MiB article [D: 3 MiB x 16 x 17], all of it inside the owner mutex.

A POST that is refused after its body has streamed (a body limit, a late authority change) leaves blob blocks that no committed
record references; they return to the free set (the grid's free set is part of the checkpoint, TigerBeetle data-file.md), so the
refusal costs disk bandwidth and nothing durable.

## 1.4 ARTICLE at 16 readers: the minimum bytes scanned and copies

**Assumptions.** A 2 KiB article (the T-READ cell), the 2.4 KiB record of §1.3, addressed by Message-ID or by group number. Indexes
are fixed-width resident columns (§1.6). Payloads live in fn2's own block cache (§1.7) or are read cold with one O_DIRECT read.

**Per ARTICLE, warm:**

| step | bytes touched | cost |
|---|---|---|
| parse the command line | ~50 B (an NNTP command line is at most 512 octets, RFC 3977 §3.1) | ~50 ns |
| Message-ID hash | ~40 B (at most 250, RFC 5536 §3.1.3) | ~50 ns |
| Message-ID table probe | one slot, one 64 B line (open addressing at load <= 0.5: expected probes ~1.5) | ~100 ns, one DRAM miss |
| the article row | one 64 B row: locator, length, head length, checksum | ~100 ns, one miss |
| exact identity | compare the requested Message-ID with the one stored in the record (in the cached block) | ~20 ns |
| reply | status line + the record's wire-form range + `.\r\n`, as **3 iovecs over the cached block**; no rendering, no dot-stuffing (stored stuffed) | one `send` |
| **bytes scanned** | **~200 B of index and command, 0 B of payload** (the payload is not read by the CPU at all; the kernel copies it) | |
| **copies** | **1**: the kernel's copy from the pinned cache block into the socket buffer | |
| syscalls | 1 `recv` + 1 `send` (classic); ~2/k (io_uring) | |
| CPU | **~3-5 µs**, nearly all of it the kernel's TCP send path ([M] FLOOR: 0.0091 ms for client and server together at 2 KiB) | |

Zero-copy send (`MSG_ZEROCOPY`, io_uring `SEND_ZC`) is not worth it at 2 KiB: the completion notification costs more than copying
2 KiB (~0.2 µs) [A]; it pays above ~10-16 KiB, so a large ARTICLE uses it and a small one does not. The block stays **leased** (pinned,
immutable, not evictable) until the send's completion; that is the runtime contract's :out lease, and it is what makes the copy-free
reply safe.

**Cold**: add one O_DIRECT read of the record's sectors, `ceil(2.4 KiB / 4 KiB) = 1` sector, **4 KiB** (read amplification 1.7x),
~80-100 µs on NVMe at low queue depth [A], ~1 µs of CPU; the record's checksum (held in the row, outside the block) is verified when
the block enters the cache (BLAKE3 of 4 KiB, ~2 µs), and never again while it is cached. Under buffered I/O the kernel's readahead
would read up to 128 KiB for this 4 KiB (`POSIX_FADV_RANDOM` is needed), and a cache hit cannot be told from a disk read, so a
buffered design must either hash every read or trust the page cache; O_DIRECT has no such ambiguity (§1.7).

**Today** ([M] DESIGN-RESOURCE-MODEL §2): a random 2 KiB ARTICLE reads 12.8-24.5 KB (a cold window reads the whole ~19 KB entry and
BLAKE3-hashes it), 3.7-4.2 reads and 3 writes, 1.7-2.2 ms of CPU, plus a row reconstruction with two tree decodes and a decisions-log
line. ARTICLE's three buffer copies are fine ([M] REPRESENTATION-HISTORY §2.3); the cost is the work around them.

**At 16 readers** [D]: 16 x ~5 µs = 80 µs of executor time per round of one ARTICLE from each reader. With one poster at 5 POSTs/s,
the executor is busy ~0.1% of the time. Queueing behind 15 other ARTICLEs adds at most 75 µs, so **p99(16)/p99(1) is ~1**, bounded by
the network and client, not the server; p50 is the loopback RTT plus ~5 µs. The bar (p50 <= 5 ms, p99 <= 50 ms, ratio <= 2) is met
with three orders of magnitude to spare, as long as no step does work proportional to anything but its own reply. Today's 131.6 ms
p99 at R16 is 16 readers serialized on the owner at ~4.9 ms each.

**Ceilings, one core** [D]: ~5 µs per warm ARTICLE is ~200k/s; at 2.5 KiB per reply that is 500 MB/s, above 1 GbE's ~117 MB/s, so a
public node is **network-bound at ~46k ARTICLE/s** and a 10 GbE node CPU-bound at ~200k/s. Cold, a client NVMe at QD 64 gives
~400k random 4 KiB reads/s [A], so the disk is not the ceiling either.

**OVER-40 at the floor** [D]: 40 consecutive rows (2.5 KiB, one 64 KiB index block) plus 40 overview entries (~300 B each [A], 12 KB,
appended at ingest to an overview pool) rendered into one send buffer: ~12 KB copied once, 1 `send`, **~5-10 µs**. The FLOOR's 6 KB
40-line reply is 0.0103 ms [M]; today 7.20 ms and 645 syscalls.

## 1.5 Group commit at 100 and 1,000 POSTs/s

**The rule** (DESIGN-RESOURCE-MODEL §3-4; TigerBeetle's "batches automatically become smaller under light load"): one flusher; while
a flush is in flight, records queue; when it completes, everything queued goes out as one write and one flush. Nothing waits for a
batch to fill, so light load gets single-record latency and heavy load gets large batches.

**The model** [D]: Poisson arrivals at rate λ, a deterministic flush time t_f, x = λ t_f. Mean-field: a flush carries the record
that started it plus the arrivals during the previous flush when the flusher was busy, b = 1 + x·U with utilization U = x/b, so
**b = (1 + sqrt(1 + 4x²)) / 2**, **flushes/s = λ/b**, **mean ack latency ≈ t_f (1 + U/2)**, worst ≈ 2 t_f plus the write. Bytes per
second = λ x 2.4 KiB + (flushes/s) x ~2 KiB of mean tail pad.

| site (t_f) | λ | x | b | flushes/s | U | mean ack | worst ack | device bytes/s |
|---|---|---|---|---|---|---|---|---|
| client NVMe (4.0 ms [M]) | 100/s | 0.4 | 1.14 | 88 | 0.35 | 4.7 ms | ~8 ms | ~0.42 MB/s |
| client NVMe | 1,000/s | 4.0 | 4.5 | 221 | 0.88 | 5.8 ms | ~8 ms | ~2.9 MB/s |
| hbox ZFS HDD (8.35 ms [M]) | 100/s | 0.84 | 1.47 | 68 | 0.57 | 10.7 ms | ~17 ms | ~0.38 MB/s |
| hbox ZFS HDD | 1,000/s | 8.35 | 8.9 | 113 | 0.94 | 12.3 ms | ~17 ms | ~2.7 MB/s |
| PLP NVMe (~0.1 ms [A]) | 100/s | 0.01 | 1.0 | 100 | 0.01 | 0.1 ms | ~0.2 ms | ~0.44 MB/s |
| PLP NVMe | 1,000/s | 0.1 | 1.01 | 990 | 0.10 | 0.1 ms | ~0.2 ms | ~4.4 MB/s |

What the table says:
- **Both rates are trivial for the device.** 1,000 POSTs/s is ~2.4 MB/s of payload; the flush count, not bytes, is the cost, and
  group commit holds the flush count at or below 1/t_f (250/s on client NVMe, 120/s on hbox ZFS) whatever λ is.
- **Latency stays within 2 t_f at any rate up to the batch cap.** The POST bar (p50 <= 20 ms, p99 <= 250 ms) is met on every site;
  on hbox ZFS by ~1.2-2x margin at p50 (12.3 ms), which is why DESIGN-RESOURCE-MODEL §3's SLOG question is the real latency lever there.
- **CPU** at ~15 µs per POST [D] is 0.15% of a core at 100/s and 1.5% at 1,000/s. Today 3.0 ms per POST [M] would be 3 cores at 1,000/s,
  on one owner: the measured c8 ceiling is 149.6/s.
- **The client is the limit at one connection.** A closed-loop poster waits 2 RTT + the ack per POST: ~6 ms on NVMe is ~170 POSTs/s per
  connection, ~80/s on hbox ZFS; 1,000/s needs >= 6 (NVMe) or >= 13 (ZFS) concurrent posters, or one TAKETHIS stream.
- **Ceiling** [D]: with a batch cap of 1,024 records or 4 MiB (§1.8), b/t_f is 256k records/s on client NVMe, where the bytes reach
  614 MB/s; CPU at ~15 µs is ~67k POSTs/s per core, so **CPU is the ceiling at ~10^4.8/s**, 450x today's measured c8 rate and above
  fn2's database-node target.
- **akapug's 0.08 rows/s** is the λ -> 0 row: b = 1, ack = t_f. Wake latency = the flush plus one send per waiter.

## 1.6 Memory for a 1M-article store with fixed-width columns

**Assumptions** [A]: n = 2^20 articles; mean record 2.4 KiB (§1.3); mean 1.5 groups per article (crossposts); Message-ID mean 40 B
(max 250); overview entry (Subject, From, Date, Message-ID, References, bytes, lines) mean ~300 B; 4,096 groups in use, 65,536 the
ceiling; 256 connections.

**The article row, 64 B, one cache line**, by sequence number (a u32 `seq` addresses 4G articles):

| field | width | use |
|---|---|---|
| locator: data-file offset | u64 | where the record starts (sector-aligned base + offset) |
| record checksum | u128 | external checksum (TigerBeetle hash-chaining: the parent holds the child's checksum, so a misdirected read or write is detected) |
| arrival stamp | u64 | NEWNEWS binary search (monotone in seq) |
| txid | u64 | |
| Message-ID hash | u64 | second-level identity check before the byte compare |
| record length, head length | u32 + u32 | HEAD/BODY ranges without parsing |
| membership index | u32 | first (group, number) of this article in the membership pool |
| group count, flags (withdrawn, large) | u16 + u16 | |

**Terms** [D]:

| structure | per article | at 1M | resident? |
|---|---|---|---|
| article rows | 64 B | 64 MiB | paged through the block cache (hot tail resident); resident if the box has room |
| Message-ID table: open addressing, 2^21 slots (load 0.48), slot = `seq u32` + 32-bit tag of the hash | 16 B (2 slots) | 16 MiB | **resident**: an absent-ID probe (IHAVE/CHECK, the common peering case) costs 0 disk reads; a tag match is confirmed by the row's 64-bit hash and then by the record's bytes, so identity is exact (fn's P2) at ~1 read per *present* lookup |
| per-group number -> seq arrays | 1.5 x 4 B | 6 MiB | resident |
| membership pool (group u16 + number u32, padded to 8) | 1.5 x 8 B | 12 MiB | resident (Xref and the group list without a read) |
| group summary rows (count, low, high, next, flags) | | 65,536 x 64 B = 4 MiB at the ceiling | resident |
| overview pool, appended at ingest | ~300 B | ~300 MiB | **paged** (on disk, cached on demand) |
| payload log | 2.4 KiB | ~2.4 GiB | on disk; hot blocks in the cache |

**Resident index: ~38 MiB at 1M articles with rows paged, ~102 MiB with rows resident** (16 + 6 + 12 + 4, plus 64), i.e. **~36-100 B per
article**. Today: ~8 KB of anonymous heap per article (the slope from 10k to 50k, [M] DESIGN-RESOURCE-MODEL §2), which is **8 GB at 1M**.
The ratio is **80-220x**.

**A whole-process budget, 1M articles, 256 connections** [D], everything allocated once at start:

| term | size | note |
|---|---|---|
| binary, libraries, stacks | ~10 MiB | a native binary [A]; an SBCL image adds its measured floor (anon 63.9 MiB + file 65.5 MiB at rest, [M] GAUNTLET L-RSS arm A) |
| resident index | 38 MiB | as above, rows paged |
| block cache (payload, rows, overview) | 64 MiB | the operator's figure, the only large free choice |
| connections: 16 KiB receive + 16 KiB send + ~1 KiB state | 256 x 33 KiB = 8.3 MiB | the receive buffer holds a whole head (16 KiB max) |
| TLS session state | 256 x ~50 KiB = ~12.5 MiB | [A] OpenSSL per-connection buffers; kTLS or a smaller record buffer cuts it |
| commit pipeline: 2 batch buffers of 4 MiB | 8 MiB | one filling, one flushing |
| large uploads: 16 x 2 x 256 KiB | 8 MiB | §1.3 |
| reply lease pool | inside the block cache | a reply pins cache blocks; it owns no memory of its own |
| io_uring rings: SQ 4,096 x 64 B, CQ 8,192 x 16 B | 0.4 MiB | |
| **total** | **~150 MiB** | to fit 128 MiB, the cache is 40 MiB; the small preset (T = 16,384: index 0.6 MiB) fits in ~70 MiB with a 32 MiB cache |

The bound is a function of the configuration, written down before start, and the process cannot exceed it: no allocator runs after
start. The gauntlet's slow-reader bar (owner growth <= readers x reply size) is met structurally: a slow reader holds at most one
leased window of cache blocks, and its growth is 0.

**A finding the arithmetic forces: do not persist the hash table.** A hash index scatters inserts: after 4,096 inserts into a 16 MiB
table of 4 KiB pages essentially every page is dirty, so a checkpoint "by dirty page" of the Message-ID table is the whole table each
time, the Θ(n) publication fn has today in another form. Two ways out: an LSM for the ID index (TigerBeetle's id tree, lsm.md), or
**rebuild it at open**: read the rows sequentially (64 MiB at ~2 GB/s, ~32 ms) and insert 1M hashes (~50 ns each, ~50 ms) [D], **~0.1 s
at 1M**. The rebuild is simpler, has no crash story of its own, and costs less than the open bar (<= 10 s at 40k) by two orders. The
same argument applies to every derived index (group summaries, the stamp search): persist only append-only data (the log, the rows,
the per-group arrays, the overview pool, each dirtying only its tail pages, so a checkpoint is O(K x row width) as DESIGN-RESOURCE-MODEL
§4 wants), and derive the rest. A withdrawal (cancel) is the one in-place row change; it is rare, and it can be an appended tombstone
instead.

## 1.7 What io_uring and O_DIRECT change against the page cache

At fn's rates the throughput difference is small (a 2 KiB buffered write is ~1-2 µs of CPU against a 4 ms flush). The differences
that matter are **correctness under faults, tail latency under our own control, and the cost of a syscall per operation**.

| | buffered I/O + `fdatasync` (fn today) | O_DIRECT + own block cache | + io_uring |
|---|---|---|---|
| CPU copies, write | user -> page cache (kernel copy), then writeback DMA | 0: DMA from the aligned user buffer | same |
| CPU copies, read | page cache -> user (kernel copy), cache shared with the kernel | 0: DMA into a cache block | same, with registered buffers (no per-I/O page pinning) |
| alignment | none | offset, length and buffer address aligned to the logical block (512 B or 4 KiB): tail pads, never rewrite an acknowledged sector | same |
| durability | `fdatasync`; on failure the error may be reported once and the dirty pages marked clean; ext4/XFS keep the unwritten data in cache, Btrfs reverts (Rebello ATC 20). The only safe answer to a failed fsync is to crash and recover from the log. | per-I/O errors on each write's completion; still needs a flush (or FUA writes) for a volatile device cache; no page-cache view to disagree with the disk | flush as a ring entry linked after the writes (`IOSQE_IO_LINK`), or `RWF_DSYNC` per write |
| ordering at a crash | fn's model lets survivors land in issue order per file. That is an assumption, and only the page cache is even a candidate for it (writeback does not promise it either for multi-page appends) | **none**: in-flight writes complete in any order and a crash lands any subset (crash-model row 11); a commit must be gated on completions and checked by checksums at recovery (§2.5) | completions arrive out of order by design (Axboe 19) |
| read integrity | a cache hit and a disk read look the same, so either hash every read or trust the page cache | verify once when a block enters the cache; hits are our own memory | same |
| readahead | up to 128 KiB per random 4 KiB read unless `POSIX_FADV_RANDOM` | exactly what was asked | same |
| tail latency | dirty throttling (`balance_dirty_pages`) can stall the writer; writeback storms; memory pressure evicts our working set | the cache is ours, sized at start; nothing evicts it | the executor never blocks in a syscall |
| syscalls per POST | 4 + 2/b (+ `epoll_wait`) | same | **~(4 + 2/b)/k**, k operations per `enter`; 0 with SQPOLL |
| memory accounting | file pages: outside RssAnon but inside a cgroup's `memory.max`; the L-RSS row's "file 65.5 MiB" is this | anon, counted, exactly the configured cache | |
| file system needed | yes | no: works on a raw block device (TigerBeetle architecture.md, "Direct IO") | |
| portability | every POSIX system | Linux, FreeBSD; darwin has only `F_NOCACHE`, OpenBSD none | Linux 5.1+, and **often disabled** |

Two cautions:
- **io_uring and untrusted input.** TigerBeetle justifies io_uring because it "only deals with trusted integer data" (concepts-safety.md);
  io_uring is disabled in Google's production kernels and in many container seccomp profiles after its 2022-23 exploits. fn2 parses
  untrusted strings from the public internet. The host therefore needs **a second backend with the identical submission/completion
  interface**: epoll for sockets plus a small pool of blocking I/O workers for `pread`/`pwrite`/`fdatasync` (an O_DIRECT read on an
  epoll loop still blocks). The workers execute actions and return completions; they never step a machine (RUNTIME-MODEL §1).
- **The flush on client NVMe is the latency floor whichever path is used**: 4.0 ms [M]. O_DIRECT removes the jbd2 journal commit that
  `posix_fallocate`d extents cost (~23 KB and 2.85 device writes per POST [M]) only if segments are zero-filled once by real writes;
  that fix is independent of O_DIRECT and fn could take it today.

**Recommendation**: O_DIRECT into a single preallocated, zero-filled data file (or a raw block device), its own block cache, io_uring
where the kernel allows it and the epoll/worker backend where it does not, with the same completion interface over both. The page
cache path remains only as darwin's development backend (`F_NOCACHE` + `F_FULLFSYNC`), which never claims the O_DIRECT fault model.

## 1.8 The bounds fn2 should hard-code

Two kinds of number, kept apart. A **ceiling** is a compile-time constant: it fixes a field width or a table's index type, and the
relationships between ceilings are compile-time assertions (tiger-style.md: "assert the relationships of compile-time constants").
A **profile value** is the operator's, chosen at `format`/start within the ceiling and fixed for the life of the process: every pool,
table and ring is allocated from it once, before the loop starts (TigerBeetle architecture.md, "Static Memory Allocation": the worst
case per object type, computed from the arguments). That keeps fn's D27 ("a constant that bounds data is a defect": data bounds are
the operator's) and TigerStyle's "put a limit on everything" in one rule. The presets: **small** (fn's small preset, a 128-249 MB
node) and **default** (a public node).

| bound | ceiling | small | default | reason |
|---|---|---|---|---|
| sector (I/O alignment and the never-rewritten unit) | 4 KiB | | | O_DIRECT alignment on 4Kn and 512e devices; the unit a batch pads to; an acknowledged sector is never written again (a 4 KiB write may tear at 512 B on 512e) |
| grid block (index, overview, blob and log blocks; the cache unit; the checksum-addressed unit) | 64 KiB | | | 1,024 rows or ~200 overview entries per block, so OVER-40 touches 1-2 blocks; fine cache granularity at a 40 MiB cache (640 blocks); a 3 MiB body is 48 blocks. TigerBeetle uses 512 KiB for a much larger working set |
| log extent (sequential append and cleaning unit) | 1 MiB (16 blocks) | | | appends stay sequential; cleaning moves at most 1 MiB of live records per victim |
| superblock copies, quorum | 4, read quorum 2 | | | TigerBeetle data-file.md: a misdirected read can hide the single latest copy |
| checkpoint interval | 65,536 records or 64 MiB of log | | | open replays at most 64 MiB (~30 ms of reads [D]) and rebuilds derived indexes (~0.1 s at 1M, §1.6) |
| `max_article_octets` A | 16 MiB | 32 KiB | 1 MiB | fn's default A is 16 MiB, its small preset 32 KiB, and the resource contract names 1 MiB as what a public node must allow; A bounds the blob-reference list (256 blocks) and the upload's duration (16 MiB at 1 GbE is 134 ms), never memory |
| `max_head_octets`, fields, lines | 16 KiB, 64, 256 | same | same | fn's defaults (STO-030); the head is parsed and edited whole inside one receive buffer, so this sets the receive buffer |
| injected header octets (Path, Date, Xref, Injection-Info) | 4 KiB | | | Xref is the long one: groups-per-article x (name + number); asserted against the next two rows |
| `max_groups_per_article` | 32 | 16 | 32 | one array append per group per POST, so POST work is O(32); Xref <= 32 x (64 B typical name + 12) fits the 4 KiB injected budget at typical names, and the parser refuses a post whose Xref would not |
| `max_group_name_octets` | 256 | 64 | 256 | fn's codec ceiling |
| `max_groups` (in the store) | 65,536 | 1,024 | 16,384 | a u16 group id in every membership entry; group summaries are 64 B each, 4 MiB at the ceiling; a full Usenet active file is tens of thousands [A] |
| Message-ID octets | 250 | | | RFC 5536 §3.1.3 |
| command line octets | 512 | | | RFC 3977 §3.1 (including CRLF) |
| `max_articles` T | 2^32 - 1 | 16,384 | 2^20 | a u32 seq in the ID table and group arrays; T sizes the ID table (2T slots, 16 B per article) at start |
| `max_connections` C (all kinds: readers, posters, peers, waiters, web, control) | 4,096 | 256 | 1,024 | a u16 slot index plus an incarnation; ~33 KiB of buffers + ~50 KiB of TLS each [A]; akapug's 30 seats on 4 boxes need <= 120; fn today: 32 |
| waiters (served `wait`) | = C | | | a wait is a state of a connection, so its bound is the connection bound and the 12-waiter cap disappears; wake lists are intrusive per-group lists through the connection slots, and a commit wakes at most the waiters of the groups it touched (charged to that step's budget) |
| `max_consumers` (durable cursors) | 65,536 | 256 | 4,096 | fn's profile field 8; a cursor is a 32 B row |
| control clients | 16 | | | fn's `:control-clients` |
| POSTs in flight per connection | 1 | | | NNTP runs one command at a time per connection; pipelined commands wait in the receive buffer |
| TAKETHIS window per peer | 64 records | | | streaming without the 340 round trip; bounded by the batch cap below |
| commit batch | 1,024 records or 4 MiB | | | one write and one flush per batch; 4 MiB writes in ~2 ms at 2 GB/s, under one client-NVMe flush; 1,024 is above λ t_f at 250k POSTs/s |
| commit pipeline depth | 2 batches | | | one filling while one flushes, which is all the group-commit rule needs |
| large uploads in flight | 16 x 2 chunks of 256 KiB | 4 | 16 | 16 concurrent 25 ms transfers saturate 1 GbE; a 17th upload is backpressured by not reading its socket |
| disk reads in flight | 64 | 16 | 64 | NVMe 4 KiB reads saturate around QD 32-64 [A]; one cold read per connection at most |
| disk writes in flight | 16 x 256 KiB | | | a 4 MiB batch in one round of writes |
| io_uring SQ / CQ entries | 4,096 / 8,192 | | | SQ >= the sum of every component's in-flight maximum (2C + 64 + 16 + 1 + 2 x 16 + timers) at the default, so a submission never waits for a ring entry; CQ = 2 x SQ so completions never overflow |
| completions handled per loop iteration | 1,024 | | | bounds one iteration's work; the rest wait in the CQ for the next |
| machine step budget q | 64 KiB rendered or 1,024 rows scanned | | | work beyond q becomes the machine's resumable state (RUNTIME-MODEL §1, "Work budget"); LIST over 65,536 groups is 64 steps, interleaved with everyone else's |
| reply window per connection | 64 KiB | | | fn's `:send-window-octets`; a reply pins at most one window of cache blocks, so a slow reader's memory is O(window), not O(article) |
| send stall | 10 s below 4,096 B/s | | | fn's `:send-stall-seconds`, `:send-min-octets-per-second` |
| TLS handshakes in flight, deadline | 16, 5 s | | | fn's rows; at ~1 ms of CPU each, 16 handshakes are ~16 ms of executor time unless handshakes run on a worker |
| tick | 10 ms | | | TigerBeetle's tick; every deadline is a tick count, so time is an input, not a call |
| block cache | operator | 32 MiB | 256 MiB | the only large free choice in the memory sum (§1.6) |

Every row has an outcome when reached, by name, never a degraded mode: a connection past C is refused at accept; a POST past A or the
head limits is refused with its reason; an upload past its slots waits on its own socket; a batch past its cap closes and the next
opens; T reached is a named store-full refusal. Nothing in the table grows at run time.

---

# Part 2. The host model

## 2.1 What the host is, and what it is today

**The rule.** The core is a deterministic machine: `step(state, events, now) -> (state, actions)`. The host owns exactly three things:
the **executor loop** that turns actions into operating-system operations and completions back into events; the **pool, slot and
outstanding-use tables** that make buffer ownership checkable at the boundary; and **the primitives** (§2.3). Every decision (what to
accept, when to flush, whom to wake, when to refuse, when a deadline has passed) is the core's. That is fn's own contract
(RUNTIME-MODEL-DRAFT §1: actions `(kind id incarnation op args)`, exactly one completion per action, A-HOST-COMPLETES; one executing
thread; workspace / borrowed / leased buffers; `:commit` is not an action but the transition on a barrier's completion), already
written as `books/runtime-contract*.lisp` (23 books on origin/dev: slots :free/:live/:closing/:draining, the pool's :free / :workspace
/ :leased :in|:out / :handed states, the uses table, T6 "a completion that matches no outstanding use changes nothing", the q + c step
budget, the explicit hand).

**Today** the host is 75,678 lines in 123 files, 3,546 defuns ([M] M3-HOST-PLAN §1 at `d187817f6`): io 401 functions / 6,105 lines,
policy 450 / 5,797, book-branching 1,163 / 22,341, seams 256 / 10,437. `host/native/io.lisp` alone has **554 `fnn-` defuns** on
origin/dev `6521f18c4` [M: `git grep -c '^(defun fnn-'`], spanning file plumbing (`fnn-open`, `fnn-fstat`, `fnn-list-directory-window`,
`fnn-link`, `fnn-replace`, `fnn-rename-no-replace`, `fnn-flock` ...), four barrier spellings (`fnn-durable-barrier`, `fnn-fsync-dir`,
`fnn-fsync-file`, `fnn-fsync-regular`), a log subsystem of ~90 functions (`fnn-log-pwrite` ... `fnn-log-spare-*` ... `fnn-log-sync-
collected`), checkpoint writers, store init/import/export, node-secret files, filesystem identity probes (`fnn-statfs-*`,
`fnn-mountinfo-best`), the reader loop, socket setup, the verb registry and `fnn-main`. ANATOMY's "781 I/O primitives" is that
stratum across the host. Under them the host reaches the OS through only **~40 distinct libc entry points** (sb-posix: open, close,
fstat/lstat/stat, lseek, ftruncate, fsync, unlink, rename, link, mkdir, rmdir, chmod, opendir/readdir/closedir, fcntl, pipe, kill,
getpid; alien: pread, fdatasync, posix_fallocate, renameat2, syncfs, statvfs, flock, ioctl, setsockopt, realpath, sysconf, recv,
shutdown, pthread_kill; sb-bsd-sockets: socket, bind, listen, accept, connect, send, receive, peername, get-host-by-name) plus OpenSSL
(~45 routines), libsodium, and fn's own BLAKE3, deflate and ML-DSA-65 shims [M: grep of `host/native` on origin/dev]. **The 781 are
policy and plumbing in the shape of I/O, not I/O.** The lock lattice (230 functions / 8,023 lines), cold-wait queues (2,221 lines)
and the owner's time policy (6,166 lines) are the three decisions with no wired book (M3-HOST-PLAN §2): exactly the executor's work.

`docs/host.md` does not exist on origin/dev; the host contract lives in `specs/host.md` (2,073 lines: HST-001 the host runs the core's
definitions; HST-002 generations reject stale completions, partial writes tracked by offset, never rerun a transition to finish a
write; HST-026 the disk as an adversarial environment, with barrier deadlines and 441 "the disk is slow" shedding; the durability
barrier table: darwin `F_FULLFSYNC` then `fsync`, else `fsync`).

**What fn2 removes from the host by layout, before any code**: a single data file (or block device) replaces the store's directory
tree (`objects/`, `journal/`, `checkpoints/`, `staging/`, `indexes/`, config records, node-secret files), so **every directory
operation, rename, link, unlink, directory fsync, staging sweep and filesystem-identity probe leaves the served host**. Store init,
import, export and inspection become offline tools over the same file format, not served code. The decisions journal written per
command (66-68 B with its own `write`, [M] DESIGN-RESOURCE-MODEL §2) becomes records in the commit batch.

## 2.2 The executor loop

One thread. Every table below is an array sized at start from the profile (§1.8); nothing is allocated after `init`.

```
// ---- state owned by the host (all fixed arrays) ----
Buffer   { generation: u32, state: BufState, owner: SlotRef, len: u32 }        // bytes live in one region
BufState = Free
         | Workspace                      // the owner machine may read and write it
         | LeasedIn  { op: u64 }          // a worker writes it (recv, read); hidden from every machine
         | LeasedOut { holders: u16 }     // workers read it (send, write); immutable, not recyclable
         | Handed    { to: SlotRef }      // in transit between two instances; hidden from both
Slot     { incarnation: u32, status: Free | Live | Closing | Draining, kind: Listener | Owner | Conn | Flusher | ... }
Use      { op: u64, slot: SlotRef, incarnation: u32, kind: OpKind, handle: Handle? }   // one per submitted action
Handle   = (buffer index h, generation g, offset, length)
// Invariant (fn's fn-rtc-invp): Use(op) names handle (h,g)  ==>  state(h) in {LeasedIn, LeasedOut}, generation(h) = g,
//            and the bytes [off, off+len) do not change until that Use's completion is processed.

init(profile):
  region   = memory_reserve(total_bytes(profile))          // one call; carve every pool, table, ring from it
  carve(region) -> buffers[], slots[], uses[], cache blocks[], rings
  storage  = storage_open(path, profile.size)              // exclusive; reports sector size
  listener = listen(profile.addresses)
  seed     = entropy(32)                                   // core's DRBG; the simulator passes its seed here
  core     = core_init(profile, seed)                      // recovery runs as ordinary steps over storage_read completions
  submit(core.initial_actions())                           // e.g. read superblock copies, accept on each listener

loop:                                                      // the event loop; assert it never returns
  now = Clock { monotonic: clock_monotonic(), realtime: clock_realtime() }   // read once per iteration
  events.clear()

  // 1. harvest: bounded by COMPLETIONS_PER_ITERATION (1,024)
  for c in ring.reap(max = COMPLETIONS_PER_ITERATION):
    u = uses.take(c.op)                       // absent: a duplicate, a forgery or a late completion of a retired op
    if u is none: stats.stray += 1; continue  //   -> changes nothing (T6); the layer checks, it does not assume
    assert slots[u.slot].incarnation >= u.incarnation
    if u.handle: lease_end(u.handle, c)       // LeasedIn -> Workspace (bytes now visible) ; LeasedOut holders -= 1
    if slots[u.slot].incarnation != u.incarnation: continue        // completion of a closed instance: drop by rule
    events.push(Event { slot: u.slot, inc: u.incarnation, op: u.op, kind: u.kind, outcome: c.outcome })
  events.push_all(timer_wheel.expire(now.monotonic))               // ticks: Event { kind: Tick, ... }
  events.push_all(signals.drain())                                 // shutdown / reload as ordinary events

  // 2. step: the core sorts events by machine and kind and runs homogeneous batches
  //    (all commit completions, then all reads, then all sends ...): control flow out of the inner loops
  actions = core.step(events, now, budget = STEP_BUDGET)           // pure; deterministic; bounded output
  assert actions.len <= ACTIONS_PER_ITERATION

  // 3. validate and submit: every action names only its own buffers (fn-rtc-submit-okp)
  for a in actions:
    assert slots[a.slot].incarnation == a.incarnation
    if a.kind == Hand:    hand(a); continue                        // in-process: Workspace -> Handed -> target's Workspace
    if a.kind == Pool:    pool_wait(a); continue                   // waits in issue order; granted at once when a buffer frees
    if a.handle: assert buffers[a.handle.h].owner == a.slot and state == Workspace
                 lease_begin(a.handle, direction(a.kind))         // Workspace -> LeasedIn | LeasedOut
    op = next_op; next_op += 1                                     // process-monotonic, never reused
    uses.insert(Use { op, slot: a.slot, incarnation: a.incarnation, kind: a.kind, handle: a.handle })
    ring.prepare(a.kind, a.args, user_data = op)                   // never fails: SQ >= sum of in-flight maxima (§1.8)
  grant_pool_waiters()                                             // oldest first; a grant is never a refusal

  // 4. one syscall: submit everything, wait for >= 1 completion or the next deadline
  ring.enter(min_complete = 1, timeout = min(timer_wheel.next_deadline - now.monotonic, TICK))
```

What is *not* in the loop: no lock (one thread; the only synchronization is the ring itself), no retry (a failed operation is an
outcome the core sees), no timeout of its own (a deadline is a `Tick` event, and the core decides to `cancel`), no allocation, no
decision about which batch to flush. **Group commit is a core machine**, the flusher: it owns the two batch buffers, emits
`storage_write` for the filling batch when the previous flush's completion arrives, then `storage_flush` once every write of the batch
has completed, and on that flush's completion emits the 240s (each a `send` of a small reply) and the wake-ups. The host never knows
what a POST is.

**Cancellation and close** (fn's rule, kept): `cancel(op)` asks; the use, and any lease it holds, ends only on the operation's own
completion (`:cancelled` included). A close moves the slot to Closing, and to Draining when the close completes; the slot is Free (and
its next accept takes incarnation + 1) only when no use names its incarnation. A deadline followed by a cancel bounds how long any
action pins its slot and its buffer.

**The worker backend** (where io_uring is unavailable): `ring` is an epoll set for sockets plus N blocking I/O workers for storage
operations, joined by two fixed-size queues (submissions, completions) and an eventfd that wakes the executor. Workers execute one
operation and post one completion; they never touch machine state. `ring.enter` becomes `epoll_wait` + draining the completion queue.
Same `Use`, same invariants, same core.

## 2.3 The primitive set

Signatures in a language-neutral notation. `-> op` means the call is a submission whose result arrives as one completion; every
completion outcome is one of `Done(n) | Short(n) | Failed(reason) | Cancelled`, and the reasons are the closed set listed per row.
A primitive never retries, never blocks the executor, and never synthesizes an outcome (no completion on a timeout: A-HOST-COMPLETES).

### Startup only (before the loop; failure is a named refusal to start)

| # | primitive | signature | Linux | notes |
|---|---|---|---|---|
| 1 | `memory_reserve` | `(bytes: u64, align: u32) -> Region` | `mmap(MAP_PRIVATE\|MAP_ANONYMOUS\|MAP_POPULATE)`, optional `mlock`, huge pages | the only allocation the process makes |
| 2 | `storage_open` | `(path, mode: Format(size) \| Open) -> Storage { sector_size: u32, size: u64 }` | `open(O_RDWR\|O_DIRECT\|O_CLOEXEC)`; `flock(LOCK_EX\|LOCK_NB)` (file) or `O_EXCL` (block device); at Format, preallocate **and zero-fill by real writes**, then `fdatasync` | one data file or a raw device; no directories |
| 3 | `listen` | `(addr: Inet(ip, port) \| Unix(path), backlog: u16) -> Listener` | `socket`, `setsockopt(SO_REUSEADDR)`, `bind`, `listen` | the control socket is a Unix listener: no separate control plane |
| 4 | `tls_config` | `(role: Server \| Client, cert_chain: bytes, key: bytes, roots: bytes, alpn: [bytes]) -> TlsConfig` | OpenSSL `SSL_CTX` or rustls `ServerConfig` | reload is a new config plus an atomic swap at a step boundary |
| 5 | `entropy` | `(out: Buffer) -> ()` | `getrandom` | seeds the core's DRBG; reseed is the same call; the simulator supplies the seed |

### Data plane (submissions through the ring)

| # | primitive | signature | failure reasons | Linux (io_uring op) |
|---|---|---|---|---|
| 6 | `accept` | `(listener) -> op ⇒ Done(conn, peer: Addr, cred: PeerCred?)` | `Exhausted` (EMFILE/ENFILE), `Aborted` | `ACCEPT` (multishot where available); `SO_PEERCRED` on Unix sockets |
| 7 | `connect` | `(addr: Addr) -> op ⇒ Done(conn)` | `Refused`, `Unreachable`, `TimedOut`, `Reset` | `SOCKET` + `CONNECT` |
| 8 | `recv` | `(conn, into: Handle) -> op ⇒ Done(n) \| Done(0)=eof` | `Reset`, `Closed` | `RECV` (provided buffers optional) |
| 9 | `send` | `(conn, from: Handle) -> op ⇒ Done(n) \| Short(n)` | `Reset`, `Closed`, `Pipe` | `SEND`, or `SEND_ZC` above ~16 KiB (one extra notification completion, still one Use) |
| 10 | `close` | `(conn, how: Graceful \| Abort) -> op` | none (always completes) | `SHUTDOWN(SHUT_WR)` then `CLOSE`; Abort sets `SO_LINGER{1,0}` |
| 11 | `tls_handshake` | `(conn, TlsConfig, server_name: bytes?) -> op ⇒ Done(TlsInfo { version, alpn, peer_cert_digest: u256, exporter: [u8; 32] })` | `Handshake(alert)`, `Reset`, `TimedOut`-by-cancel | memory BIOs over 8/9 on the executor, or a handshake worker; then kTLS (`setsockopt(TLS_TX/TLS_RX)`) so 8 and 9 carry plaintext; the exporter is the channel binding fn uses today (`SSL_export_keying_material`) |
| 12 | `storage_read` | `(offset: u64, into: Handle) -> op` (offset, length and address sector-aligned) | `Io` (EIO, the latent-sector case), `Short` | `READ_FIXED` on a registered buffer |
| 13 | `storage_write` | `(offset: u64, from: Handle, fua: bool) -> op` (aligned) | `Io`, `NoSpace` (a copy-on-write file system can refuse an overwrite), `Short` | `WRITE_FIXED`, `RWF_DSYNC` when `fua` |
| 14 | `storage_flush` | `() -> op`: every write *completed before submission* is durable on `Done` | `Io` (the core treats a failed flush as a crash: it stops and recovers) | `FSYNC` with `IORING_FSYNC_DATASYNC` |
| 15 | `cancel` | `(target: op) -> op ⇒ Done \| NotFound` | none | `ASYNC_CANCEL`; the target still delivers its own completion |
| 16 | `signal_wait` | `() -> op ⇒ Done(Shutdown \| Reload)` | none | `signalfd` + `READ` (one standing op) |

### Inputs and process (no completion)

| # | primitive | signature | Linux | notes |
|---|---|---|---|---|
| 17 | `clock_monotonic` | `() -> u64 ns` | `clock_gettime(CLOCK_BOOTTIME)` | read once per iteration; every deadline is computed from it; jumps forward after suspend |
| 18 | `clock_realtime` | `() -> i64 ns` | `clock_gettime(CLOCK_REALTIME)` | for Date, NEWNEWS stamps and labels only; the core clamps it monotone (fn's `:clock-regressed` count) and never orders anything by it |
| 19 | `ring_enter` | `(min_complete: u32, timeout_ns: u64) -> ()` | `io_uring_enter(IORING_ENTER_GETEVENTS)` | the executor's single blocking point; owned by the loop, not by the core |
| 20 | `trace` | `(level, bytes) -> ()` | `write(2)` to stderr / journald, non-blocking, dropped when the pipe is full (counted) | best effort; never durable; durable facts are log records |
| 21 | `exit` | `(code: u8) -> never` | `exit_group` | fn's outcome classes (exit 1 refused, 4 fault); an assertion failure is `abort` |

**Count: 21 primitives** (5 at startup, 11 data-plane submissions, 5 inputs and process), against `host/native/io.lisp`'s 554 `fnn-`
defuns and ANATOMY's 781 I/O-shaped functions. Optional 22nd: `resolve(name) -> [Addr]`, a blocking control-plane call on a worker,
only if peers are configured by name (fn has `fnn-peer-resolve-ipv4`); a configuration of addresses removes it.

**Not primitives: compute intrinsics.** BLAKE3, Ed25519 sign/verify (libsodium today), ML-DSA-65 sign/verify (fn's shim), SHA-512,
deflate/inflate: **~6 pure functions**. They have no effect and need no simulation; they are libraries the core links (or, where the
core is ACL2-derived, the attached executable of a function the logic specifies). Counting them, the host surface is ~27 entries.

**What is absent, on purpose**: directories, rename, link, unlink, stat, readdir, `fsync(dirfd)`, `posix_fallocate` (zero-fill at
format instead), `statvfs` (the data file is preallocated, so free space is a fact of the file, not of the file system), `flock`
beyond the open, threads, mutexes, condition variables, `kill`/`tgkill` (fn's 5 tgkill and 75-261 rt_sigprocmask per command are
SBCL's stop-the-world signalling and thread churn, [M] PERF-MEASUREMENTS), `ioctl(SIOCOUTQ)` probes (a send's completion says what was
taken), and every timer except the loop's single wait bound.

## 2.4 Linux (io_uring) against robigalia (seL4: no kernel file system)

The primitive set is chosen so that **its shape is robigalia's, and Linux implements it on a file**. A storage interface of
`read(offset) / write(offset, fua) / flush` over sectors is exactly what an NVMe or virtio-blk driver offers; a file system is one way
to provide it, not a requirement (TigerBeetle runs on a raw block device for this reason).

| concern | Linux | robigalia on seL4 [A: the seL4 component model; sDDF-style shared-memory queues] |
|---|---|---|
| the ring | io_uring SQ/CQ in shared memory, `io_uring_enter` | a pair of shared-memory descriptor queues per driver component (submissions, completions), signalled by seL4 notifications; `ring_enter` is `seL4_Wait` on the executor's notification object, with the timer component's notification as the timeout |
| buffers and leases | registered buffers; the lease is a convention the host enforces with its tables | the pool region is mapped into fn2 and into each driver; a lease can be **enforced by mapping**: an :out buffer mapped read-only to the network or block driver, an :in buffer writable by the driver and unmapped from fn2's machines (the borrow view becomes a page-table fact) |
| storage | a preallocated, zero-filled data file opened `O_DIRECT`, or a raw block device; flush = `fdatasync` | the block driver component; flush = NVMe FLUSH / `VIRTIO_BLK_T_FLUSH`; FUA where the device has it; the sector size from the device. **User-level durability**: the superblock copies, the log, the grid and the checkpoint are fn2's own format, unchanged, because Linux already had them in one file |
| durability semantics | the kernel and file system sit between fn2 and the device: fsync error reporting, a CoW file system's `ENOSPC` on overwrite, a FS that may itself ignore a write error (IRON, row 7) | nothing between fn2 and the device's own volatile cache: the device-level model (crash-model row 15: volatile write cache, flush, FUA, sector atomicity) is the whole model |
| network | kernel TCP; `accept/connect/recv/send` | a user-level TCP/IP component (lwIP or smoltcp class) behind the same queue interface; the operations are the same five; zero-copy is natural (the stack and fn2 share the buffer region) |
| TLS | OpenSSL or rustls in process, plus kTLS for record crypto | rustls (or another user-level TLS) in fn2 or in its own component; no kTLS; the handshake's CPU is either a worker component or charged to the executor's step budget |
| clocks | `CLOCK_BOOTTIME`, `CLOCK_REALTIME` | a timer driver component (monotonic) and an RTC/NTP component (realtime) |
| entropy | `getrandom` | a device RNG component, or a seed provisioned by the system |
| trace | stderr / journald | a serial or log component |
| exclusive access | `flock` / `O_EXCL` | a capability: only fn2 holds the block device's capability, so exclusivity is structural |
| exit | `exit_group` | the component faults or signals its supervisor |

**What changes in the core between the two: nothing.** Everything that differs is below the 21 primitives. The cost on Linux is that a
few Linux conveniences go unused (the page cache, the file system's namespace); the gain is that the robigalia port is a new host of
~1K lines over driver components that are not fn2's (§2.7), and that the Linux deployment already runs the fault model robigalia will
have (§2.5), instead of a weaker one that a port would silently strengthen.

**One Linux-only obligation**: on a file (rather than a device) the file system must not move or reallocate the data file's blocks
under O_DIRECT (true of ext4 and XFS for a preallocated, already-written file; *not* of ZFS or Btrfs, which are copy-on-write and
whose O_DIRECT support is partial). The host refuses to start on a copy-on-write file system unless the operator says the page-cache
backend is acceptable, and that backend runs the tougher model too (it is not allowed to rely on issue order).

## 2.5 The crash and fault model the executor must honour

The baseline is fn's crash model v2 (`books/byte-store.lisp`, specs/crash-model-v2.md §1): pending operations, per-inode and
per-directory fences, a crash landing an issue-ordered subsequence of pending operations, torn writes landing as written / zeros /
garbage, `:eio` and `:enospc`, and `read` with no outcome. The papers README's table (~/paperbin/README-fn2-20261028.md, "Crash model:
what ours misses") lists 22 behaviours; its verdict is that rows 1-6 (the durable state treated as perfect) make every checksum in fn
unexercised by its own model, and row 11 is the first thing a high-performance I/O path hits. fn2 adopts the tougher model as the
environment the executor runs in. **The host's obligation is fidelity**: report every outcome as it happened, never retry, never
synthesize success, never hide an error behind a later success. **The core's obligation is detection, then repair or a named stop**.

| # | the environment may | host obligation | core response |
|---|---|---|---|
| 1, 6 | corrupt durable data at rest, or on a power cut corrupt data that was not being written | none beyond delivering the bytes read | every block and record carries a checksum held **outside** it, in its parent (row, block reference, superblock); a mismatch is a read fault (row 2), never data |
| 2 | fail a read of durable data (latent sector error, uncorrectable flash) | `storage_read` has an outcome (`Io`); fn's `fn-bs-read` has none | the record is unreadable by name (an ARTICLE answers a typed refusal, not a crash); a replicated fn2 repairs the block from a peer by checksum (TigerBeetle's grid repair); a scrubber reads cold data at a stated cadence (Maneas FAST 20 gives the rates) |
| 3, 4 | misdirect a write onto another block, or return another block's data for a read | none | the external checksum binds identity: a block read for reference (index, checksum) that does not match is rejected; the block header also carries its own address; the superblock is read from 4 copies with a quorum of 2 (data-file.md: a misdirected read can hide the single latest copy) |
| 5 | lose an acknowledged write (a device that acknowledges a flush it did not do) | none | detection only, at open and by scrub: the superblock's hash chain names what must be present; a single node reports the loss by name and stops serving the affected range; a replicated node repairs. Theorems say "detected", not "prevented" |
| 7 | die stickily (dead device; a journal failure remounting read-only) | report every subsequent failure | a run of failures past a bound moves the store to a named read-only or stopped state; reads continue where they can |
| 8, 9 | after a failed `fsync`, show the unwritten data (ext4/XFS) or the old data (Btrfs); deliver the error once, or to another descriptor | one descriptor, one process, O_DIRECT: there is no page-cache view to read back | a failed `storage_flush` is treated as a crash: stop, reopen, recover from the log (PostgreSQL's post-fsyncgate rule); nothing is acknowledged from a batch whose flush failed |
| 10 | tear a write inside the declared unit (512 B pieces of a 4 KiB write) | none | per-record and per-block checksums detect a torn piece; acknowledged sectors are never rewritten, so a tear can only damage the batch in flight, which was never acknowledged |
| 11 | complete in-flight writes in any order, and land any subset at a crash | completions are delivered as they arrive; the host imposes no order | **the commit rule** below |
| 12 | interleave several threads' system calls at a crash | the executor is one thread, so this row is a premise, not a behaviour | stated as a theorem premise: the single-executor rule |
| 13 | crash during recovery, repeatedly | none | recovery writes nothing until it has decided, and every recovery write is idempotent; the simulator crashes it at every step |
| 14 | provide `fdatasync`, `O_DSYNC`, FUA, `fallocate` and more | the host uses only `storage_flush` and the `fua` flag | each has its own fence in the model; nothing else is used |
| 15 | be a raw block device with a volatile write cache | the storage primitives are block-shaped | the device model is the model; the file is an implementation of the device |
| 19 | succeed slowly (fail-slow, gray failure: 10-1,000x latency) | completions carry the time they were reaped | every action that can stall has a deadline as a `Tick` and a `cancel`; a barrier past its deadline puts the disk in fn's `slow` posture (HST-026: POST answered 441 "the disk is slow", nothing stored; reads unaffected); `stalled` past the stall limit |
| 20 | (replicated) tear the log's tail or corrupt its middle | none | never truncate on a bad checksum before telling a torn tail (the batch after the last acknowledged one) from mid-log corruption (Alagappan FAST 18, PAR) |
| 22 | return a short write, EINTR, other errnos | map every errno into the closed reason set; EINTR never reaches the core | a short storage write is `Failed`-uncertain; a short `send` is progress (the core tracks the offset, HST-002) |

Rows 16-18 (raw flash, persistent memory, cross-tenant stale data) do not apply until fn2 drives flash or PM or hosts tenants; row 21
(the model checked against real kernels) is a validation obligation on the simulator (§2.6), not on the executor.

**The commit rule** (row 11, with one flush per batch). For a batch:
1. Write every block the batch's records reference (blob blocks of large POSTs) and the batch's log sectors. The log sectors carry,
   for each record, the checksums of the blocks it references, and the batch header carries its predecessor's checksum (fn's chained
   entries, kept).
2. When **all** of those writes have completed (completion-gated, never submission-ordered), submit `storage_flush`.
3. On the flush's `Done`, the batch is the commit point: send the 240s, wake the waiters, publish to readers.
4. At recovery, scan the log forward from the checkpoint's position; accept a batch only if its header checksum, its chain link and
   every referenced block's checksum verify; stop at the first batch that does not. Every batch past that point was never
   acknowledged, because acknowledgement waited for a flush that would have made it whole, so discarding it loses nothing that was
   promised (P1 Durable acceptance holds: "a 240 means the article is on stable storage").

The flush in step 2 is the only barrier: the device may reorder the batch's writes within its cache, and step 4 is what makes that
harmless. With FUA on a device that honours it, the batch's final sector can be written FUA and the flush skipped; a PLP device makes
the flush nearly free either way (§1.5).

**Network faults** (the core's, delivered faithfully by the host): resets at any byte; half-open connections; arbitrary
fragmentation of the byte stream (fn's F6 cell already tests 64 split points); clients that never read (slowloris on send), never
write, or send garbage; TLS failing mid-stream. Each is an outcome of `recv`/`send`/`tls_handshake` or a deadline the core set.
**Clock faults**: the monotonic clock jumps forward (suspend; every deadline expires at once, and the core's step budget bounds the
burst); realtime steps backward (clamped, counted, never used for order). **Memory faults**: none at run time; `memory_reserve`
failing is a refusal to start.

## 2.6 Deterministic simulation (VOPR-style)

Because every effect crosses the 21 primitives and the core is a pure step, **a simulator is a second host**: `SimHost` implements the
same primitives over in-memory state, and the whole node (core and executor loop, unchanged) runs on one thread, with virtual time,
from one seed (tigerbeetle2026-internals-vopr.md: "all non-deterministic parts of the system are stubbed out ... the clock, network,
and disk"; a failure replays from the seed and the commit).

**SimStorage** (the environment of §2.5, executable):
- state: a sector array split into *durable* and *pending* (written, not yet flushed) sectors; an outstanding-operation set;
- completion order: a random permutation of the outstanding set, with latencies drawn from a per-run distribution (a fail-slow run
  draws a heavy tail: row 19);
- `storage_flush`: moves the sectors of writes completed before its submission from pending to durable, or fails (row 8-9);
- faults, each with a per-run probability (swarm testing: each seed draws its own mix): read `Io` (row 2), bit flips in durable
  sectors (rows 1, 6), misdirected writes and reads (rows 3, 4), lost flushes (row 5), torn writes at 512 B pieces landing as
  written / zeros / garbage (row 10), `NoSpace`, sticky death after a point (row 7);
- **crash**: drop every outstanding operation, land a random subset of pending sectors (any order: row 11), tear the ones landing
  partially, then restart the node from storage alone. Crash during recovery is the same event at a later point (row 13);
- a fault budget per run, so a single-node run stays within what detection must catch and the checker can tell "detected" from
  "survived" (TigerBeetle bounds faults so that some copy survives; a single-node fn2 asserts detection and a named stop).

**SimNetwork**: connections are in-memory byte pipes with random fragmentation at every byte boundary, delays, resets, half-open
peers and slow or non-reading clients. **Clients are workload machines**: posters (POST and TAKETHIS), readers (ARTICLE, OVER,
GROUP, NEWNEWS), waiters (akapug's wait/ack), peers (feed and pull), operators (control verbs), each a small state machine driven by
the same seed. **SimClock**: ticks advance virtual time; injected jumps (monotonic forward, realtime backward). **Entropy**: from the
seed.

**Checkers** (run on every step, and at the end):
- *P1 durable acceptance*: every POST answered 240 is readable, byte-equal, after any sequence of crashes and recoveries (fn's F2S cell,
  over every crash point instead of 13 named ones);
- *P2 exact identity*: every present ID resolves to its bytes, every absent ID is absent, no duplicate is accepted (fn's F4 with forced
  hash collisions: shrink the tag width in the simulator's build);
- *P8 framing*: reply streams equal the unfragmented reference whatever the split (fn's F6);
- *bounded service*: no step exceeds its budget; no queue exceeds its bound (assertions in the code; static allocation makes memory
  a non-question);
- *ownership*: the `Use`/lease invariant of §2.2 on every submission and completion (stale and duplicate completions injected on
  purpose: fn's F1 "late completion after slot reuse");
- *detection*: every injected corruption is either never read or reported by name; none is served as data;
- *liveness*: after faults stop, every eligible request is answered within a bound (TigerBeetle's liveness mode).

Time is virtual, so a run that covers hours of node time takes seconds; runs are cheap enough to be the default test, and
assertions stay on in production (vopr.md: "it is far better to stop operating than to continue operating in an incorrect state").

**The simulator and the proofs.** SimStorage *is* the executable form of the crash model v3 that the papers table asks for. It should
be the same definition as the logic's environment model (one source; the model is the oracle and the simulator is its evaluation),
or, failing that, checked against it trace by trace. Row 21's obligation (the model checked against real kernels) is then a third
backend: record block traces from Linux on ext4/XFS under power-cut injection (Zheng OSDI 14's method) and replay them through the
model as an oracle (Ridge's SibylFS, Mohan's CrashMonkey).

## 2.7 The host's size

Estimated in lines of a systems language (Rust, Zig or C), by component, each from the primitive count and what the component must
hold [D, with each per-unit figure an assumption stated in the row]:

| component | lines | reasoning |
|---|---|---|
| executor loop, slot / pool / use tables, lease transitions, hand and pool grant, timer wheel | 500-700 | §2.2's pseudocode is ~70 lines; each table is an array with 4-6 transitions, each transition asserted twice (tiger-style "pair assertions") |
| io_uring backend | 400-600 | 11 submission kinds x ~25 lines (prepare + decode the completion into the closed outcome set) + ring setup, registered buffers and files |
| epoll + worker backend | 500-700 | the same 11 kinds over epoll for sockets and a fixed worker pool for storage, two bounded queues and an eventfd |
| storage open and format | 150-250 | O_DIRECT probe, sector size, exclusive lock, preallocate and zero-fill, refuse copy-on-write file systems by default |
| sockets setup (listen, address parse, Unix credentials) | 150-200 | |
| TLS adapter | 500-900 | memory-BIO handshake state, kTLS hand-off, config load and swap, exporter; fn's `host/native/tls.lisp` is 1,251 lines for OpenSSL over SBCL's alien layer |
| clocks, entropy, signals, trace, exit, memory reserve | 150-200 | thin |
| profile parse and startup (compute the memory sum, carve the region, open, recover, enter the loop) | 300-400 | the static-allocation arithmetic lives here and is asserted |
| **production host, Linux** | **~2.7K-4K** | |
| darwin development backend (kqueue + workers, `F_NOCACHE`, `F_FULLFSYNC`) | 500-700 | development only; claims the weaker model |
| robigalia host (queues over driver components, notifications, mapped leases) | 800-1,200 | the drivers, TCP/IP stack and TLS component are not fn2's lines |
| SimHost (storage, network, clock, entropy, fault scheduler, crash/restart) | 1,500-2,500 | the workload machines and checkers are tests, counted separately |

**The production host is ~3-4K lines**, against fn's 75,678 [M] (M3-HOST-PLAN §1), M3's honest landing of ~15-16K and its decision-
sized floor of ~50K, and ANATOMY's ~10K hypothesis (ember's frame: "sel4 was like 10k lines of logic", GOALS G4). The difference from
M3's landing is not a better shrink of the same host: it is that fn2's layout and contract take out, before any code exists, every
category M3 could only move, namely the lock lattice (no second thread), the cold-wait queues (completions are events), the
owner's time policy (ticks are events, deadlines are the core's), the directory tree (one data file), the checkpoint writers (the
core writes blocks through `storage_write`), the verb surfaces (the core renders; the host has no verbs), and the entry-guard stratum
(one boundary of 21 typed primitives instead of 2,684 book functions called from the host). M3-HOST-PLAN's "what M3 must not touch"
list reduces to: TLS (kept, as an adapter), the crypto and deflate intrinsics (kept, as libraries), the durable log's recovery (now the
core's), and the process-death cut points (now every step of the simulator).

The estimate's risk is TLS: a TLS library that cannot run its handshake over memory buffers forces a handshake thread, which is a
second thread with its own queue (~200 lines more, and a premise in the single-executor theorem that the TLS thread touches no
machine state).

## 2.8 Owed before the bounds are frozen

Measurements, each one FLOOR row on a quiet box with a same-day baseline (none run here):
1. O_DIRECT 4 KiB-sector append + `fdatasync` on persvati's ext4, zero-filled segment against `posix_fallocate`d (the 23 KB / 2.85-write
   journal tax, DESIGN-RESOURCE-MODEL §6 already owes it).
2. The same on a PLP NVMe (a rented box), to replace the [A] 0.1 ms flush.
3. io_uring against epoll + workers for the 2 KiB POST and ARTICLE loops, syscalls and CPU per operation.
4. OpenSSL per-connection resident memory at an idle TLS session, to replace the [A] 50 KiB in §1.6.
5. Message-ID table rebuild at 1M rows (the §1.6 ~0.1 s).

Decisions for ember: whether the single data file (and with it the end of the store's directory layout) is fn2's storage shape;
whether fn2 refuses copy-on-write file systems by default (hbox's ZFS would then run the page-cache backend or a zvol); whether the
default preset's `max_article_octets` is 1 MiB with a 16 MiB ceiling.
