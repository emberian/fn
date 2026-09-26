# The v1 service envelope, measured (lane service-envelope, 2026-09-26)

Brief: `build/coordinator/queue/done/w4-service-envelope.txt` (wave 4, lane
10; answers §3, mandate §15, D26). Ids: SCN-109, PKT-476, PKT-477; no PRF
(no book changed). Branch `lane/service-envelope` from dev 5c6825b2. Nothing
deployed; the live node was not touched. Every row is a loopback scripted
measurement on hbox: not a multi-machine result, not a human study, not a
power-loss or hostile-network qualification.

## 1. The throughput gate's signed-POST row (PKT-377)

`tools/throughput_gate.py` gains the phase `signed`. It uses a second tmpfs
store with the served profile and A = 16,384: a hybrid carrier of a 2,048-octet
source is 9,522 octets, past the served store's A of 4,096, and keeping the
unsigned rows on their own store keeps them comparable with every earlier run.
The phase enrols one hybrid author through the control socket and builds a
history of 1,000 articles, 32 of them hybrid-signed carriers spread evenly (the
history measure_signed.py used). It then times 100 signed POSTs on one
connection, the same way the unsigned POSTs are timed. The metrics are
`post_signed_median_ms`, `post_signed_p95_ms` and `post_signed_owner_cpu_ms`,
with floors of 25, 50 and 25 ms. The owner CPU per signed POST counts as
load-insensitive, so an under-load run still compares it. A return of the
whole-history replay (signed-history-index: 0.101 s against 0.355 s a signed
POST at N = 1,000) is a step of about 250 ms, past every floor. `baseline` takes
a metric in NEW_METRICS from the dev run alone when the release run predates
it, and prints that; any other missing figure is still refused. Carriers are
signed by the image's own `hybrid-sign-carrier` (tools/signed_carriers.py);
Python signs nothing. Tests: tests/test_throughput_gate.py, 12 cases, 4 of them
new.

**The run** (the brief's one run; `run --under-load --wait-quiet 120`, label
`service-envelope`, image native-img-a80534ed4f71, core 7a55fabb…, finished
2026-09-26T12:41:42Z, box CPU busy median 0.363, load average 8.3):

| metric | value |
| --- | ---: |
| post_signed_median_ms | **85.211** |
| post_signed_p95_ms | **107.173** |
| post_signed_owner_cpu_ms | **89.1** |
| carriers: history / signed in it / probes / octets | 1,000 / 32 / 100 / 9,522 |

JSON: `planning/evidence/service-envelope-2026-09-26/gate-a80534ed4f71-service-envelope-20260926T123825Z.json`.
The baseline is not written here (the deputy writes it).

**This JSON is deliberately not in `planning/evidence/throughput/`.** Its
unsigned `post_owner_cpu_ms` is 3.1. The baseline is 1.6 and its limit 2.6, so
`throughput_gate.py check` would print REGRESSION for revision a80534ed. The
deputy's run of the same image 12 minutes earlier (batch-pq-under-load,
12:26Z) read 1.9, with the box at CPU busy 0.177 against 0.363 here. The
bytes are the same, so this is not a regression of the image. It shows that the
gate's "load-insensitive" owner CPU moves by about 60 percent between a box at
18 percent busy and one at 36 percent: on SMT siblings, CPU time is not the same
as work. So `post_signed_owner_cpu_ms` from this run is a lenient baseline,
taken on the busier box. PKT-477 (1) holds the decision this raises.

## 2. The harness: tools/service_envelope.py

This is a new harness. rep_measure.py stays as it is, because it takes its
greeting before the store loads and has no signed row, the two gaps PKT-335
names. It runs on hbox, and every step is its own unit `senv-*` under
`MemoryMax=40G` and `RuntimeMaxSec=1800`, driven one at a time by
`planning/evidence/service-envelope-2026-09-26/envelope.sh`.

**The profile, `scale-1m`**: `operator init --profile scale
--max-transactions 1048576 --max-history-octets 4294967296
--max-article-octets 16384 fn.test`. It is the scale preset that the throughput
gate, signed-history-index and publish-program measure, with T raised for
N = 100,000 plus the measured POSTs, H raised to 4 GiB, and A at 16 KiB so a
carrier fits. The workload:

- Articles are 2,048-octet unsigned articles (the brief's; answers §3 names
  about 32 KiB, which PKT-476 keeps). One in 256 is a hybrid-signed carrier of
  a 2 KiB source (9.5 KiB): 39 of 10,000, 390 of 100,000.
- There is one group, one group per article, no pins and no relay debt.
- The listener is loopback, so the exposure rows are off.

I chose `scale` over the mission profile because every existing matched row is
on scale. The mission profile's BP and relay terms are not exercised by this
harness.

**The rows**:

- **greeting**: 100 fresh connections, each timed from connect to the 200 line.
- **OVER**: 100 `OVER lo-hi` over a 40-article window and 100 over a
  100-article range, both spread over the store.
- **unsigned and signed POST p95**: taken from the terminating line to the
  durable reply. The command-to-reply interval is kept too.
- **sustained rate**: 60 s of closed-loop POSTs on 1 connection, then on 8,
  while 3 connections loop ARTICLE. The window starts after every poster's
  connection is open, so the connect cost is its own field, and the rate is
  counted per 10 s window.
- **every owner start**: its seconds to LISTENING, VmHWM, and the owner's own
  `OWNER-OPEN` line (`open=checkpoint:S suffix=K` or `open=full-replay
  reason=R`). The full-replay row is taken on a copy whose derived
  `store-checkpoint.fnsc` was removed (`clone --drop-checkpoint`). The
  from-checkpoint row is taken after an explicit `store checkpoint`.
- **beside each row**: owner CPU from /proc, VmRSS and VmHWM, store disk octets
  and inodes, the box load, the filesystem, and on ZFS `zfs list` and
  `zpool list`.

Two figures are not measured. Bytes consed needs the heap-hook image, and the
mutex-held fraction is not exposed by the owner. Both are recorded as not
exposed rather than estimated. The ZFS rows run on a copy of a tmpfs-loaded
store (`clone`), so the preload does not spend a unit's budget on the pool's
commit latency, and the pool's cache holds the copy (the full replay's ZFS
figure is still 72 s wall against 14 s CPU).

## 3. The rows

hbox, 24 CPUs, the box shared with other lanes throughout (load average 7 to
14 in every row: none is a quiet-box figure). ZFS: pool `tank`, 2.73T, 2.50T
allocated, 237 to 241G free (**91 percent full**), fragmentation 47 to 48
percent, no SLOG (no log device), dataset `tank`.

Images:

- **before**: native-img-a80534ed4f71, dev a80534ed4f71, core 7a55fabb…. This is
  before served-path-scale.
- **after**: native-img-1770d68709bb, dev 1770d687, served-path-scale merged.
  Both are developer images built by the throughput gate's step 6b.

### N = 10,000 (the store 10,000 articles, 39 of them signed; 2 KiB)

| row | tmpfs, after | ZFS, after | tmpfs, before | ZFS, before | target (answers §3) |
| --- | ---: | ---: | ---: | ---: | ---: |
| full-replay reopen, to LISTENING | 12.7 s | 72.4 s (14.3 s CPU) | not run¹ | not run¹ | 30 s |
| reopen from a fresh checkpoint (suffix 0) | 11.9 s | 10.6 s | 43.2 s | 37.6 s | 15 s |
| reopen from the store's own checkpoint (8,650, suffix 1,351) | — | — | 43.4 s | 31.6 s | — |
| greeting, loaded, p95 (median) | **1,294 ms** (214) | **1,544 ms** (226) | 14,035 ms (12,869)² | 12,144 ms (11,416)² | 50 ms |
| OVER, 40-article window, p95 | **317 ms** | **321 ms** | 276 ms | 262 ms | 50 ms |
| OVER, 100-article range, p95 | 703 ms | 811 ms | 629 ms | 635 ms | — |
| unsigned POST p95 (median), terminator to durable reply | **6.5 ms** (4.6) | **607 ms** (446) | 10.2 ms (6.0) | 344 ms (100) | 250 ms |
| signed POST p95 (median) | **282 ms** (253) | **786 ms** (460) | 202 ms (196) | 799 ms (646) | 500 ms |
| owner CPU per unsigned / signed POST | 13.1 / 257 ms | 15.9 / 219 ms | 12.8 / 198 ms | 28.2 / 290 ms | — |
| sustained POST rate, 1 connection, 3 readers | **72.9 /s** | **1.42 /s** | 11.1 /s³ | 0.57 /s³ | 10 /s |
| sustained POST rate, 8 connections, 3 readers | **62.2 /s** | **2.10 /s** | 0.022 /s³ | 0.015 /s³ | 10 /s |
| POST p95 under the 8-connection rate | 490 ms | 10,428 ms | — | — | — |
| `store checkpoint` (offline) at 10,150 | 17.5 s | 17.6 s | 39.4 s | 50.5 s | — |
| peak RSS (VmHWM) | **16.9 GB** (after the rates, N = 18,260) | 3.7 GB | 3.6 GB | 3.6 GB | — |
| box load average (median) | 12.7 | 12.5 | 7.7 | 9.4 | — |

¹ The before image's rows ran before `clone --drop-checkpoint` existed. Their
first open was from the store's own automatic checkpoint (at 8,650, suffix
1,351), shown in its own row.
² On the before image a greeting costs 13 s of owner CPU (served-path-scale's
whole-state walk per connection). The row was capped at 10 and 11 samples
within its 120 s budget, and it says so.
³ In the before rows the rate window included the posters' and readers'
greetings (13 s each, serialized): 11.1 /s and 0.022 /s measure greetings, not
POSTs. The harness now opens every connection before the window
(`connect_s`: 0.8 s and 14.4 s on the after image).

Store: tmpfs 41.3 MB and 10,009 inodes at N = 10,000 (after the full replay; the
before copy with its checkpoint 109 MB); ZFS 47.5 MB.

JSONs: `t10k-after.json`, `z10k-after.json`, `t10k-before.json`,
`z10k-before.json` in `planning/evidence/service-envelope-2026-09-26/`.

### N = 100,000, tmpfs, once

The RSS ceiling was named before the start: each unit had `MemoryMax=40G`
with no swap. Inside that ceiling the owner's own limit is SBCL's dynamic
space of 32,000 MiB (33,554,432,000 octets).

**The first load died at N = 32,729** (the image after served-path-scale). The
unit ran `senv-t100k-load-a-after`, one owner process loading from 0, from
13:18:04 to 13:31:56Z, and consumed 17 min 15 s of CPU with a memory peak of
31.7G.

- **How it died.** The owner printed `Heap exhausted during garbage
  collection` and `Heap exhausted, game over.`, with the backtrace in
  `ACL2::FN-SCC-FRAMES` (`APPEND`). That is the automatic checkpoint capture.
  Bytes allocated were 33,528,241,120, 99.9 percent of the dynamic space.
- **What the client saw.** POST 32,729 got an empty reply: the connection
  closed. Its outcome is uncertain, and the resumed load asks the store (STAT)
  rather than assuming.
- **The captures before it.** The owner published an automatic checkpoint
  about every 2,100 commits (sequence 2,209, 4,329, … 29,453). Each capture
  took longer than the one before: 4.2 s at 2,209, 24.2 s at 10,626, 54.2 s at
  21,050 and 90.1 s at 29,453. The capture's work and garbage grow with N, and
  one process that keeps posting keeps them in its old generations
  (generations 3, 4 and 7 held 10.0, 11.4 and 4.6 GB).
- **Evidence.** The owner's non-`accepted` stderr is
  `planning/evidence/service-envelope-2026-09-26/t100k-load-a-after-owner.stderr.txt`
  (sha256 fe27d708…).

This is PKT-191's "the checkpoint capture exhausts 32 GB", reproduced on the
current image during sustained posting, at N = 32,729 rather than 100,000.
**One owner process that posts without a restart cannot reach N = 100,000
on this image.**

The continuation reaches 100,000 as an operator would have to. It runs
`envelope-100k.sh` with `--session-posts 15000`: at most 15,000 preload POSTs
per owner process, then a restart that the next unit resumes from. That is not
a smaller case: the store still reaches 100,000, and the restarts are part of
what the row reports.

(the rows at 100,000: pending at this commit)

## 4. Findings

1. **Storage decides the POST rows on this pool.** On tmpfs, an unsigned POST's
   durable reply has a p95 of 6.5 ms and a signed one 282 ms. On `tank` (91
   percent full, no SLOG, load 12.5) they are 607 and 786 ms: 94 percent of an
   unsigned POST's wall time is the durable publication, not owner CPU (15.9 ms
   of 446 ms median). The pool meets neither the 250 ms nor the 10 POST/s
   target. It sustains about 1.4 to 2.1 POSTs a second. This is the weaker tier
   docs/operator.md publishes. marker-sharing (seven barriers to six) works on
   this term; a SLOG or a less full pool is the operator's lever.
2. **The greeting is still the widest miss after served-path-scale**: p95 1.3
   to 1.5 s at N = 10,000 (median 214 to 226 ms) against 50 ms, with 0.45 s of
   owner CPU per greeting. The p95 is the median's tail under the box's load,
   with the owner under the mutex for the whole walk. PKT-455 (its three
   remaining whole-state recognizers) is this row.
3. **OVER is linear in the rows it returns and slow per row**: about 8 ms a
   row (317 ms for 40, 703 ms for 100), unchanged by served-path-scale, and
   the same on both filesystems (CPU, not storage). No lane owns it: PKT-476 (3).
4. **A signed POST's owner CPU grows with N**: 89 ms at N = 1,000 (the gate),
   257 ms at 10,000 on tmpfs (signed-history-index's "after" was 0.241 s at
   10,000 with 32 signed: the same linear term, PKT-330 (2)).
5. **Memory under sustained posting**: on tmpfs the owner's VmHWM reached
   16.9 GB after the two rate windows had added 8,110 articles, against 3.7 GB
   on the ZFS copy, which added 218. RSS after the latency rows was 4.8 GB
   (tmpfs) against 0.9 GB (ZFS) with the same HWM of 7.5 GB. Peak residency
   follows the posting volume, not N alone. This is the risk for N = 100,000
   below.
6. **A checkpoint open is no faster than a full replay at N = 10,000 on
   tmpfs** (11.9 against 12.7 s). On ZFS it avoids the reads (10.6 against
   72.4 s wall).
7. **Concurrent posting costs owner CPU per POST.** From 1 to 8 connections the
   owner CPU per POST rises from 14.1 to 20.1 ms on tmpfs, and the POST p95
   under load goes from 18 to 490 ms. The rate windows swing from 150 to 1,361
   POSTs in 10 s, the signature of collections under the mutex. The before
   image's first tiny probe (N = 4,000 after a checkpoint open, 8 connections)
   collapsed to 0.49 POSTs a second at 2 s of owner CPU each. It was not
   reproduced in a matched probe (c1: 51 /s), and it is recorded here, not
   explained.

## 5. Logs and reproduction

The driver's log of every unit (`senv-*`, its start order and exit code) is
`planning/evidence/service-envelope-2026-09-26/driver.log`. The drivers are
`envelope.sh` (N = 10,000; `envelope.sh IMAGE REV TAG "10k"`) and
`envelope-100k.sh` (N = 100,000). Each runs inside a light driver unit on hbox
and each step runs as its own unit. The client files are shipped to
`/tank/fn/scratch/service-envelope/client/` and the JSONs are written to
`/tank/fn/scratch/service-envelope/`. Copies of the JSONs are here.
