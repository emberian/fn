# What fn costs, 2026-09-26: the performance ledger

Lane `lane/perf-ledger` (Opus 5.5), from dev `f314a5a3`, under the Fable
mandate §7 ("a fast helper is not a fast command"). Brief:
`build/coordinator/queue/done/w4-perf-ledger.txt`. No book and no host file
changed. Profiles and scripts: `planning/evidence/perf-ledger-2026-09-26/`.

## For ember

**Why the node is still slow.** Three things, in this order of what a user
feels. First, whole-state work on the served path: every connection's
greeting still runs the whole-state recognizer `fn-statep` over every
article, which walks every retained payload octet by octet
(`fn-articlep` → `fn-octet-listp` is 87 percent of a greeting's CPU); an
OVER still finds each requested article number by walking the group's index
entries and re-validating each entry's Message-ID as it goes
(`fn-gidx-find-number-entry` → `fn-nntp-index-entry-available`, 95 percent of
OVER's CPU), so a newsreader's 40-row OVER costs 320 ms and a 2,000-row OVER
costs 17.7 s at N = 10,000 and 37.8 s at N = 20,000; and a POST still walks the
pins and the article list to test the new Message-ID
(`fn-retain-known-id-scanp` and `fn-find-article`, 50 percent of its CPU).
Second, the octet-list representation everywhere else: the replay, the
checkpoint open, the automatic checkpoint capture and the BP codec spend
their time walking and copying cons lists of octets (sixteen bytes per
retained octet; the capture of a 20,000-article store takes 74 s and a
15.7 GB peak, and past about N = 33,000 it exhausts the 32 GB heap and kills
the node). Third, fsync on a full pool: on `tank` (91 percent full, no SLOG)
an unsigned POST's durable reply is 446 ms median against 4.6 ms on tmpfs,
because a commit is 7.2 fsyncs of 40 to 60 ms each. One surprise from this
lane's profiles: the BP bundle codec costs about 7.7 µs per octet (a 1 MiB
bundle encodes in 8.0 s and decodes in 15.4 s), and 99 percent of that is a
bitwise CRC-32C whose XOR is computed one bit at a time by `floor`
(`fn-bpp-xor`, books/bp-primary.lisp).

**What one decision would unlock.** PKT-293 (answer (a): the records freeze
as two views of one record, a held record whose payload is an arena handle
beside the wire record the codec keeps). The first group above is
lane work and is listed below as fix lanes; the third is the pool
(PKT-442 / PKT-477 (2)) and no code removes it. But everything in the
second group waits on PKT-293: it is what lets the retained payload be one
byte per octet (5.55 GB live at 10,000 x 32 KiB becomes about 0.6 GB), what
lets the checkpoint carry each payload once (PKT-307), and what removes the
per-octet recognizers that are the top three entries of both the full-replay
and the checkpoint-open profiles (`fn-cbor-octet-listp`,
`fn-record-string-octets-aux`, `fn-record-payloadp`: 50 to 70 percent of an
open). Until it is answered the lanes can remove walks but not octets.

## The ranking

Seconds a user waits per common action, then heap. "Now" is a lane can do it
today; "ember" waits on a decision. Figures are this lane's (hbox, tmpfs,
N = 10,000 x 2 KiB, dev `f314a5a3`, load average 13 to 16, so times are
indicative and shares and bytes are the robust figures) unless a record is
named.

| # | What the user does | Waits | Cause (the function) | Fix pattern | Owner | Expected |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | open a group in a newsreader (OVER over the range) | 40 rows 320 ms median, 490 ms p95; 2,000 rows 17.7 s (37.8 s at N = 20,000); 263 MB and 17 GB consed | `fn-gidx-find-number-entry` walks the group's entries per requested number, calling `fn-nntp-index-entry-available` (Message-ID re-validated through `fn-nntp-string-octets`) on each | carried invariant + index by number | **fix lane 1** (PKT-476 (3)) | O(rows): OVER 2,000 under 1 s; OVER 40 near STAT's 0.7 ms plus 40 NOV lines |
| 2 | connect (greeting) | 238 ms median, 328 ms p95, 245 ms owner CPU at 10,000; 642 ms at 20,000; 1.3 to 1.5 s p95 and 3.9 s median at 36,208 (service-envelope) | `fn-statep` of the view's archive twice and `fn-node-statep` once (`fn-ocfg-open` → `fn-peer-open-session`), each `fn-articlep` → `fn-octet-listp` over every payload, under the owner mutex | carried invariant | served-path-scale-2 (running; PKT-455 (1)) | O(groups): below 1 ms (0.34 ms is the pre-load floor, hot-path-checker) |
| 3 | POST on the pool | 446 ms median, 607 ms p95 unsigned; 460 / 786 ms signed (service-envelope, `tank` at 91 percent) | 7.2 fsyncs per commit on ZFS with no SLOG (commit-regression) | I/O + hardware | marker-sharing-3 (7 to 6 barriers); **ember** PKT-442 / PKT-477 (2) | 6/7 of today's from the barrier; the rest is the pool |
| 4 | signed POST | 253 ms median tmpfs, 257 ms owner CPU at 10,000; 921 ms at 36,208 | a linear term per signed POST (PKT-330 (2)); not profiled here | carried invariant (profile first) | **fix lane 5** | flat in N: 89 ms at N = 1,000 is the level (the gate's row) |
| 5 | POST (CPU) | 10.2 ms median, 10.8 ms owner CPU, 2.25 MB consed at 10,000 (4.7 ms, 1.84 MB near N = 0) | `fn-owner-prepare-buffer` 52.8 %: `fn-retain-known-id-scanp` 28.0 %, `fn-rclb-existing-action` → `fn-find-article` 21.9 % and `fn-acceptedp` 10.2 % walk the pins and articles with `equal`; ingress bytes `fn-scar-feed-counted` 11.5 % (49.5 % of the bytes) | carried index (the event index's Message-ID trie) | **fix lane 3**; ingress-span (running) for the bytes | about 4.5 ms owner CPU, flat in N |
| 6 | read a large article | ARTICLE 3 MiB 5.0 s wall, 0.9 s owner CPU, 571 MB consed; 32 KiB 88 ms wall, 5.8 MB; POST 3 MiB 3.6 s, 1.94 GB consed | the reply built as an octet list (`fn-nntp-crlf-lines-aux`, `fn-ag-rev-onto`, `fn-owner-output`); 4 s of the 5 s wall is not owner CPU (below) | codec / representation (the reply as a buffer range) | **fix lane 4** (PKT-491) | ARTICLE in O(L) octets written, no list; the pacing term needs its own look |
| 7 | read by number (ARTICLE n, HEAD n, BODY n) | ARTICLE 2 KiB by number 7.2 ms vs 2.4 ms by Message-ID | the same walk as row 1, one number | as row 1 | fix lane 1 | about 2.4 ms |
| 8 | restart: full replay | 16.5 to 29.5 s at 10,000 tmpfs under load (12.7 s tmpfs, 72.4 s ZFS in service-envelope); 162 s at 20,000 (chain fixture); 164 s and 22.5 GB at 10,000 x 32 KiB (rep-wave-d-2) | the history recognizer and decode over octet lists: `fn-record-string-octets-aux` 24.2, `fn-cbor-octet-listp` 20.5, `fn-record-payloadp` 20.3 percent (served-path-scale) | representation; carried invariant for the per-record recognizers | served-path-scale-2 (PKT-455 (2)); **ember** PKT-293 | the recognizer half is walks (lane); the octets are the arena |
| 9 | restart: from a checkpoint | 14.6 s at 10,000; 68.9 s at 20,000 on the chain; 132 s, 19.3 GB at 10,000 x 32 KiB (rep-wave-d-3) | `fn-record-p` 27.3 / 33.3 %, `fn-sf-record-listp` 23.8 / 11.5 %, `fn-sccr-decode-plan` 34.2 / 15.7 %, and on the chain `fn-ccc-decode-link` 29.8 % (every link decoded at each open); `fn-store-sco-prefix-octets` (PKT-041) 0.0 % | carried invariant (the recognizer), codec (the link walk) | PKT-041 is **not** the cost (below); the recognizer is PKT-455 (2); the link walk PKT-168 (3) | about half the checkpoint open is the re-recognition |
| 10 | automatic checkpoint capture (posting continues; the node's ceiling) | 74.1 s and a 15.7 GB peak at 20,000; 90 s at 29,453; heap death at 32,729 and 36,208 (service-envelope) | `fn-ock-publication` 84.2 %: the list codec `fn-scc-file-octets` 70.9 % (`fn-scc-frames` 38.7, `fn-scc-renc` 12.6, SHA-256 over lists 20.0) | codec over the buffer | checkpoint-capture-stream (running; PKT-191) | the verb's buffer path: halved residency (rep-wave-d-2), no heap death |
| 11 | a BP bundle (encode, decode) | 1 MiB: encode 8.0 s, decode 15.4 s; 48 KiB: 0.37 / 0.71 s; SCN-077's receiver open of 1,311 held rows 51.9 s, of it encode 23.5 s and decode 15.7 s (bp-lifecycle-5) | `fn-bpp-crc32c-scan` 99.4 % of encode, 95.4 % of decode: `fn-bpp-xor` by `floor`, 32 recursions per XOR, 288 per octet | codec (an `:exec` twin: `logxor`, a table-driven CRC-32C) | **fix lane 2** (PKT-414) | codec to about 1 % of today; the 51.9 s open to about 13 s |
| 12 | `store checkpoint` (offline) | 24.5 s, 2.7 GB peak at 10,402 (17.5 s service-envelope); 154 s, 22.5 GB at 10,000 x 32 KiB | the replay first, then the buffer writer (0.12 µs per octet export call, PKT-315) | codec | checkpoint-capture-stream (PKT-315 in its LANEDUMP) | the replay dominates |
| 13 | offline `operator` request | 9 to 10 s at 700 to 800 records; O(N^2) over N requests (8,336 s for 1,100) | the whole configuration log replayed at every open (PKT-501) | carried invariant (a configuration checkpoint) | caps-to-profile-2 (running) | flat per request |
| 14 | `store compact` | 523 s at 20,000 (pack-chain-open, 8cc3cd4c: before served-path-scale; its open was then the quadratic freshness walk) | not re-measured on dev | — | unmeasured (PKT-554 below) | — |
| 15 | consumer poll | 127 ms median at ACK 0, 135 ms at ACK 96 (118 events; 58 ms on a quieter box, 2026-09-24) | CLI-inclusive: the process start of a 32 GB-dynamic-space image dominates; flat in the position | — | none needed at this size | — |
| 16 | `store reclaim` | 2.6 s for 300 reclaimed (reclaim-lifecycle-2) | no scale figure | — | unmeasured (PKT-554) | — |

**Heap.** Live: sixteen bytes per retained octet (5.55 GB at 10,000 x 32 KiB,
rep-wave-d), and a checkpoint-opened owner holds each payload twice (19.3 GB
peak, PKT-307): both ember's (PKT-293). Peak: the capture, 15.7 GB at 20,000
and death at about 33,000 (checkpoint-capture-stream). Garbage per request
(consed, not held): OVER 2,000 rows 17 GB, POST 3 MiB 1.94 GB, ARTICLE 3 MiB
571 MB, OVER 40 rows 263 MB, POST 2 KiB 2.25 MB.

### What waits on ember, and what a lane can do now

- **Waits on ember:** PKT-293 with PKT-167 (the records freeze and the arena:
  rows 8 and 9's octet half, the live heap, the checkpoint's second copy
  PKT-307); PKT-442 / PKT-477 (2) (the pool: row 3's remainder after
  marker-sharing-3).
- **Running now:** served-path-scale-2 (rows 2, 8, 9's recognizers:
  PKT-455), checkpoint-capture-stream (rows 10, 12), ingress-span (row 5's
  and row 6's POST bytes), marker-sharing-3 (row 3's barrier),
  caps-to-profile-2 (row 13).
- **Now, unowned:** rows 1 and 7, 11, 5's identity walks, 6's reply, 4.

### The next five fix lanes, in order

1. **over-number-index** (rows 1, 7; PKT-476 (3)). Serve an article number's
   entry from an index keyed by number instead of `fn-gidx-find-number-entry`'s
   walk, and carry "every entry's Message-ID is valid" in the group index's
   relation instead of re-deciding it per entry per lookup. Subject:
   `fn-gidx-entry-number-article` (books/group-bucket-article.lisp), reached
   from `fn-owner-chunk`. Expected: OVER 40 rows from 320 ms to tens of ms,
   OVER 2,000 from 17.7 s to under 1 s at 10,000, ARTICLE by number from
   7.2 to about 2.4 ms. Evidence: 94.9 percent of OVER's samples are under
   `fn-gidx-find-number-entry`; OVER 2,000 doubles from N = 10,000 to
   20,000 (17.7 to 37.8 s), so its cost is rows x N; ARTICLE by Message-ID,
   which does not walk, is 2.4 ms.
2. **bp-crc-exec** (row 11; PKT-414). `fn-bpp-xor` and the CRC-32C step get
   `:exec` bodies (`logxor`; a 256-entry table), each proved equal to the
   bitwise definition; no statement moves. Expected: the codec at about
   1 percent of today (99.4 and 95.4 percent of encode and decode samples are
   the CRC), so a 1 MiB bundle in about 0.1 s and SCN-077's 51.9 s receiver
   open (39.2 s of it encode and decode) near 13 s; then PKT-308 (4)'s
   three encodes per row matter again.
3. **post-identity-index** (row 5). `fn-retain-known-id-scanp`,
   `fn-rclb-existing-action`'s `fn-find-article` and `fn-acceptedp` answered
   from the Store's derived event index (the Message-ID trie, whose relation
   `fn-ceis-indexedp` is already established at open and preserved,
   PRF-144), the pattern of hot-path-scans-2's `fn-sbud-count`. Expected:
   about 60 percent of a POST's owner CPU at N = 10,000 (10.8 to about
   4.5 ms) and flat in N. Evidence: the POST profile's graph, callers named:
   `fn-retain-admissiblep` → `fn-retain-known-id-scanp` 28.0,
   `fn-rclb-existing-action` → `fn-find-article` 21.9, `fn-accept-prepare`
   → `fn-acceptedp` 10.2 percent; 670 of EQUAL's 676 self samples are under
   these three.
4. **egress-span** (row 6; PKT-491). The served reply as a buffer range
   the writer drains, the reply-side twin of ingress-span. Expected: ARTICLE
   3 MiB's 571 MB of conses and its 0.9 s of owner CPU to O(L) octet
   copies; the 4 s of wall that is not owner CPU is examined first (the
   profile shows `clock_nanosleep` in the owner: pacing or the writer).
5. **signed-post-linear** (row 4; PKT-330 (2)). Profile a signed POST at
   N = 10,000 first; the envelope's rows say linear in N (257 ms at 10,000,
   921 ms at 36,208, 89 ms at 1,000).

## The rows in full

Each row: wall and CPU, tmpfs and pool where measured, allocation, the top
profile entries with shares, the cause, the fix pattern, the owner, and the
expectation's evidence. "(this lane)" rows are hbox, tmpfs, image of dev
`f314a5a3` (below); others cite their record.

### Open (restart)

- **Full replay.** N = 10,000 x 2 KiB (this lane): 16.5 to 29.5 s to
  LISTENING over four reopens (`OWNER-OPEN open=full-replay reason=absent`;
  the load-average spread), VmHWM 1.5 to 1.9 GB. N = 10,000
  (service-envelope): 12.7 s tmpfs, 72.4 s ZFS (14.3 s CPU). N = 20,000:
  162.0 s on the chain fixture (this lane; `reason=checkpoint-open-refused`,
  6.5 GB VmHWM), 103 to 110 s in served-path-scale. N = 10,000 x 32 KiB:
  164 s, 22.5 GB (rep-wave-d-2). Profile (served-path-scale, N = 20,000):
  `fn-record-string-octets-aux` 24.2, `fn-cbor-octet-listp` 20.5,
  `fn-record-payloadp` 20.3 percent. Cause: the history recognizer and the
  record decode walk every payload as an octet list. Fix: the per-record
  recognizer is carried (the decode establishes what it re-checks), the
  octets are the arena. Owner: served-path-scale-2 (PKT-455 (2)); PKT-293.
- **From a checkpoint.** N = 10,000 (this lane): `store checkpoint` 24.5 s
  (22.1 s user, 2.7 GB peak, 80,413,030 octets), then the open 14.6 s
  (`open=checkpoint:10402 suffix=0`), VmHWM 2.6 GB. Profile
  (`n10k/sprof-ckptopen-flat.txt`, graph totals): `fn-sccr-decode-plan`
  34.2, `fn-record-p` 27.3, `fn-sf-record-listp` 23.8, `fn-sn-statep` 13.0,
  `fn-store-sco-prefix-octets` 0.0 percent. N = 20,000 on the chain (this
  lane): 68.9 s (`open=checkpoint:20000 suffix=0`), 5.7 GB VmHWM; `fn-record-p`
  33.3, `fn-ccc-decode-link` 29.8, `fn-sccr-decode-plan` 15.7,
  `fn-sf-record-listp` 11.5 percent. **PKT-041 is not the cost**: the
  prefix octets rebuild has 3 samples of 8,000 and 39,594. The cost is the
  re-recognition of every decoded record (`fn-record-p`, `fn-sf-record-listp`
  under `fn-sn-statep`) and, on a chain, decoding every link at each open
  (PKT-168 (3), `fnn-pack-lower-bound`). N = 10,000 x 32 KiB: 132 s, 19.3 GB
  (rep-wave-d-3).
- **From a chain.** 196 s at bf5b2471 (pack-chain-open), then dominated by
  the quadratic freshness walk that served-path-scale removed; today the
  fixture's checkpoint is refused by format, so a chain open is the full
  replay above plus the link decode.

### Greeting (this lane: `n10k/greet-64.json`, `n10k/sprof-greet-flat.txt`)

64 fresh connections on the loaded owner at N = 10,000: 238 ms median,
328 ms p95, 245 ms owner CPU each. At N = 20,000 on the chain: 642 ms median,
802 ms p95. Graph totals: `fn-ocfg-open` 98.0, `fn-peer-open-session` 98.0,
`fn-statep` 91.8, `fn-own-reader-context` 65.4, `fn-nntp-projectionp` 62.2,
`fn-node-statep` 35.8, `fn-own-open` 32.6 percent; flat: `fn-octet-listp`
79.4, `fn-octetp` 30.8, `fn-articlep` 87.1 percent. So the linear term is
per retained octet, not per article: at 32 KiB articles it is sixteen times
this. Owner: served-path-scale-2 (PKT-455 (1)), whose design takes the
recognizers from `fn-ocl-relation`.

### GROUP, STAT, ARTICLE, OVER (this lane: `n10k/reads.json`, `n10k/sprof-over2000-flat.txt`)

At N = 10,000: GROUP 47 ms (0.11 s at 20,000); STAT by number 0.72 ms,
38.9 KB; ARTICLE 2 KiB by number 7.2 ms, 420 KB; OVER one row 8.9 ms,
4.8 MB; OVER 40 rows 320 ms median, 490 ms p95, 263 MB; OVER 1-2000 17.7 s
(five profiled: 17.2 to 19.2 s; 89.3 s owner CPU over 90.1 s wall), 17.1 GB
consed each. At N = 20,000: OVER 40 rows 450 ms median, 784 ms p95; OVER
1-2000 37.8 s. OVER profile, graph totals: `fn-gidx-find-number-entry`
94.9, `fn-nntp-index-entry-available` 91.9, `fn-nntp-string-octets-aux`
72.3, `fn-nntp-index-msgid-okp` 58.4, `fn-nntp-message-id-tokenp` 26.9
percent. Cause and fix: fix lane 1. hot-path-checker's PKT-448 (c) named
the served read walks as OVER's candidates; this profile names the one
that costs.

Large articles (this lane: `big/big.json`, `big/sprof-article3m-flat.txt`;
a default-profile store with `--max-article-octets 4194304`, N < 30):

| op | wall median | owner CPU per op | consed per op |
| --- | ---: | ---: | ---: |
| POST 2 KiB | 4.7 ms | 5 ms | 1.84 MB |
| POST 32 KiB | 39.5 ms | 42 ms | 20.9 MB |
| POST 3 MiB | 3,576 ms | 3,557 ms | 1.94 GB |
| ARTICLE 2 KiB | 5.5 ms | (under the tick) | 416 KB |
| ARTICLE 32 KiB | 88 ms | 8 ms | 5.8 MB |
| ARTICLE 3 MiB | 5,248 ms (p95 8,643) | 1,067 ms | 571 MB |

ARTICLE's wall is mostly not owner CPU (3 MiB: 15.3 s wall, 2.7 s owner CPU
over the three profiled); the samples show `clock_nanosleep` and `poll` in
the owner, and the client reads line by line, so the remaining wall is the
writer's pacing or the client, not yet separated (PKT-555 below). The owner
CPU is the reply built as lists: `fn-ag-rev-onto` 19.4, `fn-nntp-crlf-lines-aux`
31.5, `revappend` 11.7, `fn-octet-listp` 8.4 percent. POST's is the ingress
byte machine (ingress-span).

### POST (this lane: `n10k/post-200-cpu.json`, `post-200-alloc.json`, the two flats)

At N = 10,000, 200 POSTs of 2 KiB on a reopened owner: 10.2 ms median,
15.6 ms p95, 10.8 ms owner CPU, 2,254,254 bytes consed each. The load's
quarters: 3.6 ms median in the first 2,500, 6.1 ms in the last (48.3 s for
10,000). Before served-path-scale the same point consed 7.97 MB per POST
(hot-path-scans-2, whose base lacked served-path-scale); `fn-own-refresh`
is now 1.4 percent of POST CPU: **PKT-324 (1) is closed by
`fn-gidx-refresh`** (the 5.7 MB per POST was the group-index rebuild).
CPU, graph totals: `fn-owner-prepare-buffer` 52.8, `fn-retain-known-id-scanp`
28.0, `fn-rclb-existing-action` 22.0, `fn-scar-feed-counted` 11.5,
`fn-acceptedp` 10.2 percent. Allocation, graph totals:
`fn-scar-feed-counted` 49.5, `fn-wire-feed-byte` 19.9, `fnn-owner-publish-prepared`
19.5, `fn-wire-make-state` 17.5, `fn-served-make-conn-group-indexed` 15.6,
`fn-article-parse-lines` 11.4 percent. On ZFS: 446 ms median, 607 ms p95
(service-envelope; 7.2 fsyncs a commit, commit-regression). Signed POST:
service-envelope's rows (282 ms p95 tmpfs, 786 ms ZFS at 10,000; 963 ms at
36,208); not profiled here.

### Automatic checkpoint capture (this lane: `chain20k/chain.json`, `chain20k/sprof-capture-flat.txt`)

The chain fixture's copy, first open (full replay, the fixture's checkpoint
refused by format), then the capture the open triggers: `CHECKPOINT auto
sequence=20000 suffix=20000 octets=151595032 ms=74126`; owner VmHWM 6.5 GB at
LISTENING and 15.7 GB after the capture. Graph totals: `fn-ock-publication`
84.2, `fn-scc-file-octets` 70.9, `fn-scc-frames` 38.7, `fn-shs-digest-list`
20.0, `fn-scc-renc` 12.6, `fnn-octets` 10.6, `fn-sco-extend` 1.7 percent. The
ground truth (build/coordinator/ground-truth-checkpoint-capture.md) holds on
dev: the automatic path is the list codec. service-envelope's series (4.2 s
at 2,209, 24.2 s at 10,626, 54.2 s at 21,050, 90.1 s at 29,453, death in
`FN-SCC-FRAMES` at 32,729 and 36,208) is the row's scale. Owner:
checkpoint-capture-stream.

### BP (this lane: `bpenc.out`, `bp-encode-256k-flat.txt`, `bp-decode-256k-flat.txt`)

The developer core's raw Lisp (what `fnn-core` runs after the guard), one
bundle per payload size built by `fn-bpn-send-bundle`:

| payload | guard `fn-bpb-bundlep` | encode | decode | consed (encode, decode) |
| ---: | ---: | ---: | ---: | ---: |
| 4,096 | 1 ms | 28 ms | 61 ms | 197 KB, 328 KB |
| 49,152 | 1 ms | 370 ms | 706 ms | 2.4 MB, 3.9 MB |
| 1,048,576 | 23 ms | 8,037 ms | 15,362 ms | 50 MB, 84 MB |

Linear, 7.7 µs an octet to encode and 14.6 to decode, and not allocation (48
bytes an octet). Profile of a 262,144-octet bundle: `fn-bpp-crc32c-scan`
99.4 percent of encode and 95.4 of decode; self time in `floor` (61 and 63
percent) under `fn-bpp-xor`. PKT-414's "0.31 s for 49,254 octets" was this
term; its "three scans encode every candidate" multiplies it. 10 MiB
(bp-lifecycle-5): authored as 2,622 fragments in 27.3 s, 1,311 received in
90.2 s (under 70 ms a fragment), and the receiver's open of those rows
51.9 s, 39.2 s of it `fn-bpb-encode` and `fn-bpb-decode`. A 1 MiB transfer
end to end was not run (PKT-554).

**Result (bp-crc-exec, 2026-09-26, PRF-190):** the CRC-32C runs a table and
`fn-bpp-xor` runs `logxor`, each proved equal to the bitwise definition; on
hbox back to back a 1 MiB bundle encodes in 0.058 s against 3.68 s and
decodes in 0.140 s against 7.65 s on the base image (1.5 and 1.8 percent), the
wire bytes identical. Row 11 narrowed to the allocation and PKT-546
(planning/evidence/bp-crc-exec-2026-09-26.md).

### Consumer poll (this lane: `consumer-poll.json`)

tests/perf/native_consumer_poll_cost.py on this image: 127 ms median at ACK 0
and 135 ms at ACK 96 of 118 events (58 ms on 2026-09-24's quieter box). A
poll answers at most one 16-event cursor window, so "a 1,000-entry page" is
about 63 polls; each is a CLI process, and the process start is the cost.
The fixture's development profile caps the journal at 128 events: a poll at
depth 1,000 or 10,000 is not measured (PKT-554).

## Measurements taken here

- **Image.** dev `f314a5a3` shipped to `hbox:/tank/fn/scratch/perf-ledger/tree`
  (`git archive`), certified wholly from `/tank/fn/certcache` (the default
  profile's roots, `--incremental`), `proof_artifacts acquire`/`validate`,
  the developer image (launcher `99efff4a…`, core `addf58ae…`) and its
  profiling twin with `prof-raw.lisp` (launcher `662e5387…`, core
  `90544f4c…`; `image.sha256`), built under `swarm-build` at 14:55 to
  15:00Z, before BRIEF-COMMON's batch rule (15:06Z) that a lane builds no
  image; no further image was built.
- **Harness.** `perf.py` (phases load, post, reads, greet, ckptopen, chain,
  big) driven by `drive.sh`, each phase its own `systemd-run --user --scope`
  with `MemoryMax=24G` and no swap (the chain phase 40G, BRIEF-COMMON's figure
  for N >= 10,000), stores on `/dev/shm`, one phase at a time. A CPU window
  is sb-sprof `:cpu` at 1 ms over all threads between two trigger files; an
  allocation window is `:alloc`; bytes consed per operation come from the
  heap hook (`heap.lisp`) bracketing a batch; owner CPU is
  `/proc/PID/stat`. The BP rows: `bpenc.sh`/`bpenc.lisp` and
  `bpprof.sh`/`bpprof.lisp` in the developer core. Consumer poll: the
  committed fixture, `FN_NATIVE_DEVELOPER_HOST` the developer image.
- **The box.** Load average 13 to 16 throughout (15:00 to 15:25Z). Running
  user units beside each phase (in each JSON's `box_before`/`box_after`):
  `qual-dfa810fc-chaincuts`, `qual-dfa810fc-chainM`, `qual-dfa810fc-mixed`,
  `sps2-chain1` and `sps2-fix-base` (served-path-scale-2),
  `throughput-gate-6addf2944899-…` (15:06Z), `fn-node` (the live node, not
  touched), `spike-reader-node`, `spike-reader-web`, the dregg services.
  Times are indicative; profile shares, bytes consed and owner CPU per
  operation are the figures to compare.
- **Files.** `planning/evidence/perf-ledger-2026-09-26/`: `SHA256SUMS`
  covers every file there. The call graphs (about 180 KB each) are kept at
  `hbox:/tank/fn/scratch/perf-ledger/graphs/` with their SHA-256s in
  `graphs.sha256`; the graph totals quoted above come from them.

## Not measured, and packets

The brief assigned PKT-500 to 509, but every one of them was already taken
on dev (PKT-500 live `bp-obligation status`, 501 the configuration replay,
502 to 509 sweep 19 and 20's). This lane therefore takes no id; its packets
were named A to E; the deputy numbered them PKT-554 to PKT-558 at the merge
(the backlog carries them).

- **PKT-554 (was PKT-A): rows not measured on dev.** `store compact` at 20,000 (523 s on
  8cc3cd4c predates served-path-scale); `store reclaim` at scale; a 1 MiB and
  a 10 MiB BP transfer end to end; a consumer poll at journal depth 1,000 and
  10,000 (the fixture's profile caps it at 128); signed POST's profile;
  anything on the pool (every row here is tmpfs); a quiet box.
- **PKT-555 (was PKT-B): ARTICLE 3 MiB's wall is not owner CPU.** 15.3 s wall against 2.7 s
  owner CPU over three; `clock_nanosleep` and `poll` in the owner's samples.
  Separate the writer's pacing from the client's line reads before
  egress-span claims a wall-time gain.
- **PKT-556 (was PKT-C): the chain open decodes every link.** `fn-ccc-decode-link` is 29.8
  percent of the checkpoint open at 20,000 (PKT-168 (3)); a checkpoint open
  needs only the links past its sequence.
- **PKT-557 (was PKT-D): PKT-041 retired as a cost.** `fn-store-sco-prefix-octets` has 3
  samples in each checkpoint-open profile; the checkpoint open's cost is
  `fn-record-p` and `fn-sf-record-listp` re-recognizing what the decode
  produced (fold into PKT-455 (2)).
- **PKT-558 (was PKT-E): the POST's per-connection group index.**
  `fn-served-make-conn-group-indexed` is 15.6 percent of a POST's bytes at
  10,000; examine whether it rebuilds per request.
- The five fix lanes above are the packets for the unowned rows (PKT-476 (3),
  PKT-414, the POST identity walks, PKT-491, PKT-330 (2)).

## Assurance chain

This lane proves nothing and changes no book or host line. What it observes:
native entries `operator CONFIG run` (host/native/owner.lisp), `store STORE
checkpoint` (`fnn-command-state-checkpoint`), the owner's automatic
publication (`fnn-owner-maybe-publish`), and the BP codec's executed
functions called in the image; the profiles name the executed ACL2 subjects
under those entries. Every figure names its image (core SHA-256 in each
JSON), the box's load and units, the filesystem, and its file.
