# W7 extent-cache contention: PARTIAL, no verdict yet (lane load-w7)

Verdict: NOT JUDGED. 4 of 24 A/B cells of record exist (R1 and R4, run 0, both arms). The bar
(p99 at 16 <= 2x p99 at 1; hit ratio not falling) needs R16, which has not run. Pessimistic first:
the only R16 figures are the unlocked/loaded dev runs below, where dev itself is at 5.8x.

Arms: dev = c3-0b4d3b183 images (`/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host`);
lane = s-extent-cache@9b6958f93 (`persvati:/home/ember/fn-gates/sxc-c3/native-sxc-9b6958f93/tree/build/fn-host`).
Box persvati, cores 12-23 under `flock /tank/fn/scratch/timing-12-23.lock`, MemoryMax 16G, ext4 on /dev/nvme0n1p2.
Workload (S, final): `--profile scale` unraised, 2,000 articles, 90% 8 KiB / 10% ~32 KiB, Zipf s=1.0,
ARTICLE by message-id, 10 s warm-up + 30 s measured, readers are processes. Heap decided by the image probe
(14463 MB, recorded per cell). Driver `tools/load/w7_extent.py`, hook `w7hook.lisp`, loop `ab.sh`.

## Of record (quiet check passed: 5 s mean busy < 0.15, max < 0.5 before each cell; load average noted per cell)

| arm | R | p50 ms | p99 ms | articles/s | 403+drops | preads/ARTICLE |
|---|---|---|---|---|---|---|
| dev  | 1 | 50 | 69  | 19.4 | 0 | 0 |
| lane | 1 | 49 | 67  | 19.5 | 0 | 0 |
| dev  | 4 | 50 | 77  | 75.4 | 0 | 0 |
| lane | 4 | 53 | 109 | 69.5 | 0 | 0 |

One run each (not worst-of-3); lane R4 p99 is 1.4x dev's, a single sample. Measured-window busy on 12-23
was 0.16-0.25 mean (our own load included). Hit ratio is the lower bound 1 - preads/article (`*fnn-extent-stats*`
hits count octets, not articles); it is 1.0 everywhere because the whole ~21 MB store fits the dev cache.

## Not of record: dev only, cores 12-23 shared (busy 0.55-0.98), loaded; worst of 3 p99/p50 ms
(run3 locked but without the quiet check; run2 unlocked) R1 100/60, R4 164/66, R16 525/160, R31 921/287.
p99(16)/p99(1) = 5.3x on these (dev fails the bar under load). Raw: `persvati:/tank/fn/scratch/load/w7-ab/`.

## Findings
1. **403 "article temporarily unavailable; cold read resources unavailable"** (S files COLD-READ-WORKERS-REFUSE-AT-16):
   0 at R1 and R4 in every run; at R16 1,042-6,571 per 40 s cell (steady state: 2,335-4,584 of them after warm-up) and at
   R31/32 3,983-8,458; the node logs `cursor quantum: payload read read-resources-unavailable`. R32 additionally has
   500-1,200 dropped connections (the 400 too-many-connections cap), so the spec runs R=31.
2. Small preset refuses a 512 KiB article: `init: max-record-octets 196608 is below 529547, the record of one article at
   max-article-octets 524288 in max-groups-per-article 16 groups` (MAX-RECORD-OCTETS-BELOW-THE-ARTICLE-RECORD).
3. "no decided profile admits 512 KiB articles at C3 (A = 32,768 in every profile)" -- owner unassigned, for the coordinator.
4. development: the 128th POST gets `441 posting failed; the store is full: no capacity for this article (unaffordable)`
   (T = 128). With `--max-transactions 4096`, H = 24 MiB binds at 1,873 of 2,000 articles:
   `441 ... the store's history budget is exhausted (history-exhausted)`. Plain scale holds all 2,000.
5. Lock wait: measurable only with the hook in full mode (contended grabs timed through `sb-thread::mutex-wait`, since
   with-mutex is inlined); NOT measured in the A/B (stats mode); the A/B cells carry no hook in the lock path.
6. W7b (20,000 articles, scale): not run (`W7_ARTICLES=20000`).

## Pending
Detached A/B on persvati: pids 330595 (bash), 330597 (timeout), 330598 (ab.sh); log
`persvati:/tank/fn/scratch/load-w7/run4/ab.log`, cells `.../run4/cells.jsonl`. 20 of 24 cells remain
(R16, R31 run 0; all of runs 1-2), order dev,lane per R. Judge with `python3 tools/load/w7_extent.py evaluate cells.jsonl`
(cells with `quiet_check.quiet` false are not judged). Raw copies of earlier runs: `persvati:/tank/fn/scratch/load/w7-ab/`.
