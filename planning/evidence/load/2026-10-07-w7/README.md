# W7 extent-cache contention (lane load-w7)

Verdict, pessimistic first: the BAR IS MISSED BY BOTH ARMS, and the lane misses it by more. Worst of 3 p99 at 16 readers
over p99 at 1 reader: **lane 4.87x (440.7 / 90.5 ms), dev 3.15x (220.8 / 70.1 ms)**, against the bar of 2x. Hit ratio did not
fall in either arm (1.0 throughout, preads/ARTICLE 0). Every one of the 24 cells passed the quiet check (mean busy < 0.15,
max < 0.5 on cores 12-23 for 5 s before the cell). The lane is the slower arm and sheds fewer requests with the 403 (see
below), so its p99 is not bought by refusing more. Box persvati, load average 5-19 (per cell in the JSON), cores 12-23.

Worst of 3 (max p50 / max p99 ms; min articles/s), persvati, scale, ext4, dev=c3-0b4d3b183, lane=s-extent-cache@9b6958f93:

| R | dev p50 / p99 | dev art/s | lane p50 / p99 | lane art/s |
|---|---|---|---|---|
| 1  | 50.1 / 70.1  | 19.1  | 50.1 / 90.5  | 18.7 |
| 4  | 51.0 / 82.9  | 73.6  | 57.0 / 135.0 | 64.6 |
| 16 | 84.2 / 220.8 | 103.1 | 141.1 / 440.7 | 56.1 |
| 31 | 141.5 / 421.8 | 95.8 | 329.9 / 970.4 | 43.9 |

Hit ratio 1.0 and preads/ARTICLE 0 in every cell of both arms (a lower bound; the ~21 MB store fits the dev cache, so the lane's
8-entry cap did not cause misses here). 403 "cold read resources unavailable" plus drops per 40 s cell, R16: dev 6,578-7,308
(4,716-5,330 steady), lane 3,859-4,319 (2,875-3,112 steady); R31: dev 8,233-8,816, lane 3,500-4,379; R1 and R4: 0 in both
arms. p99 covers successful ARTICLEs only. Lock wait NOT MEASURED in these stats-mode cells (hook full mode needed).

Arms: dev = c3-0b4d3b183 images (`/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host`);
lane = s-extent-cache@9b6958f93 (`persvati:/home/ember/fn-gates/sxc-c3/native-sxc-9b6958f93/tree/build/fn-host`).
Box persvati, cores 12-23 under `flock /tank/fn/scratch/timing-12-23.lock`, MemoryMax 16G, ext4 on /dev/nvme0n1p2.
Workload (S, final): `--profile scale` unraised, 2,000 articles, 90% 8 KiB / 10% ~32 KiB, Zipf s=1.0,
ARTICLE by message-id, 10 s warm-up + 30 s measured, readers are processes. Heap decided by the image probe
(14463 MB, recorded per cell). Driver `tools/load/w7_extent.py`, hook `w7hook.lisp`, loop `ab.sh`.

## Of record: the 24 cells above

Per-cell JSON (image sha, decided heap, uptime, per-core busy, refusals per second) is in `persvati:/tank/fn/scratch/load/w7-ab/cells-run4-ab.jsonl`.

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

## Not run
W7b (20,000 articles, scale): `W7_ARTICLES=20000`. Full-mode lock-wait cells. The A/B job (pids 330595/330597/330598) has finished; nothing is pending.
