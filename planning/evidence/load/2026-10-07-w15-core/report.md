# Load run w15-core

## W15@1k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.572 | - | - | - | - | 174024 | 52928 | 121096 | 244084 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 162156 | 41060 | 121096 | 244084 | 0.03 | 0 | 0 | - | - |
| census | 1 | - | - | - | - | 162540 | 41444 | 121096 | 244084 | 0.06 | 0 | 0 | - | - |
| publish | 1.29 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 0.429 | - | - | - | - | 163808 | 42888 | 120920 | 182172 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [25.0, 22.55, 21.21] at start and [24.17, 22.58, 21.26] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-core/W15_1k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w15-census.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

## W15@10k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.79 | - | - | - | - | 219508 | 98240 | 121268 | 379592 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 200292 | 79024 | 121268 | 379592 | 0.05 | 0 | 0 | - | - |
| census | 0.5 | - | - | - | - | 200868 | 79600 | 121268 | 379592 | 0.09 | 0 | 0 | - | - |
| publish | 9.86 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 1.84 | - | - | - | - | 215948 | 95192 | 120756 | 307392 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [24.17, 22.58, 21.26] at start and [23.12, 22.53, 21.3] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-core/W15_10k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w15-census.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

## W15@25k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 11.4 | - | - | - | - | 295928 | 174864 | 121064 | 488672 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 263416 | 142352 | 121064 | 488672 | 0.07 | 0 | 0 | - | - |
| census | 0.5 | - | - | - | - | 264184 | 143120 | 121064 | 488672 | 0.13 | 0 | 0 | - | - |
| publish | 25.5 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 4.53 | - | - | - | - | 307720 | 186612 | 121108 | 584868 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [23.12, 22.53, 21.3] at start and [22.93, 22.48, 21.36] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-core/W15_25k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w15-census.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

## W15@50k  target=fn-core arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 26.5 | - | - | - | - | 526208 | 405360 | 120848 | 671640 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 852168 | 731320 | 120848 | 852168 | 20.9 | 0 | 0 | - | - |
| census | 1 | - | - | - | - | 536704 | 415856 | 120848 | 864456 | 1.08 | 0 | 0 | - | - |
| publish | 53.7 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 8.1 | - | - | - | - | 454280 | 333104 | 121176 | 831104 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [22.93, 22.48, 21.36] at start and [20.48, 22.14, 21.39] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-core/W15_50k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w15-census.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

## W15  target=fn-core arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-OPEN | owner start to LISTENING from checkpoint at 50k (the fixture nearest F6's 40k, so stricter) and the exponent of open time against n (full replay and checkpoint) | open_s.checkpoint@50k <= 10 | 7.98 | NOT-MEASURED (box loaded (load 25.0 at start, 20.48 at end; a time bar needs <= 4 at both)) |
|  |  | open_s.checkpoint.exponent <= 1 | 0.845 |  |
|  |  | open_s.replay.exponent <= 1 | 0.965 |  |
| T-PUB | publication (checkpoint) wall at 40k; longest POST stall while it runs <= 2 s; octets written O(changed) | publish.stall_max_s <= 2 | - | NOT-MEASURED (box loaded (load 25.0 at start, 20.48 at end; a time bar needs <= 4 at both); longest POST stall during an online publication needs W8 (POSTs while a publication runs)) |
|  |  | publish.write_octets.exponent <= 0.5 | 0.957 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|

Conditions: box hbox (16 cores), load [25.0, 22.55, 21.21] at start and [20.48, 22.14, 21.39] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w15-core/W15_1k-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w15-census.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w15-core/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
