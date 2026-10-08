# Load run w15-img2

## W15@1k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.688 | - | - | - | - | 620932 | 56212 | 564720 | 691100 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 609400 | 44680 | 564720 | 691100 | 0.03 | 0 | 0 | - | - |
| census | 2 | - | - | - | - | 608156 | 43436 | 564720 | 691100 | 1.54 | 0 | 0 | - | - |
| publish | 1.24 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 0.631 | - | - | - | - | 610940 | 46384 | 564556 | 664108 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [21.67, 22.44, 21.48] at start and [20.9, 22.17, 21.41] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-img2/W15_1k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-img2/W15_1k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@10k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.39 | - | - | - | - | 666336 | 101844 | 564492 | 830436 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 647668 | 83176 | 564492 | 830436 | 0.05 | 0 | 0 | - | - |
| census | 2 | - | - | - | - | 647280 | 82788 | 564492 | 830436 | 1.44 | 0 | 0 | - | - |
| publish | 8.95 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 1.71 | - | - | - | - | 664492 | 99980 | 564512 | 755428 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [20.9, 22.17, 21.41] at start and [19.49, 21.69, 21.28] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-img2/W15_10k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-img2/W15_10k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@25k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 14.5 | - | - | - | - | 744112 | 179788 | 564324 | 923944 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 711368 | 147044 | 564324 | 923944 | 0.12 | 0 | 0 | - | - |
| census | 2 | - | - | - | - | 710908 | 146584 | 564324 | 923944 | 1.67 | 0 | 0 | - | - |
| publish | 24.1 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 3.62 | - | - | - | - | 755504 | 191040 | 564464 | 998220 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [19.49, 21.69, 21.28] at start and [23.3, 22.45, 21.58] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-img2/W15_25k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-img2/W15_25k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15@50k  target=image arm=- rep=1  status=complete

No bar names this cell; the figures below are reported only.

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 23.5 | - | - | - | - | 973164 | 408700 | 564464 | 1191624 | - | - | - | - | - |
| at-rest | 20 | - | - | - | - | 989268 | 424804 | 564464 | 1193944 | 20.9 | 0 | 0 | - | - |
| census | 2.5 | - | - | - | - | 939796 | 375332 | 564464 | 1193944 | 2.69 | 0 | 0 | - | - |
| publish | 58.4 | - | - | - | - | - | - | - | - | - | - | - | - | - |
| reopen-checkpoint | 9 | - | - | - | - | 905240 | 340816 | 564424 | 1305032 | - | - | - | - | - |

Conditions: box hbox (16 cores), load [23.3, 22.45, 21.58] at start and [18.47, 21.01, 21.16] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-img2/W15_50k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-img2/W15_50k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W15  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-OPEN | owner start to LISTENING from checkpoint at 50k (the fixture nearest F6's 40k, so stricter) and the exponent of open time against n (full replay and checkpoint) | open_s.checkpoint@50k <= 10 | 8.71 | NOT-MEASURED (box loaded (load 21.67 at start, 18.47 at end; a time bar needs <= 4 at both)) |
|  |  | open_s.checkpoint.exponent <= 1 | 0.76 |  |
|  |  | open_s.replay.exponent <= 1 | 0.918 |  |
| T-PUB | publication (checkpoint) wall at 40k; longest POST stall while it runs <= 2 s; octets written O(changed) | publish.stall_max_s <= 2 | - | NOT-MEASURED (box loaded (load 21.67 at start, 18.47 at end; a time bar needs <= 4 at both); longest POST stall during an online publication needs W8 (POSTs while a publication runs)) |
|  |  | publish.write_octets.exponent <= 0.5 | 0.957 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|

Conditions: box hbox (16 cores), load [21.67, 22.44, 21.48] at start and [18.47, 21.01, 21.16] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/dev/shm/fn-load-w15-img2/W15_1k-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w15-img2/W15_1k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w15-census.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w15-img2/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
