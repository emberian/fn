# Load run w13-core-ab

## W13  target=image arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 187888 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 202296 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.15 | - | - | - | - | 133452 | 14232 | 119220 | 151476 | - | - | - | 3 | 24.3 |
| fill | 10.3 | POST 1000 | 8.07 | 50.8 | 96.9 | 187260 | 54472 | 132788 | 196160 | 13.2 | 0 | 0 | 709 | 2377.0 |
| idle-connections | 4.53 | - | - | - | - | 187888 | 54248 | 133640 | 202296 | 2.39 | 0 | 0 | 146 | 456.4 |
| idle | 20 | - | - | - | - | 187888 | 54248 | 133640 | 202296 | 0.03 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [24.93, 21.79, 17.17] at start and [25.51, 22.31, 17.54] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-core-ab/W13-image-A-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w13-core-ab/W13-image-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp idle-gc-off, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 155316 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 200412 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.147 | - | - | - | - | 133624 | 14388 | 119236 | 151300 | - | - | - | 3 | 23.8 |
| fill | 8.92 | POST 1000 | 7.67 | 35.6 | 112.1 | 181516 | 48252 | 133264 | 200412 | 11.8 | 0 | 0 | 608 | 2054.3 |
| idle-connections | 4.36 | - | - | - | - | 188256 | 54744 | 133512 | 200412 | 2.16 | 0 | 0 | 135 | 427.5 |
| idle | 20 | - | - | - | - | 155316 | 21804 | 133512 | 200412 | 0.04 | 0 | 0 | 1 | 25.3 |

Conditions: box hbox (16 cores), load [25.51, 22.31, 17.54] at start and [26.88, 23.05, 17.97] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-core-ab/W13-image-B-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w13-core-ab/W13-image-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=fn-core arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 107392 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 128364 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.171 | - | - | - | - | 65784 | 12976 | 52808 | 84680 | - | - | - | 3 | 19.7 |
| fill | 11.2 | POST 1000 | 8.49 | 99.9 | 89.4 | 115288 | 57832 | 57456 | 122368 | 15.1 | 0 | 0 | 764 | 2158.9 |
| idle-connections | 4.48 | - | - | - | - | 107392 | 49552 | 57840 | 128364 | 2.8 | 0 | 0 | 161 | 422.8 |
| idle | 20 | - | - | - | - | 107392 | 49552 | 57840 | 128364 | 0.01 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [26.97, 23.13, 18.03] at start and [25.46, 23.24, 18.28] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w13-core-ab/W13-fn-core-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w13-idle-gc.lisp idle-gc-off, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=fn-core arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 79164 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 122660 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.169 | - | - | - | - | 66080 | 13156 | 52924 | 84988 | - | - | - | 3 | 19 |
| fill | 9.96 | POST 1000 | 7.92 | 63.4 | 100.4 | 108332 | 50416 | 57916 | 118508 | 13.6 | 0 | 0 | 664 | 1910.8 |
| idle-connections | 4.32 | - | - | - | - | 104828 | 46336 | 58492 | 122660 | 2.34 | 0 | 0 | 142 | 401.6 |
| idle | 20 | - | - | - | - | 79164 | 20672 | 58492 | 122660 | 0.05 | 0 | 0 | 1 | 26.2 |

Conditions: box hbox (16 cores), load [25.46, 23.24, 18.28] at start and [25.47, 23.47, 18.54] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w13-core-ab/W13-fn-core-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=A rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 181788 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 194972 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.125 | - | - | - | - | 133976 | 14556 | 119420 | 151868 | - | - | - | 3 | 21.4 |
| fill | 14.3 | POST 1000 | 11.9 | 83.3 | 69.7 | 181556 | 48344 | 133212 | 191988 | 15.8 | 0 | 0 | 742 | 2729.7 |
| idle-connections | 4.5 | - | - | - | - | 181788 | 48324 | 133464 | 194972 | 2.83 | 0 | 0 | 166 | 560.6 |
| idle | 20 | - | - | - | - | 181788 | 48324 | 133464 | 194972 | 0.01 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [25.47, 23.47, 18.54] at start and [26.05, 23.93, 18.93] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-core-ab/W13-image-A-r2/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w13-core-ab/W13-image-A-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp idle-gc-off, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 155892 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 203124 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.152 | - | - | - | - | 133428 | 14232 | 119196 | 151068 | - | - | - | 3 | 23.6 |
| fill | 13.5 | POST 1000 | 10.4 | 69.8 | 74.1 | 184224 | 52056 | 132168 | 195624 | 15.8 | 0 | 0 | 798 | 2796.5 |
| idle-connections | 4.59 | - | - | - | - | 193664 | 60256 | 133408 | 203124 | 2.6 | 0 | 0 | 156 | 515.5 |
| idle | 20 | - | - | - | - | 155892 | 22484 | 133408 | 203124 | 0.04 | 0 | 0 | 1 | 27.1 |

Conditions: box hbox (16 cores), load [26.05, 23.93, 18.93] at start and [25.78, 24.15, 19.22] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-core-ab/W13-image-B-r2/hooked/fn-host-developer --fn operator /dev/shm/fn-load-w13-core-ab/W13-image-B-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=fn-core arm=A rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 104096 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 126264 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.171 | - | - | - | - | 66276 | 13256 | 53020 | 85084 | - | - | - | 3 | 20.1 |
| fill | 13.6 | POST 1000 | 10.9 | 102.5 | 73.8 | 89396 | 31908 | 57488 | 126264 | 16.5 | 0 | 0 | 796 | 2399.7 |
| idle-connections | 4.76 | - | - | - | - | 103520 | 44964 | 58556 | 126264 | 2.84 | 0 | 0 | 156 | 470.3 |
| idle | 20 | - | - | - | - | 104096 | 45540 | 58556 | 126264 | 0.02 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [25.78, 24.15, 19.22] at start and [25.67, 24.32, 19.49] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w13-core-ab/W13-fn-core-A-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w13-idle-gc.lisp idle-gc-off, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=fn-core arm=B rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 79012 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 126424 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.176 | - | - | - | - | 66148 | 13220 | 52928 | 84992 | - | - | - | 3 | 20.2 |
| fill | 17 | POST 1000 | 13.4 | 116.3 | 58.8 | 107832 | 50520 | 57312 | 123848 | 19.4 | 0 | 0 | 911 | 2893.4 |
| idle-connections | 4.4 | - | - | - | - | 124440 | 66072 | 58368 | 126424 | 1.95 | 0 | 0 | 119 | 341.4 |
| idle | 20 | - | - | - | - | 79012 | 20644 | 58368 | 126424 | 0.03 | 0 | 0 | 1 | 27.3 |

Conditions: box hbox (16 cores), load [25.67, 24.32, 19.49] at start and [27.79, 25.08, 19.98] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-w13-core-ab/W13-fn-core-B-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w13-core-ab/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
