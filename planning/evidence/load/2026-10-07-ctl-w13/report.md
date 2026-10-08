# Load run ctl-w13

## W13  target=image arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 194712 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 196408 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.114 | - | - | - | - | 134420 | 16940 | 117480 | 154728 | - | - | - | 3 | 24.3 |
| fill | 5.76 | POST 1000 | 4.57 | 19 | 173.7 | 181112 | 49492 | 131620 | 192088 | 8.28 | 0 | 0 | 580 | 1509.7 |
| idle-connections | 4.23 | - | - | - | - | 194712 | 62084 | 132628 | 196408 | 1.15 | 0 | 0 | 93 | 233.5 |
| idle | 20 | - | - | - | - | 194712 | 62084 | 132628 | 196408 | 0.01 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [16.08, 15.45, 12.96] at start and [16.67, 15.63, 13.11] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-ctl-w13/W13-image-A-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-ctl-w13/W13-image-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/mem-batch/native-mb3/tree/build/fn-host-developer (core sha256 ee068942630e8faf), tree 964b105259808fc5c9b732cec5802aba4297889b, hook load-hook.lisp idle-gc-off, driver rev 964b105259808fc5c9b732cec5802aba4297889b.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 157732 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 199872 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.109 | - | - | - | - | 134560 | 16872 | 117688 | 154360 | - | - | - | 3 | 20.9 |
| fill | 5.99 | POST 1000 | 5.14 | 38.4 | 166.9 | 185176 | 53560 | 131616 | 196840 | 8.81 | 0 | 0 | 608 | 1519.4 |
| idle-connections | 4.23 | - | - | - | - | 196592 | 63768 | 132824 | 199872 | 1.38 | 0 | 0 | 130 | 276.2 |
| idle | 20 | - | - | - | - | 157732 | 24908 | 132824 | 199872 | 0.03 | 0 | 0 | 1 | 14 |

Conditions: box hbox (16 cores), load [16.67, 15.63, 13.11] at start and [17.19, 15.85, 13.27] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-ctl-w13/W13-image-B-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-ctl-w13/W13-image-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/mem-batch/native-mb3/tree/build/fn-host-developer (core sha256 ee068942630e8faf), tree 964b105259808fc5c9b732cec5802aba4297889b, hook load-hook.lisp, driver rev 964b105259808fc5c9b732cec5802aba4297889b.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=A rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 185168 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 201888 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.11 | - | - | - | - | 134632 | 16888 | 117744 | 154608 | - | - | - | 3 | 21.8 |
| fill | 5.97 | POST 1000 | 4.86 | 45 | 167.4 | 191284 | 58672 | 132612 | 201888 | 8.8 | 0 | 0 | 628 | 1591.9 |
| idle-connections | 4.24 | - | - | - | - | 185168 | 52172 | 132996 | 201888 | 1.42 | 0 | 0 | 142 | 286.6 |
| idle | 20 | - | - | - | - | 185168 | 52172 | 132996 | 201888 | 0.01 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [17.19, 15.85, 13.27] at start and [16.66, 15.86, 13.37] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-ctl-w13/W13-image-A-r2/hooked/fn-host-developer --fn operator /dev/shm/fn-load-ctl-w13/W13-image-A-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/mem-batch/native-mb3/tree/build/fn-host-developer (core sha256 ee068942630e8faf), tree 964b105259808fc5c9b732cec5802aba4297889b, hook load-hook.lisp idle-gc-off, driver rev 964b105259808fc5c9b732cec5802aba4297889b.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 157280 | FAIL |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 202544 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.108 | - | - | - | - | 134336 | 16856 | 117480 | 153960 | - | - | - | 3 | 21.3 |
| fill | 5.11 | POST 1000 | 4.03 | 14.4 | 195.6 | 180608 | 48756 | 131852 | 191532 | 7.42 | 0 | 0 | 568 | 1276.2 |
| idle-connections | 4.25 | - | - | - | - | 185184 | 52756 | 132428 | 202544 | 1.33 | 0 | 0 | 132 | 277.9 |
| idle | 20 | - | - | - | - | 157280 | 24852 | 132428 | 202544 | 0.03 | 0 | 0 | 1 | 16.3 |

Conditions: box hbox (16 cores), load [16.66, 15.86, 13.37] at start and [17.42, 16.17, 13.57] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-ctl-w13/W13-image-B-r2/hooked/fn-host-developer --fn operator /dev/shm/fn-load-ctl-w13/W13-image-B-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/mem-batch/native-mb3/tree/build/fn-host-developer (core sha256 ee068942630e8faf), tree 964b105259808fc5c9b732cec5802aba4297889b, hook load-hook.lisp, driver rev 964b105259808fc5c9b732cec5802aba4297889b.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-ctl-w13/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
