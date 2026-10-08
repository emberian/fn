# Load run w13-prod

## W13  target=image arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 128880 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 166700 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.082 | - | - | - | - | 116736 | 14148 | 102588 | 134596 | - | - | - | 3 | 11.1 |
| fill | 3.88 | POST 1000 | 2.86 | 7.73 | 257.6 | 142640 | 35976 | 106664 | 160412 | 4.96 | 0 | 0 | 486 | 709.5 |
| idle-connections | 4.17 | - | - | - | - | 153464 | 46116 | 107348 | 166700 | 1.19 | 0 | 0 | 140 | 213.3 |
| idle | 20 | - | - | - | - | 128880 | 21532 | 107348 | 166700 | 0.02 | 0 | 0 | 1 | 13.3 |

Conditions: box hbox (16 cores), load [30.38, 29.03, 22.57] at start and [25.64, 28.02, 22.47] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-prod/W13-image-B-r1/hooked/fn-host --fn operator /dev/shm/fn-load-w13-prod/W13-image-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=2  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-RSS | owner VmRSS, whole process (file-backed core pages included), 20 s idle after the workload | rss_kib.vmrss <= 131072 | 128832 | PASS |
| L-HWM | owner VmHWM over the same workload (red item if above twice the L-RSS bar) | rss_kib.hwm <= 262144 | 164628 | PASS |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.068 | - | - | - | - | 116360 | 13944 | 102416 | 134040 | - | - | - | 3 | 9.2 |
| fill | 2.86 | POST 1000 | 2.11 | 6.64 | 350.2 | 154120 | 47480 | 106640 | 164492 | 3.96 | 0 | 0 | 446 | 554.3 |
| idle-connections | 4.14 | - | - | - | - | 136488 | 28940 | 107548 | 164628 | 0.85 | 0 | 0 | 109 | 125.9 |
| idle | 20 | - | - | - | - | 128832 | 21284 | 107548 | 164628 | 0.02 | 0 | 0 | 1 | 9.9 |

Conditions: box hbox (16 cores), load [25.64, 28.02, 22.47] at start and [22.27, 26.95, 22.29] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-w13-prod/W13-image-B-r2/hooked/fn-host --fn operator /dev/shm/fn-load-w13-prod/W13-image-B-r2/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook w13-idle-gc.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w13-prod/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
