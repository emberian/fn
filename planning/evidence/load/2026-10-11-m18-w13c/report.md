# Load run m18-w13c

## W13  target=image arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-HWM | owner VmHWM, whole process (file-backed core pages included), over the whole workload (ruling 16: a Pi kills on the peak); at-rest VmRSS 20 s idle after it is printed beside (L-REST), not judged | rss_kib.hwm <= 131072 | 164840 | FAIL |
| L-RSS | at-rest owner VmRSS, 20 s idle after the workload (reported beside L-HWM, not judged; ruling 16) | rss_kib.vmrss reported - | 159376 | REPORTED |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.081 | - | - | - | - | 112052 | 24244 | 87808 | 119384 | - | - | - | 1 | 2 |
| fill | 5.5 | POST 1000 | 4.59 | 28.5 | 181.8 | 151160 | 61452 | 89708 | 161316 | 7.92 | 0 | 0 | 650 | 1418.6 |
| idle-connections | 4.03 | - | - | - | - | 159376 | 69668 | 89708 | 164840 | 2.13 | 0 | 0 | 247 | 438.8 |
| idle | 20 | - | - | - | - | 159376 | 69668 | 89708 | 164840 | 0.02 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [18.17, 13.71, 12.22] at start and [17.51, 14.06, 12.4] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-m18-w13c/W13-image-A-r1/hooked/fn-host --fn operator /dev/shm/fn-load-m18-w13c/W13-image-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/integrate-20261011a/native-3119f7d3253e/tree/build/fn-host (core sha256 fe94c948812a35c8), tree 3119f7d3253eeeafcd694a8e28e3d9a5df686e9a, hook w13-idle-gc.lisp idle-gc-off, driver rev 3119f7d32.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-HWM | owner VmHWM, whole process (file-backed core pages included), over the whole workload (ruling 16: a Pi kills on the peak); at-rest VmRSS 20 s idle after it is printed beside (L-REST), not judged | rss_kib.hwm <= 131072 | 158620 | FAIL |
| L-RSS | at-rest owner VmRSS, 20 s idle after the workload (reported beside L-HWM, not judged; ruling 16) | rss_kib.vmrss reported - | 119592 | REPORTED |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.079 | - | - | - | - | 113388 | 24844 | 88544 | 120492 | - | - | - | 1 | 3.7 |
| fill | 5.86 | POST 1000 | 4.88 | 15.3 | 170.6 | 134948 | 45120 | 89828 | 158620 | 8.11 | 0 | 0 | 591 | 1437.4 |
| idle-connections | 4.03 | - | - | - | - | 142600 | 52772 | 89828 | 158620 | 1.68 | 0 | 0 | 168 | 338.7 |
| idle | 20 | - | - | - | - | 119592 | 29764 | 89828 | 158620 | 0.04 | 0 | 0 | 1 | 16.7 |

Conditions: box hbox (16 cores), load [17.51, 14.06, 12.4] at start and [16.57, 14.17, 12.49] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-m18-w13c/W13-image-B-r1/hooked/fn-host --fn operator /dev/shm/fn-load-m18-w13c/W13-image-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/integrate-20261011a/native-3119f7d3253e/tree/build/fn-host (core sha256 fe94c948812a35c8), tree 3119f7d3253eeeafcd694a8e28e3d9a5df686e9a, hook w13-idle-gc.lisp, driver rev 3119f7d32.
Every row is loopback on one box (client and node on the same host).


Raw output: hbox:/tank/fn/scratch/load-harness/runs/m18-w13c/ (result.json, cells.jsonl, run.log, census/prof files). Not committed.
