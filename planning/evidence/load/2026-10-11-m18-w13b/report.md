# Load run m18-w13b

## W13  target=image arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-HWM | owner VmHWM, whole process (file-backed core pages included), over the whole workload (ruling 16: a Pi kills on the peak); at-rest VmRSS 20 s idle after it is printed beside (L-REST), not judged | rss_kib.hwm <= 131072 | 136976 | FAIL |
| L-RSS | at-rest owner VmRSS, 20 s idle after the workload (reported beside L-HWM, not judged; ruling 16) | rss_kib.vmrss reported - | 131584 | REPORTED |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.061 | - | - | - | - | 88760 | 24284 | 64476 | 96524 | - | - | - | 1 | 1.5 |
| fill | 5.03 | POST 1000 | 3.96 | 15.3 | 198.7 | 114812 | 49508 | 65304 | 132672 | 7.06 | 0 | 0 | 618 | 1267.4 |
| idle-connections | 4.02 | - | - | - | - | 131584 | 66280 | 65304 | 136976 | 1.55 | 0 | 0 | 182 | 317.1 |
| idle | 20 | - | - | - | - | 131584 | 66280 | 65304 | 136976 | 0.02 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [17.53, 12.0, 11.57] at start and [18.2, 12.78, 11.85] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-m18-w13b/W13-image-A-r1/hooked/fn-host --fn operator /dev/shm/fn-load-m18-w13b/W13-image-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/memory/native-m18-n2/tree/build/fn-host (core sha256 23ee1349c5539df4), tree e63c2b12aa1a47decc57dcf8d9af0f1a8330aa72, hook w13-idle-gc.lisp idle-gc-off, driver rev a269ac0c1.
Every row is loopback on one box (client and node on the same host).

## W13  target=image arm=B rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-HWM | owner VmHWM, whole process (file-backed core pages included), over the whole workload (ruling 16: a Pi kills on the peak); at-rest VmRSS 20 s idle after it is printed beside (L-REST), not judged | rss_kib.hwm <= 131072 | 137656 | FAIL |
| L-RSS | at-rest owner VmRSS, 20 s idle after the workload (reported beside L-HWM, not judged; ruling 16) | rss_kib.vmrss reported - | 95304 | REPORTED |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.074 | - | - | - | - | 89640 | 24892 | 64748 | 96780 | - | - | - | 1 | 2.1 |
| fill | 5.78 | POST 1000 | 4.71 | 40.5 | 172.9 | 124424 | 58808 | 65616 | 134012 | 7.95 | 0 | 0 | 583 | 1403.7 |
| idle-connections | 4.03 | - | - | - | - | 117460 | 51844 | 65616 | 137656 | 1.71 | 0 | 0 | 175 | 351.3 |
| idle | 20 | - | - | - | - | 95304 | 29688 | 65616 | 137656 | 0.02 | 0 | 0 | 1 | 18.6 |

Conditions: box hbox (16 cores), load [18.2, 12.78, 11.85] at start and [18.47, 13.37, 12.08] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-m18-w13b/W13-image-B-r1/hooked/fn-host --fn operator /dev/shm/fn-load-m18-w13b/W13-image-B-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/memory/native-m18-n2/tree/build/fn-host (core sha256 23ee1349c5539df4), tree e63c2b12aa1a47decc57dcf8d9af0f1a8330aa72, hook w13-idle-gc.lisp, driver rev a269ac0c1.
Every row is loopback on one box (client and node on the same host).


Raw output: hbox:/tank/fn/scratch/load-harness/runs/m18-w13b/ (result.json, cells.jsonl, run.log, census/prof files). Not committed.
