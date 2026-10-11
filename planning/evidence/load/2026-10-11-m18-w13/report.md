# Load run m18-w13

## W13  target=image arm=A rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-HWM | owner VmHWM, whole process (file-backed core pages included), over the whole workload (ruling 16: a Pi kills on the peak); at-rest VmRSS 20 s idle after it is printed beside (L-REST), not judged | rss_kib.hwm <= 131072 | 133400 | FAIL |
| L-RSS | at-rest owner VmRSS, 20 s idle after the workload (reported beside L-HWM, not judged; ruling 16) | rss_kib.vmrss reported - | 114500 | REPORTED |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.067 | - | - | - | - | 84200 | 24284 | 59916 | 90816 | - | - | - | 1 | 1.4 |
| fill | 2.96 | POST 1000 | 2.28 | 7 | 338.5 | 116504 | 51760 | 64744 | 129656 | 4.03 | 0 | 0 | 502 | 665.3 |
| idle-connections | 4.02 | - | - | - | - | 114500 | 49756 | 64744 | 133400 | 0.82 | 0 | 0 | 131 | 141.2 |
| idle | 20 | - | - | - | - | 114500 | 49756 | 64744 | 133400 | 0.02 | 0 | 0 | 0 | 0 |

Conditions: box hbox (16 cores), load [13.37, 10.32, 11.04] at start and [15.45, 11.09, 11.28] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/dev/shm/fn-load-m18-w13/W13-image-A-r1/hooked/fn-host --fn operator /dev/shm/fn-load-m18-w13/W13-image-A-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/memory/native-m18-n2/tree/build/fn-host (core sha256 23ee1349c5539df4), tree e63c2b12aa1a47decc57dcf8d9af0f1a8330aa72, hook w13-idle-gc.lisp idle-gc-off, driver rev a269ac0c1.
Every row is loopback on one box (client and node on the same host).


Raw output: hbox:/tank/fn/scratch/load-harness/runs/m18-w13/ (result.json, cells.jsonl, run.log, census/prof files). Not committed.
