# Load run pr-tmpfs

## W1  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-POST | sustained POSTs/s, closed loop, on tmpfs, at 1 and 8 connections | post.rate_c1 >= 10 | 148.1 | NOT-MEASURED (box loaded (load 20.2 > 8)) |
|  |  | post.rate_c8 >= 10 | 133.9 |  |
| T-POST | durable POST (last line to 240), 2 KiB, 1 connection: p50 / p99 and owner CPU per POST, on ZFS | post.cpu_ms_per_op.c1 <= 16 | - | NOT-MEASURED (metric absent from the run) |
| T-RATE | sustained POSTs/s, closed loop, 1 and 8 connections, 3 readers: >= 10 /s on ZFS, >= 50 /s on tmpfs | post.rate_c1r3 >= 50 | - | NOT-MEASURED (metric absent from the run) |
|  |  | post.rate_c8r3 >= 50 | - |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.123 | - | - | - | - | 251340 | 30860 | 220480 | 268288 | - | - | - | - | - |
| c1 | 20 | POST 2962 | 5.67 | 59.8 | 148.1 | 310888 | 90408 | 220480 | 394716 | 31.3 | 0 | 0 | - | - |
| c8 | 20.1 | POST 2686 | 45.5 | 466.4 | 133.9 | 357284 | 136804 | 220480 | 416080 | 31.5 | 0 | 0 | - | - |

Refusals by name: 440-posting-not-permitted-now x6

Conditions: box hbox (16 cores), load [20.21, 22.17, 21.52] at start and [23.06, 22.64, 21.71] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset filled, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host --fn operator /dev/shm/fn-load-pr-tmpfs/W1-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).
