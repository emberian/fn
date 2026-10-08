# Load run pr-zfs

## W1  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-POST | sustained POSTs/s, closed loop, on tmpfs, at 1 and 8 connections | post.rate_c1 >= 10 | 5.85 | NOT-MEASURED (box loaded (load 23.1 > 8)) |
|  |  | post.rate_c8 >= 10 | 26.3 |  |
| T-POST | durable POST (last line to 240), 2 KiB, 1 connection: p50 / p99 and owner CPU per POST, on ZFS | post.p50_ms.c1 <= 20 | 141.9 | NOT-MEASURED (box loaded (load 23.13 at start, 24.52 at end; a time bar needs <= 4 at both); metric absent from the run) |
|  |  | post.p99_ms.c1 <= 250 | - |  |
|  |  | post.cpu_ms_per_op.c1 <= 16 | - |  |
| T-RATE | sustained POSTs/s, closed loop, 1 and 8 connections, 3 readers: >= 10 /s on ZFS, >= 50 /s on tmpfs | post.rate_c1r3 >= 10 | - | NOT-MEASURED (metric absent from the run) |
|  |  | post.rate_c8r3 >= 10 | - |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.546 | - | - | - | - | 251316 | 30820 | 220496 | 268304 | - | - | - | - | - |
| c1 | 20.5 | POST 120 | 141.9 | - | 5.85 | 308532 | 88036 | 220496 | 308532 | 9.09 | 1318294 | 1021235 | - | - |
| c8 | 20.1 | POST 528 | 252.0 | 1051.0 | 26.3 | 313092 | 92596 | 220496 | 346844 | 6.89 | 30613624 | 12362639 | - | - |

Conditions: box hbox (16 cores), load [23.13, 22.66, 21.72] at start and [24.52, 23.1, 21.92] at end, ZFS ARC None -> None bytes, filesystem zfs, preset filled, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host --fn operator /tank/fn/scratch/load-harness/work-zfs/pr-zfs/W1-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-pr-zfs/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
