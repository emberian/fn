# Load run fresh2

## L-FRESH  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-FRESH | a fresh node starts under a whole-process limit of 256 MB and of 1024 MB and serves one POST and one ARTICLE | fresh.256.ok == 1 | 0 | FAIL |
|  |  | fresh.1024.ok == 1 | 0 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| limits | 0.688 | - | - | - | - | - | - | - | - | - | - | - | - | - |

Refusals by name: fresh-1024-fn-refused-machinecannotholdthreads-reservation1030-mb x1, fresh-256-fn-refused-machinecannotholdprofile-heap497-mb x1

Conditions: box hbox (16 cores), load [21.27, 19.59, 20.12] at start and [21.27, 19.59, 20.12] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host --fn operator /dev/shm/fn-load-fresh2/L_FRESH-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-fresh2/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
