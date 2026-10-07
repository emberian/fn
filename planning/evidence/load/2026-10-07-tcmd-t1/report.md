# Load run tcmd-t1

## T-CMD@1k  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-CMD | per-command p99 for GROUP, OVER-40, STAT, HEAD, LIST, greeting at 1k/10k/40k, and its exponent against n | cmd.p99_ms.max <= 50 | 1432.9 | NOT-MEASURED (box loaded (load 18.25 at start, 19.56 at end; a time bar needs <= 4 at both); metric absent from the run) |
|  |  | cmd.p99_exponent.max <= 0.2 | - |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.497 | - | - | - | - | 619228 | 55756 | 563472 | 689100 | - | - | - | - | - |
| commands | 387.1 | GROUP 300 | 24.3 | 30.3 | - | 710728 | 147256 | 563472 | 847312 | 61.1 | 0 | 0 | - | - |

Conditions: box hbox (16 cores), load [18.25, 21.45, 21.62] at start and [19.56, 18.94, 20.27] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset scale-1m, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer --fn operator /dev/shm/fn-load-tcmd-t1/T_CMD_1k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).
