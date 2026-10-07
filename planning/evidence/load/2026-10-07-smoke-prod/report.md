# Load run smoke-prod

## smoke  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-SMOKE | the smoke workload completes: 50 POSTs admitted, 50 ARTICLEs read by 1 reader, no refusals | smoke.articles >= 50 | 50 | PASS |
|  |  | posts.admitted >= 50 | 50 |  |
|  |  | posts.refused == 0 | 0 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.125 | - | - | - | - | 116164 | 15208 | 100956 | 132388 | - | - | - | - | - |
| post | 0.314 | POST 50 | 4.38 | - | 159.2 | 133932 | 30184 | 103748 | 133932 | 0.29 | 0 | 0 | - | - |
| read | 0.273 | ARTICLE 50 | 4.59 | - | 183.4 | 134384 | 28860 | 105524 | 136860 | 0.2 | 0 | 0 | - | - |

Conditions: box hbox (16 cores), load [25.34, 21.46, 16.89] at start and [25.39, 21.53, 16.94] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset small, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host --fn operator /dev/shm/fn-load-smoke-prod/smoke-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).
