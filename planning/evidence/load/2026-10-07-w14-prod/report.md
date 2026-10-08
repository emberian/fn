# Load run w14-prod

## W14  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-LIN | ARTICLE wall time ratio t(8N)/t(N), sizes 64 KiB and 512 KiB (exponent reported); target 10.0 | article.ratio_8n_over_n <= 15 | 10.6 | NOT-MEASURED (box loaded (load 12.1 > 8)) |
| T-LIN | ARTICLE time vs article size: t(8N)/t(N) and the fitted exponent | article.ratio_8n_over_n <= 15 | 10.6 | NOT-MEASURED (box loaded (load 12.13 at start, 12.13 at end; a time bar needs <= 4 at both)) |
|  |  | article.exponent <= 1.1 | 1.12 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.101 | - | - | - | - | 259244 | 38868 | 220376 | 276248 | - | - | - | - | - |
| sizes | 18.9 | ARTICLE 9 | 45.3 | - | - | 447532 | 227156 | 220376 | 694316 | 19.9 | 0 | 0 | - | - |

Conditions: box hbox (16 cores), load [12.13, 13.54, 17.2] at start and [12.13, 13.42, 17.06] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset big-articles, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host --fn operator /dev/shm/fn-load-w14-prod/W14-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host (core sha256 fc94e5059e8211e5), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w14-prod/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
