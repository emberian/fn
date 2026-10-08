# Load run w2-10k-d

## W2@10k  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-READ | ARTICLE p99 at 16 readers beside one poster (2 KiB articles, tmpfs) | article.p99_ms.R16 <= 50 | 377.5 | NOT-MEASURED (box loaded (load 27.0 > 8)) |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.29 | - | - | - | - | 724244 | 161016 | 563228 | 799836 | - | - | - | - | - |
| R1 | 20 | ARTICLE 2002 | 5.43 | 112.9 | 99.9 | 745552 | 182324 | 563228 | 799836 | 24.3 | 0 | 0 | - | - |
| R4 | 20.1 | ARTICLE 999 | 67.7 | 231.3 | 49.8 | 775292 | 212064 | 563228 | 799836 | 52.8 | 0 | 0 | - | - |
| R16 | 20.1 | ARTICLE 937 | 86.8 | 377.5 | 46.7 | 740208 | 176980 | 563228 | 804076 | 56.6 | 0 | 0 | - | - |
| R64 | 20.1 | ARTICLE 822 | 99.3 | 398.1 | 41 | 742524 | 179296 | 563228 | 821808 | 48.4 | 0 | 0 | - | - |

Refusals by name: conn-400-too-many-connections-try x34

Conditions: box hbox (16 cores), load [26.99, 25.3, 20.29] at start and [39.15, 29.34, 22.13] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset filled, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer --fn operator /dev/shm/fn-load-w2-10k-d/W2_10k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-w2-10k-d/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
