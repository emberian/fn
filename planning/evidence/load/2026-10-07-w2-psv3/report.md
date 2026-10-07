# Load run w2-psv3

## W2@10k  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| L-READ | ARTICLE p99 at 16 readers beside one poster (2 KiB articles, tmpfs) | article.p99_ms.R16 <= 50 | 676.1 | NOT-MEASURED (box loaded (load 16.1 > 8)) |
| T-READ | ARTICLE 2 KiB p50 / p99 at 16 readers beside one poster; p99(16) / p99(1) | article.p50_ms.R16 <= 5 | 139.9 | NOT-MEASURED (box loaded (load 16.11 at start, 16.87 at end; a time bar needs <= 4 at both)) |
|  |  | article.p99_ms.R16 <= 50 | 676.1 |  |
|  |  | article.p99_ratio_16_1 <= 2 | 6.49 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 4.25 | - | - | - | - | 760020 | 162368 | 597652 | 850308 | - | - | - | - | - |
| R1 | 20.2 | ARTICLE 2110 | 3.01 | 104.1 | 104.6 | 800496 | 202832 | 597664 | 850308 | 32.3 | 0 | 0 | - | - |
| R4 | 20.1 | ARTICLE 887 | 85.8 | 119.1 | 44 | 814816 | 217408 | 597408 | 850308 | 55.8 | 0 | 0 | - | - |
| R16 | 20.1 | ARTICLE 559 | 139.9 | 676.1 | 27.9 | 747820 | 150412 | 597408 | 850308 | 46.9 | 0 | 0 | - | - |
| R64 | 20.2 | ARTICLE 241 | 286.2 | 945.2 | 11.9 | 771296 | 173888 | 597408 | 850308 | 31.5 | 0 | 0 | - | - |

Conditions: box persvati (16 cores), load [16.11, 15.39, 12.56] at start and [16.87, 15.77, 12.95] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset filled, launch `/tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer --fn operator /dev/shm/fn-load-w2-psv3/W2_10k-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook none, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).
