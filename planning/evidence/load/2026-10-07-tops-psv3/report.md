# Load run tops-psv3

## T-OPS  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-ALLOC | bytes consed per command (process-wide, hooked window over 100 commands): POST 2 KiB, GROUP, ARTICLE 2/8/32/128 KiB; ARTICLE consing exponent in article size <= 0.1 | alloc.article.exponent <= 0.1 | 0.893 | FAIL |
|  |  | alloc.POST_2k reported - | 3020947 |  |
|  |  | alloc.GROUP reported - | 35881222 |  |
|  |  | alloc.ARTICLE_2k reported - | 1319109 |  |
|  |  | alloc.ARTICLE_32k reported - | 13684965 |  |
| T-CALLS | host-to-ACL2 calls per command (outermost fnn-call per thread, E's hook) | calls.POST_2k reported - | 0 | REPORTED |
|  |  | calls.GROUP reported - | 0 |  |
|  |  | calls.ARTICLE_2k reported - | 0 |  |
|  |  | calls.ARTICLE_32k reported - | 0 |  |
| T-SYNC | the owner's own fdatasync/fsync (fnn-durable-barrier, fnn-log-fdatasync) per POST and their wall time per POST (hooked), beside the site's 4 KiB write+fdatasync p50/p99 | sync.own_calls_per_post reported - | 0 | REPORTED |
|  |  | sync.own_ms_per_post reported - | 0 |  |
|  |  | site.fdatasync_p50_ms reported - | 0.001 |  |
|  |  | site.fdatasync_p99_ms reported - | 0.004 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.384 | - | - | - | - | 712456 | 114172 | 598284 | 712456 | - | - | - | - | - |
| prof | 34 | - | - | - | - | 719436 | 121120 | 598316 | 779156 | 6.08 | 0 | 0 | - | - |

Conditions: box persvati (16 cores), load [6.72, 11.72, 11.97] at start and [7.7, 11.22, 11.78] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset big-articles, launch `/dev/shm/fn-load-tops-psv3/T_OPS-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-tops-psv3/T_OPS-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook prof2.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-tops-psv3/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
