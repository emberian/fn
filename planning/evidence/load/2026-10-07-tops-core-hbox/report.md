# Load run tops-core-hbox

## T-OPS  target=fn-core arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-ALLOC | bytes consed per command (process-wide, hooked window over 100 commands): POST 2 KiB, GROUP, ARTICLE 2/8/32/128 KiB; ARTICLE consing exponent in article size <= 0.1 | alloc.article.exponent <= 0.1 | 0.889 | FAIL |
|  |  | alloc.POST_2k reported - | 2799698 |  |
|  |  | alloc.GROUP reported - | 35887514 |  |
|  |  | alloc.ARTICLE_2k reported - | 1336934 |  |
|  |  | alloc.ARTICLE_32k reported - | 13684965 |  |
| T-CALLS | host-to-ACL2 calls per command (outermost fnn-call per thread, E's hook) | calls.POST_2k reported - | 406.0 | REPORTED |
|  |  | calls.GROUP reported - | 103.8 |  |
|  |  | calls.ARTICLE_2k reported - | 121.6 |  |
|  |  | calls.ARTICLE_32k reported - | 278.0 |  |
| T-SYNC | the owner's own fdatasync/fsync (fnn-durable-barrier, fnn-log-fdatasync) per POST and their wall time per POST (hooked), beside the site's 4 KiB write+fdatasync p50/p99 | sync.own_calls_per_post reported - | 1 | REPORTED |
|  |  | sync.own_ms_per_post reported - | 0 |  |
|  |  | site.fdatasync_p50_ms reported - | 0.001 |  |
|  |  | site.fdatasync_p99_ms reported - | 0.003 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.384 | - | - | - | - | 227604 | 106264 | 121340 | 227604 | - | - | - | - | - |
| prof | 32.4 | - | - | - | - | 264512 | 142980 | 121532 | 290096 | 6.31 | 0 | 0 | - | - |

Conditions: box hbox (16 cores), load [17.05, 14.55, 16.3] at start and [16.15, 14.64, 16.25] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset big-articles, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-tops-core-hbox/T_OPS-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook prof2.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-tops-core-hbox/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
