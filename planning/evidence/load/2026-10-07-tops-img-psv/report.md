# Load run tops-img-psv

## T-OPS  target=image arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-ALLOC | bytes consed per command (process-wide, hooked window over 100 commands): POST 2 KiB, GROUP, ARTICLE 2/8/32/128 KiB; ARTICLE consing exponent in article size <= 0.1 | alloc.article.exponent <= 0.1 | 0.89 | FAIL |
|  |  | alloc.POST_2k reported - | 4843373 |  |
|  |  | alloc.GROUP reported - | 35886465 |  |
|  |  | alloc.ARTICLE_2k reported - | 1335886 |  |
|  |  | alloc.ARTICLE_32k reported - | 13686014 |  |
| T-CALLS | host-to-ACL2 calls per command (outermost fnn-call per thread, E's hook) | calls.POST_2k reported - | 444.2 | REPORTED |
|  |  | calls.GROUP reported - | 105.0 |  |
|  |  | calls.ARTICLE_2k reported - | 122.5 |  |
|  |  | calls.ARTICLE_32k reported - | 282.8 |  |
| T-SYNC | the owner's own fdatasync/fsync (fnn-durable-barrier, fnn-log-fdatasync) per POST and their wall time per POST (hooked), beside the site's 4 KiB write+fdatasync p50/p99 | sync.own_calls_per_post reported - | 1.03 | REPORTED |
|  |  | sync.own_ms_per_post reported - | 0 |  |
|  |  | site.fdatasync_p50_ms reported - | 0.002 |  |
|  |  | site.fdatasync_p99_ms reported - | 0.009 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.542 | - | - | - | - | 712496 | 114220 | 598276 | 712496 | - | - | - | - | - |
| prof | 45.9 | - | - | - | - | 732904 | 134560 | 598344 | 779040 | 10.2 | 0 | 0 | - | - |

Conditions: box persvati (12 cores), load [13.93, 13.21, 12.46] at start and [14.29, 13.4, 12.57] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset big-articles, launch `/dev/shm/fn-load-tops-img-psv/T_OPS-image-x-r1/hooked/fn-host-developer --fn operator /dev/shm/fn-load-tops-img-psv/T_OPS-image-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/converge-3/native-c3-0b4d3b183/tree/build/fn-host-developer (core sha256 5e342d1984b955a8), tree 0b4d3b18385a53209146a78296e282d06c17e573, hook prof2.lisp, driver rev 0b4d3b18385a53209146a78296e282d06c17e573.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-tops-img-psv/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
