# Load run tops-core-psv

## T-OPS  target=fn-core arm=- rep=1  status=complete

| bar | quantity | check | value | verdict |
|---|---|---|---|---|
| T-ALLOC | bytes consed per command (process-wide, hooked window over 100 commands): POST 2 KiB, GROUP, ARTICLE 2/8/32/128 KiB; ARTICLE consing exponent in article size <= 0.1 | alloc.article.exponent <= 0.1 | 0.889 | FAIL |
|  |  | alloc.POST_2k reported - | 2811232 |  |
|  |  | alloc.GROUP reported - | 35886465 |  |
|  |  | alloc.ARTICLE_2k reported - | 1336934 |  |
|  |  | alloc.ARTICLE_32k reported - | 13686014 |  |
| T-CALLS | host-to-ACL2 calls per command (outermost fnn-call per thread, E's hook) | calls.POST_2k reported - | - | NOT-MEASURED (E's hook counted 0 fnn-call and 0 barrier calls for every operation: its encapsulations did not fire in this target (calls compiled direct), so calls and the owner's own sync are NOT-MEASURED here (bytes consed stand)) |
|  |  | calls.GROUP reported - | - |  |
|  |  | calls.ARTICLE_2k reported - | - |  |
|  |  | calls.ARTICLE_32k reported - | - |  |
| T-SYNC | the owner's own fdatasync/fsync (fnn-durable-barrier, fnn-log-fdatasync) per POST and their wall time per POST (hooked), beside the site's 4 KiB write+fdatasync p50/p99 | sync.own_calls_per_post reported - | - | NOT-MEASURED (E's hook counted 0 fnn-call and 0 barrier calls for every operation: its encapsulations did not fire in this target (calls compiled direct), so calls and the owner's own sync are NOT-MEASURED here (bytes consed stand)) |
|  |  | sync.own_ms_per_post reported - | - |  |
|  |  | site.fdatasync_p50_ms reported - | 0.002 |  |
|  |  | site.fdatasync_p99_ms reported - | 0.012 |  |

| phase | s | ops | p50 ms | p99 ms | ops/s | VmRSS KiB | anon | file | HWM | CPU s | read B | write B | GC n | GC ms |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| open | 0.86 | - | - | - | - | 239744 | 114828 | 124916 | 239744 | - | - | - | - | - |
| prof | 54.4 | - | - | - | - | 270408 | 145600 | 124808 | 289716 | 14.8 | 0 | 0 | - | - |

Conditions: box persvati (16 cores), load [13.71, 11.9, 11.92] at start and [15.64, 12.85, 12.25] at end, ZFS ARC None -> None bytes, filesystem tmpfs, preset big-articles, launch `/tank/fn/scratch/extract-core/tree4/build/core/fn-core --fn operator /dev/shm/fn-load-tops-core-psv/T_OPS-fn-core-x-r1/fn.toml run (SBCL_USER_ARGS='--dynamic-space-size 1068MB --tls-limit 16384')`, image /tank/fn/scratch/extract-core/tree4/build/core/fn-core (core sha256 2d0a0e443ea524c4), tree None, hook prof2.lisp, driver rev None.
Every row is loopback on one box (client and node on the same host).

Raw output: hbox:/tank/fn/scratch/load/2026-10-07-tops-core-psv/ (result.json, cells.jsonl, run.log, census and prof files; not committed).
