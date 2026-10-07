# The disk's reason before the memory's; a complete POST holds its size (lane credits-stall, B8, 2026-09-28)

Lane credits-stall (Claude Opus 5.5), branch `lane/credits-stall` from origin/dev f286c0204.
Row B8; PRF-377, PRF-380; PKT-887; SCN-194. The finding came from four
places, all reported 2026-09-28: generators, durability-bugs-fair
(PKT-887), credits (SCN-194), and batch BB. On dev 6fb2b3d6a,
tests.test_native_slow_disk failed 3 of 10.

## What the failures were

1. `test_reads_and_control_stay_flat...` and
   `test_a_stop_with_clients_mid_article...` got the memory 440 at a POST
   command while the disk was still healthy.
   - The class's store is the default preset with A = 1 MiB. One article
     credit is 2 x 16 x (512 + A + HDR) = 34,095,104 octets, so the 64 MiB
     pool holds ONE article in flight.
   - The tests hold 2 and 17 articles in flight at once.
   - The disk was not the cause: the tests assumed an in-flight capacity the
     worst-case credit does not give at A = 1 MiB.
2. PKT-887 (4 short POSTs behind a 1.5 s barrier: 83 memory 440s). A
   complete, queued submission was charged a whole worst-case reserve, and
   so was the batch holding it. Separately, the slot count added
   `(len inflight)`, which is the submission record's 4 or 6 fields, not 1.
3. The source test grepped owner-host for `(fn-otm-read-span`. The host has
   called the slots' and then the credits' read since zero-copy-commit.

## What changed

- **The disk's classification before the memory's**
  (books/owner-article-slots.lisp `fn-oas-refusal-line`,
  `fn-oas-refusal-line-follows-the-disk-unfolds`).
  - The served read has always run `fn-otm-read-span` before the slots, and
    while the time model sheds, a POST is answered the disk's 440 there.
  - The slots' refused-POST tier used to put the memory line in place of
    every generic 440 whatever the disk. It now uses the time model's own
    line (`fn-otm-post-command-reply`) while the model sheds, and the
    memory line otherwise.
  - Teeth, in tests/acl2/owner-article-slots-tests.lisp: at *t2-stalled*
    the tier says the disk's line, which is the line `fn-otm-read-span`
    gives. The pre-lane substitution, as a mutation, says the memory's.
- **The count.** `fn-oas-held` counts the submission in flight once
  (`fn-oas-inflight-count`). The host's count of articles in flight is now
  `*fn-heap-article-slots-most*` (32, the default configuration's
  connections), and the octets are bounded by the credits (PRF-380).
- **A complete submission holds its size** (books/owner-credits.lisp
  `fn-mca-sub-charge`, PKT-887).
  - A connection mid-article holds the worst case (reserve to finish).
  - Once the article is complete, its queued submission, the committer's
    take and the batch in flight hold 2 x 16 x (512 + 2 x its octets),
    never more than the reserve.
  - Teeth, in tests/acl2/owner-credits-tests.lisp: a poster with a short
    article queued behind a barrier is offered 340 for its next POST in one
    reserve of room. The pre-lane charge (a reserve per queued submission)
    needs two reserves.

## The in-flight numbers (until chunked-body, B6)

| Preset, A | reserve (octets) | articles mid-body at once |
|---|---:|---:|
| small, 32 KiB | 1,589,248 | 32 |
| default, 64 KiB | 2,637,824 | 25 |
| default, 1 MiB | 34,095,104 | 1 |
| development, 4 MiB | 134,758,400 | 1 |

Complete submissions add their own size, up to the count of 32.
Chunked-body shrinks the reserve about 32-fold. tests/test_native_slow_disk
now inits A = 64 KiB: it tests the disk and holds 17 articles at once.

## What ran

- REPL on hbox, all forms admitted: owner-article-slots and
  owner-article-held, owner-credits, and both test books.
- Certified: persvati certify-20260928T231552Z-3865231 (manifest archived),
  the 5 affected roots, all passed.
  - owner-credits: 89,425 steps. Its wall time, 11.6 s at 6 jobs under load
    20, is mostly the include of owner-article-slots.
- Native on hbox native-cs1 (credits-stall's tree; developer and production):
  - tests.test_native_slow_disk: 10/10 (with A = 64 KiB).
  - tests.test_native_article_slots: 3/3.
  - tests.test_native_credits: 2/2 (SCN-194).
  - tests.test_native_owner_scheduler: 8/8 at its UNCHANGED A = 1 MiB.
    Under 4 posters of short articles behind a 1.5 s barrier, the memory
    440 deferrals fell from 138 (BB at f286c0204) to 4. That is PKT-887:
    a queued short POST no longer holds a 1 MiB reserve.
- slow_disk still needs A = 64 KiB, because at A = 1 MiB two bodies cannot
  be mid-article at once (pool 64 MiB, reserve 32.5 MiB). This is a
  capacity statement, not a disk behaviour.
  - Raising the pool (*fn-heap-article-slot-budget*, 64 MiB) is a change to
    the figure and a decision for ember.
  - B6 (packed body chunks) removes it by shrinking the reserve about
    32-fold.
