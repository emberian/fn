# span-borrow (Sonnet), 2026-10-05
Worktree /Users/ember/dev/fn/build/lanes/span-borrow, branch lane/span-borrow (pushed) from origin/dev 319aee828.

## What landed (commit order; shas on the branch)
1. 5c2d2c460 books/page-window-span.lisp (+ owner wrappers in host/page-window-executor-host.lisp, tests/acl2/page-window-span-tests.lisp): fn-pwr-span / fn-pwr-span-at over a caller-owned `fn-ew-span` stobj; keystones span octet k = scalar borrow at i+k, refuses where the scalar refuses, answers when its ends do, refusal leaves the buffer; guard-verified; positive + removal witnesses (boundp, plan, publication, bound, descriptor). Certified run-20261005T150053Z-a391.
2. 0e3413c38 extent.lisp: fnn-extent-window-span-at / fnn-extent-window-span-octet: one lock + one ACL2 call per <=16 KiB span, copy held on the worker (`span` slot of fnn-cold-worker, cleared where `result` is cleared). Scalar fnn-extent-window-byte(-at) kept.
3. e0eb97e73 tests/test_native_scaling.py (smoke tier row in tests/scenarios/tiers.tsv, module-map row).
4. 3b8842ac1 compressed-extent octet realizer: vector instead of fn-oct-nth on a list (was N^2/2).
5. 938c30b2e tools/loop_call_check.py + baseline (123 loops/29 files) + tests + Makefile step.
6. image-world + interfaces commits (generated files: world.py output; interface_emit --write).
7. b8a63a2ea warm path: fn-pwc-span-at (cache hits as spans).
8. ARTICLE quantum: books/article-stream-owner.lisp fn-asto-quantum (16384, parametric; override via FN_NATIVE_OVER_WINDOW), owner.lisp fnn-owner-article-window used by the article preflight and render quanta (was the OVER cursor's 256), mux.lisp fnn-mux-plan-yield: an ARTICLE plan (or its preflight) resumes immediately (due now: next loop pass, other ready connections served first) instead of after fn-splan-cursor-resume-ms = 1 ms. OVER keeps its positive delay.
9. Decoded (compressed) windows: books/decoded-window-span.lisp (fn-pwz-span, fn-pwz-span-at, fn-dwj-span-at, fn-pwz-cache-span-at + keystones), owner rows in host/page-decoded-window-host.lisp, extent-decoded.lisp: per-job span copy (no descriptor/lock/ACL2 call for octets after the first) and cached-window spans.
Certify runs: see commit messages; last: run-20261005T155057Z-c3d0 (decoded span + article-stream-owner).

## Diagnosis correction (PERF-REGRESSION-20261005.md has the ranked table)
fnn-extent-window-byte has no caller. The per-octet loop is the ACL2 renderer's fn-arena-get -> raw fn-durable-realize-octet -> fnn-extent-window-realize-octet -> fnn-extent-window-byte-at. The ACL2 renderer is unchanged; only the host seam borrows spans.

## NOT DONE / owed
- MEASUREMENTS: DONE — see the End-of-batch evaluation section (successor #3, 2026-10-06). One optional 2-minute leftover for a quieter box: reread_driver.py on meas-after/A (no dev REPL), to pair the 0.46 s fresh-owner warm read with reread-before's exact conditions; m1-durable's rep run held the box at the end of this shift.
- PROOF-OWED-DECODED-SPAN-TEETH (repair ledger): decoded span keystones have no reachable positive witness (the scalar's lacks one too).
- Cost tables / generated files (planning/current.md, cost-*.json, interfaces.json regenerated locally only) belong to the integrator; fn-asto-quantum is a new ACL2 constant and may need cost regeneration.
- host_check --load, check-lane, and tests.test_native_over_*/article tests have NOT been run on the new quantum/immediate-resume (a 16384-octet write per quantum; verify tests/test_native_over_window.py, over_pins, host_lifecycle still pass; FN_NATIVE_OVER_WINDOW=1 tests are unaffected).
- Raw window re-digest quadratic (verified streaming lane); the 64-octet pread quantum is ACL2's (fn-ews-effect) and not touched.

## Overlaps for the merger
Edited on this branch although claimed elsewhere: books/page-window-read.lisp untouched, but host/page-window-executor-host.lisp, host/native/extent.lisp (serve-next, stopped, uncommitted WIP incl. a list-returning span in books/page-window-read.lisp and window=256K); host/native/owner.lisp (rl02: one new function fnn-owner-article-window + 2 call sites), host/native/mux.lisp (reclaim-optin: fnn-mux-plan-yield only), host/interfaces.lisp (rl02: rows only), host/page-decoded-window-host.lisp, Makefile, books/image-world*.lisp. serve-next's window parameter (16384 -> profile-derived) must adopt: fn-pwr-span-copy's guards (16384 literals), *fn-ew-span-capacity* = 16384 (the span buffer is independent of the window size; the host asks spans of <= 16384), fnn-extent-span-capacity, and fn-pwz-span's `(<= (nth 4 z) 16384)`. Their list-returning span should be dropped in favor of the buffer one.

## Continuation
1. Wait for/inspect certify c3d0 and host builds; run the image build (developer,production) at head, then `tests.test_native_scaling` and the over/article natives; ping breadstuffs-f2 "fn image done, hbox free" (Mini root was told to hold; no ping sent yet).
2. End-of-batch evaluation (before = 3e53d7bc5 developer image).
3. Next hunt targets: fnn-extent-window-run's 64-octet preads (ACL2 quantum), `fn-oct-nth`-like list walks left in ACL2 renderer paths (profile), owner.lisp:1260 quadratic `append` in feed write batch (minor).

## End-of-batch evaluation (successor #2 started, #3 finished; 2026-10-05/06)
BEFORE = image set 3e53d7bc5 developer (/tank/fn/images/3e53d7bc5dbd72de73042b46e6174d316ef7a63d/fn-host-developer),
taken under load 4.7-4.9 (a concurrent lane's ACL2 job; the box was not held for this);
BEFORE-quiet = the same image re-read on a quiet box (loadavg 1.8-1.9, 2026-10-06,
reread_driver.py on the existing meas-before store; its "cold" is owner-cold only — the store
was page-cache-hot after the first run, hence cold==warm there);
AFTER = the native5 run's developer image at 79b391c04 (developer,production,dtn-developer).
Driver: measure_served.py (branch: build/span-borrow-measure/; hbox: /tank/fn/scratch/span-borrow/),
run from the run's tree under systemd-run MemoryMax=40G; owners started the installed way,
heap by the launcher's probe (decided_launch). Logs: /tank/fn/scratch/span-borrow/{meas-before,meas-after,reread-before,sprof-after}.log
(plus sprof-flat.txt / sprof-graph.txt). TRAP: an eval ERROR inside a dev-eval quantum
stops the owner outright (fence; exit=04, zero-byte REPL reply) — and this SBCL's
sb-sprof:report has NO :limit key (the keys are :type/:stream/:max; the working
precedent is tools/fixture_scripts/post-identity-index-2026-09-26/sprof.lisp).

| measurement | BEFORE (3e53d7bc5 dev, load 4.7-4.9) | BEFORE quiet re-read (load 1.8-1.9) | AFTER (native5 dev, load 0.5 start / 3.7 end) |
|---|---|---|---|
| 1 MiB ARTICLE cold: to the 220 line (s) | 18.92 | 5.25 | 10.3 |
| 1 MiB ARTICLE cold: total (s) | 42.03 (1048809 octets) | 15.52 (1048809) | 18.04 (1048809) |
| 1 MiB ARTICLE warm: to the 220 / total (s) | 14.12 / 32.58 | 5.2 / 15.48 | 7.79 / 15.47 |
| scaling gate (module, production, DEFAULT sizes 64K/512K): 220 s / total s / ratio | 0.651/1.661 and 5.612/14.946; ratio 9.00 (run native-before-overwin, load ~5.9) | not re-read | 0.102/0.266 and 1.710/3.345; ratio 12.59 (run native5 --no-build, load ~5.2). Gate OK both (ceiling 15.0). The higher AFTER ratio is the same owed re-digest (item 5) over a smaller linear base. FN_SCALING_N=131072 is OUT of the gate's contract: 8N == max-article-octets exactly and the owner's added fields make the stored record exceed it (441); the 1 MiB numbers come from the driver rows above |
| OVER 1-10000: first line / total (s) | 0.01 / 0.27 (1567788 octets) | 0.02 / 0.27 | 0.01 / 0.27 |
| 1000 POSTs of 2304 octets after 9000 fills (s) | 114.9 (115 ms each; fill 917.9 s) | not re-read | 20.5 (20.5 ms each; fill 202.5 s) |
| catch-up: owner start to done round at position 10001 (s) | 2347.7 (~4.3 articles/s; 440 backoff-retry during the fill: 'articles in flight fill the memory'; imported 2102, duplicate 3) | not re-read | 1989.1 (~5.0 articles/s; imported 868, duplicate 1). Flat: both sit on the per-article commit-barrier floor — that axis is feed-pace/catchup3's offer window, not span-borrow's |
| sb-sprof top-20 of a live owner under ARTICLE load | n/a | n/a | warm reads, fresh owner on meas-after/A (dev REPL on, load ~3.6 — m1-durable's concurrent rep run): warmup read 0.46 s / 1048809 octets, 8 profiled reads 4.7 s; self: FN-AST-AT 15.9%, syscall 9.7%, FN-AST-RENDER-ONE 5.4 self / 39.7 total, GENERIC-- 3.8, poll 3.7, FN-AST-SCAN-ONE 3.6 / 26.4, FN-AST-SCAN-STEP 3.2 / 34.2, FN-AST-RENDER-WINDOW-AUX 3.0 self / 49.6 total, FN-AST-SOURCE-BYTE 2.8, TRUE-LISTP 2.8, FLOOR1 2.2, FN-ARN-EXTENTP+LZ 4.3, FN-ARENA$X-GET 1.9 / 9.5. Full tables: sprof-flat.txt, sprof-graph.txt |

Read (successor #3, 2026-10-06):
1. The load-4.7-4.9 BEFORE column overstated serve cost: quiet, the baseline's 1 MiB ARTICLE is 15.5 s total (5.2 s to the 220). The 42 s "cold" was mostly the concurrent ACL2 job.
2. The quiet warm-total tie (15.48 vs 15.47) is an artifact of the AFTER figure's conditions, not the path's floor: a FRESH owner on the AFTER image serves the same 1 MiB article warm in 0.46 s (~33x) — the 15.47 mid-sequence number is owner heap state after the 10001-post session (GC), i.e. where serve time actually goes under posting load on this image.
3. Where the remaining warm serve time goes (the sprof): the ACL2 renderer — RENDER-WINDOW-AUX 49.6% total, RENDER-ONE 39.7%, FN-AST-AT 15.9% self, the AST scan/source walks, arena extent predicates and FLOOR1 the rest; syscall+poll ~14%. The host span seam no longer appears: Continuation item 3's targets (renderer list walks, the 64-octet pread quantum, owner.lisp:1260 append) are the right next hunt.
4. The POST path is the batch's big measured win: 115 -> 20.5 ms per POST and fill 917.9 -> 202.5 s (linear feed-batch seen-set 79b391c04 + compressed-extent vector realizer 938c30b2e). Its BEFORE side was also load-4.7, so treat the ratio as load-confounded; the direction is the algorithmic one.
5. Catch-up stays flat (2347.7 vs 1989.1 across differing load): both sit on the per-article commit-barrier floor — feed-pace/catchup3's offer window owns that axis, not span-borrow.

Owed on the AFTER image (native5 tree 12ff7e656, images' identity source 79b391c04):
tests.test_native_over_pins FAILED 1 ERROR of 9 = test_a_large_article_drained_slowly (the
root-accepted NATIVE-R2 standing red; other 8 green).  tests.test_native_host_lifecycle FAILED
1 of 11 = PendingAcceptBoundTests.test_accepted_sockets_stay_bounded (the root-accepted r71-F13
standing red; rest green).  tests.test_native_over_window CANNOT EXECUTE anywhere on current
dev: with FN_OPEN_DEPTH_FIXTURES it fails 'refused operator run open reason=schema-digest: the
store was made under another schema' on BOTH the new image (02:32Z) and the baseline set
(control run native-before-overwin 02:38Z) -- the fixtures (MANIFEST: built 2026-09-28, revs
9127a2912/01f654446) predate the current store schema; regenerating them is an environmental
item for their owner, not a lane red.  tests.test_native_scaling OK on the new image at its
calibrated default sizes.  host_check --load GREEN (58/58, 0 findings, 3.9 s, laptop).
check-lane: first run RED with one lane-owned finding (decoded-span seam stubs: the raw harness
neither stubbed nor extracted fnn-extent-decoded-span-hit / -window-span-octet, stale derived
block) -> fixed 12ff7e656 (harness_check --write-stubs, pushed).  After it the lane's FAILED set
is BYTE-IDENTICAL to an origin/dev reference check-lane run (build/lanes/span-borrow-devref):
auth_admin_fidelity 2, catchup_spool_source 1, control 1, heap_default_source 3,
init_status_probe 1, program_check 1, raw_scripts 6 (incl. lz_scalar + decoded_*: dev seams such
as fnn-extent-read-stall, commit 24281d120), trace 1, wire-grammar.json (mini-contract's
candidate).  All dev-wide; zero lane-specific reds remain.
Events: m1d5-head waited out (done 21:48Z status 1, m1-durable lane's own); native5 resubmitted
21:52Z (--build-only, developer,production,dtn-developer, 79b391c04, pid 2871264; install reused
the killed run's partial cache, certify + host-ld green); IMAGE DONE 02:19Z all three exit 0;
Mini root pinged "fn image done, hbox free" 02:2xZ.  Owed natives + scaling gate submitted 02:2xZ
(--no-build, label native5, tree 12ff7e656, images' identity source stays 79b391c04; env
FN_SCALING_N=131072 -> the gate measures 128 KiB and 1 MiB).
Measurement driver validated end to end on the baseline image (smoke: OVER needs GROUP first,
max-open-suffix <= max-transactions, [log] section needed for the catch-up await).
