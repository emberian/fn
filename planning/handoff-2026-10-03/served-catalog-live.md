# LANEDUMP served-catalog-live (Opus 5.5, 2026-10-02/03)

Worktree build/lanes/served-catalog-live, branch lane/served-catalog-live (pushed), head 45c9ec0f6 (origin/dev merged).
WOUND DOWN 2026-10-03 on coordinator order. 45c9ec0f6 sent to runner a8c1198f67920c411 for the all-onto-dev merge (SCL1 ledger state=ready).
PENDING, NOT HARVESTED: natives scl-a3 at 45c9ec0f6 (`tools/hbox_native.sh status scl-a3`; includes tests.test_native_over_cursor_cost = the AFTER numbers), farm run-20261003T020434Z-f323 (`tools/farm.py status hbox run-20261003T020434Z-f323`), regen at 45c9ec0f6 (log scratch regen2.log; planning/current.md needs regen after the merge).

## READY 1 (in progress): OVER on the cursor, O(1) quantum guard, drain idle, off-lock cold miss
- Cause of over_pins 0/4: fn-nntp-xref-reply-cat answered OVER/XOVER ranges whole whenever an Xref server
  name was configured (every real node); cursor reached only with no name. Fix: cursor carries SERVER.
- Keystones: fn-nntp-over-range-ovw-expands-to-over-range-served-cat, fn-ovw-run-is-over-range-served-cat;
  fn-nntp-archive-command-cat-is-pinned statement unchanged.
- r67 F1: fn-cat-handles-inp removed from guards on the quantum path (no body used it); per-quantum guard
  (natp w). Teeth assert the world's guards.
- r67 F3 / Astra c07: fn-exp-progress + fn-exp-idle-keeps-after-progress; host calls it from fnn-mux-after
  when a reply's drain outlasted its step (conn drained-late flag), one clock reading per long reply.
- r67 F2 for OVER: fnn-owner-cursor-step runs under *fnn-extent-no-io*; a miss is issued under the mutex,
  awaited off it (fnn-owner-cold-await), quantum reruns warm; past deadline the reply is terminated.
- Restricted route still answers OVER whole (registry scoped).
- Natives scl-a2 (cafc2bf68): cursor tests and idle OVER green; fixture bugs fixed after. scl-a3 at 45c9ec0f6 running
  (+ tests.test_native_over_cursor_cost with fresh fixtures in /tank/fn/scratch/served-catalog-live/fixtures).
- BEFORE (4aa332295 images, whole-step OVER of the first group): 1k 0.047 s / max hold 42.8 ms / 26.6 MB;
  10k 0.52 s / 473 ms / 259 MB; 100k 6.0 s / 5,474 ms one hold / 4.57 GB.
## NEXT (continuation)
- First: harvest scl-a3 / f323; fix forward any red on dev; put the before/after table in the SCL1 READY; then base on origin/dev.
- READY 1 once scl-a3 + farm f323 + regen are green (GROUP 211 subtest stays red: READY 2).
- READY 2: GROUP count option 2' (decisions/group-count-after-reclaim-2026-10-03.md DECISION), incl. S042 NEXT/LAST.
- Then restricted route on the cursor, LIST option A (discovery snapshot), paged catalog default. S043 waits for def-cursor.
