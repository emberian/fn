# fn2 A+D DSL continuation (layer A's forms and what D and B build on; present state, rewritten whole)

Seat: Opus, writing the code itself. Brief: `build/coordinator/briefs/FN2-SEAT-COMMON.md` (dev is the
branch; shared tree /Users/ember/dev/fn on dev; `git commit -F msg -- <paths>`; foundation edits in a
worktree, landed as one commit with the export green; READY per commit). Syntax notes owned here:
`lanes/a-to-d-arm-contracts.md` (now has "Row fields: the read set"), `lanes/a-to-bcd-ranges.md`.

## Landed this session (all on dev and origin/dev; READY sent in the seat report)
| sha | what |
|---|---|
| 6b8e453a9 | DM3 1/n: TRACE per case (`fn2-check-trace-cases-turn`, sim/check-trace.lisp), named loop stops (`fn2-concrete-loop-stop-p`, `fn2-ref-loop-stop-p`), A4 hook `tests/q1-case-hook.lsp`, tally `tests/evidence/q1-a4-tally.lisp`, `tests/q1-evidence.lisp` (in owed-export), export lists cases with/without a passing check. Coverage 0 -> 53 (34 Q1 cases + 19 arm BOUND rows) |
| 6b2f6ef5b | Read sets: a callback takes only the ROW- fields its body reads (inferred, nothing for D to declare); per-field readers `K-ROW-<field>` with width lemmas; K-SNAPSHOT / -READ / VALUESP deleted; owed BOUND/FRAME bind only reads. fn2-conn 30 fields, widest read set 17 |
| 71c1fb2f2 | Section split: core init -> `assembly-init` (`fn2-core-init-events`); commit kind -> `assembly-callbacks-b` + `assembly-callbacks` (`fn2-commit-events`, `-2`, shared `fn2-commit-local-theory`). Forge max assembly book now assembly-access 39.8 s |

Current OWED: 349 rows; check coverage 53 rows with a passing, exercised check. Q1 catalogue is 67
labels since D3 (fn2-conn's 13 added); A4 exercises 34 of 67; unexercised are listed in OWED.md.

## Queue (main's order as of the last message)
1. D7's six seams (fn2/docs/d-machines-nntp.md section 13.6 on dev 1d6cce7ca), each its own small
   commit, A's drivers unchanged, reply with shas: S1 `:listener-principals` profile key + booking at
   Accept via `fn2-account-book` / `-unbook` (admission `:copy (principal-slot account-ref)`); S2
   `fn2-account-charge-run` after `fn2-machine-run` in fn2-exec-principal and on the system row in
   fn2-exec-service; S3 weighted calendar in `fn2-sched-init` (weights; all-1 = today's calendar entry
   for entry; L = sum w + 4*ceil(sum w/16) <= 4096; calendar-validp and starvation hyps follow); S4
   `(fn2-sched-reattribute machine to fn2-sched) -> (mv code fn2-sched)`; S5 a fourth grant source in
   fn2-machine-grant-ready-p / -grant-one (`fn2-account-grant-ready-p`, `fn2-account-grant-one`);
   S6 an `:account` stop reason in exec-state's enum. S1, S2, S5 call D's functions: they need D's
   accounts.lisp first (or D lands its wrappers and A wires the call sites); S3, S4, S6 are A-only.
2. R6a1 rest, parked on branch fn2/r6a1c at 65209c7b5 in this worktree (based on 6b8e453a9, so
   rebase onto dev first): new range primitives in pool-ranges.lisp (set-range, span, put/get-u32,
   word loops, fold u32 lemmas; certify fine) and core wrappers + defcosts; scribe fill/patch/verify
   on them (`fn2-scribe-fill-sector`, `-verify-sector`), per-byte loops kept only in
   tests/scribe-ranges-unit.lisp as the reference; quantum 65,536 in machines-a :budget with
   `*fn2-run-bytes-quantum*` in operations.lisp (formula Q >= 10*F*R) and an assert; turn-refinement
   statement uses constants; own-read-hook reports range reads/writes per byte. OPEN: the guard of
   `fn2-scribe-fill-run` fails in tests/core-child-assembly-callbacks (goal about machine-kind after
   update-fn2-scribe-table of (mv-nth 2 (fn2-scribe-fill-sector ...))): the helper returns a core and
   the callback emitter needs its frame; likely fix: inline the fill chain in the callback body (all
   calls are defcost'd wrappers) or make the helper a wrapper whose frame is visible. Then the
   simulator fill-range port (sim-transfer input kinds: collect bytes, one fill-range), A4 new
   baseline (summaries may change in that commit only), formula in layer doc section 7.
3. DM3 2/n: the per-case teeth `FN2-Q1-CASE-i-POSITIVE/-NEGATIVE` are still forward references.
   Plan: certified fixtures per label kind (tiny profile, lists consistent with the concrete
   scheduler; run labels by waking one row of kind K in phase P; observe labels by a posted
   completion; router by a stale owner; clock/signal by fn2-post-clock / fn2-post-signal;
   service/empty principal by calendar cursor), positive = one lockstep G1 step passes at the
   fixture, negative = an untouched reference field perturbed fails it.
4. R6a2, R6b, A5r (Accept peer-address aux words), A6.

## Forge
- Trees: /build/lanes/ad-split (clean clone of fn2/a-split; has build/split-run.sh, evtimes.py
  per-event profiler) and /build/lanes/ad-r7b. Run detached jobs as
  `setsid nohup sh -c "..." < /dev/null & echo $! > build/X.pid` so the whole group can be stopped
  by its PID file; ssh with `< /dev/null`.
- ORPHANS, no PID file (reported, not killed): in /build/lanes/ad-r7b an old certify of
  assembly-core (certify.sh pid 255348, make 255355, sbcl 255931) started 06:42 forge time whose
  wrapper I stopped; it loops in a guard proof (per-child init attempt, abandoned) and holds that
  tree's certify lock; a later split-run.sh (pid in build/split-run.pid there, child forge-certify
  347415) waits on that lock. Ask main/ember to stop them or leave ad-r7b unused.
- B's sim-layer-b sweep at 6b2f6ef5b's code was running in ad-split (log build/sim-layer-b.log),
  passing at scenario 14 case 2000/10000; check its end (`B3 TIMING`) and report.

## Tooling
- Worktree /Users/ember/dev/fn/build/lanes/fn2/r7-arms on branch fn2/a-readsets (== dev 71c1fb2f2).
- Closure list build/seat-ad/closure.txt (now with q1-evidence, scribe-ranges-unit [only valid on
  fn2/r6a1c], commit-proof-unit, conn-unit, conn-answer-unit, runs-unit, identity-unit; pass
  books/assembly-init.lisp and books/assembly-callbacks-b.lisp explicitly or rely on deps).
  Local: `FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 sh fn2/tools/certify.sh
  --export-owed -j 4 books/assembly.lisp $(grep -v scribe-ranges closure.txt)`.
- Summaries: `python3 build/seat-ad/compare.py <dir> build/seat-ad/baseline-r5e2-a4.log` (a `Q1 `
  line ends a block).
- Evidence refresh: run the A4 driver on forge, scp `fn2/tests/evidence/q1-a4-tally.lisp`, certify
  tests/q1-evidence.lisp + export, commit with the code.

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; one certify at a time
through the slot pool; a book over 60 s blocks the commit; disk < 60 GiB: stop.
