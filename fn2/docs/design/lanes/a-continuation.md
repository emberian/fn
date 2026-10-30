# fn2 A+D DSL continuation (layer A's forms and what B, C and D build on; present state, rewritten whole)

Seat: Opus, writing the code itself. Brief: `build/coordinator/briefs/FN2-SEAT-COMMON.md` (dev is the
branch; shared tree /Users/ember/dev/fn on dev; `git commit -F msg -- <paths>`; foundation edits in a
worktree; **a foundation commit certifies the whole tree** (every book under books/ sim/ tests/, which
`fn2/tools/forge-certify.sh` with no books does) with the export green and OWED.md regenerated in the
commit; READY per commit). Syntax notes owned here: `lanes/a-to-d-arm-contracts.md`, `lanes/a-to-bcd-ranges.md`
(not yet updated for S1's listener offer and books-p: add a paragraph under "Admission").

## Landed this session (dev and origin/dev)
| sha | what |
|---|---|
| 6c8f3d1a0 | fix forward: tests/commit-resource-unit.lisp reads both commit sections (my 71c1fb2f2 split had broken it) |
| 57054a247 | S6 `:account` stop reason (code 22) |
| 7fd40d0b7 | S4 `fn2-sched-reattribute machine to fn2-sched -> (mv code fn2-sched)` |
| 578174649 | C2c seam: `fn2/books/words.lisp` (fn2-u32, fn2-u32-mul, fn2-prng-mix32) |
| 91950f63a | S3 weighted calendar: `fn2-sched-init profile weights n`, weights = `fn2-profile-weights` (`:accounts` `(SLOT :state S :weight W)`, default 1), pass-interleaved, L = W + 4 ceil(W/16), weighted L <= 4096; `fn2-sched-calendar-validp weights`; owed starvation over weights; reference `fn2-ref-calendar weights` / `fn2-ref-lists weights ...`. `fn2-profile-weights` is DISABLED on purpose (open, it makes fn2-core-init's guard proof loop in assembly-init) |
| 63a7412fe | S2 run charges: `fn2-exec-charge-run` (executor-access) after fn2-machine-run, service visits on the system row (sched nprincipals); the reference makes the same calls |
| b31e5d4de | S5 the ledger as fourth grant source; `(fn2-account-events)` at the head of assembly-access; the test assembly instance includes accounts-core |
| ba644c1de | S1 booking at Accept (books-p from admission :copy account-ref; refused booking admits unbooked -> 400; unbook on failed issue/Accept/refused admission); dispatcher takes the fixed `*fn2-machine-listener-offer*` (mode principal-slot account-ref); `:listener-principals`; `fn2-listener-bookings p core`. D's files touched by main's rulings: conn.lisp (:copy, greeting arm), accounts-core.lisp (defcost fn2-account-book), owed-conn.lisp, check-account.lisp, sim-layer-d.lsp (row's 8th element). D's sim-layer-d four sets PASS, flood refuses 10-12/15 |

Lessons (callback language, guards): no `&` binders in callback bodies (mv-let + declare ignore); an
observer must not rebind the core inside a let value (branch at the top, each arm returns (mv id core));
read row fields before any rebinding; a guard naming a non-recursive profile helper needs the helper
disabled or its lemmas never match.

## Queue (main's order)
1. DM3 2/n. WIP (uncommitted; nothing left in any worktree) saved in build/seat-ad/dm3b/:
   `wip.patch` (check-trace.lisp: `fn2-ref-queues-of-core`, `fn2-check-trace-reseeded-turn`;
   q1-case-hook.lsp: `fn2-q1-hook-install-turn profile` replacing fn2-turn, prefixed tally writer;
   q1-evidence.lisp: second evidence record per case/arm from `evidence/q1-d-tally.lisp`),
   `q1-teeth.lisp` (per-label fixtures on the tiny profile; positive = one fn2-trace-lockstep step labelled
   and passing; negative = another kind's row generation perturbed on the reference refused, restored
   accepted; generates FN2-Q1-CASE-i-POSITIVE/-NEGATIVE for every label and asserts them),
   `sim-layer-d-evidence.lsp` (D's unchanged sim-layer-d.lsp under the turn hook, tally written from
   sb-ext:*exit-hooks*), `teeth-repl.lsp` (iterate on a certified forge tree). NOT YET RUN. Re-apply on dev
   (the patch predates S1/S2/S5; its files are not touched by them). Unverified: that replacing fn2-turn's
   symbol-function reaches D's callers; that good-bye runs the exit hooks; that the observe fixtures (op
   slot 0 written directly with fn2-ops-put, then fn2-post-result) satisfy fn2-post-eligiblep; that
   `fn2-machine-write-phase` exists. The teeth book goes into fn2/tools/owed-export.lsp's list. D4/D5 kinds
   may have grown the catalogue: fixtures come from it, so new labels get teeth or fail loudly.
2. A-S7 taken kinds (D doc 14.7): offered to D as a foundation commit on top of S1; review its diff.
3. A-S8 `fn2-pool-copy-across` (+ `fn2-core-copy-across`, defcost), sibling of fn2-pool-compare: a
   performance item now.
4. R6a1 rest: branch fn2/r6a1d in worktree build/lanes/fn2/a-r6a1 (rebased on 0160c5a69; rebase again);
   uncommitted try for the fill-run guard: `fn2-scribe-fill-sector` kept disabled instead of enabled. Then
   the simulator fill-range port and the 64 KiB quantum with the A4 re-baseline (that commit only).
5. R6a2, R6b, A5r, A6.

## Forge
- /build/lanes/a3b: my acceptance clone. `build/forge-accept.sh SHA[:certify] ...` = whole-tree certify,
  owed export, A's seven drivers in parallel; results in build/acc/<sha>/. Start detached as
  `setsid sh -c "echo \$\$ > build/accept.pid; exec sh build/forge-accept.sh ..."` (PID = process group:
  stop with `kill -- -$(cat build/accept.pid)`). From zsh write `${A}:certify` (`$A:c` is a zsh modifier).
  D's scenario: `SECS=7200 sh fn2/tools/forge-driver.sh sim-layer-d` (PID file build/sim-layer-d.pid, ~10
  min). Whole tree ~11 min at load 5-7.
- Compare: `python3 build/seat-ad/compare.py <dir with sim-layer-a-a4-driver.log> build/seat-ad/baseline-r5e2-a4.log`.
- /build/lanes/a3: older clone; a stale run of mine (pid 552805) may linger; benign, main knows. ad-r7b's
  orphaned certify has ended (no process left there).
- Treadmill: dev moves several times an hour; rebase, certify the tip once, land at once; if only disjoint
  files moved meanwhile, cherry-pick and land.

## Rules
PID files only (group leader); never stash / add -A; named paths; secrets check before push; one certify
at a time; a book over 60 s blocks the commit (slowest ~46 s: assembly-access, runs-assembly); disk < 60 GiB: stop.
