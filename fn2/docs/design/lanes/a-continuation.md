# fn2 A+D DSL continuation (layer A's forms and what D, B and C build on; present state, rewritten whole)

Seat: Opus (third), writing the code itself. Brief: `build/coordinator/briefs/FN2-SEAT-COMMON.md` (dev is
the branch; shared tree /Users/ember/dev/fn on dev; `git commit -F msg -- <paths>`; foundation edits in a
worktree, landed with the export green; READY per commit; **a foundation commit certifies the whole
tree's closure**: every fn2/tests/*-unit.lisp, not only the seat's list; `fn2/tools/forge-certify.sh`
with no books does exactly that). Syntax notes owned here: `lanes/a-to-d-arm-contracts.md`,
`lanes/a-to-bcd-ranges.md`.

## Landed (dev and origin/dev)
| sha | what |
|---|---|
| 6c8f3d1a0 | fix forward: tests/commit-resource-unit.lisp reads both commit sections (my split 71c1fb2f2 had broken it) |
| 57054a247 | S6: `:account` stop reason (code 22) appended to fn2-stop-reason |

## In flight (fn2/a-seams3 in worktree build/lanes/fn2/r7-arms; dev locally = 7fd40d0b7, NOT yet pushed)
| sha | what | state |
|---|---|---|
| 7fd40d0b7 | S4 `fn2-sched-reattribute machine to fn2-sched -> (mv code fn2-sched)` (cherry-pick of b02c6e099, accepted on the pre-C base: closure, export identical, 7 drivers, 113 blocks) | on local dev in the shared tree, push after the run below |
| c95c35ef7 | C2c seam: `fn2/books/words.lisp` (fn2-u32, fn2-u32-mul, fn2-prng-mix32 moved from sim/prng.lisp); C deletes fn2-ribbon-mul32/-mix | forge acceptance in /build/lanes/a3b (PID file build/accept.pid is the process group: stop with `kill -- -PID`) |
| 427a2dd83 | S3 weighted calendar: `fn2-sched-init profile weights n`, weights = `fn2-profile-weights` (`:accounts` `(SLOT :weight W)`, default 1), pass-interleaved, L = W + 4 ceil(W/16), weighted L <= 4096; `fn2-sched-calendar-validp weights`, starvation statement over weights; reference `fn2-ref-calendar weights`, `fn2-ref-lists weights ...` | same run; S3 changes the owed statement of fn2-sched-starvation, so the regenerated OWED.md (acc/427a2dd83/OWED.md on forge) is amended into the S3 commit before landing |

Landing: `cd /Users/ember/dev/fn; git fetch origin; git merge --ff-only origin/dev` (if dev moved, cherry-pick
and re-accept), `git merge --ff-only fn2/a-seams3` (or cherry-pick), secrets check, push, READY to main per sha.

## Queue
1. After landing: tell main S3/S4/words shas; D7 doc 13.6 is D's to update.
2. S1, S2, S5 wait on D's accounts.lisp (fn2-account-book/-unbook, -charge-run, -grant-ready-p/-grant-one).
3. DM3 2/n, WIP (uncommitted) in r7-arms, also saved as build/seat-ad/dm3b/{wip.patch,q1-teeth.lisp,sim-layer-d-evidence.lsp}:
   - `fn2/tests/q1-teeth.lisp`: per-label fixtures from the tiny profile (drain the scheduler; run labels:
     row 0 of kind K, `fn2-machine-write-phase`, `fn2-exec-wake`; observe labels: op slot 0 written as a
     submitted op owned by the row, phase set to one accepting the event, `fn2-post-result`; router: stale
     owner gen; clock/signal: fn2-post-clock/-signal; services: flag + cursor P+j; empty principal: flag 0 +
     cursor 0), reference by fn2-ref-reset, lists from the concrete scheduler; positive = one
     `fn2-trace-lockstep` step labelled and passing; negative = another kind's row generation perturbed on
     the reference is refused, restored is accepted. Generates FN2-Q1-CASE-i-POSITIVE/-NEGATIVE for all 67
     and asserts them. NOT YET RUN: iterate with build/seat-ad/dm3b/teeth-repl.lsp on a certified forge tree.
   - `sim/check-trace.lisp`: `fn2-ref-queues-of-core`, `fn2-check-trace-reseeded-turn` (reference reseeded
     from the concrete core each turn). `tests/q1-case-hook.lsp`: `fn2-q1-hook-install-turn profile`
     (replaces fn2-turn), tally writer takes a prefix. `tests/sim-layer-d-evidence.lsp`: runs D's
     unchanged sim-layer-d.lsp under the hook, writes `tests/evidence/q1-d-tally.lisp` from an exit hook.
     `tests/q1-evidence.lisp`: second evidence record per case and per arm from the D tally. Unverified:
     that replacing fn2-turn's symbol-function reaches D's callers; that good-bye runs sb-ext:*exit-hooks*.
4. R6a1 rest: rebased clean onto dev 0160c5a69 as branch fn2/r6a1d in worktree build/lanes/fn2/a-r6a1;
   uncommitted try for the fill-run guard: `fn2-scribe-fill-sector` kept disabled (its fn2-core-preserves
   lemmas then apply) instead of enabled. Untested. Then the simulator fill-range port, quantum 64 KiB
   with the A4 re-baseline (that commit only).
5. R6a2, R6b, A5r, A6.

## Forge
- /build/lanes/a3b: my acceptance clone; `build/forge-accept.sh SHA[:certify] ...` (closure certify of
  every book, owed export, then A's seven drivers in parallel; results build/acc/<sha>/result).
  Start detached as `setsid sh -c "echo \$\$ > build/accept.pid; exec sh build/forge-accept.sh ..."`.
- /build/lanes/a3: older clone; a stale run of mine (pid 552805, no valid PID file) may still be
  certifying there; benign, main knows. ad-r7b's orphan awaits ember.
- Compare: `python3 build/seat-ad/compare.py <dir with sim-layer-a-a4-driver.log> build/seat-ad/baseline-r5e2-a4.log`.

## Rules
PID files only (group leader); never stash / add -A; named paths; secrets check before push; one certify at
a time; a book over 60 s blocks the commit (slowest now ~43 s, assembly-access); disk < 60 GiB: stop.
