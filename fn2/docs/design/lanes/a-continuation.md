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
| 6c8f3d1a0 | fix forward: tests/commit-resource-unit.lisp reads both commit sections |
| 57054a247 | S6: `:account` stop reason (code 22) |
| 7fd40d0b7 | S4: `fn2-sched-reattribute machine to fn2-sched -> (mv code fn2-sched)` |
| 578174649 | C2c seam: `fn2/books/words.lisp` (fn2-u32, fn2-u32-mul, fn2-prng-mix32); C uses it (d2f2ea9e8) |

## In flight: branch fn2/a-seams4 (worktree build/lanes/fn2/r7-arms) over dev a98d3c7c5
| sha | what |
|---|---|
| 61ce57fc6 | S3 weighted calendar (`fn2-sched-init profile weights n`; weights from `:accounts` `:weight`; `fn2-profile-weights` DISABLED after its definition, or fn2-core-init's guard loops in assembly-init) |
| edaea0d84 | S2 run charges: `fn2-exec-charge-run` (executor-access), principal runs and service visits (system row = sched nprincipals); the reference makes the same calls |
| 5a94dd215 | S5 ledger grant source; `(fn2-account-events)` moved to the head of assembly-access |
| 59f41e76a | S1: `:listener-principals`; listener books at Accept for targets whose admission copies account-ref (`fn2-machine-admission-books-p`); refused booking admits unbooked (400 at greeting); unbook on failed issue/Accept/refused admission; dispatcher copies (mode principal-slot account-ref); conn.lisp's :admission copies, greeting arm no longer books (main's ruling) |
Acceptance on forge /build/lanes/a3b (group PID file build/accept.pid): 61ce57fc6 full, S2/S5 certify, S1 full;
then D's `fn2/tests/sim-layer-d.lsp` at S1 (four sets; flood refuses 10-12 of 15, principal 1 reserve
intact). S3's commit also needs the regenerated OWED.md (acc/61ce57fc6/OWED.md) amended in before landing
(the fn2-sched-starvation statement changed). Landing: ff dev (cherry-pick if dev moved), push, READY per sha.

## Queue
1. Land the D7 stack above. A-S7 (taken kinds, D doc 14.7): D writes it as a foundation commit after S1
   lands; I review its diff. A-S8 (fn2-pool-copy-across + core wrapper + defcost) after, mine.
2. DM3 2/n below.
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
