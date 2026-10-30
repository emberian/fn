# fn2 A+D DSL continuation (layer A's forms and what D and B build on; one seat; present state, rewritten whole)

Seat: Opus, writing the code itself (Codex only for bounded pieces with real signatures; every
returned line read). Brief: `build/coordinator/briefs/FN2-SEAT-COMMON.md` (dev is the branch; shared
tree /Users/ember/dev/fn on dev; commit `git commit -F msg -- <paths>`; foundation edits in a worktree,
landed as one commit with export green; READY per commit). Syntax notes this seat owns:
`lanes/a-to-d-arm-contracts.md`, `lanes/a-to-bcd-ranges.md`.

## Queue (main's order)
1. DM3 (per-case Q1 teeth and check evidence). 1/n landed; 2/n (the teeth) next.
2. R6a1 rest (ruling: proceed): bytes quantum is a profile value, raised until a run's fixed cost is
   under 10% of its work at B's measured rates (262,144 yields/s at 1 GiB/s, C BLAKE3); A4 summaries
   MAY change in that commit only, recorded as a new baseline with the formula in layer doc section 7;
   scribe port onto fold/copy deletes its per-byte loops in the same commit (loop survives only as
   the reference the primitive must equal, as D2c did); fill-range with the simulator port
   (sim/sim-transfer.lisp per-byte adapter-write loop).
3. R6a2 packed handles. 4. R6b postures (D0's bundles; the five sim-acquisition bundles marked
   :owed-by :r6b must pass and the driver's verdict rule flips them). 5. A5r (native adapter redone;
   peer-address words in the Accept result's aux, D3's interim). 6. A6.
Seams from D3 and C arrive through main and take priority.

## Done this session
| sha | what |
|---|---|
| 6b8e453a9 (READY) | DM3 1/n: TRACE per case (`fn2-check-trace-cases-turn`), named loop stop conditions (`fn2-concrete-loop-stop-p`, `fn2-ref-loop-stop-p`), A4 hook `tests/q1-case-hook.lsp`, tally `tests/evidence/q1-a4-tally.lisp`, evidence book `tests/q1-evidence.lisp` (in owed-export), export lists cases with/without a passing check. Coverage 0 -> 53 (34/54 Q1 cases + 19 arm BOUND rows); 21,100 turns, 180,838 transitions G1-checked; 113 A4 blocks identical; other five drivers + acquisition pass; books < 60 s on forge (max 48.6 s) |

Unexercised Q1 cases (listed in OWED.md): echo/scribe :free, echo :retired, scribe :stopped, all 14
fn2-commit (no commit scenario in A4), router fallback, executor signal. FRAME rows get no record
(only their next-phase half is asserted at run time).

## Next: DM3 2/n, the per-case teeth
Rows name `FN2-Q1-CASE-i-POSITIVE/-NEGATIVE` (unresolved forward references). Plan: a certified test
book (tests/q1-teeth.lisp, included by owed-export, `fn2-assert-owed-teeth` on the 54 rows) building
one fixture per case on the tiny profile (both cores initialised alike, lists consistent with the
concrete scheduler): (:run K P) = row of kind K woken alone with phase P; (:observe K E) = a posted
completion owned by the row (`fn2-post-result`); router = stale owner; clock/signal =
`fn2-post-clock`/`fn2-post-signal`; service/empty-principal = calendar cursor positions. Positive:
`fn2-q1-label` gives the case and one lockstep G1 step passes; negative: the same fixture with an
untouched reference field perturbed fails the step. Probe APIs first (REPL scripts in
build/seat-ad/dm3/).

## How the evidence is regenerated
On forge (tree /build/lanes/ad-r7b, reset to the pushed branch): `build/dm3-run.sh` (closure certify
via forge-certify.sh with build/closure.txt, then forge-driver.sh sim-layer-a-a4-driver). scp back
`fn2/tests/evidence/q1-a4-tally.lisp`, certify `tests/q1-evidence.lisp` + `--export-owed` locally,
amend. compare.py now ends a block at a `Q1 ` line.

## Tooling
- Worktree: /Users/ember/dev/fn/build/lanes/fn2/r7-arms on branch fn2/dm3 (== dev at 6b8e453a9).
- Closure list: build/seat-ad/closure.txt (now includes tests/q1-evidence.lisp; add tests/runs-unit.lisp
  when C changed). Local certify: `FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 sh
  fn2/tools/certify.sh [--export-owed] -j 4 $(cat closure.txt)` with a PID file.
- Summaries: `python3 build/seat-ad/compare.py <dir> build/seat-ad/baseline-r5e2-a4.log`.
- Probes: build/seat-ad/dm3/probe*.lsp (core difference costs ~25 us tiny, ~0.2 ms concrete).
- ssh to forge with `< /dev/null` when backgrounding there, or the session hangs.

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; one certify at a time
through the slot pool; a book over 60 s blocks the commit; disk < 60 GiB: stop.
