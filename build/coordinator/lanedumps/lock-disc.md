# lock-disc — lock_discipline burn-down lane

Branch `lane/lock-discipline` from origin/dev d8efa5c5e (2026-10-06).
Worktree `build/lanes/lock-disc`. Claim in the shared workq:
`LOCK-DISC-BURNDOWN` (contracts JSON + checker + baseline + its test).
`catchup3` holds `host/native/pull-service.lisp` (CATCHUP-WINDOW) — its rows
stay in the queue below until that lane lands or the coordinator routes them.

## Queue statement (ground truth, not the briefed count)

`python3 tools/lock_discipline_check.py --check --summary` at d8efa5c5e:
**401 findings; 270 baselined rows (weight 1339); 129 NEW; 4 STALE baseline
rows; exit 1.**  The 129 NEW rows are the queue (/tmp/lockd-newrows.txt on the
lane machine has the full list; regenerate with `--json` and diff against the
baseline keys).  The 4 STALE rows (`R2|fnn-extent-pread|{E,O}:{probe-file,sleep}`)
are the read-stall refactor moving those leaves to `fnn-extent-read-stall`;
they can only be lowered once no NEW key remains (`--write-baseline` refuses
raises), so they land at the end or at merge.

Rule mix of the 129: R2 41, R1b 31, R7 26, R5 13+2, R10 7, R1 4 (3 violation
+ 1 unresolved), R4 2, R9 2, R3 1.

## Done in this lane

1. **Audit wired into the gate** (commit 7556221ee): `--check`'s default
   verdict now includes the `--audit-callbacks` analysis (CALLBACK-AUDIT
   rows fail the gate); the flag keeps its standalone meaning; `--summary`
   prints the audit count line.  Tests 62 → 64 (wired path fails a moved
   marker through `main()`, agreeing marker passes).  `make check-fast`'s
   line is unchanged (`--check --summary`).

## Shift log

- **Shift 1 (2026-10-06)**: ground truth (129 rows, not 146/130); audit
  wired + tested + committed; workq claim LOCK-DISC-BURNDOWN; the seven R10
  rows declared truthfully (commit 9af0acc1c, 129 -> 122); mux R1 pair
  root-caused (section-wrapped cleanup thunks; see above); observed-wait
  cluster framed as one design question; the baseline-vs-contracts history
  of mux debt documented.  STOP at shift limit: 13 rows dispositioned
  (7 declared, 6 escalated with evidence), 116 open.  Successor order:
  (1) extent.lisp R2 cluster (10 rows: read-stall refactor rename-drift of
  baselined fnn-extent-pread debt — verify each leaf moved, then a
  coordinator decision: re-baseline via --initial as explicit debt, or
  declare E/O io-ok, or fix); (2) the io.lisp R2 swarm under E from
  fnn-owner-limit-serialized (admin.lisp:574-598 — many rows share that one
  caller; check what that function holds and whether the E-held io is the
  same baselined debt under new leaf names); (3) R7 rows: compare each
  against its baselined `swallow:ignore-errors` siblings; the new shape is
  `handler clause serious-condition consumes [...]` — failure_scopes has a
  `private` scope mechanism, check its existing entries for the pattern;
  (4) R5 unresolved lock-object rows (tls-reload *fnn-tls-kx-lock*,
  pull-service wake lock, feed-service manual grab-mutex of W) — likely need
  `locks` entries naming the object form, same as the baselined
  fnn-owner-service-mux-slot-lock rows; (5) the mux R1b ten (baselined
  siblings exist for passes/polling).

## Classification so far

Counts by class (mission 3): moved / declared / passed / escalated.
**Declared 7 (all R10 close_sites, commit 9af0acc1c), moved 0, passed 0,
escalated 6 (mux R1 x2 root-caused; observed-wait cluster R2 x2 + R9 x2),
open 116.  Queue after shift 1: 122 new rows.**

### mux R1 rows 71/72 (mux.lisp:1768 fnn-mux-start#lambda1) — root-caused, ESCALATED

Both trails run mux-thread -> fnn-mux-run -> iterate -> take-inbox -> begin ->
fnn-mux-handshake-refused -> fnn-mux-finish -> the access.  The flagged
accesses are DIRECT `fnn-owner-core` calls (a declared region accessor of
owner-live-state, lock O) at mux.lisp:410 (`'fn-owner-handshake-leave`) and
mux.lisp:1115 (`'fn-owner-handshake-done id`), both added by 25879ea69
(tls-handshake-budget, PRF-986, 2026-09-29).

Runtime truth: both sites pass `sectionp=t` to `fnn-mux-cleanup-attempt`
(mux.lisp:329-332), so the thunk runs inside `(fnn-quantum-mux-finish service
nil #'call ...)` — a `def-section` (owner.lisp:2741) whose envelope IS the
owner gate: **O is held when the core call runs.**  Not a live violation; an
analysis gap: the checker attributes a cleanup thunk's body to the enclosing
defun with an empty lockset (thunk-to-section wiring is not modeled;
`an.param_sites = {}` is disabled in `analyze_tree`).

Why sibling sites do not fire: the neighboring cleanup thunks call the
`fnn-owner-action` WRAPPER (mux.lisp:413 `:owner-close`), which the checker
models (empirically: `--rule R1 --function fnn-owner-action` -> 0 findings),
while 410/1115 call the raw region accessor directly.  Two candidate repairs
for the coordinator to route (BOTH outside this lane's declaration scope):
1. host edit (forbidden zone, needs claim): use `fnn-owner-action` at
   mux.lisp:410 and 1115 (both expect the keyword `:ok`, which is exactly
   what the action wrapper checks) — matches sibling cleanup sites.
2. tool edit (this lane's claimed file, successor): model the def-section
   entry's thunk as running under O (param_sites is disabled; check git
   history for why before re-enabling).

### observed-wait cluster (rows 40/41 R2, 69/70 R9, 31 R1b) — ESCALATED as one design question

io.lisp:178/184 `fnn-observed-condition-wait` (the observer-instrumented
condition wait; 178 = unobserved branch, 184 = observed branch):
- R2 x2: the extent executor (extent.lisp:783 `fnn-extent-executor-loop`)
  waits while lexically holding E.  sb-thread:condition-wait RELEASES the
  mutex while parked, so the shape is the standard producer/consumer wait on
  the pool lock; whether the r71 model accepts an await leaf inside an E
  region for the cold workers is a design call (locks.io-ok on E is a big
  claim), not lane paperwork.
- R9 x2: actor mux-loop parks in condition-wait.  Trail: mux-run ->
  stop-loop -> finish -> start-waiting-handshake -> proxy-or-admit -> admit
  -> after -> work -> step -> handle-chunk-step -> chunk-results ->
  cold-line -> cold-await -> the wait.  The mux actor is declared
  `no_await: true` (r71 F7); this path parks it.  `await_ok_functions`
  exists (gate-enter, executor-observe-returned) — whether cold-await during
  a handshake-wait finish belongs there is a model decision.
- R1b row 31 (`*fnn-native-wait-release*`, io.lisp:182, unlocked-read,
  writes under E, 56 sites): the observation-mode diagnostic binding of the
  same helper; same cluster, likely an instrumentation-global publication
  row once the design question is settled.

### Historical pattern worth knowing

The mux file's accepted debt lives in the BASELINE, not the contracts
(R1b fnn-mux-iterate passes/polling unlocked-writes, R7 ignore-errors
swallows, R8 handoff pushes are all baselined rows).  The shrink-only rule
means this lane cannot add the new same-shape rows (R1b conns/queued/waiting/
draining/wake, R7 serious-condition consumes) to the baseline: `--write-
baseline` refuses any key not already present.  Those rows are either
declared truthfully, fixed, or the coordinator re-baselines with `--initial`
as an explicit debt decision.  Successor: check each new R1b/R7 row against
its baselined sibling before inventing a new declaration shape.


| file | rows | dispositioned | notes |
|---|---|---|---|
| host/native/mux.lisp | 18 | 2 (escalated, root-caused) | R1 x2 analyzed (see above); R1b x10, R2 x1, R7 x4 open — check baselined siblings first |
| host/native/io.lisp | 45 | 9 (7 declared R10 + cluster escalation) | R10 x5 declared (9af0acc1c); rows 40/41/69/70 escalated + note on 31 (observed-wait cluster, see above) |
| host/native/owner.lisp | 22 | 0 | R1 x2, R1b x5, R2 x3, R5 x4, R7 x7, R10 x0 |
| host/native/extent.lisp | 10 | 0 | R2 x10 (read-stall refactor cluster; likely rename-drift of baselined debt) |
| host/native/pull-service.lisp | 6 | 0 | HELD: catchup3's claim covers the file |
| host/native/dev-repl.lisp | 4 | 0 | R1b 1, R4 1, R7 2 |
| host/native/tls.lisp | 4 | 0 | R2 x4 (probe-file under XTLSINIT/XTLSRELOAD) |
| host/native/tls-reload.lisp | 3 | 0 | R5 unresolved x3 (*fnn-tls-kx-lock* unknown lock object) |
| host/native/web-host.lisp | 4 | 0 | R7 x4 |
| host/native/catchup-spool.lisp | 3 | 0 | R3 1, R4 1, R7 1 |
| host/native/feed-service.lisp | 3 | 0 | R5 x2 (manual grab-mutex of W), R7 x1 |
| host/native/tcpcl.lisp | 1 | 1 (declared) | R10 |
| host/native/workflow.lisp | 1 | 1 (declared) | R10 |
| host/native/bp-session.lisp | 1 | 0 | R1b |
| host/native/extent-decoded.lisp | 1 | 0 | R1b |
| host/native/heap.lisp | 1 | 0 | R2 (stat under O) |
| host/native/bp-app.lisp | 1 | 0 | R5 unresolved |
| host/native/immutable-publish.lisp | 1 | 0 | R7 |

## Mechanism notes for successors

- Declarations live in `tools/lock_discipline_contracts.json`, not the host
  files.  Kinds: `callback_contexts` {lambda-id: {runs_in, why}} (R1 async /
  stored-callback rows; why carries an own-file `file.lisp:NNN` marker the
  audit holds to the ordinal's line), `unlocked_publication` {var: {writers:
  [fns]}} (R1b; EVERY writer must be named or the row re-fires as
  `var:undeclared-writer`), `close_sites` {fn: why} (R10), `threads` (R4),
  `borrows` (R3), `failure_scopes` (R7 private scopes), `locks` io-ok (R2),
  `direct_owner_sites` / `lock_order` (R5).
- A declaration is truthful paperwork for an analysis gap; if the access is
  genuinely unsafe the row is ESCALATED in this file, never declared away.
- Baseline is shrink-only (`--write-baseline` refuses raises; new keys count
  as raises).  Resolve rows first; lower the 4 stale rows last.
- R5 `unresolved` rows ("manual grab-mutex of W", "lock object (X)") mean the
  analyzer cannot see the lock region/object — check whether the lock object
  needs a `locks` declaration (name -> object form) before escalating.

## Anything weird

- `--check --summary --audit-callbacks` used to print ONLY the audit line and
  exit 0 (the standalone branch returned before the findings verdict); the
  wiring commit makes that combination moot (audit is in the default verdict;
  the flag alone stays standalone).
- The mux R1 rows are THREAD roots (the mux loop thunk), not stored
  callbacks — `callback_contexts` does not apply to them; the honest fix is
  either the loop holding what it touches or an escalation.
