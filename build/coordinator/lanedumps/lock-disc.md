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

## Classification so far

Counts by class (mission 3): moved / declared / passed / escalated.
**Declared 0, moved 0, passed 0, escalated 0 — grind starts at mux.lisp.**

| file | rows | dispositioned | notes |
|---|---|---|---|
| host/native/mux.lisp | 18 | 0 | R1 x2 (thread root reaches O), R1b x10, R2 x1, R7 x4, R9 x2 (R9 rows sit in io.lisp:178/184 fnn-observed-condition-wait but are mux-actor rows) |
| host/native/io.lisp | 45 | 0 | R10 x5, R1b x9, R2 x21, R5 x2, R7 x6, R9 x2 |
| host/native/owner.lisp | 22 | 0 | R1 x2, R1b x5, R2 x3, R5 x4, R7 x7, R10 x0 |
| host/native/extent.lisp | 10 | 0 | R2 x10 (read-stall refactor cluster; likely rename-drift of baselined debt) |
| host/native/pull-service.lisp | 6 | 0 | HELD: catchup3's claim covers the file |
| host/native/dev-repl.lisp | 4 | 0 | R1b 1, R4 1, R7 2 |
| host/native/tls.lisp | 4 | 0 | R2 x4 (probe-file under XTLSINIT/XTLSRELOAD) |
| host/native/tls-reload.lisp | 3 | 0 | R5 unresolved x3 (*fnn-tls-kx-lock* unknown lock object) |
| host/native/web-host.lisp | 4 | 0 | R7 x4 |
| host/native/catchup-spool.lisp | 3 | 0 | R3 1, R4 1, R7 1 |
| host/native/feed-service.lisp | 3 | 0 | R5 x2 (manual grab-mutex of W), R7 x1 |
| host/native/tcpcl.lisp | 1 | 0 | R10 |
| host/native/workflow.lisp | 1 | 0 | R10 |
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
