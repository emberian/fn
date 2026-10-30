# fn2 squares experiments continuation (present state, rewritten whole after every experiment)

Seat: Opus monitor (successor seat since 2026-10-29 ~01:45; predecessor's harness restarted); Astra (codex exec)
builds. Brief: `build/coordinator/briefs/SQUARES-EXPERIMENT-20261028.md` over `FN2-SEAT-COMMON.md`. Read inputs:
`fn2/COHERENCE.md` (§2, §4, §5, §6), `fn2/DSL-METATHEORY.md` §3, §5.6-5.7, §9, `fn2/TRANSPORT.md` §4/§9,
`fn2/HIGHER-STRUCTURES.md` §4 (all under build/coordinator/).

## Where things are (2026-10-29)
- Branch `fn2/squares` on origin = d42d18c33: rebased onto fn2/main 92b50637c, raw records filtered out of
  history (coordinator request 2026-10-29; reported READY to merge, diff +10,679 lines / 83 files). The LIVE
  worktree `/Users/ember/dev/fn/build/lanes/fn2/squares` is still on the pre-rebase local commit ca50b353a
  (same squares tree, old A base 137695dfc) because E3's Codex runs in it. Temp worktree
  `/Users/ember/dev/fn/build/lanes/fn2/squares-rebase` (branch fn2/squares-rebase = d42d18c33) is mine.
- After E3 exits: in the live worktree `git checkout -B fn2/squares d42d18c33` (untracked e3/ and ignored raw
  records survive; E3's NOTES-TO-A.md append is an unstaged modification: carry it), `git worktree remove
  ../squares-rebase` and `git branch -D fn2/squares-rebase`; re-certify A4 closure on the new base (~26 min, one
  certify, PID file), then E2 run.py and E3's acceptance on the new base before E3's commit.
- Raw records rule: `fn2/experiments/squares/.gitignore` ignores results/ pass2/results/ mutants/ *.sexp, the
  processes ledgers and e2 generated sexp; E1-RESULTS.md "Raw records" names the regenerating commands. E3's
  e3/*.sexp(.gz) captures must be ignored the same way (add lines to that .gitignore), cited by command.
- Fences: only new files under `fn2/experiments/squares/` (or new books); A's files never edited; requests to A
  go in `fn2/experiments/squares/e2/NOTES-TO-A.md` (items 3+; items 1-2 in the E1 NOTES-TO-A.md).
- Quest files: `build/coordinator/fn2/lanes/squares-quests/<E>.{prompt,log,pid,last.md,REPORT.md}`;
  `resume-retry.sh <E> <session-id>` for capacity/auth stops; `wait.sh <pidfile>` as a background waiter.

## Experiments
| exp | state | session | commit |
|---|---|---|---|
| E1 generator mode measured | READY (reported): no demonstrated search improvement on layer A at this budget | 01a1859f-16cf-7091-979d-3a3a1b7e8d72 | 4f2a101e4, c134ae187 |
| E2 defsquare, two consumers | READY (reported 2026-10-29): SHARE (one envelope, specialized templates); section 9 item 1 claim-specific | 01a18603-0d96-7573-bb73-35100d162f40 | 2a123b0ff |
| E3 composition of two adjacent G1 certificates (send-result -> borrow-released, cases 11/12) | E3 pass 1 reviewed (proved route, join, teeth accepted); E3b RUNNING (E3b.pid, ~03:00): NOVEL-composite count for the verdict (341 joined = 341 executed adjacencies?) and .sexp.gz captures moved to build/e3 + .gitignore lines | 01a1863d-f056-7371-85ed-e5bfa643c34e | - |

## Review record
- E1 pass 1 and 2: read whole and accepted; findings in E1-RESULTS.md.
- E2 pass 1: Q1 accepted; Q4 refused (rows copied each theorem's own formula: circular check).
- E2c: Q4 accepted (sq-fs-formula generates statements from `*sq-q4-contract*`; five proved; count-contract
  control false; borrowing refused). Refused: Q1's template hardcoded its roles; declared contract decorative.
- E2d (read: defsquare.lisp role check, q1-contract template, q1-bindings, q1-template-tests, q4-square
  unused-roles, q4-template-tests divergence control, role-refusals.txt). Accepted. Envelope: every effective
  contract/side function must occur in all-fnnames of the translated statement, else an exact `:unused-roles`
  list; Q1 none, Q4 converter/composition/event rows list theirs. Both divergence controls refused for
  (:contract :relation). Q1's 39 translated formulas hash-identical to pass 2 (c2b514f2...).
- Seat run of `run.py` (FN_ACL2 slot env): 14 books, slowest q1-bindings 3.809 s; E2 ACCEPTANCE PASS rows=45
  Q1=40-owed Q4=5-proved. Numbers: Q1 19/39 cases exercised (10,004 G1 checks); handwritten Q1 6 decl + 347,
  Q4 8 decl + 361 + 631 copied, envelope/driver 392, controls 171; package 2,085 physical lines.

## E3 findings to relay with READY
- tools/proof_repl.py `--cached-only` install_closure (line ~1877) purged the worktree's warm certificates before
  refusing; Astra rebuilt a closure under build/e3/cert-tree (173 MB). Tool defect, not A's.
- A's assembly book took 119.6 s wall (108 s ACL2) on the old base 137695dfc: over the one-minute rule (A's to fix;
  recheck on 92b50637c).
- Join: 341 certified, 0 control failures, held-out seed 0/322 (all keys absent); full keys ~500 KB each,
  certificate 4.9 MB shared (326 KB gz); join 0.016 s vs evidence load ~21-24 s.

## After E3 exits
Read build/REPORT.md, E3-RESULTS.md and fn2/experiments/squares/e3/ whole; check the proved route's composite
`:requires` names exactly the two case rows and that label adjacency is a stated premise; check that the join
executes no transition (control re-run separate and timed); check teeth (a) coverage gap, (b) context mismatch
refused, (c) M4. Run its books/acceptance myself; commit named files under e3/ + E3-RESULTS.md (+ NOTES-TO-A
if appended); secrets check; push; READY to main via SendMessage to "main"; rewrite this file.

## Commands that work
- Launch (from squares-quests/): `nohup codex exec -C /Users/ember/dev/fn/build/lanes/fn2/squares
  --skip-git-repo-check --sandbox workspace-write -c sandbox_workspace_write.network_access=false
  --output-last-message $PWD/<E>.last.md "$(cat <E>.prompt)" < /dev/null > <E>.log 2>&1 & echo $! > <E>.pid`.
- Resume with a new pass: from the worktree, `codex exec resume <session> --skip-git-repo-check -c
  sandbox_mode=workspace-write -c sandbox_workspace_write.network_access=false --output-last-message ... "<prompt>"`.
- Commit: zsh array of named files; `python3 tools/secrets_check.py "${F[@]}"`; `git add "${F[@]}"`;
  `git commit --no-gpg-sign -F build/commit-<e>.txt`; `git push origin HEAD:fn2/squares`.

## Pitfalls hit
- tools/acl2's default slot pool (~/.cache/fn-acl2-slots) is outside Codex's sandbox: every prompt says
  FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6.
- `build/` and `*.cert` are git-ignored; copy build/REPORT.md to squares-quests/<E>.REPORT.md.
- zsh: `echo =====` fails (`=` expansion); use quoted separators.
