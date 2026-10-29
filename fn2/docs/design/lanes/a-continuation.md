# fn2 layer A continuation (present state, rewritten whole; 2026-10-29 ~04:20, fourth monitor)

Seat: Opus monitor for layer A (pool, vocabulary, host, simulator, executor, and the DSL owner:
defcolumns, defmachine, defcorechild, defthm-owed, declare.lisp). Brief:
`build/coordinator/briefs/FN2-LAYER-A-POOL-HOST-SIM.md` over `FN2-SEAT-COMMON.md` (re-read it: it now
carries the one-minute rule, assert-never-absorb, DSLs generate meaning, layers meet at seams, and the
Codex multi-agent rule). Binding inputs, read before acting: `fn2/REVIEW-20261028.md`,
`fn2/REVIEW-SINS-20261028.md`, `fn2/DSL-METATHEORY.md` (§1-2, §5-7, §9 whole), `fn2/HIGHER-STRUCTURES.md`
(closing + entries 1, 2, 3, 9). All paths under `/Users/ember/dev/fn/build/coordinator/`.

## State now (fourth monitor, ~04:20)
- Committed and pushed (READY sent for each): DM1 9cc09f2bf, L1 ec89a5c7b, DM0b d8ec35855, seal move
  26570c101 (coverage resolve + obligation seal now in fn2/tools/owed-export.lsp, top of the world;
  coordinator ruling), R5e1 825ab9187 merged as 0cad033b0.
- R5e2 RUNNING: Codex session 01a186ab-60a6-7661-b500-a17efcf77e92, PID file a-quests/R5e2.pid, log
  R5e2.log, last message R5e2.last.md. Prompt carries the seat's R5e1 follow-ups (items 7-10: FNV
  known-answer teeth, named trace/WORK fields in check-work, real per-field :why reasons, rename
  fn2-profile-exports-compliant-p). On exit: read build/REPORT.md and the diff whole, run
  build/seat-merge-accept.sh (nohup, PID file build/seat-merge-accept.pid; ~4-5 min; note
  seat-merge-accept.exit is stale until the run ends: wait on the PID), commit build/commit-r5e2.txt
  (write it), merge origin/fn2/main, secrets check, push, READY.
- Then R6a1.prompt and R6a2.prompt (R6a split; R6a.prompt renamed .superseded), R6b (has a "From L1"
  section), then DM2.prompt (WRITTEN: defsquare envelope into fn2/books over fn2-squares, one identity
  kind, catalogue = E1's 39 labels, Q1 bound, role refusals, statement fidelity vs E2's SHA), then re-cut R7
  (emit arm obligations through defsquare/defthm-owed; decision 2 restricted arm language).
- Queue is sequential in this worktree (all quests touch machines/pool/columns). The second worktree
  a-sim-storage (branch fn2/a-sim-storage, at 26570c101) is free for small disjoint fixes.
- Recertify after a merge: closure list in build/r5e1/closure.json (79 paths);
  `sh fn2/tools/certify.sh --export-owed -j 3 <paths without fn2/>` under nohup with a PID file.
- Carries: defthm-owed identities (:owed NAME) beside readers' (:square NAME) (DM2 unifies). L1's
  simulator attributes every listener Close as :admission-refused (R6b must keep that true).
  fn2-columns-preserves takes 17 positional parameters (expansion-time only; DM4/DM5 kit work).
- L1's owed items are folded into R6b.prompt ("From L1" section).

- COORDINATOR (02:00), binding on the R7 re-cut: defsquare landed on fn2/squares 2a123b0ff
  (fn2/experiments/squares/E2-RESULTS.md, envelope under fn2/experiments/squares/). Rulings: (1) share
  declarations between a square's sides, keep independent semantic judgments (the correspondence never
  substitutes for the client oracle); (2) the envelope refuses a row whose declared contract roles do not
  appear in its generated statement unless listed unused (macro refusal). In R7 the 39 dispatch cases
  enter fn2-squares through that envelope, adopted from the experiment branch into fn2/books by this seat
  as a readable diff. Q1 template exercised 19/39 at the 20,000-transition cap; the rest need scenarios
  reaching scribe labels beyond reserve, the router fallback and signal.

## Queue (all prompts prewritten in a-quests/; launch in this order)
| # | quest | prompt | note |
|---|---|---|---|
| 1 (DONE ec89a5c7b) | L1 liveness defect from the squares experiment (c=1, accept-credits=1: 133 :unattributed drops; fn2-sim-run-echo returns :pass with live drops) | L1.prompt | coordinator: first after DM1, before DM0b; one readable diff |
| 2 (DONE d8ec35855) | DM0b callback map, operation emitter, fn2-call (the listener's 14-scalar forwarding), stale-row fix, staged :at requirements, per-input seals | DM0b.prompt | |
| 3 (R5e1 DONE 825ab9187; R5e2 RUNNING) | R5e names for every number, defcolumns generates put/row-snapshot/copy/diff/preserves, ABI equations E1-E5 + E1/E2 landing counters, TRACE selection/state labels, A4/A9/A11-A22/A28/A29/A31-A34 | R5e.prompt | RE-CUT against DSL-METATHEORY §5.1 and DM0a/DM1/DM0b before launch (header says so) |
| 4 | R6a range primitives (copy, compare with two owners, fold, scan, drop-prefix, fill-range), packed handles (A16), bytes-quantum measurement (B's BLAKE3 finding), note to B | R6a.prompt | |
| 5 | R6b resources.md, :on-refusal postures, protected credits (A30), pool-wait FIFO, named wait links (A10, A26) | R6b.prompt | L1's admission fix may pre-empt part; reconcile |
| 6 | R7 arm contracts: :cost :writes :tables :next :uses :holds, defcost, restricted arm language (ember decision 2), one cost-composition + one budget lemma, line-scanner and compaction example, obligations into fn2-squares | R7.prompt | RE-CUT before launch; three layer-A kinds |
| 7 | A5r native adapter redone (rulings in prompt; record + foreign replay as membership checks) | A5r.prompt | network_access=true; the seat runs the Linux backend on hbox |
| 8 | A6 ACCOUNT (per-row holds), checker registry with transfer kinds, scenarios 10/12/19 whole | A6.prompt | last |
Later, per DSL-METATHEORY §7.2: DM2 (case catalogue, defsquare), DM3 (Q1 binding), DM4-DM10, DMBC.
The fn2/squares seat also builds defsquare under fn2/experiments/squares/: coordinate before DM2.

## DSL-METATHEORY §9 open items
- Timing: DECIDED DM1 before R7 (layer doc §10; coordinator told).
- Shared declaration on both sides: ember decision 1 (sharing allowed for representation/compiler
  refinement, recorded, independent contracts for consequential behaviour + shared-handler mutation
  control); apply in DM1's store (done there if the review confirms) and DM3/DM10.
- Enforcement strength: ember decision 2 (restricted arm language where completeness is promised);
  apply in R7's re-cut.

## Standing rules (coordinator/ember, binding)
- No book over 60 s; every quest's acceptance includes a certify-time table; a book over 60 s blocks
  the commit (W1 brought all to < 60 s).
- Diff read whole before commit; REPORT copied to a-quests/<Q>.REPORT.md; continuation rewritten whole.
- After every commit: `git merge origin/fn2/main` then push, so main fast-forwards.
- Overlap only on disjoint files (the second worktree `/Users/ember/dev/fn/build/lanes/fn2/a-sim-storage`,
  branch fn2/a-sim-storage, is free for that; fast-forward it first).
- Codex multi-agent: prompts split disjoint files among sub-agents; shared files stay top-level.
- Report to main only READY (sha + numbers), RED, BLOCKED. Neighbour seats fn2/squares and fn2/lean-meta:
  do not touch their files; lean-meta may ask for a stable printer of the world tables (a small ACL2
  book; do it when asked).
- Box safety: PID files only (no pattern kills), no stash, no add -A, Codex never pushes, disk < 60 GiB
  free = stop (446 GiB free at handoff), secrets check before every push.

## Quests done (all on fn2/a-pool-host-sim, pushed unless noted)
| quest | commit | one line |
|---|---|---|
| A1-A4 | a7db9f4f1 0d78dc1ed e0cd1f4dd bed9edc28 | original build (diffs not read whole; the reviews found the misses) |
| R2, R1 | 9f7b974cd, 22686aa97 | ACCOUNT claim corrected; echo fault density, attribution, liveness phase |
| R3 | c7f4f1e68 | independent list-scheduled reference; TRACE as differential; refinement restated |
| R4 | 1151b6b66 | defmachine, per-kind tables, A-STORAGE-ABI |
| S1 | 4d46304db (merged 13645d2f7) | sim storage stamp discipline (B's two defects), fence slots |
| T0 | 8b0a09a47 | every .lsp driver exits 1 on failure, regenerates revision |
| R5a 1+2, pass 3 | 428c49d05, 009141a0c | per-kind states, guarded setters, :observes, :u64/widths, named callbacks, teeth name functions, generated OWED.md, linear declaration cost |
| R5c | d90b821b3 (merged 957b018c1) | defcorechild seam, open registry, layer A as a library, assembly |
| R5d | 137695dfc | assert-don't-absorb (named stops), fault landings per class, swarm seeds |
| W1 | 1fa1fe24b | every book < 60 s (one cause: generic per-array NTH rules) |
| R5b | 127f7b877 | WORK charges and recomputes real work; OWN observes real reads |
| DM0a | 4cf85c4a8 | declare.lisp identities and :generated manifest; B's prefix favour |
| R5e1 | 825ab9187 (merge 0cad033b0) | defcolumns PUT/ROW-SNAPSHOT/COPY/DIFF/PRESERVES, 26 twin generators deleted, :why policy, A31 (sim-adapter-base 25 s) |
| seal | 26570c101 | obligation seal to owed-export (coordinator ruling for B) |
| DM0b | d8ec35855 | operations.lisp emitter, callback maps, fn2-call (15 forwards), stale-row refresh, :at resolution, input seals |
| L1 | ec89a5c7b | admission row reservation, :admission-refused, live drops fail, C=1 regression |
| DM1 | 9cc09f2bf | fn2-squares store, defthm-owed its view, separate counts, :shared rule, derived layer |

## Current numbers (seat run at DM1, 9cc09f2bf; identical to 4cf85c4a8)
Acceptance driver exit 0, 0 TRACE differences: pool TINY 10000/10000, NEAR-LIMIT 1000/1000; 26 fault
controls; scribe 19 cases; echo seed 20261028 accepted=1000 echoed=224 dropped=776 (0 unattributed)
turns=38425 deaths=76; liveness 200/200, observed-max 124 vs bound 4740; all 26 fault classes landed
(device phase 16,384 trials); OWN 113,686 real scribe reads; swarm mode with printed seed.
Certify (two jobs, laptop): every book < 60 s; slowest sim-adapter-base ~42-46 s, assembly sections
<= 18 s each, vocab ~13 s, sim ~23 s, echo ~12 s, machines books ~1-9 s; 41-field declaration ~5 s.
Per-book tables: a-quests/W1.REPORT.md, DM0a.REPORT.md, DM1.REPORT.md.

## Known carries (not yet in a prompt only where noted)
- Fault and record ids, wait reasons, WORK record kinds still integers (R5e A14).
- defmachine-callback calls pass ROW scalars positionally; snapshot staleness (DM0b).
- Global (disable update-nth) in columns.lisp (R5e item 5); the test-only hint rewriter in
  sim-allocation.lisp (R5e item 5).
- A5's parked work: local branch fn2/a5-native-wip (6a6170a35), unreviewed; A5r redoes it.

## Commands that work
- Launch: `cd a-quests && nohup codex exec -C <wt> --skip-git-repo-check --sandbox workspace-write -c
  sandbox_workspace_write.network_access=false --output-last-message $PWD/<Q>.last.md "$(cat <Q>.prompt)"
  < /dev/null > <Q>.log 2>&1 & echo $! > <Q>.pid`. Wait with a background `while kill -0 $(cat <Q>.pid)`.
- Amend a finished session: `cd <wt> && nohup codex exec resume <session-id> --skip-git-repo-check -c
  sandbox_mode=workspace-write -c sandbox_workspace_write.network_access=false --output-last-message
  $D/<Q>.last.md "$(cat $D/<msg>)" ...` (session id: `grep -m1 'session id' <Q>.log`).
- Capacity errors: `a-quests/resume-retry.sh <Q> <session-id>` (nohup, PID file; loops 10 min).
- Codex cannot write .git (index.lock): after a merge resolution, the seat stages the files.
- Certify: `sh fn2/tools/certify.sh --jobs 2 <paths relative to fn2/>` (`--export-owed` regenerates
  fn2/docs/OWED.md; keep B's include lines in fn2/tools/owed-export.lsp). Driver output is wrapped by
  ACL2: extract with `tr -d '\n' < log | grep -o 'ECHO SCENARIO .\{0,200\}'`.
- Commit: `F=($(git status --short | awk '{print $2}'))` (named files from status; check the list),
  `python3 tools/secrets_check.py "${F[@]}"`, `git add "${F[@]}"`, `git commit --no-gpg-sign -F build/commit-<q>.txt`.

## Pitfalls hit
- zsh: arrays, not word-split strings; backticks in -m messages (use -F files).
- Two concurrent quests in one worktree collide (certs, REPORT.md): use the second worktree.
- A merge of concurrent quests needs the quest's own Codex session to resolve (it holds the context).
- Codex "model at capacity" happens (A3, M1); resume by session id.
