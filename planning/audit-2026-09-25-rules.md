# Audit of the tree's rules, 2026-09-25

A proposal. No rule is changed by this document. ember asked (2026-09-25):
"What are the other rules of the tree? We're well overdue for a review of
those; many of them were probably supportive stilts that no longer are
useful or serve us."

Read: `AGENTS.md`, `planning/how-we-work.md`, `docs/proofs.md`,
`docs/README.md`, the `make check` target and the docstring of every tool it
runs, `planning/review-2026-09-18-independent.md`,
`planning/review-2026-09-24-gpt6-direction.md`, decisions through D27, and the
coordinator's memory notes that carry ember's corrections. Today's evidence
is the 97 merges and 342 other commits on `dev` since 2026-09-24 07:00 UTC,
through `087f7213`, plus the 138 evidence records dated 2026-09-24 and
2026-09-25. No farm, no hbox. `make check` was run once, in this lane's
worktree at `087f7213`.

## What today cost, in bookkeeping

- **`make check` fails on `dev` at `087f7213`.** `tools/current_view.py
  --check` reports `planning/current.md` stale. The cause is the head commit
  itself: archiving the representation lane's manifests
  (`certify-20260925T020709Z-2376326`) moves M4's "proved" column from "no:
  closure moved" to "yes". So archiving evidence makes the generated view
  stale by design. Make stops at the first failing recipe, so the fifteen
  gates after `current_view` did not run on `dev` head at all. (Run by hand
  in this worktree, they pass or report as usual.)
- Of 342 non-merge commits, 54 archive manifests, 18 edit the proof-cost
  baseline, 17 edit the v0 scoreboard, and 69 regenerate the ledger or the
  current view or fix staleness. `planning/ledger.md` changed in 59 commits.
- Merge conflicts, by file: `planning/v0-scoreboard.md` 32,
  `planning/ledger.md` 13, `planning/ledger.json` 13, `planning/proofs.json`
  4, `planning/proof-events.json` 3, `docs/prefixes.md` 2. Every conflict in a
  generated file was resolved by regenerating it. The scoreboard conflicts
  were resolved by hand.
- **The proof-cost baseline admitted books eight times** (`b6d8d714`,
  `6c0626c5`, `c60bb371`, `c91356f5`, `c14568e7`, `dfd6eb19`, `9b2e2cbd`,
  `67b028c7`). Four of those books were between 10.09 and 10.5 s, which is
  load noise ("its usual band", "it flaps around the line"). Two were
  measured at 4 jobs, and D26 now excludes those runs. Lanes also bent their
  work to the line: `native-admin` landed at 9.96 s (`f811a7af`), and
  `bp-eid-shape` was split out "to keep it under 10 s" (`6373d09d`).
- **Comment edits cost a full recertification.** The stale-comments lane
  (`03d804e8`) changed comments only and recertified 628 books in 890 s.
  Most of the stale comments were host line numbers written into books and
  proof-event notes.
- **Every image cut was qualified until ember's correction.** Before the
  "qualification theater" correction (2026-09-24 evening), each of three cuts
  (`1a9dd747`, `6c0626c5`, `47bdb9a4`) had three qualification lanes
  (matrix, campaign, native subsets): nine lanes. After it, `18c91321`,
  `4eca4148` and `c3420013` had one lane each, plus one DTN lane for
  `c3420013`.

## Verdicts

- **load-bearing:** the rule caught a real defect this cycle, or it prevents
  a class of defect the reviews named.
- **stilt:** it caught nothing, it costs attention, and what it guarded is
  now structural (a check, a generator or a theorem).
- **wrong:** it now contradicts D27, a review, or a later correction by
  ember, or it names something that does not exist.

### A. ember's corrections

These rules are ember's. The audit proposes no cut to any of them. In
several cases it proposes writing the rule into the tree, because today it
lives only in the coordinator's memory.

| # | Rule | Where it lives | What it was for | Today | Verdict |
| --- | --- | --- | --- | --- | --- |
| E1 | Never `git stash` a working tree | `~/.claude/CLAUDE.md` only | Parallel agents share working directories; a stash moves their files away | No incident; no cost | load-bearing. **Not in the tree**: add it to AGENTS.md |
| E2 | Never reset, check out or stash the main `~/dev/fn` checkout; review with `git show`/`git diff` | coordinator memory (`fn-shared-checkout-rule`) | Other agents are live in it | Followed: every lane worked in `build/lanes/*` | load-bearing. **Not in the tree**: add it to AGENTS.md |
| E3 | Run the narrowest thing that could refute you; no unfiltered suite | `~/.claude/CLAUDE.md` (the rule is written for Rust); in fn it takes the form "never `--closure` for a lane" | A 9.5 GB, two-hour suite that could not move the result | Every lane submitted affected roots. The seam lane's `--closure` ("missing 171, removed 278") is the counterexample it names | load-bearing |
| E4 | `swarm-build` around every hbox build | how-we-work, Boxes | hbox OOM and power-cycle on 2026-07-15 | Used in 26 evidence records; no OOM | load-bearing |
| E5 | `free` lies on hbox; read `arcstats` and RSS | how-we-work, Boxes | hbox misread as busy twice | No incident | load-bearing |
| E6 | About ten useful lanes; claims announce intent and do not lock | AGENTS.md "Swarm coordination"; decisions 2026-09-23 | Exclusive ownership stalled work | About 45 lanes over the day, merged as they landed | load-bearing |
| E7 | Broad concurrent waves; temporary breakage is recorded, not hidden | decisions 2026-09-24 05:37; how-we-work intro | Serial prerequisites | The day ran this way | load-bearing |
| E8 | **Waves, not per-cut qualification**: one cut at convergence, qualified once by one lane while the next wave runs; never re-qualify interim cuts | coordinator memory only (`working-with-ember`, "qualification theater") | Five cuts in a day, each with three qualification lanes | 9 lanes for 3 cuts before the correction, 1 per cut after | load-bearing. **Not in the tree.** how-we-work step 6 still says "A frozen image gets a fresh ordinary closure and its actual runtime qualification", which reads as per-cut qualification. Replace it (see H7) |
| E9 | Orient to the plan, not the audit | coordinator memory (~11:00 on 2026-09-24); the gpt-6 review says the same ("Do not make another universal audit the prerequisite for all useful work") | A morning spent re-auditing every P row | The afternoon went to the plan's packets | load-bearing. **Not in the tree**: add one line |
| E10 | D26: the ten-second number is the 2-job scoped measurement | decisions 2026-09-24 ~22:30; `tools/proof_cost.py` | Wide runs made the ratchet flap | Two 4-job admissions would not have happened under it | load-bearing |
| E11 | `proof_cost` and `certified_claims` fail `make check` | ember's night goals (2026-09-24 07:25) | Warnings nobody read | Both fail on a finding; baseline 37 → 3 over the day | load-bearing. The ratchet's band needs work (H12) |
| E12 | D27: bound work, never data | AGENTS.md; decisions D27 | "a branch that someday will fail during operation for no meaningful reason" | Today's merges added data caps under the older wording: group names limited to 128 octets "(local bound)" (`577d5152`), EIDs to 256 octets (`6373d09d`) | load-bearing. R11 contradicts it; fix R11 |
| E13 | D27: concrete representations at runtime, with a correspondence theorem | AGENTS.md; D27 | Octet-list overhead | `records-concrete` landed: POST samples down 15 to 19 percent (`5080ee73`) | load-bearing. The ledger's export-hygiene lint flags exactly these theorems (P1) |
| E14 | A lane briefed only to implement hands a failed proof to the proof owner | decisions 2026-09-24; how-we-work "Who implements" | The Luna/Sol trial | Not exercised: every Opus lane both implemented and proved | ember's to keep or retire. Proposed wording: "applies when a brief says implement-only" |

### B. Rules the coordinator or the reviews added

Row numbers skip where a rule is covered elsewhere: R12 and R13 are E12 and E13, H4 is R29, H8 is E14, H13 is E4 and E5. `AGENTS.md` is abbreviated **AG**, `planning/how-we-work.md` **HW**, and
`docs/proofs.md` **PR**.

| # | Rule, in one sentence | Where | What it was for | Caught today (defect and record) or cost today | Verdict |
| --- | --- | --- | --- | --- | --- |
| R1 | Preserve the ambitious, design-first scope in small complete steps | AG scope | Keep the vision while slicing | Nothing caught; no cost | load-bearing (a statement of purpose) |
| R2 | The decision register is authoritative; proposals are not requirements; no invented approval gate | AG scope | Agents inventing gates | Candidate decisions are marked "pending ember" (kind-8, D02 scope) | load-bearing |
| R3 | Requirement and proof IDs are stable; registry, spec and scenario change together | AG scope | Drifting contracts | Cost: PRF IDs collided twice and were renumbered at merge (PRF-075 `d0603aa0`, PRF-077 `77683a08`). `tools/next_id.py` says "claim on the board", and nobody uses the board | load-bearing. Replace the claim step: the coordinator assigns the ID at merge with `tools/next_id.py` |
| R4 | Preserve the RFCs; separate an RFC requirement, a stronger fn guarantee and a local policy | AG scope | Overclaiming RFC conformance | RFC 5537 §3.5 item 11: fn added Injection-Date wrongly (`9f672238`). Group names "stricter than the RFC, with the reason" (`91bdf0e9`) | load-bearing |
| R5 | "No server, proof, or flight-readiness claim follows from this scaffold" | AG scope | 2026-09-18, when there was only a scaffold | Now false: a deployed node exists and `current.md` has four evidence columns | **wrong** (stale). Replace: "A claim names its coordinate (source, proof manifest, qualified image, deployment); `planning/current.md` keeps the four apart and none implies another." |
| R6 | Protocol and storage decisions are executable ACL2; the host does I/O | AG discipline | A second implementation in the adapter | See R21 | load-bearing. Merge it with R21 |
| R7 | Keep the logical model separate; optimize by correspondence | AG discipline | Model/representation confusion | Superseded by D27's second bullet, which makes it mandatory | **stilt** (duplicate). Delete; D27's bullet carries it |
| R8 | Octets, parsed fields, content identities, Message-IDs and local numbers are distinct types | AG discipline | Type confusion | Transit 436: the completion compared received octets with stored, Path-prepended octets (`f0f6d5af`). D25: poster bytes versus the injected record (`a41fc03b`, `9f672238`) | load-bearing |
| R9 | Durable acceptance comes only from persisted state, never from socket writes or ACKs | AG discipline | False acknowledgement | TCPCL Completed is not a release (`ef480e2c`); kind-8 retry (`bd497bd2`) | load-bearing |
| R10 | An ambiguous persistence failure is a recovery event | AG discipline | Silent rollback | W2: unclassified OS errors are uncertain, never refused (`4d1f6c79`); P5 fences and exits 4 (`ef480e2c`) | load-bearing |
| R11 | External parsing never invokes the reader; "bound lengths, nesting, work, and allocations before consuming untrusted inputs" | AG discipline | Review naiveties: reader injection, unbounded work | "Bound lengths" reads as a data cap. Today's 128-octet group-name bound and 256-octet EID bound followed that wording | **wrong** in part (contradicts D27). Replace the second sentence: "Bound the work and allocation one request may cause before consuming it; a length limit is a per-request work bound set so that no profile the operator can write is capped below it." |
| R14 | Keep conflicting evidence and provenance; no last-writer-wins | AG discipline | Merged histories | D23 provenance accessors (`817b3af8`); "never widen" keeps the raw-versus-injected conflict (`cc5dbb3c`) | load-bearing |
| R15 | No `skip-proofs`, `defaxiom` or trust tags to claim completion | AG discipline | Trust laundering | The certify runner's closure audit refuses forbidden facilities (review §5), so this is structural. It costs one line | load-bearing (keep the line; it states a value) |
| R16 | An abstract crypto model proves nothing about real signatures, disks or peers | AG discipline | Overclaim | The signed-receipt lane states the delegation profile "honestly" (`c003bb2d`); the verifier is independent (`b3a754ec`) | load-bearing |
| R17 | The theorem subject is the function the host calls; "say which host line calls it" | AG assurance (D6, D7) | Certified theorems about functions the server never runs | Caught: K4 cited over a function the host does not call (11 theorems; `91c7dc24`); P6's old headline false on the called path (`a6c12962`); PRF-028's pending subjects replaced (`f7e48768`). `reach_check --strict` holds 40 orphans by name. Cost: host line numbers written into books went stale, and the comment-only fix recertified 628 books (`03d804e8`) | load-bearing. Change "say which host line" to "name the host function that calls it". `current_view.py` resolves the line; a line number never goes into a book |
| R18 | Cite keystones, never corollaries; name restatements `-unfolds` or `-by-definition` | AG assurance (§4 rows 1 to 8) | Registry padded with tautologies | Honest names landed (`f0f6d5af` "-by-definition lemmas"). `ledger.py --check` refuses a flagged citation in `make check` | **stilt** as prose (structural now). Shrink to one clause that points at the check |
| R19 | Teeth: a reachable witness and one `must-fail` per hypothesis | AG assurance (binding witness, §4) | Theorems that bite nothing | Caught: a must-fail ("a value with a space") exposed that `bp-boundary add` accepts an EID containing a space (`f811a7af`, fixed in `6373d09d`); redundant hypotheses found (`b8ebd40a`, `f2cc79a6`); an old headline shown false (`a6c12962`). But `teeth_check` never fails and reports 156 findings that nobody triaged today | load-bearing rule; its check is a **stilt** in report mode. Make it `teeth_check --strict --changed-since REV`: a new or touched keystone fails without teeth, and the backlog stays a report |
| R20 | A named assumption is an `encapsulate` in `books/assumptions.lisp` | AG assurance (review D5, §6) | Assumptions in prose only | Quiet: 15 encapsulates; A-SIG-OBSERVE was proposed (`6d79017f`) | load-bearing (a class the review named; no cost) |
| R21 | One owner per decision, and it is ACL2; no Python or host twin | AG assurance (§4 twins) | Python recomputing ACL2 values | Caught: the host payload bound and its comparison removed (`6137465d`); host capacity comparisons removed (`ce27b18d`); the host copy of the reclaim plan deleted (`f2a0bdfc`); the audit found eight host twins still open (`91c7dc24`) | load-bearing |
| R22 | Every process-death cut is a model crash point | AG assurance (D4) | Kill tests beyond the model | `native_program_check` found two fault points with no model cut (`8827062d`). The c3420013 qualification found that the byte model's finish program has no marker file, so P10 was narrowed (`30a9dfcf`). Both checks fail `make check` | load-bearing. The prose can point at the two checks |
| R23 | The ledger is generated, never typed | AG assurance | Counts that drift | No hand-typed count found. Cost: `ledger.md` and `ledger.json` each in 13 merge conflicts; 59 commits touched `ledger.md` | load-bearing. Add: "a conflict in a generated file is resolved by regenerating it, never by hand". Consider a `merge=ours` attribute plus regeneration in the merge routine |
| R24 | Uncertain, refused and accepted stay distinct everywhere, exit codes included | AG assurance (D13) | Conflated exit codes | W1 and W2 (`4d1f6c79`); `bp send` reported a severed contact as fault 4 rather than uncertain 3 (`86857cf3`, fixed `f2f7665a`); a refused start exits 5 (`3d61f125`) | load-bearing |
| R25 | A theorem about an unreachable branch is marked `unreachable-in-composition` or the branch goes | AG assurance (storage F9, F10) | Evidence about dead code | 12 markers in books; N16 left inexpressible with its reason (`aabcf98b`) | load-bearing (cheap). Merge it with R17 |
| R26 | No whole-state revalidation on a served path; carry the invariant | AG assurance (D3, wire) | Quadratic per-command work | The day's largest wins: STAT 5.06 → 0.08 ms (`22b7eac7`), IHAVE/CHECK 1.6 → 0.12 ms (`3dee88fe`), the advance's share of POST CPU 9 → 0.4 % (`78ff9970`), commit 19.5 → 0.7 to 2.9 ms (`67ca177a`). No check enforces it | load-bearing |
| R27 | Quote the pessimistic number with its scope; the collision figure, not second-preimage | AG assurance | Flattering bounds | Merges state scope (for example "honest wall figure: the 42 ms POST is the ZFS write", `78ff9970`) | load-bearing (cheap) |
| R28 | Behaviour and its invariants land together; `green_check`; "Never `git log`." | AG assurance (2026-09-22 F4) | Commits over uncertified invariants | `green_check`: 767 of 767 books green at their digest, none owed. Every merge cites its runs. "Never `git log`" as written forbids a tool this audit's own brief required; what it meant is that a commit message is not certification | load-bearing rule; the clause is **wrong**. Replace it with "A commit message is not certification; `green_check` is." |
| R29 | Open a codec in a hint, never at the top of a book | AG assurance, HW loop 3 (2026-09-22 F3) | Proofs that stop returning | The ten-second repairs were "hints that stop rewrite through codec and response rules" (`54b9b49e`); `theory_check --strict` covers its listed books | load-bearing. Stated twice: delete HW loop 3 |
| R30 | Function prefixes are registered in `docs/prefixes.md` | AG housekeeping | Prefix collisions | No check reads it; 2 merge conflicts today | **stilt**. Generate the table from the ledger's defuns (prefix, book), or delete the rule. `ledger.py` already has every `defun` |
| R31 | Lane worktrees are removed when the lane lands | AG housekeeping | Clutter | Not followed: 29 directories in `build/lanes`, 21 registered worktrees. Cost: none observed | **stilt** as an agent rule. Move it into the coordinator's merge routine (HW) |
| R32 | Role names are defined in `swarm-cycles.md` or not used | AG housekeeping | Codex role jargon | Roles were retired on 2026-09-24 07:25 ("Role names are neutral from here") | **stilt**. Delete |
| R33 | Lanes coordinate through `LANEDUMP.md` and the swarm board | AG swarm; HW width | Coordination between lanes | LANEDUMP was used. `planning/swarm-board.md` was last edited 2026-09-24 04:46 EDT, and about 45 lanes ran without it | board is a **stilt**. Delete the board; `now.md`'s lane list plus LANEDUMP carry it |
| R34 | Reuse matching evidence; coordinate expensive runs | AG swarm; HW parallelism | Duplicate certification | Runs print "installed N of M"; persvati and hbox caches reused all day | load-bearing |
| R35 | `make check` is static; `make certify` runs ACL2; the simulator runs scenarios | AG evidence | Mistaking `check` for proof | `make check` is now twenty static gates, still ACL2-free | load-bearing. Reword "scaffolding only" to "static only" |
| R36 | "Certify only owned book roots during parallel edits. Root coordinates a frozen integrated batch." | AG evidence | Wave 1's exclusive ownership | Contradicts the 2026-09-23 correction ("file ownership is not exclusive") | **wrong**. Replace: "Certify the roots you changed and what includes them." |
| R37 | Add model, codec, fault and interop tests as layers appear | AG evidence | 2026-09-18 scaffold | Generic; R19 (teeth) and the labs carry it | **stilt**. Delete |
| R38 | Record assurance obligations per batch in the closure inventory (PR scope table) | AG evidence; PR "Assurance grows" | Scope creep without evidence | The closure inventory is archived (`planning/archive/assurance-closure.md`); `current-view.json` (obstruction, next gate) is the live mechanism | **stilt**. Replace: "a lane that changes a capability updates its obstruction and next-gate lines in `current-view.json`". Keep PR's table as reference |
| R39 | Record tool versions, invocation, digests and results for certification evidence | AG evidence | Unreproducible claims | The committed manifest carries all of these, and `evidence_manifests.py` fails on a newly cited run with no committed manifest | **stilt** (structural). Replace: "cite the committed manifest" |
| R40 | A proposed theorem is not proved; admitted is not guard-verified; tests are not a proof | AG evidence | Overclaim | Merges keep this distinction ("a form the session admits is not a certificate") | load-bearing |
| R41 | Brief lanes from `now.md`, how-we-work and `handoff-2026-09-24-winddown.md` | AG evidence; HW intro | The gpt-6 to Claude restart | The wind-down handoff describes image `863c2141`, and seven cuts have happened since | **wrong** (stale). Replace with `now.md` and `current.md` |
| R42 | Before ending, keep the milestone task and the registries accurate; report what changed, ran and is open | AG evidence | Silent drift | `proofs.json` touched in 122 commits; `milestones.md` in 2 | load-bearing (registries). Drop "the milestone's current task" and keep `now.md` |
| R43 | No deployment, publication or messaging side effects unless authorized | AG evidence | Unauthorized deploys | The node was deployed only on the coordinator's call | load-bearing |
| H1 | A capability's state is `current.md`, generated from `current-view.json`; `make check` fails when it is stale; evidence records are never edited | HW intro | The gpt-6 review's "evidence-maintenance repair" | Cost: fails `make check` on `dev` head right now, because archiving a manifest changes the proved column and so stales the view by design. The run stops there and the later 15 gates did not run. Meanwhile `v0-scoreboard.md` is still hand-edited: 32 merge conflicts, 17 commits | load-bearing idea, **wrong** mechanism. Replace: "`current.md` is regenerated in the same commit as any manifest archive or registry change (the merge routine does this); `make check` runs `current_view --check` last." Freeze the scoreboard's per-image cells: `current.md` replaces them |
| H2 | Start from ground truth: absolute paths and pasted signatures, or ask | HW loop 1 | Mirror-building agents (ember's launch lessons) | No mirror incident today | load-bearing |
| H3 | Iterate in `proof_repl`, not on the farm | HW loop 2 | Farm round trips | Used in 4 records | load-bearing (cheap) |
| H5 | Certify incrementally, never `--closure`; `green_check --changed-since` | HW loop 4 and the cost section (stated twice) | Hour-long recertification | Every lane ran affected roots | load-bearing. State it once |
| H6 | Report theorem statements, host function, teeth, `green_check` line, run and manifest, and what was not done | HW loop 5 | Unverifiable reports | Merge messages follow it | load-bearing |
| H7 | Root converges every two to three batches; "a frozen image gets a fresh ordinary closure and its actual runtime qualification" | HW loop 6 | Freeze discipline | Nine qualification lanes for three cuts before E8 | **wrong** (contradicts E8). Replace with E8's text |
| H9 | Four jobs for the combined run, at most two for a lane's scoped run | HW parallelism | Contention | Not followed: an 8-job hbox run (`certify-20260925T014952Z`) is recorded. The slot pool and `swarm-build` enforce the limits anyway, and D26 handles measurement | **stilt**. Replace: "the machine-wide slot pool and `swarm-build` are the limits; never bypass them" |
| H10 | The REPL's `FN_ACL2` and `FN_CERT_CACHE` pairs per box | HW parallelism | Wrong-toolchain sessions | Reference text, not a rule | **stilt** in how-we-work. Move it to the `proof_repl.py` header and the runbooks |
| H11 | Edit-to-verdict under three minutes, "measured by the three rows of `tools/iteration_bench.py`" | HW parallelism and cost | Slow iteration | `tools/iteration_bench.py` does not exist; nothing measured the target today | **wrong** (cites a phantom tool). Keep the target sentence and drop the tool, or build the bench; until then it is not a number |
| H12 | A book over ten seconds at two jobs is a defect; the baseline only shrinks (`proof_cost` ratchet) | HW cost; PR; D26 | Proofs that stopped returning (805 s → 3.7 s) | Load-bearing: the baseline went 12 → 3 by proof work with no statement changed (`54b9b49e`, `47b2d708`, `48e97356`). Cost: 8 admission commits, 4 of them for noise between 10.09 and 10.5 s, and lanes fitting books under 9.96 s | load-bearing rule with a noisy line. Proposed: a book not in the baseline fails above 11 s (10 %) at two jobs; 10 to 11 s is printed as `NEAR`. Four of today's eight admissions disappear |
| H14 | The five-findings table (F1 to F5) | HW | Restates the 2026-09-22 review | Duplicates AG and the cost section; F1's provisional wave (`triage.py`) was not used today | **stilt**. Delete the table; keep F2 (300 s discovery; a timeout is a finding) in the loop |
| H15 | A step is DONE or NOT; no `partial` row; the three words; pessimistic numbers; counts from tools; never "resume" someone's branch | HW | Partial claims | Merges report in this shape | load-bearing. Condense (three of the clauses repeat AG) |
| H16 | Root keeps `dev` certified with one plain-roots run after each merge batch | HW cost | Lanes recertifying from `sha256` upward for an hour | `green_check` shows 0 owed on `dev` | load-bearing |
| H17 | A lane does not merge `dev` mid-flight | HW cost | Recertifying a moving base | Three dev-into-lane merges (`b4dc77d7` to pick up a landed dependency, `24d89ea8`, `554e4cab`), with no harm | load-bearing, too strict. Add "unless it needs a landed change; then it recertifies what the merge moved" |
| H18 | "A lane reports when its run is submitted, and root harvests the manifest" | HW cost | Idle waits | Contradicts R28 and F4 ("a lane certifies its own closure before it reports"). Every lane today waited in the background and cited its own runs | **wrong** (self-contradiction). Delete; keep "one background command, then do other work" |
| H19 | Wait in the background; never reissue a foreground wait | HW cost | A night lost to ten-minute shell caps | No incident | load-bearing |
| H20 | Convergence obligations: checkpoints name what is missing; the live node is protected; intermediate reds stay visible | HW | The capability wave | Followed | load-bearing. Condense; half of it repeats AG |

### C. The checks `make check` runs

| Check | Rule it enforces | Today | Verdict |
| --- | --- | --- | --- |
| `check_scaffold` (links, `ledger --check`, v0 matrix digest) | R18, R23 | Pass | load-bearing |
| **P1** ledger shape lints (export hygiene, teeth form, include hygiene, host names) | PR "four shape lints" | 1854 `WARN` lines in every `make check`. Export hygiene flags every D27 correspondence equality (`fn-rcon-record-p-is-record-p` and 7 more in `records-concrete`, and the `fn-ccar-*-is-*` family), which is the theorem shape D27 requires | **wrong** as run. Exempt an equality whose conclusion is `(equal (concrete ...) (logical ...))` with the name `-is-`. Print a count in `make check` and the list only for `--changed-since` books. PR itself says "a noisy lint is a skipped one" |
| `certified_claims` | certified rows cite current manifests | 4 targets, 0 findings | load-bearing (cheap) |
| `current_view --check` | H1 | **Red on `dev` at `087f7213`** | see H1 |
| `proof_cost` | H12 | 0 failing, 3 baseline books | see H12 |
| `host_check` | host names, dynamic | SKIPPED without `FN_ACL2`; says it is not evidence | load-bearing (honest skip) |
| `transcribe_check`, `native_program_check` | R22 | 0 defects; caught two model-less fault points on 2026-09-24 (`8827062d`) | load-bearing |
| `session_depth` | the 2026-09-20 session misses | 0 defects, 38 hand-spelled walks counted | load-bearing (class; about 1 s) |
| `evidence_manifests check` | manifests committed | 978 of 1155 cited runs resolvable; 177 in `LOST.txt` | load-bearing. Cost: 54 archive commits |
| `teeth_check --summary` | R19 | Report only; 156 findings | stilt in report mode (see R19) |
| `harness_check` | caller signatures, arities, waivers | Caught `bp-app` dropping the ingress argument and `config.lisp` passing state-free functions (`1ac07458`) | load-bearing |
| `host_shape_check` | host multiple-value shapes | 0 findings; the class cost an image build (9c344d1d) | load-bearing (cheap) |
| `build_lists_check` | DTN image loads what it needs | Created today from the DTN image's failed `store init` (`8c63a7df`) | load-bearing |
| SpecBookTieTests | `specs/identity.md` versus books | Created today (`038b6224`) | load-bearing |
| `cite_check --strict` | phantom citations in books and tests | 0 in books; 179 reported elsewhere, including this audit's H11 phantom (`tools/iteration_bench.py` in how-we-work) | load-bearing |
| `reach_check --strict` | R17 | 40 orphans, all baselined | load-bearing |
| `green_check --summary` | R28 | 767/767 green | load-bearing |
| `theory_check` | R29 | 45 books above the codec layer still open a codec | load-bearing |

## Summary of cuts

| # | Verdict | Replacement or deletion | What makes the old text unnecessary |
| --- | --- | --- | --- |
| R5 | wrong | "A claim names its coordinate (source, proof manifest, qualified image, deployment); `planning/current.md` keeps the four apart." | `current_view.py` columns |
| R7 | stilt | delete; D27's representation bullet carries it | D27 |
| R11 | wrong | "Bound the work and allocation one request may cause before consuming it; a length limit is a per-request work bound set so that no profile the operator can write is capped below it." | D27 |
| R18 | stilt | one clause: "`ledger.py --check` refuses a flagged citation; name restatements `-unfolds`/`-by-definition`." | ledger suspect detector in `make check` |
| R19 check | stilt | `teeth_check --strict --changed-since REV` in the merge routine | teeth_check |
| R28 clause | wrong | "A commit message is not certification; `green_check` is." (replaces "Never `git log`.") | green_check |
| R30 | stilt | generate `docs/prefixes.md` from the ledger, or delete the rule | ledger.py defun inventory |
| R31 | stilt | move it to the coordinator's merge routine | merge routine |
| R32 | stilt | delete | roles retired 2026-09-24 |
| R33 (board) | stilt | delete the swarm board; `now.md` lanes plus LANEDUMP | `now.md` |
| R36 | wrong | "Certify the roots you changed and what includes them." | 2026-09-23 correction |
| R37 | stilt | delete | R19 teeth, labs |
| R38 | stilt | "update the capability's obstruction and next-gate lines in `current-view.json`" | current_view |
| R39 | stilt | "cite the committed manifest" | evidence_manifests |
| R41 | wrong | brief from `now.md` and `current.md` | current_view |
| H1 | wrong mechanism | regenerate `current.md` in the same commit as a manifest archive; `current_view --check` runs last in `make check`; freeze the scoreboard cells | current_view |
| H7 | wrong | E8's text: one cut per wave, one qualification lane, never re-qualify interim cuts | ember's correction |
| H9 | stilt | "the slot pool and `swarm-build` are the limits" | `tools/acl2` slots, swarm-build, D26 |
| H10 | stilt | move to the `proof_repl.py` header and runbooks | tool header |
| H11 | wrong | drop the phantom `tools/iteration_bench.py` | nothing: it does not exist |
| H14 | stilt | delete the F1 to F5 table | the rules it restates |
| H18 | wrong | delete "reports when its run is submitted" | R28 |
| P1 | wrong as run | exempt `-is-` correspondence equalities; `make check` prints counts only | ledger lints |

Tightened, not cut: R3 (IDs assigned at merge with `next_id.py`), R17 (name
the host function, not a line), R23 (resolve generated conflicts by
regenerating), H12 (a 10 % noise band), H17 (merge `dev` only for a landed
dependency). Added to the tree from memory: E1, E2, E8, E9.

Sizes: the proposed `AGENTS.md` is 897 words (today 1576); the proposed
how-we-work is 628 words (today 2560). Nothing in section A is cut.

---

## Proposed `AGENTS.md` (for ember to accept or edit; not applied)

```markdown
# Working on fn

Read [the project guide](docs/README.md), [architecture](docs/architecture.md),
[decisions](planning/decisions.md), [now](planning/now.md) and
[the current view](planning/current.md) before substantial changes, then the
specification for the affected subsystem. How lanes work is
[how we work](planning/how-we-work.md).

## Scope and authority

- fn is an ambitious, design-first project: a specialized store and an
  executable ACL2 news core, served over NNTP and carried over BP for
  disconnected operation. Preserve that scope; advance it in small complete
  steps.
- Agreed directions live in the decision register. Proposals and open
  questions are not requirements. This file adds no approval gate.
- Requirements live in `planning/requirements.json`, proof targets in
  `planning/proofs.json`; IDs are stable and the coordinator assigns new
  ones at merge (`tools/next_id.py`). Change the registry, the specification
  and the scenario together.
- Preserve the supplied RFCs and cite their sections; distinguish an RFC
  requirement, a stronger fn guarantee and a local policy.
- A claim names its coordinate: source revision, proof (a committed
  manifest), qualified image, deployment. `planning/current.md` keeps the
  four apart; none implies another.

## Implementation discipline

- ACL2 owns every decision: identity derivation, bounds, group tables,
  charges, framing, integrity trailers, reply lines. Host code performs I/O
  and calls it; Python and host Lisp never compute a value ACL2 also
  computes or compares. What ACL2 cannot decide yet is an open registry
  item, not a host function.
- Bound work, never data (D27). A constant that limits the size or number
  of what a store holds is a defect; such bounds are the operator's, in the
  store profile, with codec widths that never cap below any profile.
  Constants that bound work per request stay and say so.
- The executable path uses concrete representations (D27). Octet lists are
  the logical model; every boundary the host calls has a concrete twin with
  a guard-verified correspondence theorem to the list definition, measured
  on the same image before and after.
- Parsing external data never invokes the Lisp reader or evaluator. Bound
  the work and allocation one request may cause before consuming it.
- Octets, parsed fields, content identities, Message-IDs and local article
  numbers are distinct types.
- Durable acceptance comes only from persisted state, never from a socket
  write, a transport ACK or an in-memory update. An ambiguous persistence
  failure is a recovery event: never roll back silently or keep mutating.
- Keep conflicting evidence and its provenance. No last-writer-wins on
  wall-clock time; never merge local NNTP numbers globally.
- No `skip-proofs`, `defaxiom` or trust tags toward a completion claim; a
  trusted facility is isolated in the trust boundary with its assumptions.
- An abstract cryptographic model proves nothing about real signatures,
  hashes, disks or a peer's honesty.

## What makes a claim

From [the 2026-09-18 review](planning/review-2026-09-18-independent.md) and
the 2026-09-22 proof-engineering review. Green is not true.

- **The subject is the function the host calls.** A theorem about another
  function counts only with a named theorem equating the two. Name the host
  function that calls the subject; `current_view.py` finds the line, and a
  line number never goes into a book. A theorem about a branch the composed
  machine cannot reach is marked `unreachable-in-composition` or the branch
  goes. (`reach_check --strict`.)
- **Cite keystones.** `ledger.py --check` refuses a flagged corollary or
  restatement; name those lemmas `-unfolds` or `-by-definition`.
- **Teeth ship with the theorem**: a reachable non-degenerate witness and one
  `must-fail` per hypothesis, separating by more than the weakest clause.
- **A named assumption is an `encapsulate`** with a local witness in
  `books/assumptions.lisp`, and the theorems that use it mention it.
- **Every process-death cut is a model crash point.**
  (`transcribe_check`, `native_program_check`.)
- **No whole-state revalidation on a served path**: carry the invariant in
  state and prove it preserved.
- **Uncertain, refused and accepted stay distinct** at every boundary,
  exit codes and test expectations included.
- **Counts are generated** (`tools/ledger.py`, `tools/current_view.py`);
  prose carries the property, its hypotheses and its scope. A conflict in a
  generated file is resolved by regenerating it.
- **Quote the pessimistic number with its scope** in the same sentence; the
  collision figure, not the second-preimage one.
- **Behaviour and its invariants land together.** A lane certifies what it
  changed and what includes it before it reports, and cites the manifest.
  A commit message is not certification; `green_check` is.
- **Open a codec in a hint**, never at the top of a book (`theory_check`).
- A proposed theorem is not proved; an admitted definition is not
  guard-verified; passing tests are not a proof.

## Working together (ember's corrections)

- Never `git stash`, reset or check out the shared `~/dev/fn` checkout; other
  agents are live in it. Work in your own worktree under `build/lanes/`;
  the coordinator merges.
- About ten useful lanes; claims announce intent and lock nothing. Lanes
  coordinate through their `LANEDUMP.md`; the coordinator names each lane's
  model in its brief.
- Orient to the plan, not to another audit. Waves, not per-cut
  qualification: one cut at convergence, qualified once by one lane while
  the next wave runs; a regression the cut finds is the next wave's fix.
- Run the narrowest thing that could refute you: affected roots, never a
  lane `--closure`. Reuse matching evidence; coordinate expensive runs.
- On hbox: `swarm-build` around every build; `free` lies (read `arcstats`
  and RSS).
- No deployment, publication or messaging side effects unless the task
  authorizes them; the live node is protected.
- Before ending: registries and `current-view.json` accurate; report what
  changed, what ran and what remains open.
```

## Proposed `planning/how-we-work.md` (for ember to accept or edit; not applied)

```markdown
# How we work now

A lane is briefed from this page, [now](now.md) (dev, the goal, the lanes)
and [the current view](current.md). Release scope is
[the trajectory plan](plan-2026-09-22-trajectory.md) §0 to §2. The rules of
[AGENTS.md](../AGENTS.md) apply in full; this page is the loop.

## The loop

1. **Start from ground truth, in your own worktree.** The brief names the
   step, the functions and books, the host function that calls the subject,
   the theorem statements, the teeth owed, the box and the evidence file,
   with absolute paths and pasted signatures. A brief that describes a
   signature instead of pasting it is a question to ask first.
2. **Iterate in a live session.** `tools/proof_repl.py start NAME BOOK
   --upto EVENT`, then `send`; 300 s bounds a discovery attempt, and a
   timeout is a finding with the theorem named. An admitted form is not a
   certificate.
3. **Certify incrementally.** `farm.py submit <box> --affected-by <book>` (or
   the changed books and tests as plain roots): cached books install, the
   rest certify. Never `--closure` for lane work. Wait with one background
   command and do other work.
4. **Report what the tools say**: theorem statements, host function, teeth
   book, the `green_check` line, run id and committed manifest, evidence
   file, and what you did not do.
5. **The coordinator merges as lanes land**, regenerates the ledger and
   `current.md` in the merge (never hand-resolving a generated file),
   assigns new registry IDs, runs `make check` and
   `teeth_check --strict --changed-since`, removes the lane's worktree, and
   submits one plain-roots run of `dev`'s head so the cache stays current.
   A lane merges `dev` mid-flight only for a landed change it needs, then
   recertifies what that moved.
6. **Waves converge once.** At convergence, one cut: a fresh closure and one
   qualification lane over the whole set while the next wave runs. Never
   re-qualify interim cuts. A regression the cut finds is the next wave's to
   fix; deploy when green.

## Width and who proves

Start around ten lanes; add one only for substantive work. Claims announce
intent and do not reserve files; lanes that overlap agree on the interface
and on who assembles the combined change, then certify its bytes. A lane
whose brief says implement-only hands a failed proof (source, event, log)
to the proof owner rather than searching for it.

## Proof cost

- A book over ten seconds at two jobs is a defect (D26). `proof_cost` fails
  on a book not in the baseline above 11 s, or on a baseline book 25 % over
  its figure; 10 to 11 s prints `NEAR`. The baseline only shrinks, by proof
  work: read the certify log's per-event times and `Rules:`, one
  instrumented session at most, never raise a timeout or weaken a statement.
- Aim for under three minutes from edit to certified verdict; record queue,
  install, proof and total time when you claim a speedup.

## Boxes

`swarm-build` around every hbox build; `tools/acl2` for every ACL2 started by
hand (it takes a slot); the machine-wide slot pool is the limit, never
bypassed; no bare `&` in a lane shell; `free` lies on hbox; a farm run's
`--remote-root` is absolute; certificates install from the box's cache,
never from a live worktree. The box-specific environment for a remote REPL
and the full trap list are in the `proof_repl.py` header and the runbooks.

## What a step is

DONE or NOT. DONE means the theorems over the host-called subject exist with
teeth, the affected closure is green at the current bytes, the behaviour is
observed on an image, and the evidence file exists. A step that would need a
`partial` row is two steps. A branch someone else left is an input to a
brief, never a thing to resume. Intermediate reds stay visible and never
excuse a weaker statement or a host twin.
```
