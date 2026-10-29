# Scholar continuation (rewritten whole; present state 2026-10-28, deliverable complete)

Brief: `/Users/ember/dev/fn/build/coordinator/briefs/SCHOLAR-20261028.md`. Deliverable: `/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DECISIONS-SCHOLAR.md` (complete). Reported to main as READY.

## State
- All five chapters drafted, attacked by Astra once each (`fn2/scholar-astra-ch{1..5}.{prompt,log,pid,md}`; every codex process has exited; the PID files are stale and may be removed by whoever cleans the directory), and rewritten whole with the attack folded in under **[Astra]** attribution. Verdicts: keep, amended, all five; pasteable wording in each chapter's §6; closing section has the verdict table, the three tradeoffs, the running order, the identity-after-erasure question for ember, and the sources list.
- Literature scouts (two Opus agents) done; ~115 files added to `~/paperbin`; plus `lee2015-rifl-implementing-linearizability-at-scale.{pdf,txt}` fetched by the scholar. Nothing downloaded was executed.
- Scry probes (free): HN 9936711, 47819305, 26756568, 43928135, 36330508.

## If a successor is asked to continue
- A second Astra round per decision is allowed by the brief and was not needed; if ember wants one, the method is below. The most useful second round would be on chapter 4 (the witness protocol and the statement-about-the-previous-cut construction) since it changes the format most.
- Open items the report names but does not decide: erasure as a sixth decision; identity after erasure (ember's call); the interoperability profile for checkpoints (ML-DSA-44 vs D09's ML-DSA-65); the MLS client integration protocol.
- The `STORAGE-DESIGN.md` §4 paste is a coordinator act, not the scholar's (read-only in the repo).

## Method used (per chapter)
Draft (six sections) → `nohup codex exec -C /Users/ember/dev/fn -m gpt-6-astra --sandbox read-only --skip-git-repo-check --output-last-message /Users/ember/dev/fn/build/coordinator/fn2/scholar-astra-chN.md "$(cat fn2/scholar-astra-chN.prompt)" < /dev/null > fn2/scholar-astra-chN.log 2>&1 & echo $! > fn2/scholar-astra-chN.pid` → background until-loop on the PID → fold with attribution, record disagreements → save → rewrite this file. No run hit "model at capacity".

## Rules in force
Read-only in the repo (build/ is git-ignored; deliverable and scratch under build/coordinator/fn2/ by the brief); nothing on hbox; downloads into ~/paperbin only, never executed; never git stash / git add -A; never kill by pattern: stop a process only by the PID in its PID file, and only if asked; no key leaves a tool call; no command over a minute of CPU.
