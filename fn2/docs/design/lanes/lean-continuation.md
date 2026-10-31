# fn2 Lean metatheory seat continuation (present state, rewritten whole; 2026-10-31 night, the second Opus seat, distilled once)

Seat: Opus, `fn2/meta` (the aligned registry, the shallow embedding, the measure, the pathway). Brief: the work order of 2026-10-31 in `LEAN-METATHEORY.md` §-1; the rulings in its §12. Worktree `/Users/ember/dev/fn/build/lanes/fn2/lean` (branch `fn2/lean`, pushed to `dev` and `fn2/lean`). The flow is `WORKFLOW-20261031.md`: a commit by path, its Lean builds (`lake build` on the Mac), its emitter runs in ACL2, its author read the diff; push; READY to main with the sha. Nothing here gates a seat; performance is published. Astra: `codex exec -m gpt-6-astra -s read-only -C ~/dev/fn`, once per design.

## Rulings in force (main, 2026-10-31; §12)
- Decision 6, yes: the deliverable proves the served C implements the declaration, memory safety and bounded termination included. PW3 (generator correctness per arm) is this seat's next milestone.
- Decision 7, yes: an expression reader independent of the generator's rewrite (`fn2-arms-expr`) before PW3 is called a theorem.
- Order: (1) the frame half of the measure, **done, f630e8db6**; (2) the cursor joins the measure when D pushes it (main sends the sha; print from a closure that includes `cursor.lisp`; `reference.lisp` need not grow); (3) the independent expression reader, **built, 220356b42 (dev dc81b66d0)**, its tooth running (below); (4) PW3, **stated in Lean (`Fn2.Pathway`) and in §9.3**, Astra-read once still owed.

## State (dev dc81b66d0; books measured at 24fce1ecd; the lane worktree certified at f630e8db6)
- Commits: 3890af6f8 ALIGN, 9363c388e EMBED, 6903646bc MEASURE, 6e4e6006e Astra-4 fixes, f630e8db6 frame, 220356b42 reader + PW3 statement.
- The lane worktree is NOT merged with dev's ca3aded2b (B's commit.lisp): it was pushed to dev through a temporary worktree (`build/lanes/fn2/lean-push`, removed) because the mutation below is certifying in it. Merge origin/dev into the lane after the mutation restores `machine-arms.lisp`.
- Running: `fn2/meta/emit/mutations/rewrite-index-constant.sh` (PID file `build/lean-scratch/mutation-rewrite.pid`, log `build/lean-meta/mutation-rewrite/run.log`): mutates `fn2-arms-index-constant` (`*K-ADMISSION-ORDINAL*` read as KIND), certifies reference and the simulator's books, records with the mutant (`arms-record-mutant.sexp`), prints, shows what the shared rewrite makes of echo's draining ordinal (`shared.log`), restores, re-certifies, measures. Expected: generated equal on the mutant record, interp differs on echo's draining calls that free. Then: commit the script, §6's text, READY (3).
- Measure on `build/lean-meta/arms-record.sexp`: 963 calls, interp 963, generated 963, guard 963, frame 963; READ 266 expressions, 0 refused.
- Teeth: `generator-wait-steps.sh` (generated 824), `frame-dropped-child.sh` (frame 938), `rewrite-index-constant.sh` (running).
- LEAN-METATHEORY.md (untracked, coordinator tree) updated in place: §4.1, §5 (the reader), §6 (frame), §8.4, §9.2's PW3 row, §9.3 (PW3 stated), §11's table.
- The pipeline: `fn2/meta/emit/emit.sh` (print-world.lisp → `emit/world.sexp`, `emit_lean.py` → `LayerA.lean`, `emit_embed.py` → `LayerAWorld.lean`, `LayerAKinds.lean`); `tools/acl2 --timeout 3600 < fn2/meta/emit/record-arms.lsp`; `cd fn2/meta && lake build && ulimit -s 65520 && lake exe fn2-measure ../../build/lean-meta/arms-record.sexp`. LayerA.lean is left at its 24fce1ecd stamp (re-emitting changes only the stamp and costs an 11.5-min LayerAFacts rebuild).

## Next
- Finish (3): the mutation's result into §6, commit the script, READY.
- (4): Astra reads §9.3 and `Fn2/Pathway.lean` once (`codex exec -m gpt-6-astra -s read-only -C ~/dev/fn`), then the proof: total reader and evaluator, dispatch as a `match`, per-arm symbolic evaluation, echo first.
- (2) when main sends the cursor's sha.
