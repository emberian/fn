# fn2 Lean metatheory seat continuation (present state, rewritten whole; 2026-10-31 night, the second Opus seat, distilled once)

Seat: Opus, `fn2/meta` (the aligned registry, the shallow embedding, the measure, the pathway). Brief: the work order of 2026-10-31 in `LEAN-METATHEORY.md` §-1; the rulings in its §12. Worktree `/Users/ember/dev/fn/build/lanes/fn2/lean` (branch `fn2/lean`, pushed to `dev` and `fn2/lean`). The flow is `WORKFLOW-20261031.md`: a commit by path, its Lean builds (`lake build` on the Mac), its emitter runs in ACL2, its author read the diff; push; READY to main with the sha. Nothing here gates a seat; performance is published. Astra: `codex exec -m gpt-6-astra -s read-only -C ~/dev/fn`, once per design.

## Rulings in force (main, 2026-10-31; §12)
- Decision 6, yes: the deliverable proves the served C implements the declaration, memory safety and bounded termination included. PW3 (generator correctness per arm) is this seat's next milestone.
- Decision 7, yes: an expression reader independent of the generator's rewrite (`fn2-arms-expr`) before PW3 is called a theorem.
- Order: (1) the frame half of the measure, **done, f630e8db6**; (2) the cursor joins the measure when D pushes it (main sends the sha; print from a closure that includes `cursor.lisp`; `reference.lisp` need not grow); (3) the independent expression reader, **built, 220356b42 (dev dc81b66d0)**, its tooth running (below); (4) PW3, **stated in Lean (`Fn2.Pathway`) and in §9.3**, Astra-read once still owed.

## State (dev cadae2cf3; books measured at 82eb2bfc2 with a466488fe)
- Commits (latest first in the next line): 7aafd8334 PW3 1/n (total readers and evaluator; dev 5f0898ea8).
- Commits: 3890af6f8 ALIGN, 9363c388e EMBED, 6903646bc MEASURE, 6e4e6006e Astra-4, f630e8db6 frame, 220356b42 reader + PW3 stated, 40387cf53 Astra-5 + step reader + reader tooth, 2e4e7c7a7 cursor measured.
- READY sent for (1), (3), (2) and PW3's statement; Astra session 5 done (`lean-meta-astra-5.md`).
- Measure: echo and scribe 963/963/963/963 (record `build/lean-meta/arms-record.sexp`, 24fce1ecd's run); cursor 462/462/462/462 (`build/lean-meta/cursor-record.sexp`, 27 functions); READ 711, 0 refused. `:repeat` still unrecorded.
- Teeth: `generator-wait-steps.sh` (generated 824), `frame-dropped-child.sh` (frame 938), `rewrite-index-constant.sh` (interp 635/637 on the mutant record).
- **Where things run (main, 10-31 evening):** ACL2 (certify, print, record) on hbox in `~/fn2-lean-meta` (a clone at 82eb2bfc2 with reference and cursor-unit certified; ACL2_SYSTEM_BOOKS=$HOME/acl2-8.7/books FN_ACL2=$HOME/acl2-8.7/saved_acl2; certify under `swarm-build`; swarm-build returns at once, so the PID file must name the inner `sh`, read from /proc). The Mac keeps `lake build`; copy `fn2/meta/emit/world.sexp` and the records back with scp, then run `emit_lean.py` and `emit_embed.py` on the Mac.
- The lane worktree's own certs are at 82eb2bfc2 too (certified on the Mac before the ruling).
- Homebrew `node` is broken on the Mac (libsimdjson 34 vs 36): run codex as `/opt/homebrew/lib/node_modules/@openai/codex/node_modules/@openai/codex-darwin-arm64/vendor/aarch64-apple-darwin/bin/codex exec ...`.

## Next (main's order of 10-31 night)
1. PW3's proof (§9.3): step 1 done (7aafd8334). Next: per-name dispatch and guard equations emitted beside `fnTable`/`guardTable` (`fns "F" args = some (F args)` as simp lemmas); the checked-write (`put`), row-read and frame lemmas over list-valued stobjs, once; then echo's arms by symbolic evaluation (simp with the step's equations; `decide +kernel` handles the concrete readers), then scribe's. Note: `Term.eval` is well-founded, so it unfolds by `simp [Term.eval]`/its equation lemmas, not `rfl`.
2. A recorded scenario for `:repeat`, the park variants and a kind's own `:stops` (`:wake-row` is now recorded through the cursor's `hand`): drive `fn2/tests/machine-arms-unit.lisp`'s probe kinds (fn2-arms-probe: kind stops, :wake-row + :goto close with an :issue, :repeat in :loop, accept-hand in :take) from a raw-Lisp driver over live stobjs (create, init with the columns' `-init`, set row fields, call the child-form functions) under the recorder; parks need a probe kind of our own declared after `reference` (:park :pool, a declared wait without parker such as :sealable, one with a parker). Print from a world including reference and the probe book.
3. Re-record the cursor when main sends D's next sha (hbox: pull, certify reference + cursor-unit under swarm-build, print, `record-cursor.lsp`; scp back; emit and measure on the Mac).
