# fn2 lean-meta continuation (present state, rewritten whole)

Seat: Opus designer and Lean author, brief `build/coordinator/briefs/LEAN-METATHEORY-20261028.md`.
The contract: `build/coordinator/fn2/LEAN-METATHEORY.md` (a copy at `fn2/docs/design/LEAN-METATHEORY.md`
on the branch).

## Where things are
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/lean-meta`, branch `fn2/lean-meta` from
  `origin/fn2/main` at `137695dfc`. The project is `fn2/meta/` (lakefile.toml, lean-toolchain v4.30.0,
  lake-manifest.json copied from minidregg with Mathlib `1c2b90b1`).
- Lean files: `Fn2/Decl.lean`, `Fn2/Square.lean`, `Fn2/Coherence.lean`, `Fn2/Conservative.lean`,
  `Fn2/Param.lean`, `Fn2/Instances/LayerA.lean` (GENERATED), `Fn2/Instances/LayerAFacts.lean`, root `Fn2.lean`.
- Emission: `fn2/meta/emit/print-registry.lsp` (ACL2 driver), `emit_lean.py`, `emit.sh`,
  `registry.sexp` (the printed world, committed as the emitted model's source). Counts at 137695dfc:
  43 declarations (3 machines, 9 columns, 9 core children, 22 owed), 376 symbols, 31 machine-owned Q1
  cases (22 phases + 9 events); 8 non-registry labels hand-declared in LayerAFacts (flagged).
- Mutation controls: `fn2/meta/emit/mutations/{observes-row,deadline-width,retired-behaviour}.sh`
  with the two non-empty diffs; logs and mutant files in the worktree's `build/lean-meta-scratch/`.
  Results (LEAN-METATHEORY §5): observes-row 17 lines, 31->28 cases, ACL2 also refuses it at
  assembly; deadline-width 12 lines in the 6 carrying rows, no control fails; retired-behaviour
  registry byte-identical (the table-only exporter's measured limit).
- Astra: `build/coordinator/fn2/lean-meta-astra-{1,2,3}.{prompt,md,log,pid}`; sessions 2 and 3 found
  no elaboration failure (a reading, not a build); all their statement corrections and witnesses
  applied except packaging the revision teeth into one statement.
- 62 theorems, 1,379 hand-written Lean lines, 0 sorry, standard axioms only, all elaborated. Pushed: origin/fn2/lean-meta at dddc32d34.

## Builds: the Mac and hbox; no cloud box exists
Ember 2026-10-29: build on the Mac and hbox (under swarm-build) to their utmost; dregg-build and
dregg-ref are gone and not replaced. `cd fn2/meta && lake exe cache get && lake build` is green on the
Mac (618 jobs); `lake env lean AxiomCensus.lean` shows all 62 theorems elaborate with only propext,
Quot.sound, Classical.choice (no sorryAx). Logs: worktree `build/lean-meta-scratch/lake-build-{1,2,3}.log`.
Three first-build reds fixed forward (LEAN-METATHEORY §7).

## Next, in order (once a box exists)
1. Package the revision teeth as one statement (Astra session 2's last open item).
2. The general mixed-pasting schema (HM, both-sided `≈`), about a day (§6).
3. The toy completeness theorem (Mazurkiewicz projections), about two days, only once a fragment's
   interchangeability relation is declared.
4. Emit `fn2-layouts` when B merges; `fn2-squares` with DM1; the executor case source with DM2
   (then delete `nonRegistryCases`).
