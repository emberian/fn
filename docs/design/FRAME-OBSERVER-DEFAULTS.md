# Public observer defaults for frame proofs

Status: pending coherent-batch qualification. No runtime changes are proposed.

The columns candidate `379d3b77a` changes only default proof hints in
`fn2-columns-preservation-facts`. A frame equality keeps its observer opaque
when neither a per-spec hint nor a nonempty caller hint is supplied. Explicit
per-spec hints, including NIL, retain precedence. The generated theorem's
antecedent, conclusion and rule classes are unchanged.

`tests/columns-frame-opacity-unit.lisp` contains exact generated-form controls
for direct, CAR and MV result projections, unconditional frame statements,
conditional non-frame statements, rule classes and every hint override. It
also checks actual opaque-callee composition. These ACL2 controls are unrun;
source parsing and secrets checks passed. Changing columns affects its
transitive consumers, so qualify the focused fixture first and include the
foundation change in a coherent application freeze, not a live source overlay.

## Outstanding shape-macro consumer

`fn2-fc-shape` in `books/format-check.lisp` has the same abstraction-boundary
problem but does not call `fn2-columns-preservation-facts`. It generates
TYPE/WFP/ROWS conjunctions from its `outputs` argument and disables the type
and WFP predicates in its proof hint, but leaves ROWS observers enabled.

The actual consumer `FN2-RUN-SEAL-STEP-SHAPE` in `books/runs-page.lisp` failed
against source `8677da3e9`: its remaining pool-row equality expanded to raw
NTH through MV-NTH 4 of `FN2-FORMAT-RUN`, preventing use of the public
`FN2-FORMAT-RUN-SHAPE` row equality. The other five row observers were already
locally disabled. Candidate `22154548f` adds the missing pool observer to that
existing LOCAL theory event; the complete runs-page book subsequently passed its 26-book record gate and
was integrated at `2e875f9b7`.

The shared repair should derive `(TABLE-ROWS ...)` observer symbols from the
same output table names used by `fn2-fc-shape-claims` and add those symbols to
its existing disabled theory. Preserve the macro's complete generated
antecedent/conjunction and existing predicate/length exclusions. Do not add
input recognizer hypotheses to unconditional frame facts, replace the served
subject, or make the caller unfold FORMAT-RUN.

Before qualification, add controls comparing the entire old/new theorem AST
with only the hint removed, checking direct and multi-value output mappings
and all output observer exclusions, and proving a small actual opaque-callee
shape composition. Keep this in a separate source candidate until the current
runs-page gate terminates; changing format-check invalidates its descendants.

## Prepared shared shape repair

The next-batch source now implements `fn2-fc-shape-row-observers` and
`fn2-fc-shape-event` in format-check. The existing macro delegates to the
new event producer. Its theorem template is exactly the old macro template;
only its hint appends the declared output observers to the existing theory
exclusions. The existing claim producer and every runtime function, guard and
shape instance are unchanged.

`tests/test_fc_shape_observers.py` passes two source controls for exact old
statement-template identity and actual macro-to-producer connection. A separate
source audit confirms that every other pre-existing top-level form is identical.
`tests/format-shape-observers-unit.lisp` is prepared but unrun: it asserts exact
complete direct/MV/B3-word-length statements, complete hint generation including
an output table absent from the old fixed list, and actual guard-verified
opaque-callee shape composition using the real fields table. No ACL2 job has
been launched for either pending generator change.

Qualification roots are `tests/columns-frame-opacity-unit` and
`tests/format-shape-observers-unit`, followed by the actual runs-page consumer at
the coherent new foundation freeze. Query exact closure/cache keys after that
freeze; neither the earlier runs-page record nor a source test qualifies these
new generator bytes.
