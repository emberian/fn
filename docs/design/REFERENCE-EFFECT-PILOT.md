# Selected callback effects — source pilot

`books/reference.lisp` now obtains the callback result from
`fn2-selected-machine-run-ref-effect` and threads its appended literal FIFO
carrier through ordinary wake and self-tail handling. The semantic effect is
performed at the actual `fn2-core-scheduler-wake` call point. Diagnostic trace
records and native queue snapshots never supply the FIFO result.

`reference-selected-dispatcher` generates a named program from the current
`fn2-machine-run` body and its direct attachment selections. Its by-source
formula, guards, ABI, complete transitive source census and final current-world
seal describe the selected program. They assert no logical equality between an
old constrained stub and an attachment. Remaining stateful attachment calls
refuse the seal. `reference-selected-effects` then lowers that selected program,
retaining every original result position and appending FIFO last. Its complete
result obligations remain owed.

The original `fn2-turn-refinement` H/C is unchanged. Its reference call has
changed, so historical certification is not current qualification. These source
candidates have passed strict parsing and source checks only; they have not
been admitted or executed.

The first narrow executable questions are:

- `tests/reference-effect-query-unit`: actual `fn2-identity-decide` and its
  generated reference counterpart, from two actual query starts and initialized
  full typed/WFP/R state, compared after every step. The final close must append
  the owner independently of trace being disabled or lost, retain a distinct or
  identical ordinary wake, and preserve every other core component through R.
  Bounds refusal checks complete actual-core retention. Discarding just the
  returned FIFO must falsify the original post-R while all scalar/core results
  are retained. This is callback-operation coverage, not a served txn-turn
  reachability proof.
- `tests/reference-effect-query-last-unit`: two aliased real query pins,
  actual raw release `2 -> 1 -> 0`, exact complete core and LAST result,
  followed by zero-count refusal. An executed wrapper suppresses only LAST;
  the second close must fail the complete tuple oracle while every state cell
  and CODE still match. Pool dispatcher state equality alone is insufficient.
- `tests/reference-effect-partition-control`: a defensive shared-tail input
  attempts to establish the original complete paired-domain H before native
  and literal enqueue. Its two principals share one ID; appending a fresh ID
  may invalidate another principal's concrete FIFO. This is an unexecuted
  counterexample candidate, explicitly not an initialized reachable witness.

The last question is material to a universal proof: queue partition and
ownership must be established from initialization and preserved by operations,
not silently added to the old owed premise. A failed proof search or a parsed
assertion is not a counterexample.

The lowering generator must reconstruct legal nested stobj scopes and preserve
all raw multiple-value results, including query release LAST. Those emitted
program controls and verified reuse of staged generated dependencies belong to
the shared lowering generator. A source record is not their admission.

After that narrow gate, connect an actual admitted upload/transaction progression
to the selected dispatcher and test the same whole-result relation there. Direct
query helper controls do not establish served dispatcher reachability, and the
selected-source seal does not establish host execution correspondence.
