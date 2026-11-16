# Bound generated initializer compilation and reuse accessor proofs

The column generator reduces repeated proof search and the size of compiled
initializer functions while preserving the table representation and initialization
semantics. The generator and existing mixed-field fixture have an exact
[four-book record qualification](receipts/columns-initial-four-record.json).
The whole-UPLOAD experiment below remains diagnostic evidence.

Three changes compose in the owning generator:

- Raw NTH type/bound proofs use the preceding public accessor facts. Their minimal
  theories open the public reader, raw reader, row accessor, NTH and ZP. This
  normalizes NTH at index zero to CAR without reopening array invariants. These
  two hint templates preserve every existing theorem name, hypothesis, conclusion
  and rule class; public facts precede their raw consumers.
- Flat DISABLE operations are batched within existing phases and flushed at every
  theory or LOCAL boundary. Non-theory emitted events retain their order.
- Initialization uses deterministic eight-column helper functions. Each helper
  retains the exact zero-then-size resize sequence; INIT retains extra-field
  clearing and the final ROWS update. This bounds compiler units, not stored rows
  or supported profiles. Each helper is guard-verified, and a generated local
  unconditional INIT-CHUNKS-BY-DEFINITION theorem equates the composition to the
  former direct binding sequence, including off-guard logical inputs.

The source-executed accessor control compares 70 mixed-width/enum columns and
empty/single-column cases against the preceding generator. Exactly 140 hints
change; all other accessor forms match. Separate controls check theory/locality
barriers and flatten initializer chunks at nine boundary sizes, including 70
columns, preserving exact bindings, order and guards.

```sh
git show 4e26763cd:books/columns.lisp > /tmp/columns-raw-facts-baseline.lisp
FN_COLUMNS_BASELINE=/tmp/columns-raw-facts-baseline.lisp \
  sbcl --script tests/columns-raw-fact-controls.lsp
sbcl --script tests/columns-batch-controls.lsp
sbcl --script tests/columns-init-chunk-controls.lsp
```

All three controls pass. A diagnostic with 105 genuinely compiled parents
measured the unchanged whole UPLOAD declaration at 2M steps/60 seconds:
25.70 seconds and 1,353,378 steps. That run was profiling only. The combined
candidate passed its original 2M-step/20-second whole-event gate with zero
refusals, 1,398,770 steps and 20.14 seconds enclosing elapsed time. The result
includes all nine chunk functions, their guards, the equality theorem and the
remaining machine proofs; child events did not receive fresh quotas.

INIT and all nine helper admissions each rounded to 0.00 seconds, versus
2.7–2.9 seconds for the direct INIT. Fresh META constructors checked actual
emitted-form identity except for the declared hint/theory changes and exact
initializer decomposition. They were diagnostic scaffolding and are excluded
from the production patch.

The generator and mixed-field fixture passed actual author admission and record
certification. Root independently checked their four current source keys and
certificate/port/FASL payloads. This does not qualify affected consumers or the
served application. Those require new current-key records and execution; existing
certificates must never be relabeled for changed sources or dependencies.
