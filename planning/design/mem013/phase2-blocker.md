# MEM-013 phase 2: signed HWM statement is false for the draft

Status: blocked at the user's explicit stop condition, 2026-10-07.
Author: Codex, lane n-mem13. Source: c7271cbd5.

`fn-his-place-run-keeps-w-length` is unconditional. The unchanged draft
admits a call whose input word length is 0 and output word length is 2049.
ACL2 proved the concrete counterexample on persvati (750 prover steps,
0.02 seconds, zero refused forms). This is an admitted counterexample,
not an inference from a failed attempt to prove the signed statement.

The witness supplies a first cursor `(0 2047 nil)` and starts `(1 2 3 4 5)`
with `np = 6`. Its next cell triggers a flush at word 2048.
`fn-his-place-row` checks `adt-placement-ok` against `np`, but does not
check the actual store length or the cursor's consistency. `fn-hp-x-put`
then logically extends the empty word list through `update-pgs-wi`.
Its existing `fn-hp-x-put-lengths` theorem requires bounds. The signed
HWM statement has no hypotheses; malformed cursors and insufficient stores
are therefore in its domain. Adding guards alone cannot establish it.
This witness does not establish a failure on a guarded served call.

Recommendation for the resumed implementation: preserve the signed statement
and give out-of-bounds writes a total behavior that leaves the store unchanged,
with a proof that valid placement is unaffected. A row-level refusal would
also have to account for the cursor's actual page and buffered word count.
No implementation or signed statement was changed after finding the blocker.

Generator inspection completed before the diagnostic: `def-cursor/output`
and `def-cursor/batch` implement output/control budgets, not this mutable
store plus accumulator shape. This checkout's `def-loop.lisp` has no
`:resume` option. Its `:fold` shape does not provide a resumable quantum.
No generator, host, book, interface, or deletion work was undertaken after
the counterexample was confirmed. All nine signed claims remain unproved
in this lane; only the HWM claim was refuted here.

## Reproduction (persvati only)

Run from this lane. These commands use the exact draft definitions; no
handwritten implementation twin is needed. No certification is performed.

```sh
timeout 180 python3 tools/proof_repl.py start n-mem13-hwm-repro books/history-image-row-step --through fn-his-row-begin-appends-history --host persvati --cached-only --limit 10
timeout 60 python3 tools/proof_repl.py send-range n-mem13-hwm-repro planning/design/mem013/history-image-place-draft.lisp --from fn-hp-x-row --through fn-hp-x-row --host persvati
timeout 60 python3 tools/proof_repl.py send-range n-mem13-hwm-repro planning/design/mem013/history-image-place-draft.lisp --from fn-his-rc-put --through fn-his-rcs-put --host persvati
timeout 60 python3 tools/proof_repl.py send-range n-mem13-hwm-repro planning/design/mem013/history-image-place-draft.lisp --from fn-his-place-row --through fn-his-place-run --host persvati
timeout 60 python3 tools/proof_repl.py send-file n-mem13-hwm-repro planning/design/mem013/keeps-w-length-counterexample.lisp --host persvati
timeout 60 python3 tools/proof_repl.py stop n-mem13-hwm-repro --host persvati
```

Original diagnostic session: `n-mem13-phase2`, persvati,
`fn-gates/n-mem13-repl`. Its five definitions were extracted unchanged
from the draft. Diagnostic tail:

```text
ok      #1 defthm m13-keeps-w-length-counterexample: ACL2 time 0.02 s; prover steps 750; elapsed 0.0 s
[total: 1 forms, 0 refused; ACL2 time 0.02 s; prover steps 750; elapsed 0.0 s]
```

The requested farm, host, interface, and teeth gates were not run: this
is a statement blocker, not a READY implementation or certification claim.
