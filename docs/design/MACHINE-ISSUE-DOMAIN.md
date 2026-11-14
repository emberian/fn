# Per-kind issue continuations

`fn2-machine-issue-result` was unreachable in composition. Its unrestricted
kind domain was incompatible with the TLS admission kind's zero-descriptor
budget. Remove its definition, preservation event and unused cost row; retain
the actual generated per-kind issue paths and their unchanged guards.

The frozen b2 callback-A guard checkpoint requires the updated row's kind to
be different from 6. The helper's guard only requires core well-formedness and
natural bytes at most 4096. Its successful branch writes pending/wait-reason,
then calls `fn2-machine-finish` with one descriptor. This cannot satisfy every
kind's actual charge guard: the TLS admission budget allows no descriptors.
A theorem about preservation of row identity would not establish the missing
kind restriction, and a proof-search failure alone is not a counterexample.

The source inventory finds the helper only in its definition, preservation
form and cost declaration, including host and simulator sources. More
substantively, `fn2-arms-steps` handles `:issue` by generating the actual
operation call followed by success/exhaustion/refusal branches. It rejects
`:issue` in a zero-descriptor kind. `fn2-arms-terminal` handles `:wait` by
writing pending/wait-reason and generating the kind-specific returned charge.
Neither path consults or constructs the obsolete helper name. Listener,
echo and scribe source declarations use these paths directly.

`tests/machine-issue-domain-unit.lisp` checks the resulting admitted world,
not just source references: no old function or cost row, no reference in any
admitted unnormalized function body or declared machine arm body, and actual
listener/echo dispatchers remain guard compliant. Its concrete control starts
with the tiny initialized core, changes a valid directory row to the real TLS
admission kind, checks the complete old core/type/byte guard, performs the
original pending/wait writes, and checks the actual generated finish guard
is false for the reported one descriptor. It evaluates that guard rather than
calling FINISH outside its valid domain. This control addresses the old
helper's unrestricted domain; it does not claim that the constructed row is
reachable through the supported admission transition.

Source repair and controls are prepared; the narrow author gate is pending.
The frozen b2 callback-A predecessor audit reports 116 qualified dependencies
and no missing entries under the recorded toolchain. No whole closure replay
is needed to check the removed dead definition and surviving A continuations.
