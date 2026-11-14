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

The author gate passed against the exact frozen b2 predecessor world: 116
qualified books/FASLs, no misses, artifact set
`c123121efdcc62b18329169ffc7d172b13702b8d18507fba309dfca6e37e9b66`,
toolchain `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`.
Assembly-rows-other-2 key:
`41d912fb6db7eac9553b57b5717b5ba21e9a814bdaa3f28978bd655985d7a7f3`.
The 14 retained A macro forms were byte-identical to b2. This prototype
removed the inherited cost row's value locally; current source deletes its
declaration. No runtime function was redefined.

Admission prerequisites passed in 3.17 seconds/16,975 steps. The initial
inventory helper used EQ on unrestricted atoms and failed its own guard;
EQUAL repairs that fixture defect. All six corrected control forms passed,
including the complete old-guard counterexample. The first ten surviving A
forms passed. The aggregate listener macro reached the 20-second time cap;
its whole event rolled back. Its exact generated PROGN was then split into
53 events, each with the original 20-second/two-million-step cap, and all
passed in 22.58 seconds/841,125 steps. No proof statement changed. Listener
run, echo wrappers, and echo run then passed in 16.49/7.33/20.52 seconds
(the last includes 17.72 seconds proving), with 1,654,366/364,820/1,795,874
steps respectively. The final live caller/registry/generated-dispatch and
actual dispatcher guard-compliance assertion passed in 0.1 seconds.

Scope was a detached 2 GiB cgroup (kernel `memory.max=2147483648`), outer
600 seconds, session `callback-guard-b2`. The first fixture refusal was
retained in the supervisor's original return code 1; corrected later RPC
receipts above passed individually. Stop returned zero; outer/server/ACL2
PIDs 579935/580000/580004 were confirmed absent. No compute remains held.
Forge logs: `/tmp/finish-callback-guard.log`,
`/tmp/finish-callback-guard-controls-retry.log`,
`/tmp/finish-callback-listener-events.log`,
`/tmp/finish-callback-remaining.log`, `/tmp/finish-callback-inventory.log`.
Payload hashes and exact source comparison receipt are in
`/tmp/finish-callback-guard/receipt.json`.

This is an author gate, not current-source certification. New source changes
ancestor keys, including the deleted cost/macro declarations; the current
closure must be inventoried before a coordinated record run. No scribe,
full cursor, or application closure was replayed in this author gate.
