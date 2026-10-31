# fn2

The bottom-up, semantics-first rebuild of fn: the persistent event log between systems, built in place here and swapped to the repository root when it serves. Start at `docs/design/FN2-ORIENTATION.md` (ember's words, the rulings, where the tree is, the order). Each layer's own decisions as built: `docs/<layer>.md`. Owed keystones, written and unproved on purpose: `docs/OWED.md`.

## What is here
- `books/`: the ACL2 books. The declaration forms (`columns.lisp` `defcolumns`; `machines.lisp` and `machine-arms.lisp` `defmachine` with its step language; `arms.lisp` `defcost`; `layout.lisp` `deflayout`; `runs-schema.lisp` `defrunschema`; `declare.lisp`, `owed.lisp`, `squares.lisp` the registry and the obligation store); layer A's pool, vocabulary, core, scheduler, executor and reference turn; layer B's crash and log models, formats, commit batch, allocator and recovery; layer C's ordered-run engine (runs, identity, overlays, filters, folds, reads, the sealer); layer D's connection, upload and transaction machines, the grammar DSL and the principal ledger; the `assembly-*` books that make the core from the registered kinds.
- `sim/`: the deterministic simulator (the host's primitive set, seeded faults) and its checkers (OWN, WORK, TRACE, ACCOUNT, IDENTITY, WIRE, HISTORY, RECOVERY, RECLAIM, DEATH, DEADLOCK, ENVELOPE).
- `host/`: the native adapter: the event loop over the served core, the socket session, the BLAKE3 FFI.
- `tests/`: unit books, the scenario drivers, the Q1 evidence and controls, and `tests/harness/` (layer H: the Node adapter, the spec models, the surface forms run against fn1 and fn2).
- `meta/`: the Lean metatheory (squares, coherence, revision conservativity, parametricity).
- `experiments/`: the squares experiment.
- `tools/certify.sh`: certify books with the fn toolchain's ACL2.

Not yet here: a durable served POST, reading an article back, the consumer port, peering, BP, the web reader, TLS (`docs/design/FN2-ORIENTATION.md` §3).

## How changes are checked
The changed books certify, the scenarios for what changed pass in the REPL on the tiny profile, the author reads what was written; one unattended nightly runs the whole closure, every scenario, the drivers and the surface harness (`docs/design/WORKFLOW-20261031.md`). Performance is reported beside the profile, never a gate. Proofs come when assurance is wanted.

## Rules every book follows
The derived path is the only path. Assert, never absorb. The DSLs generate meaning, not storage. Layers meet at seams. One representation for bytes. Bounded everything; exhaustion is a continuation. (The full method: `docs/design/briefs/FN2-SEAT-COMMON.md`.)
