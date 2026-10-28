# fn2

The bottom-up, semantics-first rebuild of fn. Decisions and research: `docs/design/` (start at `FN2-ORIENTATION.md`; the two settled decisions are `EXECUTION-MODEL.md` and `STORAGE-DESIGN.md`). The layer's own decisions: `docs/<layer>.md`. Owed keystones, written and unproved on purpose: `docs/OWED.md`.

## What is here (layer A, the foundation; layers B and H on their branches)
- `books/columns.lisp`: `defcolumns`, the records DSL: one struct-of-arrays stobj per declaration, bounds in guards, a non-executable logical view.
- `books/machines.lisp`: `defmachine` over `defcolumns`: one table per machine kind, enum phases, per-run budget caps as guards, generated dispatch; the registry in the world carries each kind's layout and its obligation categories.
- `books/pool.lisp`: the byte pool (rule 6 of the execution model): fixed capacity, ownership states, generation-checked handles; the octet list exists only in the logic.
- `books/vocab.lisp`, `profile.lisp`, `exec-state.lisp`: the event/action vocabulary, the outstanding-operation table and outbox, the profile (every capacity is a profile field).
- `books/core.lisp`, `sched.lisp`, `executor*.lisp`: the one semantic state, the calendar scheduler, the executor turn.
- `books/reference.lisp`, `reference-state.lisp`: the independent list-scheduled reference turn the TRACE checker compares against.
- `books/machines-a*.lisp`: layer A's probe machines (listener, echo, null, scribe).
- `books/owed.lisp`: `defthm-owed`, a named keystone statement with its teeth, recorded, not proved.
- `sim/`: the deterministic simulator: the same primitive set as the host, seeded PRNG, 26 fault classes, the checkers (`check-*.lisp`: OWN, TRACE, WORK implemented; the rest arrive with their layers), the echo and scribe scenarios, the recovery stub.
- `tests/`: unit books, the fault and replay controls, the acceptance drivers (`sim-layer-a-driver.lsp` is the layer's gate).
- `tools/certify.sh`: certify a book on the laptop with the fn toolchain's ACL2.
- `host/`: the Linux adapter (21 primitives), arriving with quest A5.

## Gates
The simulator's checkers and scenarios, and the carried natives. Certify is information, never a gate. Performance is reported beside the profile, never a gate. Proofs come when assurance is wanted.

## Rules every book follows
Assert, never absorb. The DSLs generate meaning, not storage. Layers meet at seams. One representation for bytes. Bounded everything; exhaustion is a continuation. (The full method: `docs/design/briefs/FN2-SEAT-COMMON.md`.)
