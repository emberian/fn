# fn2

The bottom-up, semantics-first rebuild of fn (see build/coordinator/fn2/FN2-ORIENTATION.md: the entry point; EXECUTION-MODEL.md and STORAGE-DESIGN.md are the two decisions; the Astra round-2 tables and the Astra storage format are normative in structure).

Layout: `books/` the ACL2 core (the three DSLs, the byte pool, the journal and commit batch, the ordered-run engine, the machines); `host/` the SBCL host (the 21-primitive adapter, Linux); `sim/` the deterministic simulator (the same primitive set, faults, checkers, scenarios); `tests/` native and simulator scenarios; `docs/` the layer contracts, rewritten whole.

Gates: the simulator's checkers and scenarios, and the carried natives. Certify runs for information; it is not a gate. Proofs come when assurance is wanted (ember: semantics-first).
