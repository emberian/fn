# fn2 tests slice: certify times (baseline)

Measured 2026-10-29 on the laptop (nextop), dev 8a4875e89, `fn2/tools/certify.sh -j 2` through the slot pool, other seats running. Columns: CERTIFY-BOOK seconds (as cert.pl reports `Built`, includes loading the book's dependencies), prover seconds, seconds spent in INCLUDE-BOOK forms, and the top leaf event of an `ld` of the book source (per-event `Time:`; this excludes the compile pass certify-book does, so for compile-bound books it understates and the table says so).

Not in this baseline: `squares-unit` and `q1-unit` (not yet on dev), and the driver-only loads (sim-layer-a, sim-allocation, core-allocation, scribe-scenario, sim-fault-controls, sim-replay-controls, sim-device-broad), which are not certifiable books; they run inside the `.lsp` drivers.

| book | certify s | prove s | include s | top event (ld, per-event) |
|---|---|---|---|---|
| tests/core-child-assembly-callbacks.lisp | 35.5 | 32.41 | 1.8 | 7.15 s: DEFUN FN2-LISTENER-ADMIT |
| tests/core-child-assembly-reference.lisp | 23.0 | 0.14 | 5.2 | 1.92 s: DEFUN FN2-REF-COPY-CORE |
| tests/core-child-assembly-access.lisp | 11.8 | 7.77 | 1.4 | 0.89 s: INCLUDE-BOOK "core-child-assembly-core" |
| tests/columns-cost-unit.lisp | 10.0 | 6.24 | 0.3 | 0.44 s: DEFSTOBJ FN2-COLUMNS-COST32 |
| tests/wake-unit.lisp | 9.9 | 0.00 | 9.7 | 1.77 s: INCLUDE-BOOK "../books/executor" |
| tests/machines-a-unit.lisp | 9.5 | 6.60 | 2.3 | 2.29 s: DEFTHM FN2-MACHINE-TEST-ACCUMULATE-PRESERVES-TYPE |
| tests/core-child-assembly-core.lisp | 9.5 | 7.61 | 1.2 | 1.40 s: DEFTHM FN2-HARVEST-ONE-PRESERVES-WFP |
| tests/columns-cost-unit-20.lisp | 6.7 | 3.14 | 0.3 | 0.33 s: DEFSTOBJ FN2-COLUMNS-COST20 |
| tests/callbacks-unit.lisp | 3.7 | 0.43 | 2.9 | 1.65 s: INCLUDE-BOOK "../books/assembly" |
| tests/core-child-assembly-dispatch.lisp | 3.2 | 1.76 | 1.4 | 0.94 s: INCLUDE-BOOK "core-child-assembly-callbacks" |
| tests/sim-acquisition.lisp | 3.0 | 0.00 | 2.7 | 1.66 s: INCLUDE-BOOK "../books/resources-owed" |
| tests/reference-unit.lisp | 3.0 | 0.00 | 2.9 | 1.73 s: INCLUDE-BOOK "../books/reference" |
| tests/columns-cost-unit-10.lisp | 2.6 | 1.03 | 0.3 | 0.29 s: INCLUDE-BOOK "../books/machines" |
| tests/core-unit.lisp | 2.6 | 0.00 | 2.4 | 1.73 s: INCLUDE-BOOK "../books/assembly" |
| tests/core-child-assembly.lisp | 2.6 | 0.00 | 2.7 | 1.88 s: INCLUDE-BOOK "core-child-assembly-reference" |
| tests/columns-unit.lisp | 2.6 | 0.93 | 0.2 | 0.09 s: DEFUN FN2-WIDE-UNIT |
| tests/work-controls.lisp | 2.5 | 0.00 | 2.8 | 1.72 s: INCLUDE-BOOK "../books/executor" |
| tests/declare-unit.lisp | 2.3 | 0.78 | 0.5 | 0.27 s: INCLUDE-BOOK "../books/core-children" |
| tests/executor-unit.lisp | 2.3 | 0.01 | 2.2 | 1.86 s: INCLUDE-BOOK "reference-unit" |
| tests/core-child-unit.lisp | 2.3 | 0.03 | 2.3 | 1.85 s: INCLUDE-BOOK "core-child-assembly" |
| tests/sched-unit.lisp | 2.2 | 0.03 | 2.1 | 1.77 s: INCLUDE-BOOK "../books/assembly" |
| tests/core-child-assembly-index.lisp | 2.1 | 1.12 | 1.0 | 0.44 s: INCLUDE-BOOK "../books/machine-dispatch" |
| tests/staging-unit.lisp | 1.7 | 0.62 | 0.3 | 0.25 s: INCLUDE-BOOK "../books/core-children" |
| tests/core-child-registration.lisp | 1.7 | 0.65 | 0.3 | 0.35 s: INCLUDE-BOOK "../books/core-children" |
| tests/check-own-unit.lisp | 1.5 | 0.00 | 1.8 | 0.53 s: INCLUDE-BOOK "../sim/check-own" |
| tests/vocab-unit.lisp | 1.1 | 0.01 | 0.3 | 0.27 s: INCLUDE-BOOK "../books/vocab" |
| tests/pool-unit.lisp | 0.7 | 0.00 | 0.2 | 0.11 s: INCLUDE-BOOK "../books/pool" |
| tests/recover-unit.lisp | 0.2 | 0.00 | 0.2 | 0.20 s: INCLUDE-BOOK "../sim/recover-stub" |
| tests/network-backpressure-unit.lisp | 0.1 | 0.01 | 0.2 | 0.08 s: INCLUDE-BOOK "../sim/network" |
| tests/owed-unit.lisp | 0.1 | 0.00 | 0.1 | 0.04 s: INCLUDE-BOOK "std/testing/must-fail" |
| tests/resources-unit.lisp | 0.0 | 0.00 | 0.0 | 0.02 s: INCLUDE-BOOK "../books/resources" |

Sum of certify seconds: 160.0 over 30 books. Under 5 s: 22; 5 to 15 s: 6; over 15 s: 2 (core-child-assembly-callbacks 35.5, core-child-assembly-reference 23.0). core-child-assembly-reference proves nothing (0.14 s): its 23 s is compile and allocation (6.3 GB), so the ld column is not its cost.

## After the first day's commits (same machine, load average 150 to 180 from other seats: realtime is noisy, CPU runtime is the steadier number)

| book | baseline certify s | now certify s | now CPU s |
|---|---|---|---|
| tests/core-child-assembly-callbacks.lisp | 35.5 | 35.5 | 30.3 |
| tests/core-child-assembly-reference.lisp | 23.0 | 23.0 | 18.1 |
| tests/core-child-assembly-access.lisp | 11.8 | 11.8 | 9.2 |
| tests/columns-cost-unit.lisp | 10.0 | 10.0 | 6.0 |
| tests/core-child-assembly-core.lisp | 9.5 | 9.5 | 7.9 |
| tests/columns-cost-unit-20.lisp | 6.7 | 6.7 | 4.2 |
| tests/machines-a-unit.lisp | 9.5 | 5.2 | 4.2 |
| tests/wake-unit.lisp | 9.9 | 3.7 | 2.3 |
| tests/callbacks-unit.lisp | 3.7 | 3.7 | 2.8 |
| tests/core-child-assembly-dispatch.lisp | 3.2 | 3.2 | 2.9 |
| tests/sim-acquisition.lisp | 3.0 | 3.0 | 2.2 |
| tests/executor-unit.lisp | 2.3 | 2.7 | 2.1 |
| tests/columns-cost-unit-10.lisp | 2.6 | 2.6 | 2.0 |
| tests/core-child-assembly.lisp | 2.6 | 2.6 | 2.0 |
| tests/columns-unit.lisp | 2.6 | 2.6 | 2.1 |
| tests/work-controls.lisp | 2.5 | 2.5 | 1.9 |
| tests/reference-unit.lisp | 3.0 | 2.5 | 1.9 |
| tests/declare-unit.lisp | 2.3 | 2.3 | 1.9 |
| tests/core-child-unit.lisp | 2.3 | 2.3 | 2.1 |
| tests/core-unit.lisp | 2.6 | 2.2 | 1.9 |
| tests/sched-unit.lisp | 2.2 | 2.2 | 1.8 |
| tests/core-child-assembly-index.lisp | 2.1 | 2.1 | 1.9 |
| tests/staging-unit.lisp | 1.7 | 1.7 | 1.5 |
| tests/core-child-registration.lisp | 1.7 | 1.7 | 1.5 |
| tests/check-own-unit.lisp | 1.5 | 1.5 | 0.6 |
| tests/vocab-unit.lisp | 1.1 | 1.1 | 1.0 |
| tests/pool-unit.lisp | 0.7 | 0.7 | 0.6 |
| tests/recover-unit.lisp | 0.2 | 0.2 | 0.2 |
| tests/network-backpressure-unit.lisp | 0.1 | 0.1 | 0.1 |
| tests/owed-unit.lisp | 0.1 | 0.1 | 0.1 |
| tests/resources-unit.lisp | 0.0 | 0.0 | 0.0 |

Only machines-a-unit changed by a commit; wake-unit's 9.9 s baseline was load noise (3.7 s on a re-run, nothing changed).

Reading the table. Every test book except two certifies in under 15 s, and what is left over 3 s in the small ones is mostly INCLUDE-BOOK of the library books (the certify of a test book re-reads its dependencies' certificates and fasls twice).

Why the remaining large ones are not tests-slice problems (measured 2026-10-29):

- `core-child-assembly-callbacks` (35 s) runs the same event macros as `books/assembly-callbacks`. Per event: the guard proof of `fn2-listener-admit` (7.5 s, 607k prover steps, whose guard conjecture is 220 subgoals of path conditions over seven sequential core writes), its PRESERVES-TYPE and PRESERVES-WFP (2.2 s each) and `fn2-connection-issue` (4 s). Accumulated persistence shows no single rule: 2.0 M useful tries spread over the generated WFP/TYPE preservation rewrites and the stobj type prescriptions (`fn2-machines-rows-natp`, `fn2-listener-rows-natp`, `fn2-echo-rows-natp`, `fn2-machinesp`: 0 useful of 600k frames). Disabling those six type prescriptions saves 10% (607k to 540k steps in the defun hint), disabling tau makes it worse (754k). The structural cure is in the generator (`books/machines.lisp` `fn2-machine-callback-event`, DSL seat): the listener-admit success branch as its own declared operation (R7e) so its guard is not proved under the refusal branch's path conditions.
- `core-child-assembly-reference` (23 s) proves nothing (0.14 s). Pass-1 events are 8 s (`fn2-ref-copy-core` 2.5 s, `fn2-ref-import-boundary` 1.2 s, the 45 ref defstobjs about 2.3 s), the pass-2 include is 4 s, compile-file of the 4.6 MB fasl is about 7 s. A statistical profile of certify-book shows 20 percent in EQUAL through `%assoc-test` and `%member-test`, called from `relevant-posns-term` / `relevant-posns-clique1` (translation of the nested stobj-let). GC is 1.2 s of it; a larger nursery does not help. `books/assembly-reference` (18 s) is the same macro.
- `core-child-assembly-access` (12 s) and `-core` (9.5 s): `fn2-machine-access-events` and `fn2-core-events` (`fn2-harvest-one` PRESERVES 1.4 s each), shared with `books/assembly-access` and `books/assembly-core`.
- `columns-cost-unit` family (10 s, 6.7 s, 2.6 s): the `defcolumns` encapsulate, 3.6 s of proving for the 32-field declaration; `books/columns.lisp`.
