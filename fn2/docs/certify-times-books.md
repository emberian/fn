# fn2/books certify times (baseline, dev 8a4875e89, laptop, -j 2, load average ~40)

Wall seconds from cert.pl "Built" lines. "prove s" sums per-event Time lines of the .cert.out (nested events double count; an upper bound). Top event is the longest single top-level event.

| book | certify s | prove s (sum) | top event (s) |
|---|---|---|---|
| assembly-callbacks | 41.8 | 207.1 | PROGN (DEFUN FN2-MACHINE-DEC ...) ...) (30.7) |
| executor | 18.9 | 30.8 | PROGN (DEFTHM FN2-TRANSITION-PRESERVES-TYPE ...) ...) (13.8) |
| assembly-reference | 18.2 | 0.3 | PROGN (LOCAL ...) ...) (8.0) |
| vocab | 15.2 | 27.1 | MAKE-EVENT (VALUE ...)) (7.1) |
| machines-a | 9.5 | 24.8 | MAKE-EVENT (LET* ...)) (2.7) |
| assembly-access | 9.0 | 20.8 | PROGN (MAKE-EVENT ...) ...) (7.0) |
| executor-access | 8.3 | 11.1 | PROGN (DEFTHM FN2-EXEC-TRACE-ACTIONS-TYPE ...) ...) (4.0) |
| assembly-core | 7.9 | 18.9 | PROGN (MAKE-EVENT ...) ...) (6.5) |
| pool | 5.5 | 6.3 | MAKE-EVENT (VALUE ...)) (2.3) |
| sched | 4.5 | 3.6 | MAKE-EVENT (VALUE ...)) (1.0) |
| trace | 3.8 | 5.3 | MAKE-EVENT (VALUE ...)) (2.1) |
| executor-wake | 3.6 | 0.1 | PROGN (DEFTHM FN2-EXEC-CLOCK-TYPE ...) ...) (0.0) |
| machines | 3.4 | 2.1 | DEFUN FN2-CALLBACK-FORWARDING ...) (2.5) |
| assembly-dispatch | 3.2 | 6.7 | PROGN (FN2-RESOLVE :CALLBACKS) ...) (1.5) |
| reference | 2.4 | 0.0 | DEFUN FN2-REF-LOOP ...) (0.0) |
| assembly | 2.3 | 0.0 | - (0.0) |
| assembly-index | 2.3 | 2.4 | PROGN (DEFUN FN2-MACHINES-INIT-BASES ...) ...) (0.9) |
| resources-owed | 2.3 | 0.0 | MAKE-EVENT (VALUE ...)) (0.0) |
| machines-directory | 1.8 | 1.3 | MAKE-EVENT (VALUE ...)) (0.7) |
| machines-a-run | 1.6 | 0.0 | DEFMACRO FN2-MACHINE-A-EVENTS ...) (0.1) |
| columns | 1.5 | 0.0 | DEFUN FN2-COLUMNS-PRESERVES ...) (0.0) |
| machines-a-scribe | 1.3 | 0.0 | DEFMACRO FN2-SCRIBE-EVENTS ...) (0.0) |
| core-children-a | 1.2 | 0.0 | MAKE-EVENT (LET* ...)) (0.0) |
| machine-dispatch | 1.1 | 0.0 | DEFMACRO FN2-MACHINE-DISPATCH-EVENTS ...) (0.0) |
| reference-state | 1.0 | 0.0 | DEFMACRO FN2-REFERENCE-STATE-EVENTS ...) (0.0) |
| core | 1.0 | 0.0 | DEFMACRO FN2-CORE-EVENTS ...) (0.0) |
| machines-a-access | 0.9 | 0.0 | DEFMACRO FN2-MACHINE-ACCESS-EVENTS ...) (0.0) |
| exec-state | 0.9 | 0.6 | MAKE-EVENT (VALUE ...)) (0.3) |
| core-children | 0.9 | 0.0 | DEFUN FN2-CORE-REGISTERED-PAIRS ...) (0.0) |
| machines-all | 0.8 | 0.0 | - (0.0) |
| declare | 0.8 | 0.0 | DEFUN FN2-DECL-LAYER ...) (0.0) |
| profile | 0.6 | 0.1 | DEFTHM FN2-PROFILE-QA-BOUNDS ...) (0.0) |
| assumptions-integrity | 0.6 | 0.0 | ENCAPSULATE (((FN2-A-INTEGRITY-EVIDENCE * ...) ...) ...) ... (0.0) |
| resources | 0.6 | 0.1 | DEFTHM FN2-RESOURCE-CHAIN-INCREASES ...) (0.0) |
| operations | 0.5 | 0.0 | MAKE-EVENT (LET* ...)) (0.0) |
| owed | 0.4 | 0.0 | DEFUN FN2-SQUARE-ROWP ...) (0.0) |
| fnv | 0.4 | 0.0 | IN-THEORY (DISABLE ...)) (0.0) |

Total 179.9 s; under 5 s: 28; 5-15 s: 5; over 15 s: 4
