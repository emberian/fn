# fn2/books certify times (baseline, dev 8a4875e89, laptop, TIME_CERT=1, -j 2)

CPU seconds (user+sys from cert.pl .cert.time). Wall seconds are useless here: the laptop load average was 40-170 during measurement, which doubled wall times (an apparent 2x from disabling six type-prescriptions was load; user CPU shows ~5%). Longest-event column is ACL2 wall time and therefore noisy; use it for ranking only. executor-access.cert.time had a corrupt sys field (parsed as 4.0 user).

| book | CPU s (user+sys) | longest event (ACL2 time, s) |
|---|---|---|
| assembly-callbacks | 26.9 | PROGN (DEFUN FN2-MACHINE-DEC ...) ...) (21.6) |
| executor | 15.3 | PROGN (DEFTHM FN2-TRANSITION-PRESERVES-TYPE ...) . (13.1) |
| assembly-reference | 14.0 | PROGN (LOCAL ...) ...) (6.9) |
| vocab | 12.9 | MAKE-EVENT (VALUE ...)) (6.1) |
| assembly-access | 6.4 | PROGN (MAKE-EVENT ...) ...) (5.9) |
| machines-a | 6.3 | MAKE-EVENT (LET* ...)) (2.3) |
| assembly-core | 6.1 | PROGN (MAKE-EVENT ...) ...) (5.5) |
| executor-access | 4.4 | PROGN (DEFTHM FN2-EXEC-TRACE-ACTIONS-TYPE ...) ... (2.5) |
| pool | 4.3 | MAKE-EVENT (VALUE ...)) (2.1) |
| trace | 3.3 | MAKE-EVENT (VALUE ...)) (2.5) |
| sched | 2.8 | MAKE-EVENT (VALUE ...)) (0.7) |
| machines | 2.4 | DEFUN FN2-CALLBACK-FORWARDING ...) (1.8) |
| resources-owed | 2.3 | MAKE-EVENT (VALUE ...)) (0.0) |
| executor-wake | 2.1 | PROGN (DEFTHM FN2-EXEC-CLOCK-TYPE ...) ...) (0.0) |
| reference | 2.1 | DEFUN FN2-REF-QUEUES-DIFFERENCE ...) (0.0) |
| assembly-dispatch | 2.1 | PROGN (FN2-RESOLVE :CALLBACKS) ...) (1.1) |
| assembly | 1.9 | - (0.0) |
| assembly-index | 1.9 | PROGN (DEFUN FN2-MACHINES-INIT-BASES ...) ...) (1.0) |
| machines-directory | 1.1 | MAKE-EVENT (VALUE ...)) (0.5) |
| columns | 1.1 | DEFUN FN2-COLUMNS-PRESERVES ...) (0.0) |
| machines-a-scribe | 1.0 | DEFMACRO FN2-SCRIBE-EVENTS ...) (0.0) |
| machine-dispatch | 0.8 | DEFMACRO FN2-MACHINE-DISPATCH-EVENTS ...) (0.0) |
| machines-a-run | 0.8 | DEFMACRO FN2-MACHINE-A-EVENTS ...) (0.1) |
| exec-state | 0.8 | MAKE-EVENT (VALUE ...)) (0.4) |
| reference-state | 0.7 | DEFMACRO FN2-REFERENCE-STATE-EVENTS ...) (0.0) |
| core | 0.7 | DEFMACRO FN2-CORE-EVENTS ...) (0.0) |
| machines-all | 0.7 | - (0.0) |
| machines-a-access | 0.7 | DEFMACRO FN2-MACHINE-ACCESS-EVENTS ...) (0.0) |
| core-children-a | 0.7 | TABLE FN2-CORE-CHILDREN ...) (0.0) |
| declare | 0.5 | DEFUN FN2-DECL-LAYER ...) (0.0) |
| core-children | 0.5 | DEFUN FN2-CORE-REGISTERED-PAIRS ...) (0.0) |
| fnv | 0.4 | DEFTHM FN2-FNV-STEP-BOUND ...) (0.0) |
| operations | 0.4 | MAKE-EVENT (LET* ...)) (0.0) |
| resources | 0.4 | DEFTHM FN2-RESOURCE-CHAIN-INCREASES ...) (0.0) |
| owed | 0.3 | DEFUN FN2-SQUARE-ROWP ...) (0.0) |
| profile | 0.3 | DEFTHM FN2-PROFILE-QA-BOUNDS ...) (0.0) |
| assumptions-integrity | 0.3 | ENCAPSULATE (((FN2-A-INTEGRITY-EVIDENCE * ...) ... (0.0) |

Total 129.8 CPU s; under 5 s: 30; 5-15 s: 5; over 15 s: 2
