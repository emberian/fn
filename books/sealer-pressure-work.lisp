; Source-category binding for checked sealer pending/wake callbacks.
; Native scalar metadata GETs include core child access and repeated executed
; read-code checks. No AST evaluation charge, declared guard or CPU bound.
; Actual generated-face shape/extraction and physical refinement remain owed.
(in-package "ACL2")
(include-book "run-active-geometry")
(fn2-book-layer :c)
(defconst *fn2-sealer-pressure-id-steps* 2)
(defconst *fn2-sealer-pressure-index-steps* (+ *fn2-sealer-pressure-id-steps* 2))
(defconst *fn2-sealer-pressure-field-code-steps*
 (+ *fn2-sealer-pressure-id-steps* (* 2 *fn2-sealer-pressure-index-steps*) 2))
(defconst *fn2-sealer-pressure-field-steps*
 (+ *fn2-sealer-pressure-field-code-steps* (* 2 *fn2-sealer-pressure-index-steps*) 2))
(defconst *fn2-sealer-pressure-snapshot-steps*
 (+ *fn2-sealer-pressure-field-code-steps* *fn2-sealer-pressure-index-steps*))
(defconst *fn2-sealer-checkpoint-pending-steps*
 (+ 2 *fn2-sealer-pressure-id-steps* *fn2-sealer-pressure-snapshot-steps*
    *fn2-sealer-pressure-index-steps* *fn2-sealer-pressure-field-steps*
    *fn2-sealer-pressure-field-code-steps* *fn2-sealer-pressure-field-steps*
    *fn2-sealer-pressure-field-steps*))
; Lower resumed29 scalar cells +loader-free5 +six cells per actual source.
(defconst *fn2-sealer-pressure-resumed-steps*
 (+ 29 5 (* 6 *fn2-run-active-source-cursors*)))
; Core resumable: same checked directory access, eight borrowed children,
; actual sealer ROWS/tag, then the lower retained adoption/retirement checks.
(defconst *fn2-sealer-pressure-resumable-steps*
 (+ 2 *fn2-sealer-pressure-id-steps* *fn2-sealer-pressure-snapshot-steps*
    (* 2 *fn2-sealer-pressure-field-steps*) *fn2-sealer-pressure-index-steps*
    8 1 1 *fn2-sealer-pressure-resumed-steps*))
(defconst *fn2-sealer-checkpoint-wake-steps*
 (+ *fn2-sealer-checkpoint-pending-steps* *fn2-sealer-pressure-resumable-steps* 2))
(assert-event (equal *fn2-sealer-checkpoint-pending-steps* 102))
(assert-event (equal *fn2-sealer-checkpoint-wake-steps*
                     (+ 216 (* 6 *fn2-run-active-source-cursors*))))
; Both callbacks read only scalar metadata: zero typed payload bytes, zero IO.
; MASTER sequential face+controller/charge admission is not established here.
