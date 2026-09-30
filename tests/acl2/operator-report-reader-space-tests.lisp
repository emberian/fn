(in-package "ACL2")
(include-book "../../books/operator-report-reader-space")

; Reachable complete antecedent/conclusion for start and its next validation turn.
(defthm fn-oru-space-reachable-positive
 (let* ((cursor (fn-oru-start))
        (next (mv-nth 0 (fn-oru-reader-step cursor :validate 65 nil t)))
        (output (mv-nth 2 (fn-oru-reader-step cursor :validate 65 nil t))))
   (and (fn-oru-ready-p cursor)
        (<= (fn-oru-reader-prefix-cells cursor) 7)
        (<= (+ (fn-oru-reader-prefix-cells cursor)
               (fn-oru-reader-prefix-cells next) (len output)) 15)
        (fn-wildmat-octetp 65)
        (fn-wildmat-octet-listp output) (<= (len output) 1)))
 :rule-classes nil)

; Ready-only logical boundary, deliberately corrupted semantic state.
(defthm fn-oru-space-corrupted-ready-positive
 (let ((cursor (list :valid (list 65 65 65 65) 0)))
   (and (fn-oru-ready-p cursor)
        (not (fn-oru-invariant cursor))
        (equal (+ (fn-oru-reader-prefix-cells cursor)
                  (fn-oru-reader-prefix-cells
                   (mv-nth 0 (fn-oru-reader-step cursor :copy 65 nil t)))
                  (len (mv-nth 2 (fn-oru-reader-step cursor :copy 65 nil t)))) 15)))
 :rule-classes nil)

; Affirmative ready-hypothesis removal: five pending cells fail both bounds.
(defthm fn-oru-space-ready-removal-tooth
 (let ((cursor (list :valid (list 65 65 65 65 65) 0)))
   (and (not (fn-oru-ready-p cursor))
        (< 7 (fn-oru-reader-prefix-cells cursor))
        (< 15 (+ (fn-oru-reader-prefix-cells cursor)
                 (fn-oru-reader-prefix-cells
                  (mv-nth 0 (fn-oru-reader-step cursor :copy 65 nil t)))
                 (len (mv-nth 2 (fn-oru-reader-step cursor :copy 65 nil t)))))))
 :rule-classes nil)

; Only octet hypothesis omitted; singleton cardinality survives, octet output fails.
(defthm fn-oru-space-octet-removal-tooth
 (let* ((cursor (list :valid nil 0))
        (output (mv-nth 2 (fn-oru-reader-step cursor :copy 256 nil t))))
   (and (fn-oru-ready-p cursor) (fn-oru-invariant cursor)
        (not (fn-wildmat-octetp 256))
        (<= (len output) 1)
        (not (fn-wildmat-octet-listp output))))
 :rule-classes nil)
