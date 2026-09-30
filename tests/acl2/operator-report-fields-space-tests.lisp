(in-package "ACL2")
(include-book "../../books/operator-report-fields-space")

; Fixture traversal only. The served emitter does not compute this census.
(defun fn-orf-space-fixture (fuel c)
  (declare (xargs :guard (and (natp fuel) (fn-orf-invariant c))
                  :measure (nfix fuel)
                  :guard-hints (("Goal" :use fn-orf-step-preserves-invariant
                                 :in-theory
                                 (e/d (fn-orf-invariant)
                                      (fn-orf-step fn-orf-space-relationp
                                       fn-orf-step-preserves-invariant))))))
  (if (zp fuel) (fn-orf-space-relationp c)
    (and (fn-orf-space-relationp c)
         (mv-let (next output done) (fn-orf-step c)
           (declare (ignore output done))
           (fn-orf-space-fixture (+ -1 fuel) next)))))

(defun fn-orf-space-fixture-next (c)
  (declare (xargs :guard (fn-orf-invariant c)))
  (mv-let (next output done) (fn-orf-step c)
    (declare (ignore output done)) next))

; Reachable complete antecedent and conclusion for START and preservation,
; including zero and a natural beyond machine-word/decimal-width limits.
(assert-event
 (let* ((fields (list (list :nat 0) (list :text "borrowed")
                      (list :nat (expt 10 100))))
        (c (fn-orf-start fields)))
   (and (fn-orf-fieldsp fields) (fn-orf-space-relationp c)
        (fn-orf-space-relationp (fn-orf-space-fixture-next c))
        (fn-orf-space-fixture 512 c))))

(assert-event
 (let ((c (fn-orf-space-fixture-next (fn-orf-start '((:nat 100))))))
   (and (fn-orf-space-relationp c)
        (equal (fn-orf-phase c) :prepare)
        (equal (fn-orf-original-number c) 100)
        (equal (fn-orf-number c) 100)
        (fn-orf-space-relationp (fn-orf-space-fixture-next c))
        (< (integer-length (floor 100 10)) (integer-length 100)))))

; Corrupted-state hypothesis-removal tooth: the original complete invariant
; holds, but the omitted provenance/scratch relation fails and the literal
; preservation conclusion also fails. Zero requires a reserved final digit.
(assert-event
 (let ((c (fn-orf-cursor :prepare '((:nat 0)) "" 0 0 '(48))))
   (and (fn-orf-invariant c)
        (not (fn-orf-space-relationp c))
        (not (fn-orf-space-relationp (fn-orf-space-fixture-next c))))))

; Quotient lemma's nonredundant lower-bound hypothesis: retained NATP holds,
; 10<=n fails, and strict binary-width progress fails at zero.
(assert-event
 (and (natp 0) (not (<= 10 0))
      (not (< (integer-length (floor 0 10)) (integer-length 0)))))

; Complete START hypothesis-removal: malformed current text descriptor.
(assert-event
 (let ((fields '((:text 5))))
   (and (not (fn-orf-fieldsp fields))
        (not (fn-orf-space-relationp
              (with-guard-checking :none (fn-orf-start fields)))))))

; Quotient NATP-removal: the retained lower-bound clause holds, but a
; noninteger input has zero INTEGER-LENGTH and a positive quotient width.
(assert-event
 (and (<= 10 21/2) (not (natp 21/2))
      (not (< (integer-length (floor 21/2 10)) (with-guard-checking :none (integer-length 21/2))))))
