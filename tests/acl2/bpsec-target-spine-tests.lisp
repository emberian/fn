(in-package "ACL2")
(include-book "../../books/bpsec-target-spine")
(include-book "bpsec-target-tests")

(assert-event
 (and (eq (symbol-class 'fn-bps-target-start (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-target-unit (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-target-step (w state)) :common-lisp-compliant)))

(defun fn-bps-tst-run (cursor fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-target-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-target-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-target-step cursor 1)) (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-cursor-spinep *fn-bps-target-spine* cursor)
                    (fn-bps-cursor-spinep *fn-bps-target-spine* next))) :broken-spine
        (if (eq (fn-bps-field 0 step) :more) (fn-bps-tst-run next (1- (nfix fuel)))
          (list (fn-bps-field 0 step) (fn-bps-field 1 step) next))))))

; Literal valid caller input and complete fixed-spine conclusions at every
; quantum-one count/lookup/search transition. Structural valid is not verified.
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*))
        (run (fn-bps-tst-run cursor 2048)))
   (and (fn-bps-target-inputp *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*)
        (fn-bps-cursor-spinep *fn-bps-target-spine* cursor)
        (equal (len *fn-bps-target-spine*) 22)
        (eq (fn-bps-field 0 run) :valid)
        (fn-bps-cursor-spinep *fn-bps-target-spine* (fn-bps-field 2 run))
        (fn-bps-cursor-spinep *fn-bps-target-spine* (car (fn-bps-target-drive cursor 1024))))))
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*))
        (run (fn-bps-tst-run cursor 2048)))
   (and (fn-bps-target-inputp *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*)
        (fn-bps-cursor-spinep *fn-bps-target-spine* cursor)
        (eq (fn-bps-field 0 run) :pending-plaintext)
        (fn-bps-cursor-spinep *fn-bps-target-spine* (fn-bps-field 2 run)))))
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-bundle* nil nil *fn-bpst-limits*))
        (run (fn-bps-tst-run cursor 2048)))
   (and (fn-bps-target-inputp *fn-bpst-bundle* nil nil *fn-bpst-limits*)
        (fn-bps-cursor-spinep *fn-bps-target-spine* cursor)
        (equal (take 2 run) '(:unsupported :incomplete-security-coverage))
        (fn-bps-cursor-spinep *fn-bps-target-spine* (fn-bps-field 2 run)))))
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* nil *fn-bpst-limits*))
        (run (fn-bps-tst-run cursor 2048)))
   (and (fn-bps-target-inputp *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* nil *fn-bpst-limits*)
        (fn-bps-cursor-spinep *fn-bps-target-spine* cursor)
        (equal (take 2 run) '(:refused :opaque-set))
        (fn-bps-cursor-spinep *fn-bps-target-spine* (fn-bps-field 2 run)))))
; Affirmative hypothesis-removal witness: corrupted missing-key cursor fails
; the sole spine antecedent and both concrete drive/step conclusions.
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*))
        (corrupted (cdr cursor)))
   (and (fn-bps-target-inputp *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*)
        (not (fn-bps-cursor-spinep *fn-bps-target-spine* corrupted))
        (not (fn-bps-cursor-spinep *fn-bps-target-spine* (car (fn-bps-target-drive corrupted 17))))
        (not (fn-bps-cursor-spinep *fn-bps-target-spine* (fn-bps-field 2 (fn-bps-target-step corrupted 17)))))))
