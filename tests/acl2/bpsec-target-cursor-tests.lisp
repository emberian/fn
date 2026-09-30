(in-package "ACL2")
(include-book "../../books/bpsec-target-cursor")
(include-book "bpsec-target-tests")

(defun fn-bps-tc-result (step)
  (declare (xargs :guard t))
  (let ((status (fn-bps-field 0 step)))
    (if (member-equal status '(:valid :pending-plaintext)) status
      (list status (fn-bps-field 1 step)))))

(defun fn-bps-tc-run (cursor quantum fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-target-step fn-bps-field)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-target-step fn-bps-field)))))
  (if (zp (nfix fuel)) :test-fuel
    (let ((step (fn-bps-target-step cursor quantum)))
      (if (eq (fn-bps-field 0 step) :more)
          (fn-bps-tc-run (fn-bps-field 2 step) quantum (1- (nfix fuel)))
        (fn-bps-tc-result step)))))

(defun fn-bps-tc-case (bundle bindings opaque limits expected)
  (declare (xargs :guard t))
  (and (fn-bps-target-inputp bundle bindings opaque limits)
       (equal (fn-bps-target-check bundle bindings opaque limits) expected)
       (equal (fn-bps-tc-run (fn-bps-target-start bundle bindings opaque limits) 1 2048) expected)
       (equal (fn-bps-tc-run (fn-bps-target-start bundle bindings opaque limits) 17 2048) expected)))

(assert-event
 (fn-bps-tc-case *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits* :valid))
(assert-event
 (fn-bps-tc-case *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits* :pending-plaintext))
(assert-event
 (fn-bps-tc-case *fn-bpst-opaque-bundle* *fn-bpst-bcb-bindings* nil *fn-bpst-limits* '(:refused :opaque-set)))
(assert-event
 (fn-bps-tc-case *fn-bpst-opaque-bundle* (append *fn-bpst-bcb-bindings* *fn-bpst-bindings*) '(7)
                 *fn-bpst-limits* '(:refused :encrypted-bib-parsed)))
(assert-event
 (fn-bps-tc-case *fn-bpst-bundle* nil nil *fn-bpst-limits* '(:unsupported :incomplete-security-coverage)))
(assert-event
 (fn-bps-tc-case *fn-bpst-bundle* (list (cons 7 (fn-bpst-bib '(99)))) nil *fn-bpst-limits* '(:refused :missing-target)))
(assert-event
 (let ((bundle (fn-bpb-make-bundle *fn-bpst-primary*
                 (list *fn-bpst-cipher-bib* *fn-bpst-bcb-block* (fn-bpb-make-block 12 9 0 0 '(255)))
                 *fn-bpst-payload*)))
   (fn-bps-tc-case bundle *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits*
                   '(:unsupported :incomplete-security-coverage))))
(assert-event
 (let ((bundle (fn-bpb-make-bundle *fn-bpst-primary*
                 (list *fn-bpst-cipher-bib* (fn-bpb-make-block 12 8 0 0 (fn-bps-asb-encode *fn-bpst-bcb*)))
                 *fn-bpst-payload*)))
   (fn-bps-tc-case bundle *fn-bpst-bcb-bindings* '(7) *fn-bpst-limits* '(:refused :payload-bcb-flags))))
(assert-event
 (let* ((other (fn-bpb-make-block 11 9 0 0 (fn-bps-asb-encode *fn-bpst-asb*)))
        (bundle (fn-bpb-make-bundle *fn-bpst-primary* (list *fn-bpst-block* other) *fn-bpst-payload*))
        (bindings (list (cons 7 *fn-bpst-asb*) (cons 9 *fn-bpst-asb*))))
   (and (fn-bps-parsed-bindings-matchp bundle bindings *fn-bpst-limits*)
        (fn-bps-tc-case bundle bindings nil *fn-bpst-limits* '(:refused :duplicate-service-target)))))
(assert-event
 (fn-bps-tc-case *fn-bpst-bundle* *fn-bpst-bindings* nil
                 (fn-bps-limits-make 4096 128 16 16 2048 0) '(:refused :graph-metadata-limit)))
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*))
        (step (fn-bps-target-step cursor 0)))
   (and (fn-bps-target-inputp *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*)
        (equal (fn-bps-field 0 step) :more) (equal (fn-bps-field 2 step) cursor)
        (equal (fn-bps-field 3 step) 0))))

; Literal complete conclusion of the unconditional quantum-composition
; event, across counting, binding lookup and target lookup transitions.
(assert-event
 (let* ((cursor (fn-bps-target-start *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*))
        (first (fn-bps-target-drive cursor 3))
        (second (fn-bps-target-drive (fn-bps-field 0 first) 7)))
   (and (fn-bps-target-inputp *fn-bpst-bundle* *fn-bpst-bindings* nil *fn-bpst-limits*)
        (equal (fn-bps-target-drive cursor 10)
               (list (fn-bps-field 0 second) (+ (fn-bps-field 1 first) (fn-bps-field 1 second)))))))
