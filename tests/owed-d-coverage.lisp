; T10's registration-coverage control: the generator expanded in the test
; instance (which registers fn2-core-test-child and fn2-test-machine outside
; layer A's books) measures those children too, and the measure grows with
; the test child's declared rows.
(in-package "ACL2")
(include-book "core-child-assembly")
(include-book "../books/resident")
(fn2-resident-measure-events)
(assert-event (equal *fn2-resident-children* (strip-cars *fn2-core-children*)))
(assert-event (member-eq 'fn2-core-test-child *fn2-resident-children*))
(assert-event (member-eq 'fn2-test-machine-table *fn2-resident-children*))
(defun fn2-coverage-measure (rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (m fn2-core)
      (let ((fn2-core (fn2-core-init (put-assoc-equal :test-child-rows rows *fn2-test-child-profile*) fn2-core)))
        (mv (list (fn2-core-resident-measure fn2-core) (fn2-core-resident-breakdown fn2-core)) fn2-core))
      m)))
; Four more test-child rows of one u32 column are 16 more resident bytes,
; attributed to the test child alone.
(assert-event (equal (- (car (fn2-coverage-measure 8)) (car (fn2-coverage-measure 4))) 16))
(assert-event (equal (- (cadr (assoc-eq 'fn2-core-test-child (cadr (fn2-coverage-measure 8))))
                        (cadr (assoc-eq 'fn2-core-test-child (cadr (fn2-coverage-measure 4))))) 16))
