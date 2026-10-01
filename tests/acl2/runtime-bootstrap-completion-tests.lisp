(in-package "ACL2")
(include-book "../../books/runtime-bootstrap-completion")
; Synthetic INTERNAL installation witness: no compiled source authority or PRS
; grant. It refutes duplicate install, overflow and forged geometry routes.
(defun rbct-run (pagebytes)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-page-read-pool
  (mv-let (answer fn-page-read-pool)
   (let ((installation '(:allocation-epoch-request-budget
          (:allocation-epoch-association runtime image profile 16 1000)
          10000 nil nil nil nil nil 20 3 4 5 100)))
    (mv-let (word outcome fn-page-read-pool)
     (fn-aec-bootstrap-complete-internal installation 10 pagebytes 1000 30 fn-page-read-pool)
     (mv-let (again again-outcome fn-page-read-pool)
      (fn-aec-bootstrap-complete-internal installation 10 pagebytes 1000 30 fn-page-read-pool)
      (mv (list word outcome again again-outcome
                (fn-prp-alloc-mode fn-page-read-pool)
                (fn-prp-alloc-occupied fn-page-read-pool)
                (fn-prp-alloc-allocated fn-page-read-pool)
                (fn-prp-alloc-active-turns fn-page-read-pool)
                (fn-prp-alloc-installation fn-page-read-pool)) fn-page-read-pool))))
   answer)))
(assert-event
 (let ((r (rbct-run 16)))
  (and (equal (take 8 r)
        '(:runtime-bootstrap-installed :accepted
          :runtime-bootstrap-already-attempted :fenced :active 160 30 0))
       (fn-aec-request-budget-installationp (nth 8 r))
       (not (fn-aec-physical-installationp (nth 8 r)))
       (equal (fn-aec-ceiling (nth 8 r)) 900))))
(assert-event
 (equal (rbct-run 32)
  '(:runtime-bootstrap-geometry-refused :refused
    :runtime-bootstrap-geometry-refused :refused :uninstalled 0 0 0 nil)))
