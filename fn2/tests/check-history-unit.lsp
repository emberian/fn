; From worktree root, tools/acl2 with timeout and recorded PID.
(in-package "ACL2")
(include-book "fn2/tests/check-history-unit")
:q
(handler-case
 (progn
  (dolist (group (list (list "baseline" *fn2-history-unit-positive* *fn2-history-unit-negative*
                            *fn2-history-unit-recovery-negative*)
                      (list "preflush-fua" *fn2-history-unit-fua-positive* *fn2-history-unit-fua-negative*
                            *fn2-history-unit-fua-recovery-negative*)
                      (list "admission" *fn2-history-unit-request-positive* *fn2-history-unit-request-negative* nil)))
   (mv-let (positive np) (fn2-history-unit-recovery-count (second group) t)
    (mv-let (negative nn) (fn2-history-unit-action-count (third group))
     (mv-let (recovery nr) (fn2-history-unit-recovery-count (fourth group) nil)
      (let ((pass (and (< 0 np) (< 0 nn) (= positive np) (= negative nn) (= recovery nr))))
       (format t "HISTORY UNIT ~a positive=~a/~a action-refusals=~a/~a recovery-rejections=~a/~a verdict=~a~%"
        (first group) positive np negative nn recovery nr (if pass "PASS" "FAIL"))
       (assert pass))))))
  (sb-ext:exit :code 0))
 (cl:error (condition)
  (format *error-output* "HISTORY UNIT FAILED: ~A~%" condition)
  (sb-ext:exit :code 1)))
