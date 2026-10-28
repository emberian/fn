; From worktree root, background with a PID file. Exits 1 on any failure,
; including a failed include (the check below is then undefined).
(in-package "ACL2")
(include-book "fn2/tests/check-history-unit")
:q
(handler-case
    (mv-let (positive np) (fn2-history-unit-recovery-count *fn2-history-unit-positive* t)
      (mv-let (negative nn) (fn2-history-unit-action-count *fn2-history-unit-negative*)
        (mv-let (recovery nr) (fn2-history-unit-recovery-count *fn2-history-unit-recovery-negative* nil)
          (let ((pass (and (< 0 np) (< 0 nn) (< 0 nr)
                           (= positive np) (= negative nn) (= recovery nr))))
            (format t "HISTORY UNIT baseline positive=~a/~a action-refusals=~a/~a recovery-rejections=~a/~a verdict=~a~%"
                    positive np negative nn recovery nr (if pass "PASS" "FAIL"))
            (sb-ext:exit :code (if pass 0 1))))))
  (cl:error (condition)
    (format *error-output* "HISTORY UNIT FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
