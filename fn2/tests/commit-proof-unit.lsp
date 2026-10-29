; Run from the worktree root with tools/acl2, timeout and a recorded PID.
(in-package "ACL2")
(include-book "fn2/tests/commit-proof-unit")
:q
(handler-case
 (let* ((teeth (fn2-commit-proof-teeth))
        (passed (count t teeth)) (total (length teeth))
        (pass (and (= total 12) (= passed total))))
  (format t "B3 KEYSTONE executed-teeth=~D/~D ack-baseline=~S ack-FUA=~S fence-removal=~S timeout-baseline=~S timeout-FUA=~S dispatch-removal=~S follower-first=~S reuse-baseline=~S reuse-FUA=~S uncertain-rearm=~S duplicate-start=~S refused-retry-contract=~S verdict=~A~%"
   passed total (first teeth) (second teeth) (third teeth) (fourth teeth)
   (fifth teeth) (sixth teeth) (seventh teeth) (eighth teeth) (ninth teeth) (tenth teeth) (nth 10 teeth) (nth 11 teeth) (if pass "PASS" "FAIL"))
  (sb-ext:exit :code (if pass 0 1)))
 (cl:error (condition)
  (format *error-output* "B3 KEYSTONE FAILED: ~A~%" condition)
  (sb-ext:exit :code 1)))
