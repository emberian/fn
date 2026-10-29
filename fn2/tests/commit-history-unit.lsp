; Run through tools/acl2 with timeout and recorded PID.
(in-package "ACL2")
(include-book "fn2/tests/commit-history-unit")
:q
(handler-case
 (progn
  (dolist (mode '(0 1))
   (let* ((result (fn2-b-format-probe mode)) (controls (car (last result))))
    (format t "B3 FORMAT POOL mode=~D real-sealing=~S root-notification-digest=~D/~D verdict=~A~%"
     mode (car result) (count t controls) (length controls) (if (car result) "PASS" "FAIL"))
    (assert (eq (car result) t))))
  (sb-ext:exit :code 0))
 (cl:error (condition)
  (format *error-output* "B3 FORMAT POOL FAILED: ~A~%" condition)
  (sb-ext:exit :code 1)))
