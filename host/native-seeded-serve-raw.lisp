;;; Test-only seeded listener and logical replay. Never loaded by image-node.lsp.
(in-package "ACL2")
(load "host/native-seed-fixture.lisp")

(defun fn2-nseed-serve-main ()
  (let* ((profile (fn2-nserve-profile))
         (kill-at (fn2-nserve-kill-at (sb-ext:posix-getenv "FN2_KILL_AT")))
         (capacity (or (ignore-errors
                         (parse-integer (or (sb-ext:posix-getenv "FN2_ENVELOPE_TRACE") "0"))) 0)))
    (format t "~%NODE-PID ~d~%" (%fn2-native-getpid))
    (finish-output)
    (unless kill-at
      (format t "REFUSED kill-at~%") (finish-output)
      (return-from fn2-nseed-serve-main 2))
    (multiple-value-bind (bind address port) (fn2-host-listener-bind profile)
      (declare (ignore address port))
      (unless (eq bind :ok)
        (format t "~%REFUSED ~(~a~)~%" bind) (finish-output)
        (return-from fn2-nseed-serve-main 2)))
    (unless (fn2-core-profilep profile)
      (format t "~%REFUSED profile~%") (finish-output)
      (return-from fn2-nseed-serve-main 2))
    (let ((host (handler-case
                  (fn2-n-make-seeded-host profile *fn2-ss-seeds*
                                           :trace-capacity capacity :kill-at kill-at)
                  (error (condition)
                    (format t "~%REFUSED ~a~%" condition) (finish-output)
                    (return-from fn2-nseed-serve-main 2)))))
      (prog1 (fn2-nserve-run-host host)
        (when (plusp capacity)
          (format t "ENVELOPE ~s~%"
                  (car (fn2-ss-replay (fn2-n-trace-list host) profile *fn2-ss-seeds* nil)))
          (finish-output))))))
