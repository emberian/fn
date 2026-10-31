;;; The raw half of fn2/tests/native-serve.lsp: the served core on a configured listener.
(in-package "ACL2")

(defun fn2-nserve-dotted (text)
  "A dotted IPv4 quad as a u32, or nil."
  (let ((parts (ignore-errors
                (loop with start = 0
                      for dot = (position #\. text :start start)
                      collect (parse-integer text :start start :end dot)
                      while dot do (setf start (1+ dot))))))
    (and (= (length parts) 4) (every (lambda (p) (<= 0 p 255)) parts)
         (reduce (lambda (a p) (+ (* a 256) p)) parts :initial-value 0))))

(defun fn2-nserve-profile ()
  "The served profile, the listener from the environment (absent: the profile's defaults)."
  (let* ((profile (put-assoc-equal :trace nil *fn2-conn-wire-profile*))
         (port (sb-ext:posix-getenv "FN2_LISTENER_PORT"))
         (address (sb-ext:posix-getenv "FN2_LISTENER_ADDRESS"))
         (path (sb-ext:posix-getenv "FN2_LISTENER_PATH")))
    (when port
      (setf profile (put-assoc-equal :listener-port (or (ignore-errors (parse-integer port)) -1) profile)))
    (when address
      (setf profile (put-assoc-equal :listener-address (or (fn2-nserve-dotted address) -1) profile)))
    (when path
      (setf profile (put-assoc-equal :listener-path path profile)))
    profile))

; The ready, refusal and stop lines each start a line (fn1's harness matches
; `LISTENING <port>` at a line's start; the raw REPL's prompt precedes this call).
(defun fn2-nserve-main ()
  (let* ((profile (fn2-nserve-profile))
         (capacity (or (ignore-errors (parse-integer (or (sb-ext:posix-getenv "FN2_ENVELOPE_TRACE") "0"))) 0)))
    (multiple-value-bind (bind address port) (fn2-host-listener-bind profile)
      (declare (ignore address port))
      (unless (eq bind :ok)
        (format t "~%REFUSED ~(~a~)~%" bind) (finish-output)
        (return-from fn2-nserve-main 2)))
    (let ((host (fn2-n-make-host profile :trace-capacity capacity)))
      (format t "~%LISTENING ~d~%" (fn2-nhost-listen-port host))
      (when (fn2-nhost-local-path host)
        (format t "LISTENING-LOCAL ~a~%" (fn2-nhost-local-path host)))
      (finish-output)
      (unwind-protect
           (let ((reason (fn2-n-run host)))
             (format t "STOPPED ~d~%" reason)
             (when (plusp capacity)
               (format t "ENVELOPE ~s~%"
                       (car (fn2-envelope-replay (fn2-n-trace-list host) profile nil))))
             (finish-output)
             0)
        (fn2-n-destroy host)))))
