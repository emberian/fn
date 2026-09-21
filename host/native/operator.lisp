;;; Native `--fn operator CONFIG-PATH COMMAND ...` transport and execution.
;;;
;;; This raw module transports only bounded ASCII argv/configuration octets to
;;; host/native-operator-host.lisp.  ACL2 chooses command grammar, defaults,
;;; profile availability, the result tag, and the exit-code projection.  Only
;;; the ACL2-designated status/recover actions execute here; run/post remain
;;; owner callbacks and are explicitly reported unavailable rather than routed
;;; to a direct store shortcut.  build integration is owned by the native owner.

(in-package "ACL2")

(defun fnn-operator-argv-octets (texts max-arguments max-octets)
  (when (< max-arguments (length texts))
    (error 'fnn-usage-error :message "operator argv exceeds ACL2 bound"))
  (mapcar (lambda (text)
            (when (< max-octets (length text))
              (error 'fnn-usage-error :message "operator argument exceeds ACL2 bound"))
            (let ((octets (fnn-ascii-octet-list text)))
              (unless (every (lambda (octet) (<= octet 127)) octets)
                (error 'fnn-usage-error :message "operator argument is not ASCII"))
              octets))
          texts))

(defun fnn-operator-word (status)
  (cond ((eq status :accepted) "accepted")
        ((eq status :refused) "refused")
        ((eq status :uncertain) "uncertain")
        ((eq status :fault) "fault")
        ((eq status :usage) "usage")
        (t "fault")))

(defun fnn-operator-emit (result)
  (let ((status (fnn-core-state 'fn-native-operator-host-result-status result))
        (reason (fnn-core-state 'fn-native-operator-host-result-reason result)))
    (fnn-err "~a operator ~a" (fnn-operator-word status) reason)))

(defun fnn-operator-execute-store-action (result action)
  (let ((root (fnn-core-state 'fn-native-operator-host-result-store-root result)))
    (handler-case
        (let ((code (case action
                      (:status (fnn-command-status root))
                      (:recover (fnn-command-recover root))
                      (t +fnn-exit-fault+))))
          (fnn-err "~a operator ~a" (cond ((= code 0) "accepted")
                                            ((= code 1) "refused")
                                            ((= code 3) "uncertain")
                                            ((= code 5) "usage")
                                            (t "fault"))
                   action)
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-err "~a operator ~a" (cond ((= code 1) "refused")
                                            ((= code 3) "uncertain")
                                            ((= code 5) "usage")
                                            (t "fault"))
                   condition)
          code)))))

(defun fnn-command-operator (config-path argv)
  (let* ((config-bound (fnn-core-state 'fn-native-config-host-max-octets))
         (config-octets (fnn-octet-list (fnn-read-regular-bounded config-path config-bound)))
         (max-arguments (fnn-core-state 'fn-native-operator-host-argv-max-arguments))
         (max-octets (fnn-core-state 'fn-native-operator-host-argv-max-octets))
         (argv-octets (fnn-operator-argv-octets argv max-arguments max-octets))
         (result (fnn-core-state 'fn-native-operator-host-run config-octets argv-octets))
         (status (fnn-core-state 'fn-native-operator-host-result-status result)))
    (if (not (eq status :accepted))
        (progn (fnn-operator-emit result)
               (fnn-core-state 'fn-native-operator-host-result-exit-code result))
      (let ((action (fnn-core-state 'fn-native-operator-host-result-native-action result)))
        (case action
          ((:status :recover) (fnn-operator-execute-store-action result action))
          (:owner-required
           (fnn-err "usage operator action requires native owner callback")
           +fnn-exit-usage+)
          (t (fnn-fault "ACL2 operator returned no native action")))))))

(fnn-register-verb "operator"
                   (lambda (config-path argv)
                     (fnn-command-operator config-path argv)))
