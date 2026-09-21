;;; Native `--fn operator CONFIG-PATH COMMAND ...` transport and execution.
;;;
;;; This raw module transports only bounded ASCII argv/configuration octets to
;;; host/native-operator-host.lisp.  ACL2 chooses command grammar, defaults,
;;; profile availability, the result tag, and the exit-code projection.  RUN
;;; installs the local-control lifecycle and POST calls that control socket;
;;; neither command has a direct Store path.

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
        ((eq status :usage) "usage")
        (t "fault")))

(defun fnn-operator-status-of-exit-code (code)
  "The sole translation for pre-existing native actions' numeric exits."
  (cond ((= code +fnn-exit-ok+) :accepted)
        ((= code +fnn-exit-refused+) :refused)
        ((= code +fnn-exit-uncertain+) :uncertain)
        ((= code +fnn-exit-usage+) :usage)
        (t :fault)))

(defun fnn-operator-emit-status (status subject &optional reason)
  "One tagged result renderer for ACL2 plans and executed native actions."
  (fnn-err "~a operator ~a~@[ ~a~]"
           (fnn-operator-word status) subject reason))

(defun fnn-operator-emit-result (result)
  (fnn-operator-emit-status
   (fnn-core 'fn-native-operator-host-result-status result)
   (or (fnn-core 'fn-native-operator-host-result-command result) "request")
   (fnn-core 'fn-native-operator-host-result-reason result)))

(defun fnn-operator-execute-help (result)
  "Emit only the ACL2-normalized, bounded help text after the action succeeds."
  (let* ((arguments
           (fnn-core 'fn-native-operator-host-result-arguments result))
         (text (third arguments)))
    (unless (stringp text)
      (fnn-fault "ACL2 help action returned no text"))
    (fnn-out "~a" text)
    (fnn-operator-emit-status :accepted "help")
    +fnn-exit-ok+))

(defun fnn-operator-optional-path (result projection)
  "Decode one ACL2-projected optional path without supplying a default."
  (let ((value (fnn-core projection result)))
    (cond ((null value) nil)
          ((fnn-octet-list-p value) (fnn-octets-string (fnn-octets value)))
          (t (fnn-fault "ACL2 returned malformed optional path from ~a"
                        projection)))))

(defun fnn-operator-execute-run (result)
  "Invoke the one owner entry only with ACL2-normalized plan projections."
  (handler-case
      (let* ((auth-path
               (fnn-octets-string
                (fnn-octets
                 (fnn-core
                  'fn-native-operator-host-result-run-auth-path-octets result))))
             (auth-required
               (fnn-core
                'fn-native-operator-host-result-run-auth-requiredp result))
             (auth-protected
               (fnn-core
                'fn-native-operator-host-result-run-auth-protected-onlyp result))
             (certificate
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-tls-cert-octets))
             (private-key
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-tls-key-octets))
             (tls-context nil))
        (unwind-protect
            (progn
              ;; ACL2 already enforced paired presence.  Only a successfully
              ;; loaded and key-checked context is passed to auth/owner.
              (when certificate
                (setq tls-context
                      (fnn-tls-open-context certificate private-key)))
              (let* ((*fnn-owner-startup-hooks*
                       (list (fnn-native-auth-startup-hook
                              auth-path auth-required auth-protected)))
                     (*fnn-owner-start-hooks*
                       (cons #'fnn-feed-service-start *fnn-owner-start-hooks*))
                     (*fnn-owner-stop-hooks*
                       (cons #'fnn-feed-service-wake *fnn-owner-stop-hooks*))
                     (*fnn-owner-close-hooks*
                       (cons #'fnn-feed-service-close *fnn-owner-close-hooks*))
                     (code
                       (fnn-control-owner-run-normalized
                        (fnn-octets
                         (fnn-core
                          'fn-native-operator-host-result-run-store-octets result))
                        (fnn-octets
                         (fnn-core
                          'fn-native-operator-host-result-run-listener-host-octets result))
                        (fnn-core
                         'fn-native-operator-host-result-run-listener-port result)
                        (fnn-core 'fn-native-operator-host-result-run-oncep result)
                        (fnn-core
                         'fn-native-operator-host-result-run-max-connections result)
                        (fnn-octets (fnn-core
                                     'fn-native-operator-host-result-run-control-path-octets result))
                        (fnn-core 'fn-native-operator-host-result-run-posting-enabledp result)
                        tls-context)))
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "run")
                code))
          (when tls-context (fnn-tls-close-context tls-context))))
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "run" condition)
        code))))

(defun fnn-operator-execute-post (result)
  "Use only ACL2-normalized request fields and ACL2-framed local control."
  (handler-case
      (let* ((status
               (fnn-control-submit
                (fnn-octets
                 (fnn-core
                  'fn-native-operator-host-result-post-control-path-octets result))
                (fnn-octets
                 (fnn-core
                  'fn-native-operator-host-result-post-msgid-octets result))
                (mapcar #'fnn-octets
                        (fnn-core
                         'fn-native-operator-host-result-post-group-octets result))
                (fnn-octets
                 (fnn-core
                  'fn-native-operator-host-result-post-payload-path-octets result))))
             (class
               (fnn-core 'fn-native-control-host-status-class status))
             (code
               (fnn-core 'fn-native-control-host-status-exit-code status)))
        (fnn-operator-emit-status class "post" status)
        code)
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status
         (fnn-operator-status-of-exit-code code) "post" condition)
        code))))

(defun fnn-operator-execute-admin (result)
  "Execute only the exact accepted ACL2 administrative plan."
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (command (fnn-core 'fn-native-operator-host-result-command result))
        (plan (fnn-core 'fn-native-operator-host-result-admin-plan result)))
    (handler-case
        (let ((code (fnn-admin-execute root plan)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) command)
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    command condition)
          code)))))

(defun fnn-operator-execute-store-action (result action)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result)))
    (handler-case
        (let ((code (case action
                      (:status (fnn-command-status root))
                      (:recover (fnn-command-recover root))
                      (t +fnn-exit-fault+))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) action)
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    action condition)
          code)))))

(defun fnn-operator-read-config (path maximum)
  "Classify only ordinary configuration-file defects as usage before reading.

A fault from lstat/open/read after this precheck remains a host fault.  In
particular, this does not turn EIO or an internal bounded-read failure into a
configuration usage result."
  (let ((info (fnn-lstat path)))
    (when (null info)
      (error 'fnn-usage-error :message "operator configuration file is missing"))
    (when (or (fnn-symlink-p info) (not (fnn-regular-p info)))
      (error 'fnn-usage-error :message "operator configuration file is not regular"))
    (when (> (sb-posix:stat-size info) maximum)
      (error 'fnn-usage-error :message "operator configuration file exceeds ACL2 bound"))
    (fnn-octet-list (fnn-read-regular-bounded path maximum))))

(defun fnn-operator-dispatch-plan (result)
  (let ((status (fnn-core 'fn-native-operator-host-result-status result)))
    (if (not (eq status :accepted))
        (progn (fnn-operator-emit-result result)
               (fnn-core 'fn-native-operator-host-result-exit-code result))
      (let ((action (fnn-core 'fn-native-operator-host-result-native-action result)))
        (case action
          (:help (fnn-operator-execute-help result))
          (:run (fnn-operator-execute-run result))
          (:post (fnn-operator-execute-post result))
          ((:status :recover) (fnn-operator-execute-store-action result action))
          (:admin (fnn-operator-execute-admin result))
          (:owner-required
           (fnn-operator-emit-status :usage "action" "requires native owner callback")
           +fnn-exit-usage+)
          (t (fnn-fault "ACL2 operator returned no native action")))))))

(defun fnn-command-operator (config-path argv)
  (let* ((max-arguments (fnn-core 'fn-native-operator-host-argv-max-arguments))
         (max-octets (fnn-core 'fn-native-operator-host-argv-max-octets))
         (argv-octets (fnn-operator-argv-octets argv max-arguments max-octets))
         (preflight (fnn-core 'fn-native-operator-host-preflight argv-octets)))
    (if (fnn-core 'fn-native-operator-host-preflight-needs-config-p preflight)
        (let* ((config-bound (fnn-core 'fn-native-config-host-max-octets))
               (config-octets (fnn-operator-read-config config-path config-bound)))
          (fnn-operator-dispatch-plan
           (fnn-core 'fn-native-operator-host-run config-octets argv-octets)))
      (fnn-operator-dispatch-plan preflight))))

(fnn-register-verb "operator"
                   (lambda (config-path argv)
                     (fnn-command-operator config-path argv)))
