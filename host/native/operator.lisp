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

(defun fnn-operator-execute-run (result)
  "Invoke the one owner entry only with ACL2-normalized plan projections."
  (handler-case
      (let ((code
              (fnn-owner-run-normalized
               (fnn-octets (fnn-core
                            'fn-native-operator-host-result-run-store-octets result))
               (fnn-octets (fnn-core
                            'fn-native-operator-host-result-run-listener-host-octets result))
               (fnn-core 'fn-native-operator-host-result-run-listener-port result)
               (fnn-core 'fn-native-operator-host-result-run-oncep result)
               (fnn-core
                'fn-native-operator-host-result-run-max-connections result))))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "run")
        code)
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "run" condition)
        code))))

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
  "I/O is bounded here; all config grammar stays in native-config ACL2."
  (handler-case
      (values (fnn-octet-list (fnn-read-regular-bounded path maximum)) nil)
    ((or fnn-store-fault fnn-os-error) (condition)
      (values nil condition))))

(defun fnn-operator-dispatch-plan (result)
  (let ((status (fnn-core 'fn-native-operator-host-result-status result)))
    (if (not (eq status :accepted))
        (progn (fnn-operator-emit-result result)
               (fnn-core 'fn-native-operator-host-result-exit-code result))
      (let ((action (fnn-core 'fn-native-operator-host-result-native-action result)))
        (case action
          (:help (fnn-operator-execute-help result))
          (:run (fnn-operator-execute-run result))
          ((:status :recover) (fnn-operator-execute-store-action result action))
          (:owner-required
           (fnn-operator-emit-status :usage "action" "requires native owner callback")
           +fnn-exit-usage+)
          (t (fnn-fault "ACL2 operator returned no native action")))))))

(defun fnn-command-operator (config-path argv)
  (let* ((max-arguments (fnn-core 'fn-native-operator-host-argv-max-arguments))
         (max-octets (fnn-core 'fn-native-operator-host-argv-max-octets))
         (argv-octets (fnn-operator-argv-octets argv max-arguments max-octets))
         ; Asking ACL2 first makes config-free HELP its own normalized action.
         (preflight (fnn-core 'fn-native-operator-host-run nil argv-octets))
         (status (fnn-core 'fn-native-operator-host-result-status preflight))
         (reason (fnn-core 'fn-native-operator-host-result-reason preflight))
         (action (fnn-core 'fn-native-operator-host-result-native-action preflight)))
    (cond ((eq action :help) (fnn-operator-dispatch-plan preflight))
          ((and (eq status :usage) (eq reason :configuration-bounds))
           (let ((config-bound (fnn-core 'fn-native-config-host-max-octets)))
             (multiple-value-bind (config-octets problem)
                 (fnn-operator-read-config config-path config-bound)
               (if problem
                   (progn
                     (fnn-operator-emit-status :usage "configuration" problem)
                     +fnn-exit-usage+)
                 (fnn-operator-dispatch-plan
                  (fnn-core 'fn-native-operator-host-run config-octets argv-octets))))))
          (t (fnn-operator-dispatch-plan preflight)))))

(fnn-register-verb "operator"
                   (lambda (config-path argv)
                     (fnn-command-operator config-path argv)))
