;;; Native `--fn operator CONFIG-PATH COMMAND ...` transport and execution.
;;;
;;; This raw module transports only bounded ASCII argv/configuration octets to
;;; host/native-operator-host.lisp.  ACL2 chooses command grammar, defaults,
;;; profile availability, the result tag, and the exit-code projection.  RUN
;;; installs the local-control lifecycle and POST calls that control socket;
;;; neither command has a direct Store path.  INIT, STATUS and RECOVER are
;;; the offline store actions: they name the store the configuration declares
;;; and run the existing store entry against it, so a node is stood up,
;;; inspected and repaired with the one public verb and one binary.

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

(defun fnn-operator-init-observed (root)
  "Which ACL2-named store entries already exist beside ROOT.

This is the whole physical observation the init outcome rests on.  It opens
nothing and locks nothing: `lstat` on each name ACL2 supplied, in ACL2's
order, and the names it found handed straight back."
  (let ((found nil))
    (dolist (name (fnn-core 'fn-native-operator-host-init-marker-octets)
                  (nreverse found))
      (unless (fnn-octet-list-p name)
        (fnn-fault "ACL2 returned a malformed store marker name"))
      (when (fnn-lstat (fnn-join root (fnn-octets-string (fnn-octets name))))
        (push name found)))))

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
             ;; `[log] path', absolute by fn-native-config-log-pathp; NIL
             ;; means the owner writes its service log to stderr.
             (log-path
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-log-path-octets))
             (tls-context nil))
        (unwind-protect
            (progn
              ;; Append-only, created 0640 if absent, never through a
              ;; symlink, never truncated or rotated here.  Opened before
              ;; the store so a wrong path is refused before recovery runs.
              (when log-path
                (setq *fnn-owner-log-fd*
                      (fnn-open log-path
                                (logior sb-posix:o-wronly sb-posix:o-append
                                        sb-posix:o-creat +fnn-o-nofollow+)
                                #o640)))
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
          (when tls-context (fnn-tls-close-context tls-context))
          (when *fnn-owner-log-fd*
            (ignore-errors (fnn-close *fnn-owner-log-fd*))
            (setq *fnn-owner-log-fd* nil))))
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

(defun fnn-operator-execute-init (result)
  "Initialise the store the configuration names, through the ACL2 plan.

The observation is lstat on the ACL2-named store entries and nothing else:
no lock is opened, so a store a live owner holds is refused on the presence
of its `writer.lock' rather than on a failed acquisition.  ACL2 turns that
observation into the outcome and this function only carries it out."
  (let ((root (fnn-absolute
               (fnn-core 'fn-native-operator-host-result-store-root result))))
    (handler-case
        (let* ((observed (fnn-operator-init-observed root))
               (outcome (fnn-core 'fn-native-operator-host-init-outcome
                                  result observed))
               (status (fnn-core 'fn-native-operator-host-result-status outcome)))
          (if (not (eq status :accepted))
              (progn (fnn-operator-emit-result outcome)
                     (fnn-core 'fn-native-operator-host-result-exit-code outcome))
            (let ((groups
                    (mapcar (lambda (name)
                              (unless (fnn-octet-list-p name)
                                (fnn-fault "ACL2 returned a malformed init group"))
                              (fnn-octets-string (fnn-octets name)))
                            (fnn-core
                             'fn-native-operator-host-result-init-group-octets
                             result))))
              (unless (consp groups)
                (fnn-fault "ACL2 accepted an init plan that names no group"))
              (let* ((profile (fnn-core
                               'fn-native-operator-host-result-init-profile result))
                     (code (progn
                             (unless (consp profile)
                               (fnn-fault "ACL2 accepted an init plan with no store profile"))
                             (fnn-command-init root groups profile))))
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "init")
                code))))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "init" condition)
          code)))))

(defun fnn-operator-execute-admin (result)
  "Execute only the exact accepted ACL2 administrative plan."
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (command (fnn-core 'fn-native-operator-host-result-command result))
        (plan (fnn-core 'fn-native-operator-host-result-admin-plan result))
        (argv (fnn-core 'fn-native-operator-host-result-admin-argv result))
        (control-path-list
          (fnn-core 'fn-native-operator-host-result-admin-control-path-octets
                    result)))
    (handler-case
        (let* ((queryp (fnn-core 'fn-native-admin-host-queryp plan))
               (control-path (and (not queryp)
                                  (fnn-octet-list-p control-path-list)
                                  (fnn-octets control-path-list)))
               ;; An image without the control socket has no live owner
               ;; to hand the plan to: the direct executor takes the
               ;; exclusive lock, so a live owner of another image refuses it.
               (livep (and control-path
                           (not (fnn-image-omits-p :control))
                           (fnn-control-socket-path-p
                            (fnn-lstat (fnn-octets-string control-path)))))
               (code
                 (cond
                   ;; A query publishes no configuration record, so it has
                   ;; nothing to send the live owner and nothing to serialize
                   ;; behind its mutex: the read-only executor is the only
                   ;; one, live socket or not.
                   ((and queryp (fnn-admin-plan-acceptedp plan))
                    (fnn-operator-status-once
                     root (and (fnn-octet-list-p control-path-list)
                               (consp control-path-list)
                               (fnn-octets control-path-list))
                     :peers))
                   (queryp (fnn-admin-query root plan))
                   (livep
                    (fnn-core 'fn-native-control-host-status-exit-code
                              (fnn-control-admin control-path argv)))
                   (t (fnn-admin-execute root plan)))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) command)
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    command condition)
          code)))))

; host/native/checkpoint.lisp installs `fnn-command-compact' here after it
; loads.  An image built without it (the DTN image) has no compaction.
(defvar *fnn-compact-callback* nil)

(defun fnn-operator-execute-store-action (result action)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result)))
    (handler-case
        (let ((code (case action
                      (:status (fnn-command-status root))
                      (:recover (fnn-command-recover root))
                      (:upgrade-profile
                       (let ((profile (fnn-core
                                       'fn-native-operator-host-result-upgrade-profile
                                       result)))
                         (unless (consp profile)
                           (fnn-fault "ACL2 accepted a store plan with no profile"))
                         (fnn-command-upgrade-profile root profile)))
                      (:compact (funcall *fnn-compact-callback* root))
                      (:checkpoint (fnn-command-state-checkpoint root))
                      (:needs-upgrade (fnn-command-needs-upgrade root))
                      (:rollback-check
                       (fnn-command-rollback-check
                        root
                        (fnn-octets-string
                         (fnn-core 'fn-native-operator-host-result-rollback-path-octets
                                   result))))
                      (t +fnn-exit-fault+))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    (string-downcase (symbol-name action)))
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    (string-downcase (symbol-name action)) condition)
          code)))))

;;; The status report (`status', `pins', `obligations', `peer list').
;;;
;;; With an owner running, the owner answers from the state it carries over
;;; its control socket; with none, the Store is opened read-only.  Which of
;;; the two is `fn-nls-route''s, and both print the octets ACL2 rendered
;;; (books/native-live-status.lisp); this file renders nothing.

(defun fnn-operator-status-once (root control-path kind)
  (let* ((socket-present
           (and control-path
                (not (fnn-image-omits-p :control))
                (fnn-control-socket-path-p
                 (fnn-lstat (fnn-octets-string control-path)))))
         (answer (if socket-present
                     (fnn-control-live-status control-path kind)
                   :none)))
    (if (and (consp answer) (eq (first answer) :done))
        (progn (fnn-write-report (second answer)) +fnn-exit-ok+)
      (case (fnn-core 'fn-native-live-status-host-route socket-present answer)
        (:offline (fnn-command-live-report root kind))
        (:refused +fnn-exit-refused+)
        (t +fnn-exit-uncertain+)))))

(defun fnn-operator-execute-status (result)
  "One report, or with `--watch N' one every N seconds until interrupted."
  (let* ((root (fnn-core 'fn-native-operator-host-result-store-root result))
         (command (fnn-core 'fn-native-operator-host-result-command result))
         (kind (fnn-core 'fn-native-operator-host-result-status-kind result))
         (watch (fnn-core 'fn-native-operator-host-result-status-watch result))
         (path-list (fnn-core
                     'fn-native-operator-host-result-status-control-path-octets
                     result))
         (control-path (and (fnn-octet-list-p path-list) (consp path-list)
                            (fnn-octets path-list))))
    (loop
      (let ((code (handler-case (fnn-operator-status-once root control-path kind)
                    (error (condition)
                      (let ((code (fnn-exit-code-for condition)))
                        (fnn-operator-emit-status
                         (fnn-operator-status-of-exit-code code) command condition)
                        (return-from fnn-operator-execute-status code))))))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) command)
        (unless (and (integerp watch) (plusp watch))
          (return code))
        (sleep watch)))))

(defun fnn-operator-execute-principal (result)
  "Execute only the credential plan and credential path projected by ACL2.
The configured store is the one whose writer lock says whether an owner is
serving the old credentials (fn-native-auth-admin-effect-word)."
  (let ((*fnn-native-auth-admin-store-root*
          (fnn-octets-string
           (fnn-core 'fn-native-operator-host-result-principal-store-octets
                     result))))
    (fnn-native-auth-admin-execute
     (fnn-core 'fn-native-operator-host-result-principal-plan result)
     (fnn-octets-string
      (fnn-core 'fn-native-operator-host-result-principal-auth-path-octets
                result)))))

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
        (let ((omitted (case action
                         ((:run :post) :nntp-service)
                         (:principal :credentials))))
          (when (and (eq action :compact) (null *fnn-compact-callback*))
            (fnn-operator-emit-status
             :usage "action" "compact needs the checkpoint surface, which this image omits")
            (return-from fnn-operator-dispatch-plan +fnn-exit-usage+))
          (when (and omitted (fnn-image-omits-p omitted))
            (fnn-operator-emit-status
             :usage "action"
             (format nil "~(~a~) needs the ~(~a~) surface, which this image omits"
                     action omitted))
            (return-from fnn-operator-dispatch-plan +fnn-exit-usage+)))
        (case action
          (:help (fnn-operator-execute-help result))
          (:init (fnn-operator-execute-init result))
          (:run (fnn-operator-execute-run result))
          (:post (fnn-operator-execute-post result))
          (:status (fnn-operator-execute-status result))
          ((:recover :upgrade-profile :compact :checkpoint :needs-upgrade
            :rollback-check)
           (fnn-operator-execute-store-action result action))
          (:admin (fnn-operator-execute-admin result))
          (:peering (fnn-pinv-execute result))
          (:principal (fnn-operator-execute-principal result))
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
