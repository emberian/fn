;;; The operator's live surfaces: the NNTP service (`run', `post'), credential
;;; administration (`principal') and every arm that reaches a running owner
;;; over its control socket (`status' and `health' asked live, live
;;; administration, `account invite', `moderation', `article withdraw',
;;; `peer genesis|invite|accept|confirm', `keys redecide', `tls reload').
;;;
;;; host/native/operator.lisp carries the offline verbs and dispatch; this file
;;; installs the rest into it (fnn-operator-register-action and
;;; *fnn-operator-live-owner*).  host/native/build.lisp loads it after every
;;; file it calls (control, auth, auth-admin, feed-service, pull-service,
;;; peer-invite, keys, tls-reload); host/native/build-dtn.lisp loads none of
;;; them and not this file, so the DTN operator refuses those actions by the
;;; surface's name and takes the offline arms, and nothing it loads calls a
;;; function it lacks (`tools/host_check.py --load --build
;;; host/native/build-dtn.lisp').  As in operator.lisp, ACL2 decides every
;;; value; this file observes, transports and prints.

(in-package "ACL2")

(defun fnn-operator-execute-run (result)
  "Invoke the one owner entry only with ACL2-normalized plan projections."
  (setq *fnn-owner-last-fault* nil)
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
             (tls-context nil)
             (run-code nil)
             (run-failure nil))
        (setq *fnn-health-min-percent*
              (fnn-core 'fn-native-operator-host-result-health-min-percent result))
        (unwind-protect
            (handler-case
            (progn
              ;; Append-only, created 0640 if absent, never through a
              ;; symlink, never truncated or rotated here.  Opened before
              ;; the store so a wrong path is refused before recovery runs.
              (when log-path
                (setq *fnn-owner-log-fd* (fnn-owner-open-log log-path)
                      *fnn-owner-log-path* log-path)
                (fnn-operator-log-run-line
                 (fnn-core 'fn-native-health-host-run-started-line)))
              ;; ACL2 already enforced paired presence.  Only a pair ACL2
              ;; accepted (fn-tlsr-start-decide, the decision `tls reload'
              ;; applies; PRF-387) is passed to auth/owner.
              (when certificate
                (setq tls-context
                      (fnn-tls-start-context certificate private-key)))
              (let* ((web-plan
                       ;; The node's own web face (PRF-340): ACL2's plan of
                       ;; the profile's [web] table, or NIL for none.
                       (fnn-web-run-hooks
                        (fnn-core 'fn-native-operator-host-result-run-listener-port result)
                        (and tls-context
                             (fnn-core 'fn-native-operator-host-result-run-implicit-tls-port
                                       result))
                        (and tls-context t)))
                     (*fnn-owner-startup-hooks*
                       (list (fnn-native-auth-startup-hook
                              auth-path auth-required auth-protected)))
                     ;; The NEWNEWS pull feed (PRF-100) is a sibling lifecycle
                     ;; extension: host/native/pull-service.lisp.
                     (*fnn-owner-start-hooks*
                       (append (list* #'fnn-feed-service-start #'fnn-pull-service-start
                                      *fnn-owner-start-hooks*)
                               (and web-plan
                                    (list (lambda (service)
                                            (fnn-web-start service web-plan tls-context))))))
                     (*fnn-owner-stop-hooks*
                       (list* #'fnn-feed-service-wake #'fnn-pull-service-wake
                              *fnn-owner-stop-hooks*))
                     (*fnn-owner-close-hooks*
                       (list* #'fnn-feed-service-close #'fnn-pull-service-close
                              #'fnn-web-close-face
                              *fnn-owner-close-hooks*))
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
                        tls-context
                        ;; PRF-162: ACL2's implicit-TLS port, offered only
                        ;; beside the certificate and key loaded above.
                        (and tls-context
                             (fnn-core
                              'fn-native-operator-host-result-run-implicit-tls-port
                              result)))))
                (setq run-code code)
                ;; The owner's fault, when it stopped on one, is the
                ;; result line's reason: the last line the service
                ;; manager's journal shows for this run says why.
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "run"
                 (and (/= code +fnn-exit-ok+) *fnn-owner-last-fault*))
                code))
              (error (condition)
                ;; Recorded for the stop line below, then handled as before
                ;; by the outer handler.
                (setq run-failure condition)
                (error condition)))
          (let ((code (or run-code (and run-failure (fnn-exit-code-for run-failure)))))
            (when (integerp code)
              (fnn-operator-log-run-line
               (fnn-core 'fn-native-health-host-run-stopped-line code
                         (let ((reason (cond (run-failure
                                              (ignore-errors (format nil "~a" run-failure)))
                                             ((/= code +fnn-exit-ok+) *fnn-owner-last-fault*))))
                           (and (stringp reason) (fnn-octet-list (fnn-string-octets reason))))))))
          (when tls-context (fnn-tls-close-context tls-context))
          (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
            (when *fnn-owner-log-fd*
              (ignore-errors (fnn-close *fnn-owner-log-fd*))
              (setq *fnn-owner-log-fd* nil
                    *fnn-owner-log-path* nil)))))
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "run" condition)
        code))))

(defun fnn-operator-status-detail (status word)
  "STATUS, then the reason word ACL2 says the operator's line carries
(fn-native-control-reply-detail, PKT-453 (a)): its octets, not a host word."
  (let ((detail (and word (fnn-core 'fn-native-control-host-reply-detail status word))))
    (if (fnn-octet-list-p detail)
        (format nil "~a ~a" status (fnn-octets-string (fnn-octets detail)))
      status)))

(defun fnn-operator-execute-post (result)
  "Use only ACL2-normalized request fields and ACL2-framed local control."
  (handler-case
      (multiple-value-bind (status word)
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
                  'fn-native-operator-host-result-post-payload-path-octets result)))
        (let ((class (fnn-core 'fn-native-control-host-status-class status))
              (code (fnn-core 'fn-native-control-host-status-exit-code status)))
          (fnn-operator-emit-status class "post"
                                    (fnn-operator-status-detail status word))
          code))
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status
         (fnn-operator-status-of-exit-code code) "post" condition)
        code))))

(defun fnn-operator-execute-moderate (result)
  "PKT-657, PKT-575: `moderation approve|reject' and `article withdraw'.
ACL2 frames the request (FNCT kind 21) from its normalized plan; the running
owner decides it and answers the reasoned reply."
  (let ((command (fnn-core 'fn-native-operator-host-result-command result)))
    (handler-case
        (let* ((request (fnn-core 'fn-native-operator-host-result-moderate-request
                                  result))
               (path (fnn-core
                      'fn-native-operator-host-result-moderate-control-path-octets
                      result))
               (encoded (fnn-core 'fn-native-control-host-moderation-encode
                                  (first request) (second request)
                                  (third request) (fourth request))))
          (unless (and (fnn-octet-list-p encoded) (fnn-octet-list-p path)
                       (consp path))
            (fnn-fault "ACL2 refused the moderation request"))
          (multiple-value-bind (status word)
              (fnn-control-reasoned-exchange (fnn-octets-string (fnn-octets path))
                                             encoded (lambda () encoded))
            (let ((class (fnn-core 'fn-native-control-host-status-class status))
                  (code (fnn-core 'fn-native-control-host-status-exit-code status)))
              (fnn-operator-emit-status class command
                                        (fnn-operator-status-detail status word))
              code)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status
           (fnn-operator-status-of-exit-code code) command condition)
          code)))))

(defun fnn-operator-store-max-credentials (root)
  "The store profile's max-credentials (D27, PRF-102), read from config.json
without the writer lock: principal administration does not open the store.
The profile is written once, at init or import (D34), so this read sees the
bound the owner loads under."
  (let ((store (make-fnn-store root)))
    (fnn-load-config store)
    (fnn-profile-nat 'fn-store-profile-max-credentials store)))

(defun fnn-operator-execute-principal (result)
  "Execute only the credential plan and credential path projected by ACL2.
The configured store is the one whose writer lock says whether an owner is
serving the old credentials (fn-native-auth-admin-effect-word), and whose
profile bounds the credentials (max-credentials, D27, PRF-102)."
  (let ((*fnn-native-auth-admin-store-root*
          (fnn-octets-string
           (fnn-core 'fn-native-operator-host-result-principal-store-octets
                     result)))
        (*fnn-native-auth-admin-control-path*
          (let ((control (fnn-core
                          'fn-native-operator-host-result-principal-control-path-octets
                          result)))
            (and (fnn-octet-list-p control) (consp control)
                 (fnn-octets-string (fnn-octets control))))))
    (let ((code (fnn-native-auth-admin-execute
                 (fnn-core 'fn-native-operator-host-result-principal-plan result)
                 (fnn-octets-string
                  (fnn-core 'fn-native-operator-host-result-principal-auth-path-octets
                            result))
                 (fnn-operator-store-max-credentials
                  (fnn-core 'fn-native-operator-host-result-store-root result)))))
      ;; PRF-388 (PKT-560): ACL2 answered that the credential file does not
      ;; hold the login of `bind|unbind' (:account); its `account
      ;; bind|unbind' result is dispatched like any operator result, live to
      ;; the owner or offline into the store, where fn-lb-account-bind-plan
      ;; admits it only for a redeemed account.
      (if (eq code :account)
          (fnn-operator-dispatch-plan
           (fnn-core 'fn-native-operator-host-result-principal-account-result result))
        code))))

;;; The running owner, as operator.lisp's offline verbs ask it.

(defun fnn-operator-live-socket-present (control-path)
  (fnn-control-socket-path-p (fnn-lstat (fnn-octets-string control-path))))

(defun fnn-operator-live-status-tail (control-path kind)
  ;; PRF-212: the certificate the running owner serves, its names and
  ;; notAfter, in ACL2's words.
  (when (eq kind :status) (fnn-tls-status-line control-path)))

(defun fnn-operator-live-admin-observe (root control-path-list queryp)
  "PKT-344: two observations, ACL2's decision (fn-native-control-liveness-decides):
a socket node with the lock free or absent is a crashed owner's (:stale), and
only a free or absent lock starts the offline executor.  A :stale node is
removed under the control-path lease; a query does not use the :held arm (the
read-only executor's own shared lock answers it), so it prints only the
:stale note."
  (let* ((socket-path (and (fnn-octet-list-p control-path-list)
                           (consp control-path-list)
                           (fnn-octets control-path-list)))
         (liveness (fnn-core 'fn-native-control-host-liveness
                             (and socket-path
                                  (fnn-operator-live-socket-present socket-path)
                                  t)
                             (fnn-store-owner-observation root)))
         (note (fnn-core 'fn-native-control-host-liveness-note liveness)))
    (when (eq liveness :stale)
      (fnn-control-remove-stale-offline socket-path))
    (when (and (stringp note) (or (not queryp) (eq liveness :stale)))
      (fnn-err "~a" note))
    liveness))

(defun fnn-operator-live-admin (control-path argv liveness)
  "The exit code and detail of an administrative vector: the live owner's
answer (:live), or the refusal of a store whose lock an owner holds (:held)."
  (if (eq liveness :held)
      (values (fnn-core 'fn-native-control-host-status-exit-code :refused) nil)
    (multiple-value-bind (status word line)
        (fnn-control-admin control-path argv)
      ;; Row S1: a reply that carries the owner's line (a limit decision,
      ;; books/native-control-line.lisp kind 23) prints that line, ACL2's
      ;; octets (fn-native-control-printed-line-is-the-decisions).
      (let ((printed (and line (fnn-core 'fn-native-control-host-lined-detail
                                         (list :status status word line))))
            (detail (fnn-operator-status-detail status word)))
        (values (fnn-core 'fn-native-control-host-status-exit-code status)
                (cond ((fnn-octet-list-p printed)
                       (format nil "~a ~a" status (fnn-octets-string (fnn-octets printed))))
                      ((not (eq detail status)) detail)))))))

(defun fnn-operator-live-request (control-path argv)
  "PKT-868: an administrative vector the live owner answers with a word of
its own state (the compaction request): the exit code of ACL2's status, and
the word printed as ACL2 rendered it (the reply detail names only refusals)."
  (multiple-value-bind (status word) (fnn-control-admin control-path argv)
    (when (fnn-octet-list-p word)
      (fnn-out "compaction ~a" (fnn-octets-string (fnn-octets word))))
    (fnn-core 'fn-native-control-host-status-exit-code status)))

(setq *fnn-operator-live-owner*
      (make-fnn-operator-live-owner
       :socket-present #'fnn-operator-live-socket-present
       :live-status #'fnn-control-live-status
       :status-tail #'fnn-operator-live-status-tail
       :admin-observe #'fnn-operator-live-admin-observe
       :admin #'fnn-operator-live-admin
       :request #'fnn-operator-live-request))

(fnn-operator-register-action :run #'fnn-operator-execute-run)
(fnn-operator-register-action :post #'fnn-operator-execute-post)
(fnn-operator-register-action :moderate #'fnn-operator-execute-moderate)
(fnn-operator-register-action :principal #'fnn-operator-execute-principal)
(fnn-operator-register-action :peering #'fnn-pinv-execute)
(fnn-operator-register-action :keys #'fnn-keys-execute)
(fnn-operator-register-action :tls #'fnn-tls-execute)
