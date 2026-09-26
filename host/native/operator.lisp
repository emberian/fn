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
  "ACL2's hint line (what the command accepts, or what to do), if any, then
the one tagged result line."
  (let ((hint (fnn-core 'fn-native-operator-host-result-hint result)))
    (when (stringp hint) (fnn-err "~a" hint)))
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

(defun fnn-operator-execute-show (result)
  "Print ACL2's rendering of the configuration (PKT-096); decide nothing."
  (let ((octets (fnn-core 'fn-native-operator-host-result-show-octets result)))
    (unless (fnn-octet-list-p octets)
      (fnn-fault "ACL2 show action returned no octets"))
    (write-sequence (fnn-octets octets) *fnn-stdout*)
    (unless (and (consp octets) (eql (car (last octets)) 10))
      (write-sequence (fnn-octets (list 10)) *fnn-stdout*))
    (finish-output *fnn-stdout*)
    (fnn-operator-emit-status :accepted "show")
    +fnn-exit-ok+))

(defun fnn-operator-execute-mission (result config-path)
  "Write the mission's fn.toml, ACL2's rendering, at CONFIG-PATH (PKT-097).

The observation is lstat of CONFIG-PATH; ACL2 refuses an existing file.  The
file is created exclusively, so a racing writer is refused by open(2), never
overwritten.  The directories ACL2 names are created if absent."
  (let ((status (fnn-core 'fn-native-operator-host-result-status result)))
    (if (not (eq status :accepted))
        (progn (fnn-operator-emit-result result)
               (fnn-core 'fn-native-operator-host-result-exit-code result))
      (handler-case
          (let ((outcome (fnn-core 'fn-native-operator-host-mission-outcome
                                   result (and (fnn-lstat config-path) t))))
            (if (not (eq (fnn-core 'fn-native-operator-host-result-status outcome)
                         :accepted))
                (progn (fnn-operator-emit-result outcome)
                       (fnn-core 'fn-native-operator-host-result-exit-code outcome))
              (let ((octets (fnn-core 'fn-native-operator-host-result-mission-octets
                                      result))
                    (dirs (fnn-core
                           'fn-native-operator-host-result-mission-directory-octets
                           result)))
                (unless (and (fnn-octet-list-p octets) (listp dirs)
                             (every #'fnn-octet-list-p dirs))
                  (fnn-fault "ACL2 mission plan is malformed"))
                (dolist (dir dirs)
                  (let ((path (fnn-octets-string (fnn-octets dir))))
                    (unless (fnn-lstat path) (fnn-mkdir path #o700))))
                (let ((fd (fnn-open config-path
                                    (logior sb-posix:o-wronly sb-posix:o-creat
                                            sb-posix:o-excl +fnn-o-nofollow+)
                                    #o640)))
                  (unwind-protect
                       (progn (fnn-write-all fd (fnn-octets octets))
                              (fnn-fsync-file fd))
                    (fnn-close fd)))
                (fnn-out "wrote ~a" config-path)
                (fnn-operator-emit-status :accepted "mission")
                +fnn-exit-ok+)))
        (error (condition)
          (let ((code (fnn-exit-code-for condition)))
            (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                      "mission" condition)
            code))))))

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
        (setq *fnn-health-min-percent*
              (fnn-core 'fn-native-operator-host-result-health-min-percent result))
        (unwind-protect
            (progn
              ;; Append-only, created 0640 if absent, never through a
              ;; symlink, never truncated or rotated here.  Opened before
              ;; the store so a wrong path is refused before recovery runs.
              (when log-path
                (setq *fnn-owner-log-fd* (fnn-owner-open-log log-path)
                      *fnn-owner-log-path* log-path))
              ;; ACL2 already enforced paired presence.  Only a successfully
              ;; loaded and key-checked context is passed to auth/owner.
              (when certificate
                (setq tls-context
                      (fnn-tls-open-context certificate private-key)))
              (let* ((*fnn-owner-startup-hooks*
                       (list (fnn-native-auth-startup-hook
                              auth-path auth-required auth-protected)))
                     ;; The NEWNEWS pull feed (PRF-100) is a sibling lifecycle
                     ;; extension: host/native/pull-service.lisp.
                     (*fnn-owner-start-hooks*
                       (list* #'fnn-feed-service-start #'fnn-pull-service-start
                              *fnn-owner-start-hooks*))
                     (*fnn-owner-stop-hooks*
                       (list* #'fnn-feed-service-wake #'fnn-pull-service-wake
                              *fnn-owner-stop-hooks*))
                     (*fnn-owner-close-hooks*
                       (list* #'fnn-feed-service-close #'fnn-pull-service-close
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
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "run")
                code))
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
               ;; PKT-344: two observations, ACL2's decision
               ;; (fn-native-control-liveness-decides): a socket node with
               ;; the lock free or absent is a crashed owner's (:stale), and
               ;; only a free or absent lock starts the offline executor.
               (socket-path (and (fnn-octet-list-p control-path-list)
                                 (consp control-path-list)
                                 (not (fnn-image-omits-p :control))
                                 (fnn-octets control-path-list)))
               ;; An image without the control surface (the DTN image)
               ;; loads neither the decision nor the socket code: it has no
               ;; socket to observe, and its executor's exclusive lock
               ;; refuses a held store, as before PKT-344.
               (liveness
                 (if (fnn-image-omits-p :control)
                     :offline
                   (fnn-core 'fn-native-control-host-liveness
                             (and socket-path
                                  (fnn-control-socket-path-p
                                   (fnn-lstat (fnn-octets-string socket-path)))
                                  t)
                             (fnn-store-owner-observation root))))
               (note (and (not (fnn-image-omits-p :control))
                          (fnn-core 'fn-native-control-host-liveness-note liveness)))
               (livep (and control-path (eq liveness :live)))
               (code
                 (progn
                  (when (eq liveness :stale)
                    (fnn-control-remove-stale-offline socket-path))
                  ;; A query does not use the :held arm (the read-only
                  ;; executor's own shared lock answers it), so it prints
                  ;; only the :stale note.
                  (when (and (stringp note) (or (not queryp) (eq liveness :stale)))
                    (fnn-err "~a" note))
                  (cond
                   ;; A query publishes no configuration record, so it has
                   ;; nothing to send the live owner and nothing to serialize
                   ;; behind its mutex: the read-only executor is the only
                   ;; one, live socket or not.
                   ;; The report kind is the plan's
                   ;; (fn-native-admin-result-report-kind): `control list'
                   ;; reports the authority rows, `peer list' the peers.
                   ((and queryp (fnn-admin-plan-acceptedp plan))
                    (fnn-operator-status-once
                     root (and (fnn-octet-list-p control-path-list)
                               (consp control-path-list)
                               (fnn-octets control-path-list))
                     (fnn-core 'fn-native-admin-host-report-kind plan)))
                   (queryp (fnn-admin-query root plan))
                   (livep
                    (fnn-core 'fn-native-control-host-status-exit-code
                              (fnn-control-admin control-path argv)))
                   ((eq liveness :held)
                    (fnn-core 'fn-native-control-host-status-exit-code :refused))
                   (t (fnn-admin-execute root plan))))))
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
; And `fnn-command-reclaim' (`store reclaim [--dry-run]', STO-017).
(defvar *fnn-reclaim-callback* nil)

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
                      (:reclaim (funcall *fnn-reclaim-callback* root nil))
                      (:reclaim-dry-run (funcall *fnn-reclaim-callback* root t))
                      (:checkpoint (fnn-command-state-checkpoint root))
                      (:needs-upgrade (fnn-command-needs-upgrade root))
                      (:rollback-check
                       (fnn-command-rollback-check
                        root
                        (fnn-octets-string
                         (fnn-core 'fn-native-operator-host-result-rollback-path-octets
                                   result))))
                      (:rollback-snapshot
                       (fnn-command-rollback-snapshot
                        root
                        (fnn-octets-string
                         (fnn-core 'fn-native-operator-host-result-snapshot-path-octets
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

;;; The health verdict (`health', PRF-112).
;;;
;;; The running owner renders it over its control socket from the Store,
;;; configuration and feed table it carries; with none, the Store is opened
;;; read-only unless the host's observations say it is fenced.  ACL2 decides
;;; which (fn-nls-route, fn-nh-fence-of), renders every word
;;; (books/native-health.lisp), and reads the exit code back from the octets
;;; the host prints (fn-nh-report-exit-of-render).

(defun fnn-operator-health-report (root control-path min)
  "The health report's octets, or :refused when the owner refused to answer."
  (let* ((socket-present
           (and control-path
                (not (fnn-image-omits-p :control))
                (fnn-control-socket-path-p
                 (fnn-lstat (fnn-octets-string control-path)))))
         (answer (if socket-present
                     (fnn-control-live-status control-path :health)
                   :none)))
    (if (and (consp answer) (eq (first answer) :done))
        (second answer)
      (let ((route (fnn-core 'fn-native-live-status-host-route socket-present answer)))
        (if (eq route :refused)
            :refused
          (or (fnn-core 'fn-native-health-host-fenced route
                        (fnn-store-owner-observation root)
                        (and (fnn-lstat (fnn-clone-fence-path (make-fnn-store root))) t)
                        ;; Would an owner listen at all: a configured socket
                        ;; in an image that has one (an observation; ACL2's
                        ;; fn-nh-fence-of decides :starting from it).
                        (and control-path (not (fnn-image-omits-p :control)) t))
              (multiple-value-bind (store records) (fnn-open-live-store root nil)
                (declare (ignore records))
                (unwind-protect
                     (fnn-core 'fn-native-health-host-offline
                               (fnn-store-config store) min *the-live-state*)
                  (fnn-store-close store)))))))))

(defun fnn-operator-execute-health (result)
  (let* ((root (fnn-core 'fn-native-operator-host-result-store-root result))
         (path-list (fnn-core
                     'fn-native-operator-host-result-status-control-path-octets
                     result))
         (control-path (and (fnn-octet-list-p path-list) (consp path-list)
                            (fnn-octets path-list)))
         (min (fnn-core 'fn-native-operator-host-result-health-min-percent result)))
    (handler-case
        (let ((report (fnn-operator-health-report root control-path min)))
          (if (eq report :refused)
              (progn (fnn-operator-emit-status :refused "health")
                     +fnn-exit-refused+)
            (let ((code (fnn-core 'fn-native-health-host-exit report)))
              (unless (and (integerp code) (<= 0 code 99))
                (fnn-fault "ACL2 health report carries no exit code"))
              (fnn-write-report report)
              (fnn-operator-emit-status :accepted "health")
              code)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "health" condition)
          code)))))

(defun fnn-operator-store-max-credentials (root)
  "The store profile's max-credentials (D27, PRF-102), read from config.json
without the writer lock: principal administration does not open the store.
The profile only rises (fn-profile-upgradep), so a read that races an
upgrade sees a bound no larger than the one the owner will load under."
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
    (fnn-native-auth-admin-execute
     (fnn-core 'fn-native-operator-host-result-principal-plan result)
     (fnn-octets-string
      (fnn-core 'fn-native-operator-host-result-principal-auth-path-octets
                result))
     (fnn-operator-store-max-credentials
      (fnn-core 'fn-native-operator-host-result-store-root result)))))

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

(defun fnn-operator-store-outcome (result)
  "HST-008: an accepted plan that needs a store, over a root holding none of
the store's entries, becomes ACL2's :no-store refusal before any open
(fn-native-operator-store-outcome, PRF-130).  The observation is the lstat
one `init' makes; nothing is opened or locked."
  (if (eq (fnn-core 'fn-native-operator-host-result-status result) :accepted)
      (let ((root (fnn-core 'fn-native-operator-host-result-store-root result)))
        (fnn-core 'fn-native-operator-host-store-outcome result
                  (and (stringp root)
                       (fnn-operator-init-observed (fnn-absolute root)))))
    result))

;;; `store inspect MESSAGE-ID' (NNT-032): the operator's settling lookup.
;;; The host opens the stopped store exactly as `recover' does (a live
;;; owner's lock refuses it), asks the store node whether it binds the
;;; Message-ID, and prints ACL2's report line: accepted (exit 0) or absent
;;; (exit 1).  The host decides nothing.
(defun fnn-operator-execute-inspect (result)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (msgid-list (fnn-core 'fn-native-operator-host-result-inspect-msgid-octets
                              result)))
    (unless (and (fnn-octet-list-p msgid-list) (consp msgid-list))
      (fnn-fault "ACL2 accepted an inspect plan with no Message-ID"))
    (handler-case
        (multiple-value-bind (store records) (fnn-open-live-store root nil)
          (declare (ignore records))
          (unwind-protect
               (let* ((found (fnn-bridge-lookup-found-p (fnn-octets msgid-list)))
                      (report (fnn-core 'fn-native-operator-host-inspect-report
                                        msgid-list found)))
                 (unless (and (consp report) (member (first report) '(0 1))
                              (member (second report) '(:accepted :absent))
                              (stringp (third report)))
                   (fnn-fault "ACL2 returned a malformed inspect report"))
                 (fnn-out "~a" (third report))
                 (if (eql (first report) 0) +fnn-exit-ok+ +fnn-exit-refused+))
            (fnn-store-close store)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "inspect" condition)
          code)))))

(defun fnn-operator-dispatch-plan (result0)
  (let* ((result (fnn-operator-store-outcome result0))
         (status (fnn-core 'fn-native-operator-host-result-status result)))
    (if (not (eq status :accepted))
        (progn (fnn-operator-emit-result result)
               (fnn-core 'fn-native-operator-host-result-exit-code result))
      (let ((action (fnn-core 'fn-native-operator-host-result-native-action result)))
        (let ((omitted (case action
                         ((:run :post) :nntp-service)
                         (:principal :credentials)
                         ;; peer genesis|invite|accept|confirm reach the owner
                         ;; as control requests 9 to 11 (host/native/peer-invite.lisp).
                         (:peering :control)
                         ;; keys redecide reaches the owner as control
                         ;; request 12 (host/native/keys.lisp).
                         (:keys :control))))
          (when (and (member action '(:reclaim :reclaim-dry-run))
                     (null *fnn-reclaim-callback*))
            (fnn-operator-emit-status
             :usage "action" "reclaim needs the checkpoint surface, which this image omits")
            (return-from fnn-operator-dispatch-plan +fnn-exit-usage+))
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
          (:show (fnn-operator-execute-show result))
          (:init (fnn-operator-execute-init result))
          (:run (fnn-operator-execute-run result))
          (:post (fnn-operator-execute-post result))
          (:status (fnn-operator-execute-status result))
          (:health (fnn-operator-execute-health result))
          ((:recover :upgrade-profile :compact :checkpoint :needs-upgrade
            :rollback-check :rollback-snapshot :reclaim :reclaim-dry-run)
           (fnn-operator-execute-store-action result action))
          (:inspect (fnn-operator-execute-inspect result))
          (:admin (fnn-operator-execute-admin result))
          (:peering (fnn-pinv-execute result))
          (:principal (fnn-operator-execute-principal result))
          (:keys (fnn-keys-execute result))
          (:owner-required
           (fnn-operator-emit-status :usage "action" "requires native owner callback")
           +fnn-exit-usage+)
          (t (fnn-fault "ACL2 operator returned no native action")))))))

(defun fnn-command-operator (config-path argv)
  (let* ((max-arguments (fnn-core 'fn-native-operator-host-argv-max-arguments))
         (max-octets (fnn-core 'fn-native-operator-host-argv-max-octets))
         (argv-octets (fnn-operator-argv-octets argv max-arguments max-octets))
         (preflight (fnn-core 'fn-native-operator-host-preflight argv-octets)))
    (when (fnn-core 'fn-native-operator-host-preflight-needs-config-path-p preflight)
      (return-from fnn-command-operator
        (fnn-operator-execute-mission
         (fnn-core 'fn-native-operator-host-mission-run
                   (fnn-ascii-octet-list config-path) argv-octets)
         config-path)))
    (if (fnn-core 'fn-native-operator-host-preflight-needs-config-p preflight)
        (let* ((config-bound (fnn-core 'fn-native-config-host-max-octets))
               (config-octets (fnn-operator-read-config config-path config-bound)))
          (fnn-operator-dispatch-plan
           (fnn-core 'fn-native-operator-host-run config-octets argv-octets)))
      (fnn-operator-dispatch-plan preflight))))

(fnn-register-verb "operator"
                   (lambda (config-path argv)
                     (fnn-command-operator config-path argv)))
