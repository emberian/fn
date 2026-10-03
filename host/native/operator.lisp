;;; Native `--fn operator CONFIG-PATH COMMAND ...` transport and execution.
;;;
;;; This raw module transports only ASCII argv and bounded configuration octets to
;;; host/native-operator-host.lisp.  ACL2 chooses command grammar, defaults,
;;; profile availability, the result tag, and the exit-code projection.  RUN
;;; installs the local-control lifecycle and POST calls that control socket;
;;; neither command has a direct Store path.  INIT, STATUS and RECOVER are
;;; the offline store actions: they name the store the configuration declares
;;; and run the existing store entry against it, so a node is stood up,
;;; inspected and repaired with the one public verb and one binary.
;;;
;;; What this file does not carry: the NNTP service (`run', `post'), credential
;;; administration (`principal') and every arm that talks to a running owner
;;; over the control socket.  Those are host/native/operator-live.lisp's, which
;;; registers them below when an image loads it; the DTN image
;;; (host/native/build-dtn.lisp) does not, so it has none of those surfaces
;;; and this file calls nothing it lacks (`tools/host_check.py --load --build
;;; host/native/build-dtn.lisp').

(in-package "ACL2")

;;; The surfaces an image carries are the files it loaded.  An action that
;;; needs one names it here; its executor is registered by the file that
;;; implements it, and an image without that file refuses the action by the
;;; surface's name (the usage exit) before anything runs.
(defun fnn-operator-action-surface (action)
  (case action
    ((:run :post) :nntp-service)
    (:principal :credentials)
    ;; peer genesis|invite|accept|confirm reach the owner as control
    ;; requests 9 to 11 (host/native/peer-invite.lisp); keys redecide as
    ;; request 12 (host/native/keys.lisp); tls reload as request 19
    ;; (host/native/tls-reload.lisp); moderation approve|reject and article
    ;; withdraw as request 21.
    ((:peering :keys :tls :moderate) :control)
    ;; PKT-869: carry list|inspect|pause|resume|drop over the FNWF journal
    ;; (host/native/bp-obligation.lisp).
    (:carry :workflow)))

(defvar *fnn-operator-surface-executors* nil
  "Alist ACTION -> function of the operator result, one per surface action
this image loaded (fnn-operator-register-action).")

(defun fnn-operator-register-action (action executor)
  (unless (fnn-operator-action-surface action)
    (error "fnn-operator-register-action: ~s names no surface" action))
  (setq *fnn-operator-surface-executors*
        (acons action executor
               (remove action *fnn-operator-surface-executors* :key #'car)))
  action)

;;; The running owner, as the offline verbs (`status', `health', admin,
;;; `account invite') ask it.  NIL in an image without the control socket:
;;; there is no owner of this image to ask, and each verb takes its offline
;;; arm, whose exclusive lock refuses a store another image's owner holds.
;;; host/native/operator-live.lisp installs it.
(defstruct (fnn-operator-live-owner (:conc-name fnn-olo-))
  ;; (path-octets) -> true when a socket node is at the control path.
  socket-present
  ;; (path-octets kind) -> the owner's answer, fnn-control-live-status's.
  live-status
  ;; (path-octets kind) -> after a live report is written, its trailing lines.
  status-tail
  ;; (root control-path-list queryp) -> the admin liveness decision
  ;; (:live :stale :offline :held), a :stale node removed and ACL2's note
  ;; printed, as fn-native-control-liveness-decides decides.
  admin-observe
  ;; (control-path argv liveness) -> exit code and the detail word of an
  ;; administrative vector the live owner (:live) or its lock (:held) answered.
  admin
  ;; (control-path argv) -> exit code, the owner's answer word printed: the
  ;; compaction request (PKT-868).
  request)

(defvar *fnn-operator-live-owner* nil)

(defun fnn-operator-argv-octets (texts)
  "The argv as ASCII octet lists, as the kernel handed it (PKT-867: no word
count or length here; ACL2's grammar judges every word)."
  (mapcar (lambda (text)
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

;;; Row Q10a: the self-signed pair ACL2 asks for (books/tls-self-signed.lisp;
;;; host/native/tls.lisp fnn-tls-self-signed-write).  NIL when there is none
;;; to make or it was written; else ACL2's refusal, to emit.
(defun fnn-operator-make-self-signed (result)
  (let ((request (fnn-core 'fn-native-operator-host-result-self-signed result)))
    (when request
      (destructuring-bind (names days cert-octets key-octets) request
        (unless (and (fnn-octet-list-p cert-octets) (fnn-octet-list-p key-octets))
          (fnn-fault "ACL2 returned malformed self-signed paths"))
        (let* ((cert-path (fnn-octets-string (fnn-octets cert-octets)))
               (key-path (fnn-octets-string (fnn-octets key-octets)))
               (outcome (fnn-core 'fn-native-operator-host-self-signed-outcome result
                                  (and (fnn-lstat cert-path) t)
                                  (and (fnn-lstat key-path) t))))
          (if (not (eq (fnn-core 'fn-native-operator-host-result-status outcome) :accepted))
              outcome
            (let ((written (fnn-tls-self-signed-write names days cert-path key-path)))
              (if (eq written :written)
                  (progn (fnn-out "wrote ~a and ~a" cert-path key-path) nil)
                (fnn-core 'fn-native-operator-host-self-signed-refused result written)))))))))

(defun fnn-operator-execute-tls-self-signed (result)
  "`tls self-signed NAME... [--days N]': the pair at tls_cert and tls_key."
  (handler-case
      (let ((refused (fnn-operator-make-self-signed result)))
        (if refused
            (progn (fnn-operator-emit-result refused)
                   (fnn-core 'fn-native-operator-host-result-exit-code refused))
          (progn (fnn-operator-emit-status :accepted "tls")
                 +fnn-exit-ok+)))
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "tls" condition)
        code))))

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
                ;; Row Q10a: `--tls-port' -- the pair first, so fn.toml never
                ;; names files the image did not make.
                (let ((refused (fnn-operator-make-self-signed result)))
                  (when refused
                    (fnn-operator-emit-result refused)
                    (return-from fnn-operator-execute-mission
                      (fnn-core 'fn-native-operator-host-result-exit-code refused))))
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

;;; friend-path-2: the service log's run lines.  `run' writes ACL2's
;;; `run started' line when it opens `[log] path' and its `run stopped
;;; exit=NN reason=...' line before it closes it; `health' and `status', with
;;; no owner running, read the log's tail and ACL2 takes the last of those
;;; lines (books/native-health.lisp fn-nh-last-run).  Nothing here parses.

(defun fnn-operator-log-run-line (octets)
  "Append ACL2's run line and one LF to the open service log, directly (the
log writer is not running at either end of `run').  A failed write stops
nothing: the log is an operator's record."
  (when (and *fnn-owner-log-fd* (fnn-octet-list-p octets))
    (ignore-errors
     (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
       (fnn-write-all *fnn-owner-log-fd* (fnn-octets (append octets (list 10))))))))

(defun fnn-operator-log-tail (path)
  "At most ACL2's fn-nh-log-tail-octets octets from the end of the regular,
non-symlink file PATH, as an octet list; NIL when it cannot be read."
  (ignore-errors
   (let ((info (fnn-lstat path)))
     (when (and info (fnn-regular-p info))
       (let ((limit (fnn-core 'fn-native-health-host-log-tail-octets))
             (fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
         (unwind-protect
              (let* ((size (sb-posix:stat-size (fnn-fstat fd)))
                     (start (max 0 (- size limit)))
                     (want (- size start))
                     (buffer (fnn-make-octets want))
                     (offset 0))
                (sb-posix:lseek fd start sb-posix:seek-set)
                (loop while (< offset want) do
                  (let* ((chunk (fnn-make-octets (- want offset)))
                         (count (fnn-read-fd fd chunk)))
                    (when (zerop count) (return))
                    (replace buffer chunk :start1 offset :end2 count)
                    (incf offset count)))
                (fnn-octet-list (subseq buffer 0 offset)))
           (fnn-close fd)))))))

(defun fnn-operator-last-run (result)
  "ACL2's reading of the service log's last run line (fn-nh-last-run)."
  (let* ((path-list (fnn-core 'fn-native-operator-host-result-status-log-path-octets
                              result))
         (tail (and (fnn-octet-list-p path-list) (consp path-list)
                    (fnn-operator-log-tail
                     (fnn-octets-string (fnn-octets path-list))))))
    (fnn-core 'fn-native-health-host-last-run tail)))

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
              ;; PKT-582: ACL2 decides what init writes within the budget and
              ;; says so (books/heap-reservation.lisp fn-heap-init-decide);
              ;; a refusal is printed by name and nothing is created.
              ;; Finding R1 (public-node rehearsal): a named budget below the
              ;; machine init observes is ACL2's warning here, by name with
              ;; both figures, not a refusal at the service's first start.
              (multiple-value-bind (decision note)
                  (let ((request (fnn-core
                                  'fn-native-operator-host-result-init-profile result)))
                    (unless (consp request)
                      (fnn-fault "ACL2 accepted an init plan with no store profile"))
                    (fnn-heap-init-decision-noted
                     request
                     (fnn-core 'fn-native-operator-host-result-init-budget result)
                     (fnn-core 'fn-native-operator-host-result-init-sizing result)))
              (let* ((line (fnn-core 'fn-heap-init-report-line decision))
                     (warning (fnn-core 'fn-heap-init-budget-note-line note))
                     (profile (fnn-core 'fn-heap-init-decision-request decision))
                     (code (if (consp profile)
                               (progn (fnn-out "~a" line)
                                      (when (stringp warning)
                                        (fnn-err "fn: ~a" warning))
                                      (fnn-command-init-published
                                       root groups profile
                                       ;; PKT-648: the store's durability policy,
                                       ;; 1 under a mission (fn-smid-init-policy).
                                       (fnn-core 'fn-smid-init-policy
                                                 (fnn-core 'fn-native-operator-host-result-config-mission
                                                           result))))
                             (progn (fnn-err "fn: ~a" line)
                                    (fnn-core 'fn-heap-init-exit-code decision)))))
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "init")
                code)))))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "init" condition)
          code)))))

(defun fnn-operator-apply-admin (root control-path-list argv plan)
  "Apply the accepted administrative PLAN (ARGV its words) to the running
owner when ACL2's liveness decision says one holds the store, else offline:
the exit code and the live owner's refusal detail.  PKT-344: the liveness is
ACL2's over two observations (fn-native-control-liveness-decides), taken by
the live-owner surface, which also clears a stale socket node; an image
without that surface (the DTN image) has no socket to observe, and its
executor's exclusive lock refuses a held store.  Every mutating admin verb
dispatches here (`peer login', `account invite' too: sweep S104)."
  (let* ((control-path (and (fnn-octet-list-p control-path-list)
                            (fnn-octets control-path-list)))
         (live *fnn-operator-live-owner*)
         (liveness (if live
                       (funcall (fnn-olo-admin-observe live)
                                root control-path-list nil)
                     :offline)))
    (if (member liveness '(:live :held))
        (funcall (fnn-olo-admin live) control-path argv liveness)
      (values (fnn-admin-execute root plan) nil))))

(defun fnn-operator-execute-admin (result)
  "Execute only the exact accepted ACL2 administrative plan."
  (let ((live-detail nil)
        (root (fnn-core 'fn-native-operator-host-result-store-root result))
        (command (fnn-core 'fn-native-operator-host-result-command result))
        (plan (fnn-core 'fn-native-operator-host-result-admin-plan result))
        (argv (fnn-core 'fn-native-operator-host-result-admin-argv result))
        (control-path-list
          (fnn-core 'fn-native-operator-host-result-admin-control-path-octets
                    result)))
    (handler-case
        (let* ((queryp (fnn-core 'fn-native-admin-host-queryp plan))
               (code
                 (progn
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
                   (t (multiple-value-bind (exit detail)
                          (fnn-operator-apply-admin root control-path-list
                                                    argv plan)
                        (when detail (setq live-detail detail))
                        exit))))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) command
                                    live-detail)
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    command condition)
          code)))))

;;; PRF-164 (PKT-439): `account invite [--expires SECONDS]'.  The host
;;; reads the CSPRNG; ACL2 renders the code and its digest
;;; (books/accounts.lisp); the digest-only vector is planned by
;;; fn-native-admin-plan and published live through the control socket, or
;;; offline into the configuration when no owner runs (the `peer add'
;;; pattern).  The code is printed once, to stdout, and only after the
;;; pending row is durable; it is never logged, stored or put in an argv.
(defun fnn-operator-account-entropy ()
  (fnn-csprng-octets (fnn-core 'fn-acct-host-entropy-octets) "invitation code"))

(defun fnn-operator-execute-account-invite (result)
  (let* ((root (fnn-core 'fn-native-operator-host-result-store-root result))
         (seconds (fnn-core 'fn-native-operator-host-result-account-invite-seconds
                            result))
         (control-path-list
           (fnn-core 'fn-native-operator-host-result-account-control-path-octets
                     result)))
    (handler-case
        (let* ((code (fnn-core 'fn-acct-host-code-text
                               (fnn-operator-account-entropy)))
               (digest (and (stringp code)
                            (fnn-core 'fn-acct-host-code-digest-text
                                      (fnn-ascii-octet-list code))))
               (argv (and (stringp digest)
                          (fnn-core 'fn-acct-host-invite-argv digest seconds)))
               (plan (and argv (fnn-core 'fn-native-admin-host-plan argv)))
               (exit
                 (progn
                   (unless (and (stringp code) (stringp digest)
                                (fnn-admin-plan-acceptedp plan))
                     (fnn-fault "ACL2 refused its own invitation vector"))
                   (values (fnn-operator-apply-admin root control-path-list
                                                     argv plan)))))
          (when (eql exit +fnn-exit-ok+)
            (write-sequence (fnn-octets (fnn-ascii-octet-list
                                         (format nil "~a~%" code)))
                            *fnn-stdout*)
            (finish-output *fnn-stdout*))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code exit)
                                    "account")
          exit)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "account" condition)
          code)))))

;;; PKT-597, PKT-786: `account hash LOGIN'.  The host reads the current key
;;; file STORE/keys/node-secret.key through fnn-node-secret-read-entry (the
;;; checks the owner makes at start; ACL2 parses it) and the configuration's
;;; credential file under the store profile's max-credentials (the owner's
;;; bounded read, fnn-native-auth-read); ACL2 resolves LOGIN to its account
;;; (the principal the credential file names, else the invitation-code
;;; account's local principal) and computes that account's posting-account
;;; value under the current epoch's `fn/posting-account/v1' key
;;; (books/native-operator.lisp fn-nop-account-hash), and the value is
;;; printed to stdout.  The secret is never printed; nothing is written.
(defun fnn-operator-store-max-credentials (root)
  "The store profile's max-credentials (D27, PRF-102), read from config.json
without the writer lock: principal administration does not open the store.
The profile is written once, at init or import (D34), so this read sees the
bound the owner loads under."
  (let ((store (make-fnn-store root)))
    (fnn-load-config store)
    (fnn-profile-nat 'fn-store-profile-max-credentials store)))

(defun fnn-operator-execute-account-hash (result)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (login (fnn-core 'fn-native-operator-host-result-account-hash-login result))
        (auth-path (fnn-octets-string
                    (fnn-core 'fn-native-operator-host-result-account-hash-auth-path-octets
                              result))))
    (handler-case
        (let* ((store (make-fnn-store root :writable nil))
               (path (fnn-node-secret-path store))
               (current (or (fnn-node-secret-read-entry path "node secret")
                            (fnn-refuse "node secret ~a is missing: run `store ~a node-secret create' once"
                                        path root)))
               (max-credentials (fnn-operator-store-max-credentials root)))
          (multiple-value-bind (octets presentp)
              (fnn-native-auth-read auth-path
                                    (fnn-core 'fn-native-auth-host-max-octets
                                              max-credentials))
          (let ((text (fnn-core 'fn-native-operator-host-account-hash-text
                                (list current) login octets presentp
                                max-credentials)))
            (when (eq text :credential-file-refused)
              (fnn-refuse "credential file ~a is refused" auth-path))
            (unless (stringp text)
              (fnn-refuse "node secret ~a is not a node secret" path))
            (write-sequence (fnn-octets (fnn-ascii-octet-list (format nil "~a~%" text)))
                            *fnn-stdout*)
            (finish-output *fnn-stdout*)
            (fnn-operator-emit-status :accepted "account")
            +fnn-exit-ok+)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "account" condition)
          code)))))

; host/native/checkpoint.lisp installs `fnn-command-compact' here after it
; loads.  An image built without it (the DTN image) has no compaction.
(defvar *fnn-compact-callback* nil)
; And `fnn-command-reclaim' (`store reclaim [--dry-run | --recorded]', STO-017).
(defvar *fnn-reclaim-callback* nil)

(defun fnn-operator-execute-owner-request (result root offline path-fn argv-fn)
  "An operator verb a running owner answers as a request (PKT-868's
compaction, Q16's reclaim): ACL2's liveness decision, then the request vector
ARGV-FN names over the control path PATH-FN names; OFFLINE with no owner."
  (let* ((live *fnn-operator-live-owner*)
         (path-list (fnn-core path-fn result))
         (control-path (and (fnn-octet-list-p path-list) (consp path-list)
                            (fnn-octets path-list)))
         (liveness (if (and live control-path)
                       (funcall (fnn-olo-admin-observe live) root path-list nil)
                     :offline)))
    (cond ((eq liveness :live)
           ;; The owner's answer word (books/owner-compact-request.lisp
           ;; fn-ock-request-word: requested, coalesced, nothing-to-compact,
           ;; or the refusal's blocked), printed as ACL2 rendered it
           ;; (host/native/operator-live.lisp fnn-operator-live-request).
           (funcall (fnn-olo-request live) control-path (fnn-core argv-fn result)))
          ((eq liveness :held)
           (multiple-value-bind (exit detail)
               (funcall (fnn-olo-admin live) control-path (fnn-core argv-fn result)
                        liveness)
             (when detail (fnn-out "~a" detail))
             exit))
          (t (funcall offline)))))

(defun fnn-operator-execute-compaction (result root offline)
  "PKT-868: `store compact' / `store checkpoint'.  A running owner is asked
(ACL2's liveness decision over the socket and the lock, as for an
administrative vector): it answers the compaction request by name and runs
the publication itself, off its mutex (host/native/admin.lisp
fnn-owner-compaction-request).  With no owner, OFFLINE runs as before."
  (fnn-operator-execute-owner-request
   result root offline
   'fn-native-operator-host-result-compaction-control-path-octets
   'fn-native-operator-host-result-compaction-argv))

;;; Row S9: `retire [--drain SECONDS]'.  The running owner is asked
;;; (books/native-retire.lisp's vector; host/native/admin.lisp
;;; fnn-owner-retire-begin answers `retire draining' or refuses by name); with
;;; no owner the verb is refused by name (nothing drains a stopped node).
;;; After the answer the operator waits while ACL2's liveness decision over
;;; the socket and the lock says an owner runs (the owner's drain ends by its
;;; window, books/owner-retire.lisp fn-oret-drain-step-ends-by-the-window).
;;; ACL2 separately bounds this operator's observation; PRF-357 does not
;;; bound a physical final fence.  Expiry is uncertain and leaves the owner
;;; running.  After a stopped observation, print only its fresh report.
(defun fnn-retire-report-path (root)
  (fnn-join root (fnn-octets-string
                  (fnn-octets (fnn-core 'fn-nret-report-file-name)))))

(defun fnn-retire-report-identity (path)
  "(INODE MTIME) of the regular file at PATH, or NIL when it is absent or not a
regular file (a symlink, a directory)."
  (let ((st (fnn-lstat path)))
    (and st (fnn-regular-p st) (not (fnn-symlink-p st))
         (list (sb-posix:stat-ino st) (sb-posix:stat-mtime st)))))

(defvar *fnn-retire-pause* #'sleep
  "Observation scheduling seam; ACL2 supplies the poll interval.")

(defun fnn-operator-execute-retire (result root)
  ;; A report left by an earlier retire is not this drain's report (S103):
  ;; only a regular file that differs from the one present before the request
  ;; is printed.
  (let* ((before (fnn-retire-report-identity (fnn-retire-report-path root)))
         (start (fnn-now))
         (code (fnn-operator-execute-owner-request
               result root
               (lambda ()
                 (fnn-out "~a" (fnn-octets-string (fnn-octets (fnn-core 'fn-nret-not-running-line))))
                 +fnn-exit-refused+)
               'fn-native-operator-host-result-retire-control-path-octets
               'fn-native-operator-host-result-retire-argv)))
    (if (not (eql code +fnn-exit-ok+))
        code
      (let* ((live *fnn-operator-live-owner*)
             (path-list (fnn-core 'fn-native-operator-host-result-retire-control-path-octets
                                  result))
             (argv (fnn-core 'fn-native-operator-host-result-retire-argv result)))
        (loop
          (let* ((liveness (funcall (fnn-olo-admin-observe live) root path-list nil))
                 (step (fnn-core 'fn-nret-observation-step argv start (fnn-now)
                                 internal-time-units-per-second liveness)))
            (case step
              (:report (return))
              (:wait (funcall *fnn-retire-pause*
                              (fnn-core 'fn-nret-observation-poll-seconds)))
              (:uncertain
               (fnn-out "~a" (fnn-octets-string
                              (fnn-octets (fnn-core 'fn-nret-observation-expired-line))))
               (return-from fnn-operator-execute-retire +fnn-exit-uncertain+))
              (:fault
               (fnn-fault "~a" (fnn-octets-string
                                (fnn-octets (fnn-core 'fn-nret-observation-fault-line)))))
              (t (fnn-fault "ACL2 returned a malformed retire observation decision")))))
        (let* ((report (fnn-retire-report-path root))
               (after (fnn-retire-report-identity report)))
          (if (and after (not (equal after before)))
              (with-open-file (in report :element-type '(unsigned-byte 8))
                (let ((buffer (make-array (file-length in) :element-type '(unsigned-byte 8))))
                  (read-sequence buffer in)
                  (fnn-emit *fnn-stdout* (fnn-octets-string buffer))
                  +fnn-exit-ok+))
            (progn
              (fnn-out "~a" (fnn-octets-string (fnn-octets (fnn-core 'fn-nret-no-report-line))))
              +fnn-exit-uncertain+)))))))

(defun fnn-operator-execute-store-action (result action)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result)))
    (handler-case
        (let ((code (case action
                      (:status (fnn-command-status
                                root (fnn-core 'fn-omr-status-replayp result)))
                      (:recover
                       ;; Row S3: with an owner, ACL2's route answers
                       ;; (fn-omr-route); the offline recover runs only when
                       ;; no owner holds the store.
                       (let ((route (fnn-operator-maintenance-route result root)))
                         (if (eq route :offline)
                             ;; ACL2's parse: (:recover) or (:recover AT), the
                             ;; operator's confirmed repair (books/native-operator.lisp).
                             (let ((at (second (fnn-core 'fn-native-operator-result-arguments result))))
                               (fnn-command-recover root (and (stringp at)
                                                              (list "--repair" "truncate" at))))
                           (fnn-operator-execute-recover-live route root result))))
                      (:compact (fnn-operator-execute-compaction
                                 result root (lambda () (funcall *fnn-compact-callback* root))))
                      ;; Q16: on a running owner, a request for its reclaim
                      ;; pass (host/native/admin.lisp fnn-owner-reclaim-request).
                      ((:reclaim :reclaim-dry-run :reclaim-recorded)
                       (fnn-operator-execute-owner-request
                        result root
                        (lambda ()
                          (funcall *fnn-reclaim-callback* root
                                   (case action
                                     (:reclaim :reclaim)
                                     (:reclaim-dry-run :dry-run)
                                     (t :recorded))))
                        'fn-native-operator-host-result-reclaim-control-path-octets
                        'fn-native-operator-host-result-reclaim-argv))
                      (:checkpoint (fnn-operator-execute-compaction
                                    result root (lambda () (fnn-command-state-checkpoint root))))
                      (:rebind-filesystem
                       (fnn-command-rebind-filesystem
                        root
                        (fnn-core 'fn-native-operator-host-result-rebind-policy result)))
                      ;; Row S3b: with an owner, ACL2's route answers
                      ;; (fn-omr-route): the running owner writes the
                      ;; archive while serving (fnn-operator-execute-export-live);
                      ;; the offline export runs only when no owner holds
                      ;; the store.
                      (:export
                       (let ((dir (fnn-octets-string
                                   (fnn-core 'fn-native-operator-host-result-archive-path-octets
                                             result))))
                         (case (fnn-operator-maintenance-route result root)
                           (:owner (fnn-operator-execute-export-live result dir))
                           (:held (fnn-out "~a" (fnn-core 'fn-omr-held-line "export"))
                                  +fnn-exit-refused+)
                           (t (fnn-command-store-export root dir)))))
                      (:export-status
                       (case (fnn-operator-maintenance-route result root)
                         (:owner (fnn-operator-execute-export-status result))
                         (:held (fnn-out "~a" (fnn-core 'fn-omr-held-line "export"))
                                +fnn-exit-refused+)
                         (t (fnn-out "~a" (fnn-core 'fn-oex-status-no-owner-line))
                            +fnn-exit-refused+)))
                      (:bless-snapshot
                       (fnn-command-store-bless-snapshot
                        (fnn-octets-string
                         (fnn-core 'fn-native-operator-host-result-archive-path-octets
                                   result))))
                      (:import
                       (fnn-command-store-import
                        root
                        (fnn-octets-string
                         (fnn-core 'fn-native-operator-host-result-archive-path-octets
                                   result))
                        (fnn-core 'fn-native-operator-host-result-import-request result)
                        (fnn-core 'fn-smid-init-policy
                                  (fnn-core 'fn-native-operator-host-result-config-mission
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

(defun fnn-operator-not-running-step (root control-path socket-present answer)
  "ACL2's health step (fn-nh-health-step) over this invocation's observations,
the one decision `health' takes: (:not-running) when an owner would listen,
nothing answers and nothing holds the lock."
  (fnn-core 'fn-native-health-host-step socket-present answer
            (fnn-store-owner-observation root)
            (and (fnn-lstat (fnn-clone-fence-path (make-fnn-store root))) t)
            (and control-path *fnn-operator-live-owner* t)))

(defun fnn-operator-status-once (root control-path kind &optional result)
  (let* ((live *fnn-operator-live-owner*)
         (socket-present
           (and control-path live
                (funcall (fnn-olo-socket-present live) control-path)))
         (answer (if socket-present
                     (funcall (fnn-olo-live-status live) control-path kind)
                   :none)))
    (when (and (consp answer) (eq (first answer) :refused))
      ;; The owner refused by the name ACL2 decided (a report its reply's
      ;; u32 total cannot carry): a refusal, exit 1, with the word.
      (fnn-refuse "live status refused: ~(~a~)" (second answer)))
    (if (and (consp answer) (member (first answer) '(:done :done-pages)))
        (progn (if (eq (first answer) :done-pages)
                   ;; lane obligations-paged: the pages of one version, in
                   ;; order (fn-nlp-pages-join-to-the-report).
                   (fnn-write-report-pages (second answer))
                 (fnn-write-report (second answer)))
               ;; PRF-212: the certificate the running owner serves, its
               ;; names and notAfter, in ACL2's words.
               (funcall (fnn-olo-status-tail live) control-path kind)
               +fnn-exit-ok+)
      (case (fnn-core 'fn-native-live-status-host-route socket-present answer)
        (:offline
         (when (eq kind :operation)
           (fnn-write-report (fnn-core 'fn-native-operation-host-offline))
           (return-from fnn-operator-status-once +fnn-exit-ok+))
         ;; friend-path-2: say first, in ACL2's words, that the node is not
         ;; running and how its last run ended; then the store's facts.
         (when (and result (eq kind :status)
                    (eq (first (fnn-operator-not-running-step
                                root control-path socket-present answer))
                        :not-running))
           (fnn-write-report (fnn-core 'fn-native-health-host-not-running-lines
                                       (fnn-operator-last-run result))))
         ;; Row S3: a stopped store's status is its checkpoint header's
         ;; (fnn-command-stopped-status); `--replay' asks for the replay.
         ;; PRF-996: an offline `status' then names each live limit's three
         ;; values, funded=none (fnn-lim-print-values).
         (let ((code (if (and (eq kind :status)
                              (not (and result (fnn-core 'fn-omr-status-replayp result))))
                         (fnn-command-stopped-status root)
                       (fnn-command-live-report root kind))))
           (when (and (eq kind :status) (eql code +fnn-exit-ok+))
             (fnn-lim-print-values root))
           code))
        (:refused +fnn-exit-refused+)
        (t +fnn-exit-uncertain+)))))

(defun fnn-operator-execute-operation (result)
  "A bounded owner observation; a stopped owner needs no store replay."
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (path (fnn-core 'fn-native-operator-host-result-status-control-path-octets result)))
    (fnn-operator-status-once root (and path (fnn-octets path)) :operation result)))

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
    ;; PKT-648: the store's mount, as this process observes it (live or not).
    (ignore-errors (fnn-filesystem-durability-warn root))
    (loop
      (let ((code (handler-case (fnn-operator-status-once root control-path kind result)
                    (error (condition)
                      (let ((code (fnn-exit-code-for condition)))
                        (fnn-operator-emit-status
                         (fnn-operator-status-of-exit-code code) command condition)
                        (return-from fnn-operator-execute-status code))))))
        ;; PKT-016: the heap figure of this store's profile on this machine
        ;; (books/heap-figure.lisp, ACL2's line).
        (fnn-heap-print-store-line root)
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

(defun fnn-operator-health-report (root control-path min &optional result)
  "The health report's octets, or :refused when the owner refused to answer."
  (let* ((live *fnn-operator-live-owner*)
         (socket-present
           (and control-path live
                (funcall (fnn-olo-socket-present live) control-path)))
         (answer (if socket-present
                     (funcall (fnn-olo-live-status live) control-path :health)
                   :none)))
    (when (and (consp answer) (eq (first answer) :refused))
      (fnn-refuse "live status refused: ~(~a~)" (second answer)))
    ;; Every observation is taken before ACL2 decides (fn-nh-health-step,
    ;; PKT-454): the owner's answer first, then the lock, the clone fence and
    ;; whether an owner would listen (a configured socket in an image that has
    ;; one).
    (let ((step (fnn-core 'fn-native-health-host-step socket-present answer
                          (fnn-store-owner-observation root)
                          (and (fnn-lstat (fnn-clone-fence-path (make-fnn-store root))) t)
                          (and control-path *fnn-operator-live-owner* t))))
      (case (first step)
        ((:answered :fenced) (second step))
        (:refused :refused)
        ;; friend-path-2: nothing runs where an owner would listen.
        ;; Row S3: a stopped store's health is its checkpoint header's
        ;; (fnn-stopped-report), nothing replayed; MIN has no headroom to
        ;; judge without an owner.
        (:not-running
         (fnn-stopped-report root :health (and result (fnn-operator-last-run result))))
        (t (fnn-stopped-report root :health nil))))))

(defun fnn-operator-execute-health (result)
  (let* ((root (fnn-core 'fn-native-operator-host-result-store-root result))
         (path-list (fnn-core
                     'fn-native-operator-host-result-status-control-path-octets
                     result))
         (control-path (and (fnn-octet-list-p path-list) (consp path-list)
                            (fnn-octets path-list)))
         (min (fnn-core 'fn-native-operator-host-result-health-min-percent result)))
    ;; PKT-648: the store's mount, as this process observes it (live or not).
    (ignore-errors (fnn-filesystem-durability-warn root))
    (handler-case
        (let ((report (fnn-operator-health-report root control-path min result)))
          (if (eq report :refused)
              (progn (fnn-operator-emit-status :refused "health")
                     +fnn-exit-refused+)
            (let ((code (fnn-core 'fn-native-health-host-exit report)))
              (unless (and (integerp code) (<= 0 code 99))
                (fnn-fault "ACL2 health report carries no exit code"))
              (fnn-write-report report)
              (fnn-heap-print-store-line root)
              (fnn-operator-emit-status :accepted "health")
              code)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "health" condition)
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

(defun fnn-operator-store-outcome (result)
  "HST-008: an accepted plan that needs a store, over a root holding none of
the store's entries, becomes ACL2's :no-store refusal before any open
(fn-native-operator-store-outcome, PRF-130), or, when an interrupted init or
import left its stage beside the root, the :interrupted-init or
:interrupted-import refusal naming that stage (fn-nsst-store-outcome,
PRF-971; PKT-781).  The observation is the lstat one `init' makes, and the
stage lookup init and import make (fnn-import-leftover-stage), taken only
when no store entry is there; nothing is opened or locked.  Then a `run'
whose control path no platform binds whole becomes ACL2's
:control-path-too-long refusal (fn-native-operator-control-outcome)."
  (if (eq (fnn-core 'fn-native-operator-host-result-status result) :accepted)
      (let* ((root (fnn-core 'fn-native-operator-host-result-store-root result))
             (path (and (stringp root) (fnn-absolute root)))
             (observed (and path (fnn-operator-init-observed path)))
             (bare (and path (null observed))))
        (fnn-core 'fn-native-operator-host-control-outcome
                  (fnn-core 'fn-native-operator-host-store-outcome result observed
                            (and bare (fnn-import-leftover-stage path "init"))
                            (and bare (fnn-import-leftover-stage path "import")))))
    result))

;;; `store inspect MESSAGE-ID' (NNT-032): the operator's settling lookup.
;;; The host opens the stopped store exactly as `recover' does (a live
;;; owner's lock refuses it), asks the store node whether it binds the
;;; Message-ID, and prints ACL2's report line: accepted (exit 0) or absent
;;; (exit 1).  The host decides nothing.
(defun fnn-operator-maintenance-route (result root)
  "Row S3: ACL2's route for a maintenance verb (books/owner-maintenance-
request.lisp fn-omr-route over the liveness decision of the socket and the
writer lock): :owner, :held or :offline."
  (let* ((live *fnn-operator-live-owner*)
         (path-list (fnn-core 'fn-omr-control-path-octets result))
         (liveness (if (and live (fnn-octet-list-p path-list) (consp path-list))
                       (funcall (fnn-olo-admin-observe live) root path-list nil)
                     :offline)))
    (fnn-core 'fn-omr-route liveness)))

(defun fnn-operator-execute-recover-live (route root result)
  "`recover' with an owner: accepted on a live owner (ACL2's line, then that
owner's status), refused by name on a held lock (fn-omr-recover-line)."
  (let ((line (fnn-core 'fn-omr-recover-line route)))
    (unless (stringp line)
      (fnn-fault "ACL2 returned no recover line for ~a" route))
    (fnn-out "~a" line)
    (if (eq (fnn-core 'fn-omr-recover-status route) :accepted)
        (fnn-operator-status-once
         root (fnn-octets (fnn-core 'fn-omr-control-path-octets result)) :status result)
      +fnn-exit-refused+)))

(defun fnn-operator-export-exchange (control-path argv)
  "Row S3b: one export exchange with the live owner, (values WORD LINE):
WORD read back from the reply's octets by ACL2 (fn-oex-word-of-octets,
fn-oex-word-reads-back; nil for octets this release does not know), LINE
the owner's sentence (kind 23), or (values :uncertain DETAIL) when the
answer is neither accepted nor refused (the transport)."
  (multiple-value-bind (status word line) (fnn-control-admin control-path argv)
    (if (not (member status '(:accepted :refused)))
        (values :uncertain
                (if (fnn-octet-list-p word) (fnn-octets-string (fnn-octets word)) status))
      (values (fnn-core 'fn-oex-word-of-octets (and (fnn-octet-list-p word) word))
              (and (fnn-octet-list-p line) (consp line)
                   (fnn-octets-string (fnn-octets line)))))))

(defun fnn-operator-export-words (&rest words)
  (mapcar (lambda (word) (fnn-core 'fn-record-string-octets word)) words))

(defun fnn-operator-execute-export-live (result dir)
  "`store export DIR' on a running owner: the request `export request DIR'
(host/native/admin.lisp fnn-owner-export-request), its line printed as the
owner sent it (KEYSTONE fn-native-control-printed-line-is-the-decisions),
then `export status' every 250 ms until the word is no longer :in-flight
(fn-oex-in-flight-is-the-status-while-writing) and that line: exit 0 on
:done, refused otherwise; uncertain on a transport answer."
  (let ((control-path (fnn-octets (fnn-core 'fn-omr-control-path-octets result))))
    (multiple-value-bind (word line)
        (fnn-operator-export-exchange
         control-path (fnn-operator-export-words "export" "request" dir))
      (cond ((eq word :uncertain)
             (fnn-out "export uncertain reason=~a" line)
             +fnn-exit-uncertain+)
            (t
             (fnn-out "~a" (or line (fnn-core 'fn-oex-request-line word dir)))
             (cond ((null word) +fnn-exit-uncertain+)
                   ((not (eq word :requested)) +fnn-exit-refused+)
                   (t
                    (loop
                      (sleep 0.25)
                      (multiple-value-bind (status-word status-line)
                          (fnn-operator-export-exchange
                           control-path (fnn-operator-export-words "export" "status"))
                        (cond ((eq status-word :uncertain)
                               (fnn-out "export uncertain reason=~a" status-line)
                               (return +fnn-exit-uncertain+))
                              ((eq status-word :in-flight))
                              (t
                               (fnn-out "~a" (or status-line
                                                 (fnn-core 'fn-oex-outcome-line
                                                           status-word dir)))
                               (return (cond ((eq status-word :done) +fnn-exit-ok+)
                                             ;; the archive may be published:
                                             ;; uncertain, by name (lane
                                             ;; failure-scope; books/owner-
                                             ;; export-request.lisp)
                                             ((or (null status-word)
                                                  (eq status-word :archive-uncertain))
                                              +fnn-exit-uncertain+)
                                             (t +fnn-exit-refused+))))))))))))))

(defun fnn-operator-execute-export-status (result)
  "`store export --status' on a running owner: the owner's word and its
sentence (host/native/admin.lisp fnn-owner-export-status); exit 0 unless
the last export failed."
  (let ((control-path (fnn-octets (fnn-core 'fn-omr-control-path-octets result))))
    (multiple-value-bind (word line)
        (fnn-operator-export-exchange
         control-path (fnn-operator-export-words "export" "status"))
      (cond ((eq word :uncertain)
             (fnn-out "export uncertain reason=~a" line)
             +fnn-exit-uncertain+)
            (t
             (fnn-out "~a" (or line (fnn-core 'fn-oex-outcome-line word "")))
             (cond ((or (null word) (eq word :archive-uncertain)) +fnn-exit-uncertain+)
                   ((eq word :failed) +fnn-exit-refused+)
                   (t +fnn-exit-ok+)))))))

(defun fnn-operator-execute-inspect-live (result msgid-list)
  "Row S3: `store inspect ID' on a running owner is the owner's own lookup,
asked as the administrative vector `inspect request ID' (host/native/admin.lisp
fnn-owner-inspect-request); the client renders the offline verb's report from
the word (KEYSTONE fn-omr-inspect-live-is-the-offline-report).  An answer
that is neither accepted nor refused (the transport) is uncertain."
  (let ((control-path (fnn-octets (fnn-core 'fn-omr-control-path-octets result))))
    (multiple-value-bind (status word)
        (fnn-control-admin control-path
                           (list (fnn-core 'fn-record-string-octets "inspect")
                                 (fnn-core 'fn-record-string-octets "request")
                                 msgid-list))
      (cond ((not (member status '(:accepted :refused)))
             (fnn-out "inspect uncertain reason=~a"
                      (if (fnn-octet-list-p word) (fnn-octets-string (fnn-octets word)) status))
             +fnn-exit-uncertain+)
            (t
             (let ((report (fnn-core 'fn-omr-inspect-live-report msgid-list word)))
               (unless (and (consp report) (member (first report) '(0 1))
                            (stringp (third report)))
                 (fnn-fault "ACL2 returned a malformed inspect report"))
               (fnn-out "~a" (third report))
               (if (eql (first report) 0) +fnn-exit-ok+ +fnn-exit-refused+)))))))

(defun fnn-operator-execute-inspect (result)
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (msgid-list (fnn-core 'fn-native-operator-host-result-inspect-msgid-octets
                              result)))
    (unless (and (fnn-octet-list-p msgid-list) (consp msgid-list))
      (fnn-fault "ACL2 accepted an inspect plan with no Message-ID"))
    (handler-case
        (case (fnn-operator-maintenance-route result root)
          (:owner (fnn-operator-execute-inspect-live result msgid-list))
          (:held (fnn-out "~a" (fnn-core 'fn-omr-held-line "inspect"))
                 +fnn-exit-refused+)
          (t (fnn-operator-execute-inspect-offline root msgid-list)))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "inspect" condition)
          code)))))

(defun fnn-operator-execute-inspect-offline (root msgid-list)
  "The offline inspect: the store opened read-only, the lookup, the report."
  (progn
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
            (fnn-store-close store)))))

(defun fnn-operator-execute-inspect-group (result)
  "Row S3d: `store inspect --group GROUP': the group's memberships, article
numbers to Message-IDs, ACL2's report (books/owner-inspect-group.lisp
fn-oig-report) over the archive the running owner's served view carries, read
as the control report kind (:inspect-group . GROUP) through the status
exchange (books/control-evidence.lisp, FNLS frame kind 3, as `moderation list
GROUP' is read), or over the archive this process replays from the checkpoint
and its suffix when no owner runs (fnn-command-inspect-group-offline); refused
by name when an owner holds the lock and answers nothing (fn-omr-held-line).
The exit is ACL2's reading of the octets printed (fn-oig-report-exit); an
answer that is neither the report nor a refusal (the transport) is uncertain."
  (let ((root (fnn-core 'fn-native-operator-host-result-store-root result))
        (group (fnn-core 'fn-native-operator-host-result-inspect-group result)))
    (unless (stringp group)
      (fnn-fault "ACL2 accepted an inspect plan with no group"))
    (handler-case
        (let ((kind (cons :inspect-group group)))
          (case (fnn-operator-maintenance-route result root)
            (:owner
             (let* ((live *fnn-operator-live-owner*)
                    (control-path
                      (fnn-octets (fnn-core 'fn-omr-control-path-octets result)))
                    (answer (funcall (fnn-olo-live-status live) control-path kind)))
               (cond ((and (consp answer) (eq (first answer) :done)
                           (fnn-octet-list-p (second answer)))
                      (fnn-write-report (second answer))
                      (fnn-core 'fn-native-live-status-host-inspect-group-exit
                                (second answer)))
                     ((and (consp answer) (eq (first answer) :refused))
                      (fnn-out "inspect refused reason=~(~a~)" (second answer))
                      +fnn-exit-refused+)
                     (t (fnn-out "inspect uncertain reason=~(~a~)"
                                 (if (consp answer) (first answer) answer))
                        +fnn-exit-uncertain+))))
            (:held (fnn-out "~a" (fnn-core 'fn-omr-held-line "inspect"))
                   +fnn-exit-refused+)
            (t (fnn-command-inspect-group-offline root kind))))
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
        (let ((surface (fnn-operator-action-surface action)))
          (when (and (member action '(:reclaim :reclaim-dry-run :reclaim-recorded))
                     (null *fnn-reclaim-callback*))
            (fnn-operator-emit-status
             :usage "action" "reclaim needs the checkpoint surface, which this image omits")
            (return-from fnn-operator-dispatch-plan +fnn-exit-usage+))
          (when (and (eq action :compact) (null *fnn-compact-callback*))
            (fnn-operator-emit-status
             :usage "action" "compact needs the checkpoint surface, which this image omits")
            (return-from fnn-operator-dispatch-plan +fnn-exit-usage+))
          (when surface
            (let ((executor (cdr (assoc action *fnn-operator-surface-executors*))))
              (unless executor
                (fnn-operator-emit-status
                 :usage "action"
                 (format nil "~(~a~) needs the ~(~a~) surface, which this image omits"
                         action surface))
                (return-from fnn-operator-dispatch-plan +fnn-exit-usage+))
              (return-from fnn-operator-dispatch-plan (funcall executor result)))))
        (case action
          (:help (fnn-operator-execute-help result))
          (:show (fnn-operator-execute-show result))
          (:tls-self-signed (fnn-operator-execute-tls-self-signed result))
          (:init (fnn-operator-execute-init result))
          (:status (fnn-operator-execute-status result))
          (:operation (fnn-operator-execute-operation result))
          (:health (fnn-operator-execute-health result))
          ((:recover :compact :checkpoint :export :export-status :import :bless-snapshot
            :reclaim :reclaim-dry-run :reclaim-recorded :rebind-filesystem)
           (fnn-operator-execute-store-action result action))
          (:inspect (fnn-operator-execute-inspect result))
          (:inspect-group (fnn-operator-execute-inspect-group result))
          (:admin (fnn-operator-execute-admin result))
          (:account-invite (fnn-operator-execute-account-invite result))
          (:account-hash (fnn-operator-execute-account-hash result))
          (:retire (fnn-operator-execute-retire
                    result (fnn-core 'fn-native-operator-host-result-store-root result)))
          (:owner-required
           (fnn-operator-emit-status :usage "action" "requires native owner callback")
           +fnn-exit-usage+)
          (t (fnn-fault "ACL2 operator returned no native action")))))))

(defvar *fnn-operator-config-octets* nil
  "The profile octets this operator command loaded (for `run': ACL2's plan
of the node's web face from the same octets, books/web-config.lisp).")

;;; Row S8: fn.toml's relative paths are resolved under its own directory.
;;; The host observes its working directory and hands it with the path as
;;; given; ACL2 decides the directory and the resolution
;;; (books/native-config-paths.lisp).
(defun fnn-operator-run-at (config-path config-octets argv-octets)
  (fnn-core 'fn-native-operator-host-run-at
            (fnn-octet-list (fnn-string-octets (sb-posix:getcwd)))
            (fnn-octet-list (fnn-string-octets config-path))
            config-octets argv-octets))

(defun fnn-command-operator (config-path argv)
  (let* ((argv-octets (fnn-operator-argv-octets argv))
         (preflight (fnn-core 'fn-native-operator-host-preflight argv-octets)))
    (when (fnn-core 'fn-native-operator-host-preflight-needs-config-path-p preflight)
      (return-from fnn-command-operator
        (fnn-operator-execute-mission
         (fnn-core 'fn-native-operator-host-mission-run
                   (fnn-ascii-octet-list config-path) argv-octets)
         config-path)))
    (if (fnn-core 'fn-native-operator-host-preflight-needs-config-p preflight)
        (let* ((config-bound (fnn-core 'fn-native-config-host-max-octets))
               (config-octets (fnn-operator-read-config config-path config-bound))
               (*fnn-operator-config-octets* config-octets))
          (fnn-operator-dispatch-plan
           (fnn-operator-run-at config-path config-octets argv-octets)))
      (fnn-operator-dispatch-plan preflight))))

(fnn-register-verb "operator"
                   (lambda (config-path argv)
                     (fnn-command-operator config-path argv)))
