;;; Native AUTHINFO credential administration effects.
;;;
;;; ACL2 owns argv grammar, login/principal validation, secret confirmation,
;;; verifier derivation, row replacement, serialization, public reporting and
;;; every persistence phase.  This file observes a bounded secret twice, one
;;; exact OS-CSPRNG salt, filesystem state and syscall results.  It holds one
;;; adjacent exclusive lock from recovery through the terminal result.

(in-package "ACL2")

(defvar *fnn-native-auth-admin-secret-reader* nil)
(defvar *fnn-native-auth-admin-cut-callback* nil)
;; The configured store root when the verb runs under `operator CONFIG', else
;; NIL (no store is named, so no owner can be observed: ACL2 answers
;; restart-required for an unknown observation).
(defvar *fnn-native-auth-admin-store-root* nil)

(defparameter +fnn-native-auth-admin-test-cuts+
  '("cleanup-unlinked" "cleanup-directory-durable"
    "recovery-file-durable" "recovery-directory-durable"
    "stage-durable" "replace-issued" "replace-returned"
    "final-directory-durable"))

(defun fnn-native-auth-admin-test-cut ()
  "Developer-only FN_NATIVE_AUTH_ADMIN_FAULT=CUT:eio|kill selector.

Read through `fnn-developer-selector' (host/native/io.lisp): NIL on a
production image, which refuses to start with the variable set."
  (let ((raw (fnn-developer-selector "FN_NATIVE_AUTH_ADMIN_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault
           "invalid FN_NATIVE_AUTH_ADMIN_FAULT (expected CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon))
              (action (subseq raw (1+ colon))))
          (unless (member label +fnn-native-auth-admin-test-cuts+
                          :test #'string=)
            (fnn-fault "unknown FN_NATIVE_AUTH_ADMIN_FAULT cut: ~a" label))
          (let ((point (intern (string-upcase label) :keyword)))
            (cond
             ((string= action "eio")
              (lambda (seen)
                (when (eq seen point) (fnn-os-fail sb-posix:eio))))
             ((string= action "kill")
              (lambda (seen)
                (when (eq seen point)
                  (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
                  (fnn-fault "test SIGKILL did not terminate the process"))))
             (t
              (fnn-fault
               "invalid FN_NATIVE_AUTH_ADMIN_FAULT action: ~a" action)))))))))

(defun fnn-native-auth-admin-at (label)
  "A deterministic death-cut seam; production has no callback."
  (when *fnn-native-auth-admin-cut-callback*
    (funcall *fnn-native-auth-admin-cut-callback* label)))

(defun fnn-native-auth-admin-core (name &rest arguments)
  (apply #'fnn-core name arguments))

(defun fnn-native-auth-admin-read-octet-line (stream maximum)
  "Read at most MAXIMUM octets plus the terminating LF from STREAM."
  (let ((answer nil) (count 0))
    (loop
      (let ((character (read-char stream nil :eof)))
        (when (eq character :eof)
          (if (zerop count)
              (fnn-refuse "password input ended before a value")
            (return (nreverse answer))))
        (let ((octet (char-code character)))
        (when (= octet 10) (return (nreverse answer)))
        (when (>= count maximum)
          ; Continue no farther: a local input above the ACL2 bound is refused
          ; before it can allocate a larger retained secret.
          (fnn-refuse "password exceeds ACL2 bound"))
        (push octet answer)
        (incf count))))))

(defun fnn-native-auth-admin-read-secret-from (stream prompt maximum tty-fd)
  (format *error-output* "~a" prompt)
  (finish-output *error-output*)
  (let ((attributes nil) (old-flags nil))
    (when tty-fd
      (setq attributes (sb-posix:tcgetattr tty-fd)
            old-flags (sb-posix:termios-lflag attributes))
      (setf (sb-posix:termios-lflag attributes)
            (logandc2 old-flags sb-posix:echo))
      (sb-posix:tcsetattr tty-fd sb-posix:tcsanow attributes))
    (unwind-protect
         (fnn-native-auth-admin-read-octet-line stream maximum)
      (when tty-fd
        (setf (sb-posix:termios-lflag attributes) old-flags)
        (sb-posix:tcsetattr tty-fd sb-posix:tcsanow attributes)
        (format *error-output* "~%")
        (finish-output *error-output*)))))

(defun fnn-native-auth-admin-prompt-secrets ()
  "Observe two bounded password entries; ACL2 decides whether they agree."
  (let ((maximum
          (fnn-native-auth-admin-core
           'fn-native-auth-admin-host-max-secret-octets)))
    (unless (and (integerp maximum) (< 0 maximum))
      (fnn-fault "ACL2 returned an invalid password bound"))
    (let ((tty (handler-case
                   (open "/dev/tty" :direction :io :element-type 'character
                                    :external-format :latin-1)
                 (error () nil))))
      (if tty
          (unwind-protect
               (let ((fd (sb-sys:fd-stream-fd tty)))
                 (values
                  (fnn-native-auth-admin-read-secret-from
                   tty "Password: " maximum fd)
                  (fnn-native-auth-admin-read-secret-from
                   tty "Confirm password: " maximum fd)))
            (close tty))
        ; Noninteractive invocations may have no controlling terminal.  Their
        ; standard input remains bounded and secrets still never enter argv.
        (values
         (fnn-native-auth-admin-read-secret-from
          *standard-input* "Password: " maximum nil)
         (fnn-native-auth-admin-read-secret-from
          *standard-input* "Confirm password: " maximum nil))))))

(unless *fnn-native-auth-admin-secret-reader*
  (setq *fnn-native-auth-admin-secret-reader*
        #'fnn-native-auth-admin-prompt-secrets))

(defun fnn-native-auth-admin-csprng-salt ()
  "Read exactly the ACL2 salt width; short or failed entropy is a host fault."
  (let ((width (fnn-native-auth-admin-core
                'fn-native-auth-admin-host-salt-octets)))
    (unless (and (integerp width) (< 0 width))
      (fnn-fault "ACL2 returned an invalid salt width"))
    (let ((fd (fnn-open "/dev/urandom" sb-posix:o-rdonly))
          (answer (fnn-make-octets width))
          (offset 0))
      (unwind-protect
           (progn
             (loop while (< offset width) do
               (let* ((remaining (- width offset))
                      (chunk (fnn-make-octets remaining))
                      (count (fnn-read-fd fd chunk)))
                 (when (zerop count)
                   (fnn-fault "OS CSPRNG ended before one credential salt"))
                 (replace answer chunk :start1 offset :end2 count)
                 (incf offset count)))
             (fnn-octet-list answer))
        (fnn-close fd)))))

(defun fnn-native-auth-admin-paths (final)
  (values final (fnn-concat final ".lock") (fnn-concat final ".stage")
          (fnn-parent final)))

(defun fnn-native-auth-admin-check-path (path kind)
  (let ((info (fnn-lstat path)))
    (when (and info (or (fnn-symlink-p info) (not (fnn-regular-p info))))
      (fnn-refuse "AUTHINFO ~a path is not a regular file" kind))
    info))

(defun fnn-native-auth-admin-check-directory (path)
  (let ((info (fnn-lstat path)))
    (when (or (null info) (fnn-symlink-p info)
              (not (fnn-directory-p info)))
      (fnn-refuse "AUTHINFO credential parent is not an existing directory"))
    info))

(defun fnn-native-auth-admin-open-lock (path)
  (let ((fd nil))
    (handler-case
        (setq fd (fnn-open path
                           (logior sb-posix:o-rdwr sb-posix:o-creat
                                   +fnn-o-nofollow+)
                           #o600))
      (fnn-os-error (condition)
        (if (= (fnn-os-errno condition) sb-posix:eloop)
            (fnn-refuse "AUTHINFO administration lock is a symlink")
          (error condition))))
    (handler-case
        (progn
          (unless (fnn-regular-p (fnn-fstat fd))
            (fnn-refuse "AUTHINFO administration lock is not regular"))
          (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
          fd)
      (fnn-os-error ()
        (fnn-close fd)
        (fnn-refuse "AUTHINFO credential registry is already locked"))
      (error (condition)
        (fnn-close fd)
        (error condition)))))

(defun fnn-native-auth-admin-recovery-step (phase event)
  (let ((next (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-recovery-step phase event)))
    (when (equal next phase)
      (fnn-fault "ACL2 rejected AUTHINFO recovery event ~s in ~s" event phase))
    next))

(defun fnn-native-auth-admin-recover (stage final directory)
  "Recover fixed stage and observed final name under the adjacent writer lock."
  (let* ((stage-info (fnn-native-auth-admin-check-path stage "stage"))
         (final-info (fnn-native-auth-admin-check-path final "final"))
         (phase
           (fnn-native-auth-admin-core
            'fn-native-auth-admin-host-recovery-start
            (not (null stage-info)) (not (null final-info)))))
    (when stage-info
      (unless (eq (fnn-native-auth-admin-core
                   'fn-native-auth-admin-host-recovery-action phase)
                  :issue-cleanup)
        (fnn-fault "ACL2 rejected AUTHINFO stage cleanup"))
      (setq phase (fnn-native-auth-admin-recovery-step phase :cleanup-issued))
      (handler-case
          (progn
            (fnn-unlink stage)
            (fnn-native-auth-admin-at :cleanup-unlinked)
            (setq phase
                  (fnn-native-auth-admin-recovery-step
                   phase '(:cleanup-result :ok))))
        ((or fnn-os-error serious-condition) ()
          (setq phase
                (fnn-native-auth-admin-recovery-step
                 phase '(:cleanup-result :uncertain)))))
      (when (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-recovery-outcome phase)
                :uncertain)
        (fnn-indeterminate "AUTHINFO stage cleanup is uncertain"))
      (unless (eq (fnn-native-auth-admin-core
                   'fn-native-auth-admin-host-recovery-action phase)
                  :cleanup-directory-barrier)
        (fnn-fault "ACL2 rejected AUTHINFO cleanup directory barrier"))
      (handler-case
          (progn
            (fnn-fsync-dir directory)
            (fnn-native-auth-admin-at :cleanup-directory-durable)
            (setq phase
                  (fnn-native-auth-admin-recovery-step
                   phase '(:cleanup-directory-result :ok))))
        ((or fnn-os-error serious-condition) ()
          (setq phase
                (fnn-native-auth-admin-recovery-step
                 phase '(:cleanup-directory-result :uncertain))))))
    (when (eq (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-recovery-outcome phase)
              :uncertain)
      (fnn-indeterminate "AUTHINFO cleanup barrier is uncertain"))
    (when final-info
      (unless (eq (fnn-native-auth-admin-core
                   'fn-native-auth-admin-host-recovery-action phase)
                  :recovery-file-barrier)
        (fnn-fault "ACL2 rejected AUTHINFO final-file recovery barrier"))
      (handler-case
          (progn
            (fnn-fsync-regular final)
            (fnn-native-auth-admin-at :recovery-file-durable)
            (setq phase
                  (fnn-native-auth-admin-recovery-step
                   phase '(:recovery-file-result :ok))))
        ((or fnn-os-error serious-condition) ()
          (setq phase
                (fnn-native-auth-admin-recovery-step
                 phase '(:recovery-file-result :uncertain))))))
    (when (eq (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-recovery-outcome phase)
              :uncertain)
      (fnn-indeterminate "AUTHINFO final-file recovery barrier is uncertain"))
    (unless (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-recovery-action phase)
                :recovery-directory-barrier)
      (fnn-fault "ACL2 rejected AUTHINFO recovery directory barrier"))
    (handler-case
        (progn
          (fnn-fsync-dir directory)
          (fnn-native-auth-admin-at :recovery-directory-durable)
          (setq phase
                (fnn-native-auth-admin-recovery-step
                 phase '(:recovery-directory-result :ok))))
      ((or fnn-os-error serious-condition) ()
        (setq phase
              (fnn-native-auth-admin-recovery-step
               phase '(:recovery-directory-result :uncertain)))))
    (unless (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-recovery-outcome phase)
                :recovered)
      (fnn-indeterminate "AUTHINFO registry recovery is uncertain"))
    (not (null final-info))))

(defun fnn-native-auth-admin-read-held (final presentp)
  (if presentp
      (fnn-octet-list
       (fnn-read-regular-bounded
        final (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-max-octets)))
    nil))

(defun fnn-native-auth-admin-rp-step (phase event)
  (let ((next
          (fnn-native-auth-admin-core
           'fn-native-auth-admin-host-rp-step phase event)))
    (when (equal next phase)
      (fnn-fault "ACL2 rejected AUTHINFO replacement event ~s in ~s"
                 event phase))
    next))

(defun fnn-native-auth-admin-publish (stage final directory octets)
  "Publish ACL2-produced bytes; only the final directory barrier is durable."
  (let ((phase (fnn-native-auth-admin-core
                'fn-native-auth-admin-host-rp-start)))
    (unless (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-rp-action phase)
                :stage-and-file-barrier)
      (fnn-fault "ACL2 rejected AUTHINFO staging action"))
    (handler-case
        (progn
          (fnn-write-staged stage (fnn-octets octets))
          (fnn-native-auth-admin-at :stage-durable)
          (setq phase
                (fnn-native-auth-admin-rp-step
                 phase '(:stage-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (setq phase
              (fnn-native-auth-admin-rp-step
               phase '(:stage-result :known-fail)))))
    (when (eq (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-rp-outcome phase)
              :fault)
      (return-from fnn-native-auth-admin-publish :fault))
    (unless (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-rp-action phase)
                :issue-replace)
      (fnn-fault "ACL2 rejected AUTHINFO replacement action"))
    ; Enter the model cut before rename(2).  A process death after the syscall
    ; can therefore never masquerade as a known pre-publication failure.
    (setq phase (fnn-native-auth-admin-rp-step phase :replace-issued))
    (fnn-native-auth-admin-at :replace-issued)
    (handler-case
        (progn
          (fnn-replace stage final)
          (fnn-native-auth-admin-at :replace-returned)
          (setq phase
                (fnn-native-auth-admin-rp-step
                 phase '(:replace-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (setq phase
              (fnn-native-auth-admin-rp-step
               phase '(:replace-result :uncertain)))))
    (when (eq (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-rp-outcome phase)
              :uncertain)
      (return-from fnn-native-auth-admin-publish :uncertain))
    (unless (eq (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-rp-action phase)
                :directory-barrier)
      (fnn-fault "ACL2 rejected AUTHINFO final directory barrier"))
    (handler-case
        (progn
          (fnn-fsync-dir directory)
          (fnn-native-auth-admin-at :final-directory-durable)
          (setq phase
                (fnn-native-auth-admin-rp-step
                 phase '(:directory-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (setq phase
              (fnn-native-auth-admin-rp-step
               phase '(:directory-result :uncertain)))))
    (fnn-native-auth-admin-core
     'fn-native-auth-admin-host-rp-outcome phase)))

(defun fnn-native-auth-admin-reason-text (reason)
  (if reason (string-downcase (symbol-name reason)) "none"))

(defun fnn-native-auth-admin-emit (status action &optional reason)
  (fnn-err "~(~a~) operator principal ~(~a~)~@[ ~(~a~)~]"
           status action reason))

(defun fnn-native-auth-admin-result-code (result action &optional durable)
  (let ((status (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-result-status result))
        (reason (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-result-reason result)))
    (cond
     ((not (eq status :accepted))
      (fnn-native-auth-admin-emit status action reason)
      (if (eq status :refused) +fnn-exit-refused+ +fnn-exit-fault+))
     ((and durable (eq durable :uncertain))
      (fnn-native-auth-admin-emit :uncertain action :persistence)
      +fnn-exit-uncertain+)
     ((and durable (not (eq durable :durable)))
      (fnn-native-auth-admin-emit :fault action :persistence)
      +fnn-exit-fault+)
     (t
      (let ((report (fnn-native-auth-admin-core
                     'fn-native-auth-admin-host-result-report result)))
        (when report
          (write-string (fnn-octets-string (fnn-octets report))
                        *standard-output*)
          (finish-output *standard-output*)))
      ;; After the change is durable, the writer lock is observed once and
      ;; ACL2 answers whether a restart is owed (PKT-102).
      (fnn-native-auth-admin-emit
       :accepted action
       (and durable
            (fnn-native-auth-admin-core
             'fn-native-auth-admin-effect-word
             (if *fnn-native-auth-admin-store-root*
                 (fnn-store-owner-observation *fnn-native-auth-admin-store-root*)
                 :unknown))))
      +fnn-exit-ok+))))

(defun fnn-native-auth-admin-execute-held (plan-result final stage directory
                                           octets presentp)
  (case (fnn-native-auth-admin-core
         'fn-native-auth-admin-host-action-kind plan-result)
    (:list
     (fnn-native-auth-admin-result-code
      (fnn-native-auth-admin-core
       'fn-native-auth-admin-host-list octets presentp)
      :list))
    (:set-password
     (multiple-value-bind (secret confirmation)
         (funcall *fnn-native-auth-admin-secret-reader*)
       (let* ((salt (fnn-native-auth-admin-csprng-salt))
              (result
                (fnn-native-auth-admin-core
                 'fn-native-auth-admin-host-set-password
                 octets presentp
                 (fnn-native-auth-admin-core
                  'fn-native-auth-admin-host-action-name plan-result)
                 secret confirmation salt
                 (fnn-native-auth-admin-core
                  'fn-native-auth-admin-host-action-principal-text plan-result)
                 (fnn-native-auth-admin-core
                  'fn-native-auth-admin-host-action-principal-presentp plan-result)
                 (fnn-native-auth-admin-core
                  'fn-native-auth-admin-host-action-postingp plan-result))))
         (if (not (eq (fnn-native-auth-admin-core
                       'fn-native-auth-admin-host-result-status result)
                      :accepted))
             (fnn-native-auth-admin-result-code result :set-password)
           (fnn-native-auth-admin-result-code
            result :set-password
            (fnn-native-auth-admin-publish
             stage final directory
             (fnn-native-auth-admin-core
              'fn-native-auth-admin-host-result-octets result)))))))
    (t (fnn-fault "ACL2 returned no executable principal action"))))

(defun fnn-native-auth-admin-execute (plan-result auth-path)
  "Execute one ACL2-produced principal plan against AUTH-PATH."
  (unless (eq (fnn-native-auth-admin-core
               'fn-native-auth-admin-host-plan-status plan-result)
              :accepted)
    (fnn-native-auth-admin-emit
     :usage :request
     (fnn-native-auth-admin-core
      'fn-native-auth-admin-host-plan-reason plan-result))
    (return-from fnn-native-auth-admin-execute +fnn-exit-usage+))
  (multiple-value-bind (final lock stage directory)
      (fnn-native-auth-admin-paths auth-path)
    (fnn-native-auth-admin-check-directory directory)
    (let ((lock-fd (fnn-native-auth-admin-open-lock lock))
          (*fnn-native-auth-admin-cut-callback*
            (or *fnn-native-auth-admin-cut-callback*
                (fnn-native-auth-admin-test-cut))))
      (unwind-protect
           (let* ((presentp
                    (fnn-native-auth-admin-recover stage final directory))
                  (octets (fnn-native-auth-admin-read-held final presentp)))
             (fnn-native-auth-admin-execute-held
              plan-result final stage directory octets presentp))
        (ignore-errors (fnn-flock lock-fd +fnn-lock-un+))
        (fnn-close lock-fd)))))
