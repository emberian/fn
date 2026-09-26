; fn: ACL2-owned native AUTHINFO credential administration.
;
; Raw Lisp may observe one bounded file, one exact OS-CSPRNG salt and secret
; octets read from a prompt/stdin boundary.  This book alone validates those
; observations, derives the existing fn-authsec verifier and local principal,
; replaces the named row, serializes the complete credential file, and chooses
; the public listing.  The secret is never a result or report field.

(in-package "ACL2")
(include-book "native-auth-profile")
(include-book "anchor-replace")

(defconst *fn-native-auth-admin-max-secret-octets* 256)
; The local principal is books/accounts.lisp's (one function for a login
; enrolled here and a login redeemed by XREDEEM).
(defconst *fn-native-auth-admin-local-principal-tag*
  *fn-acct-local-principal-tag*)
(defconst *fn-native-auth-admin-header*
  (append
   (fn-record-string-octets
    "# fn AUTHINFO credentials (RFC 4643), format v2.  Written by") (list 10)
   (fn-record-string-octets
    "# `fn principal set-password`.  Each entry is the verifier of")
   (list 10)
   (fn-record-string-octets
    "# books/auth-secret.lisp: a 16-octet salt and the tagged SHA-256")
   (list 10)
   (fn-record-string-octets
    "# of salt || secret.  The secret itself is not stored.  This v1") (list 10)
   (fn-record-string-octets
    "# verifier is not a tunable-cost or memory-hard password KDF.") (list 10)
   (fn-record-string-octets
    "# AUTHINFO still carries the secret over an unprotected") (list 10)
   (fn-record-string-octets
    "# connection in the clear, so set [listener] tls_cert/tls_key") (list 10)
   (fn-record-string-octets
    "# with [auth] protected_only = true.") (list 10 10)))

; The public operator owns the outer `principal' command.  This parser owns
; its bounded argument tail and produces the only action shape raw Lisp may
; execute.  A password is deliberately absent from both argv and the plan.
(defun fn-native-auth-admin-plan-result (status reason action)
  (declare (xargs :guard t))
  (list status reason action))

(defun fn-native-auth-admin-plan-status (result)
  (declare (xargs :guard t))
  (fn-ncfg-first result))

(defun fn-native-auth-admin-plan-reason (result)
  (declare (xargs :guard t))
  (fn-ncfg-second result))

(defun fn-native-auth-admin-plan-action (result)
  (declare (xargs :guard t))
  (fn-ncfg-third result))

(defun fn-native-auth-admin-parse-set-options
  (words principal-text principal-presentp postingp posting-seenp)
  (declare (xargs :guard t))
  (if (atom words)
      (list :set-options principal-text principal-presentp postingp)
    (cond
     ((equal (car words) (fn-record-string-octets "--principal"))
      (if (or principal-presentp (not (consp (cdr words)))
              (not (equal (len (car (cdr words))) 64))
              (not (fn-id-hex-listp (car (cdr words))))
              )
          :bad
        (fn-native-auth-admin-parse-set-options
         (cdr (cdr words)) (car (cdr words))
         t postingp posting-seenp)))
     ((equal (car words) (fn-record-string-octets "--posting"))
      (if posting-seenp :bad
        (fn-native-auth-admin-parse-set-options
         (cdr words) principal-text principal-presentp t t)))
     ((equal (car words) (fn-record-string-octets "--no-posting"))
      (if posting-seenp :bad
        (fn-native-auth-admin-parse-set-options
         (cdr words) principal-text principal-presentp nil t)))
     (t :bad))))

(defun fn-native-auth-admin-parse-argv (argv)
  "Parse argv following the outer `principal' token; never carries a secret."
  (declare (xargs :guard t))
  (if (or (not (true-listp argv))
          (< 6 (len argv)))
      (fn-native-auth-admin-plan-result :usage :argv-bounds nil)
    (cond
       ((and (equal (len argv) 1)
             (equal (car argv) (fn-record-string-octets "list")))
        (fn-native-auth-admin-plan-result :accepted :plan (list :list)))
       ((and (<= 2 (len argv))
             (equal (car argv) (fn-record-string-octets "set-password")))
        (let* ((name (car (cdr argv)))
               (options (fn-native-auth-admin-parse-set-options
                         (cdr (cdr argv)) nil nil t nil)))
          (cond
           ((not (fn-native-auth-login-namep name))
            (fn-native-auth-admin-plan-result :usage :name nil))
           ((equal options :bad)
            (fn-native-auth-admin-plan-result :usage :options nil))
           (t
            (fn-native-auth-admin-plan-result
             :accepted :plan
             (list :set-password name (fn-ncfg-second options)
                   (fn-ncfg-third options) (fn-ncfg-nth 3 options)))))))
       ((and (consp argv)
             (equal (car argv) (fn-record-string-octets "set-password")))
        (fn-native-auth-admin-plan-result :usage :missing-name nil))
       ; `principal bind LOGIN PRINCIPAL-HEX': bind a login to the signing
       ; principal books/login-binding.lisp's posting policy compares with a
       ; served POST's FN-Authorship carrier.  `principal unbind LOGIN'
       ; removes the binding.  Both rewrite the credential file through the
       ; same replacement machine as set-password.
       ((and (equal (len argv) 3)
             (equal (car argv) (fn-record-string-octets "bind")))
        (let ((name (car (cdr argv))) (hex (car (cdr (cdr argv)))))
          (cond
           ((not (fn-native-auth-login-namep name))
            (fn-native-auth-admin-plan-result :usage :name nil))
           ((not (and (true-listp hex) (equal (len hex) 64)
                      (fn-id-hex-listp hex)))
            (fn-native-auth-admin-plan-result :usage :principal nil))
           (t (fn-native-auth-admin-plan-result
               :accepted :plan (list :bind name hex))))))
       ((and (equal (len argv) 2)
             (equal (car argv) (fn-record-string-octets "unbind")))
        (if (fn-native-auth-login-namep (car (cdr argv)))
            (fn-native-auth-admin-plan-result
             :accepted :plan (list :bind (car (cdr argv)) nil))
          (fn-native-auth-admin-plan-result :usage :name nil)))
       ((and (consp argv)
             (or (equal (car argv) (fn-record-string-octets "bind"))
                 (equal (car argv) (fn-record-string-octets "unbind"))))
        (fn-native-auth-admin-plan-result :usage :bind-arguments nil))
       ((null argv)
        (fn-native-auth-admin-plan-result :usage :missing-action nil))
       (t (fn-native-auth-admin-plan-result :usage :unsupported-action nil)))))

(defun fn-native-auth-admin-action-kind (plan-result)
  (declare (xargs :guard t))
  (if (equal (fn-native-auth-admin-plan-status plan-result) :accepted)
      (fn-ncfg-first (fn-native-auth-admin-plan-action plan-result))
    :none))

(defun fn-native-auth-admin-action-name (plan-result)
  (declare (xargs :guard t))
  (if (member-equal (fn-native-auth-admin-action-kind plan-result)
                    '(:set-password :bind))
      (fn-ncfg-second (fn-native-auth-admin-plan-action plan-result))
    nil))

; The bind action's principal text (64 lowercase hex octets), or nil for
; `unbind'.
(defun fn-native-auth-admin-action-signing-text (plan-result)
  (declare (xargs :guard t))
  (if (equal (fn-native-auth-admin-action-kind plan-result) :bind)
      (fn-ncfg-third (fn-native-auth-admin-plan-action plan-result))
    nil))

(defun fn-native-auth-admin-action-principal-text (plan-result)
  (declare (xargs :guard t))
  (if (equal (fn-native-auth-admin-action-kind plan-result) :set-password)
      (fn-ncfg-third (fn-native-auth-admin-plan-action plan-result))
    nil))

(defun fn-native-auth-admin-action-principal-presentp (plan-result)
  (declare (xargs :guard t))
  (and (equal (fn-native-auth-admin-action-kind plan-result) :set-password)
       (fn-ncfg-nth 3 (fn-native-auth-admin-plan-action plan-result))
       t))

(defun fn-native-auth-admin-action-postingp (plan-result)
  (declare (xargs :guard t))
  (and (equal (fn-native-auth-admin-action-kind plan-result) :set-password)
       (fn-ncfg-nth 4 (fn-native-auth-admin-plan-action plan-result))
       t))

(defun fn-native-auth-admin-secretp (secret)
  (declare (xargs :guard t))
  (and (consp secret)
       (true-listp secret)
       (<= (len secret) *fn-native-auth-admin-max-secret-octets*)
       (fn-nntp-printable-tokenp secret)))

(defun fn-native-auth-admin-principal (name text presentp)
  (declare (xargs :guard t))
  (if presentp
      (if (and (true-listp text) (equal (len text) 64)
               (fn-id-hex-listp text))
          (fn-id-unhex text)
        :bad)
    (fn-acct-local-principal name)))

(defun fn-native-auth-admin-upsert (name credential credentials)
  (declare (xargs :guard t))
  (if (consp credentials)
      (if (equal (fn-auth-cred-name (car credentials)) name)
          (cons credential (cdr credentials))
        (cons (car credentials)
              (fn-native-auth-admin-upsert name credential (cdr credentials))))
    (list credential)))

(defun fn-native-auth-admin-octets-lessp (left right)
  (declare (xargs :guard t))
  (cond ((atom left) (consp right))
        ((atom right) nil)
        ((< (ifix (car left)) (ifix (car right))) t)
        ((< (ifix (car right)) (ifix (car left))) nil)
        (t (fn-native-auth-admin-octets-lessp (cdr left) (cdr right)))))

(defun fn-native-auth-admin-insert-credential (credential credentials)
  (declare (xargs :guard t))
  (if (atom credentials)
      (list credential)
    (if (fn-native-auth-admin-octets-lessp
         (fn-auth-cred-name credential)
         (fn-auth-cred-name (car credentials)))
        (cons credential credentials)
      (cons (car credentials)
            (fn-native-auth-admin-insert-credential
             credential (cdr credentials))))))

(defun fn-native-auth-admin-sort-credentials (credentials)
  (declare (xargs :guard t))
  (if (consp credentials)
      (fn-native-auth-admin-insert-credential
       (car credentials)
       (fn-native-auth-admin-sort-credentials (cdr credentials)))
    nil))

(defun fn-native-auth-admin-quoted (octets)
  (declare (xargs :guard t))
  (append (list 34) (fn-authsec-octets octets) (list 34)))

(defun fn-native-auth-admin-field (name-octets value)
  (declare (xargs :guard t))
  (append (fn-authsec-octets name-octets) (list 32 61 32)
          (fn-native-auth-admin-quoted value) (list 10)))

; The login's binding in BINDINGS ((NAME . PRINCIPAL) pairs,
; books/native-auth-profile.lisp fn-native-auth-load-bindings), or nil.
(defun fn-native-auth-admin-binding (name bindings)
  (declare (xargs :guard t))
  (let ((pair (fn-native-auth-assoc name bindings)))
    (if (consp pair) (cdr pair) nil)))

(defun fn-native-auth-admin-signing-field (name bindings)
  (declare (xargs :guard t))
  (let ((principal (fn-native-auth-admin-binding name bindings)))
    (if principal
        (fn-native-auth-admin-field
         (fn-record-string-octets "signing")
         (fn-id-hex-octets (fn-authsec-octets principal)))
      nil)))

(defun fn-native-auth-admin-serialize-cred (credential bindings)
  (declare (xargs :guard t))
  (let* ((verifier (fn-auth-cred-secret credential))
         (name (fn-auth-cred-name credential)))
    (append
     (fn-record-string-octets "[login.\"")
     (fn-authsec-octets name) (list 34 93 10)
     (fn-native-auth-admin-field
      (fn-record-string-octets "principal")
      (fn-id-hex-octets
       (fn-authsec-octets (fn-auth-cred-principal credential))))
     (fn-native-auth-admin-field
      (fn-record-string-octets "salt")
      (fn-id-hex-octets (fn-authsec-octets
                         (fn-authsec-ver-salt verifier))))
     (fn-native-auth-admin-field
      (fn-record-string-octets "digest")
      (fn-id-hex-octets (fn-authsec-octets
                         (fn-authsec-ver-digest verifier))))
     (fn-native-auth-admin-signing-field name bindings)
     (fn-record-string-octets
      (if (fn-auth-cred-postingp credential)
          "posting = true"
        "posting = false"))
     (list 10 10))))

(defun fn-native-auth-admin-serialize-creds (credentials bindings)
  (declare (xargs :guard t))
  (if (consp credentials)
      (append (fn-native-auth-admin-serialize-cred (car credentials) bindings)
              (fn-native-auth-admin-serialize-creds (cdr credentials) bindings))
    nil))

(defun fn-native-auth-admin-serialize (credentials bindings)
  (declare (xargs :guard t))
  (append *fn-native-auth-admin-header*
          (fn-native-auth-admin-serialize-creds credentials bindings)))

(defun fn-native-auth-admin-public-row (credential bindings)
  (declare (xargs :guard t))
  (let ((signing (fn-native-auth-admin-binding
                  (fn-auth-cred-name credential) bindings)))
    (append (fn-authsec-octets (fn-auth-cred-name credential))
            (fn-record-string-octets " principal=")
            (fn-id-hex-octets
             (fn-authsec-octets (fn-auth-cred-principal credential)))
            (fn-record-string-octets
             (if (fn-auth-cred-postingp credential)
                 " posting=true"
               " posting=false"))
            (if signing
                (append (fn-record-string-octets " signing=")
                        (fn-id-hex-octets (fn-authsec-octets signing)))
              nil)
            (list 10))))

(defun fn-native-auth-admin-public-report (credentials bindings)
  (declare (xargs :guard t))
  (if (consp credentials)
      (append (fn-native-auth-admin-public-row (car credentials) bindings)
              (fn-native-auth-admin-public-report (cdr credentials) bindings))
    nil))

(defun fn-native-auth-admin-list (octets presentp max-credentials)
  ; Host-called list subject.  It projects only public credential fields.
  ; MAX-CREDENTIALS is the store profile's `max-credentials' (D27, PRF-102).
  (declare (xargs :guard t))
  (let ((loaded (fn-native-auth-load octets presentp nil nil nil
                                     max-credentials)))
    (if (not (equal (fn-native-auth-result-status loaded) :accepted))
      (list :refused (fn-native-auth-result-reason loaded))
      (list :accepted nil
            (fn-native-auth-admin-public-report
             (fn-native-auth-admin-sort-credentials
              (fn-auth-config-creds
               (fn-native-auth-result-config loaded)))
             (fn-native-auth-load-bindings octets presentp max-credentials))))))

(defun fn-native-auth-admin-set-password
  (octets presentp name secret confirmation salt
          principal-text principal-presentp postingp max-credentials)
  ; Host-called mutation subject.  SALT is an observation, not an ACL2 claim
  ; about OS entropy.  The output contains the derived verifier, never SECRET.
  ; MAX-CREDENTIALS is the store profile's `max-credentials' (D27, PRF-102):
  ; a new login past it is refused `:too-many-credentials', so the file this
  ; writes is one the owner's loader admits under the same field.
  (declare (xargs :guard t))
  (cond
   ((not (fn-native-auth-login-namep name))
    (list :refused :name))
   ((not (fn-native-auth-admin-secretp secret))
    (list :refused :secret))
   ((not (equal secret confirmation))
    (list :refused :secret-confirmation))
   ((not (fn-authsec-saltp salt))
    (list :fault :salt-observation))
   (t
    (let* ((principal (fn-native-auth-admin-principal
                       name principal-text principal-presentp))
           (loaded (fn-native-auth-load octets presentp nil nil nil
                                        max-credentials)))
      (cond
       ((equal principal :bad) (list :refused :principal))
       ((not (equal (fn-native-auth-result-status loaded) :accepted))
        (list :refused (fn-native-auth-result-reason loaded)))
       (t
        (let* ((old (fn-auth-config-creds
                     (fn-native-auth-result-config loaded)))
               (newp (not (fn-native-auth-name-memberp name old))))
          (if (and newp (<= (nfix max-credentials) (len old)))
              (list :refused :too-many-credentials)
            (let* ((credential
                    (fn-auth-make-cred name principal
                                       (fn-authsec-enrol salt secret)
                                       (and postingp t)))
                   (credentials
                    (fn-native-auth-admin-sort-credentials
                     (fn-native-auth-admin-upsert name credential old)))
                   ; A password change keeps the login's binding, and every
                   ; other login's (fn-native-auth-load-bindings of the file
                   ; read under the writer lock).
                   (bindings (fn-native-auth-load-bindings octets presentp max-credentials))
                   (serialized (fn-native-auth-admin-serialize
                                credentials bindings)))
              (if (or (not (fn-auth-credp credential))
                      (not (fn-ncfg-ascii-octetsp serialized))
                      (< (fn-native-auth-max-octets max-credentials)
                         (len serialized)))
                  (list :fault :serialized-profile)
                (list :accepted serialized
                      (fn-native-auth-admin-public-row credential bindings))))))))))))

; The bindings with NAME's replaced by PRINCIPAL, or removed when PRINCIPAL
; is nil.
(defun fn-native-auth-admin-rebind (name principal bindings)
  (declare (xargs :guard t))
  (if (consp bindings)
      (if (and (consp (car bindings)) (equal (car (car bindings)) name))
          (fn-native-auth-admin-rebind name principal (cdr bindings))
        (cons (car bindings)
              (fn-native-auth-admin-rebind name principal (cdr bindings))))
    (if principal (list (cons name principal)) nil)))

(defun fn-native-auth-admin-bind (octets presentp name signing-text
                                        max-credentials)
  ; Host-called mutation subject for `principal bind' / `unbind'.  The login
  ; must already be enrolled; its credential row is unchanged and only its
  ; `signing' field is written or removed.  MAX-CREDENTIALS is the store
  ; profile's (D27, PRF-102): the file is loaded and rewritten under it.
  (declare (xargs :guard t))
  (let ((loaded (fn-native-auth-load octets presentp nil nil nil
                                     max-credentials))
        (principal (if signing-text
                       (if (and (true-listp signing-text)
                                (equal (len signing-text) 64)
                                (fn-id-hex-listp signing-text))
                           (fn-id-unhex signing-text)
                         :bad)
                     nil)))
    (cond
     ((not (fn-native-auth-login-namep name)) (list :refused :name))
     ((equal principal :bad) (list :refused :principal))
     ((not (equal (fn-native-auth-result-status loaded) :accepted))
      (list :refused (fn-native-auth-result-reason loaded)))
     (t
      (let* ((creds (fn-auth-config-creds (fn-native-auth-result-config loaded)))
             (credential (fn-auth-find-cred name creds)))
        (if (not (consp credential))
            (list :refused :unknown-login)
          (let* ((bindings (fn-native-auth-admin-rebind
                            name principal
                            (fn-native-auth-load-bindings octets presentp max-credentials)))
                 (serialized (fn-native-auth-admin-serialize
                              (fn-native-auth-admin-sort-credentials creds)
                              bindings)))
            (if (or (not (fn-ncfg-ascii-octetsp serialized))
                    (< (fn-native-auth-max-octets max-credentials)
                       (len serialized)))
                (list :fault :serialized-profile)
              (list :accepted serialized
                    (fn-native-auth-admin-public-row
                     credential bindings))))))))))

(defun fn-native-auth-admin-result-status (result)
  (declare (xargs :guard t))
  (if (consp result) (car result) :fault))

(defun fn-native-auth-admin-result-reason (result)
  (declare (xargs :guard t))
  (if (and (consp result) (consp (cdr result))
           (not (equal (car result) :accepted)))
      (car (cdr result)) nil))

(defun fn-native-auth-admin-result-octets (result)
  (declare (xargs :guard t))
  (if (and (consp result) (consp (cdr result))
           (equal (car result) :accepted))
      (car (cdr result)) nil))

(defun fn-native-auth-admin-result-report (result)
  (declare (xargs :guard t))
  (if (and (consp result) (consp (cdr result)) (consp (cdr (cdr result)))
           (equal (car result) :accepted))
      (car (cdr (cdr result))) nil))

; Listing is structurally independent of the verifier.  The host-called
; report function cannot expose either the salt or digest by changing them.
(defthm fn-native-auth-admin-public-report-ignores-verifier
  (equal
   (fn-native-auth-admin-public-report
    (cons (fn-auth-make-cred name principal verifier-a postingp) rest)
    bindings)
   (fn-native-auth-admin-public-report
    (cons (fn-auth-make-cred name principal verifier-b postingp) rest)
    bindings)))

; The physical replacement protocol is exactly the already-certified FNAN
; mutable replacement machine.  These wrappers add no credential or anchor
; policy: they only give the auth host a subsystem-owned call name.
(defun fn-native-auth-admin-rp-start ()
  (declare (xargs :guard t))
  (fn-anchor-rp-start))

(defun fn-native-auth-admin-rp-recover-start (presentp)
  (declare (xargs :guard t))
  (fn-anchor-rp-recover-start presentp))

(defun fn-native-auth-admin-rp-action (phase)
  (declare (xargs :guard t))
  (fn-anchor-rp-action phase))

(defun fn-native-auth-admin-rp-step (phase event)
  (declare (xargs :guard t))
  (fn-anchor-rp-step phase event))

(defun fn-native-auth-admin-rp-outcome (phase)
  (declare (xargs :guard t))
  (fn-anchor-rp-outcome phase))

(defun fn-native-auth-admin-rp-trace (phase events)
  (declare (xargs :guard t))
  (fn-anchor-rp-trace phase events))

(defun fn-native-auth-admin-rp-has-directory-okp (events)
  (declare (xargs :guard t))
  (fn-anchor-rp-has-directory-okp events))

(defun fn-native-auth-admin-rp-has-recovery-directory-okp (events)
  (declare (xargs :guard t))
  (fn-anchor-rp-has-recovery-directory-okp events))

(defthm fn-native-auth-admin-rp-durable-trace-has-directory-barrier
  (implies
   (equal (fn-native-auth-admin-rp-trace
           (fn-native-auth-admin-rp-start) events)
          :durable)
   (fn-native-auth-admin-rp-has-directory-okp events))
  :hints (("Goal" :use ((:instance
                          fn-anchor-rp-durable-trace-has-directory-barrier)))))

(defthm fn-native-auth-admin-rp-recovered-trace-has-directory-barrier
  (implies
   (equal (fn-native-auth-admin-rp-trace
           (fn-native-auth-admin-rp-recover-start presentp) events)
          :recovered)
   (fn-native-auth-admin-rp-has-recovery-directory-okp events))
  :hints (("Goal" :use ((:instance
                          fn-anchor-rp-recovered-trace-has-directory-barrier)))))

; A fixed adjacent stage prevents an unbounded crash-debris namespace.  Before
; final-file recovery, a present stage is unlinked and that unlink is itself
; directory-barriered.  Each invocation starts from fresh presence
; observations while holding the exclusive writer lock, so a process death
; never relies on an in-memory fence from the previous invocation.
(defun fn-native-auth-admin-recovery-start (stage-presentp final-presentp)
  (declare (xargs :guard t))
  (if stage-presentp
      (list :cleanup-pending (and final-presentp t))
    (list :replace-recovery
          (fn-native-auth-admin-rp-recover-start final-presentp))))

(defun fn-native-auth-admin-recovery-phase-value (phase)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr phase))
       :exec (if (and (consp phase) (consp (cdr phase)))
                 (car (cdr phase))
               nil)))

(defun fn-native-auth-admin-recovery-action (phase)
  (declare (xargs :guard t))
  (cond ((and (consp phase) (equal (car phase) :cleanup-pending))
         :issue-cleanup)
        ((and (consp phase) (equal (car phase) :cleanup-issued))
         :observe-cleanup)
        ((and (consp phase) (equal (car phase) :cleanup-visible))
         :cleanup-directory-barrier)
        ((and (consp phase) (equal (car phase) :replace-recovery))
         (fn-native-auth-admin-rp-action
          (fn-native-auth-admin-recovery-phase-value phase)))
        (t :done)))

(defun fn-native-auth-admin-recovery-event-value (event)
  (declare (xargs :guard t))
  (if (and (consp event) (consp (cdr event)))
      (car (cdr event)) nil))

(defun fn-native-auth-admin-recovery-step (phase event)
  (declare (xargs :guard t))
  (cond
   ((and (consp phase) (equal (car phase) :cleanup-pending))
    (if (equal event :cleanup-issued)
        (list :cleanup-issued
              (fn-native-auth-admin-recovery-phase-value phase)) phase))
   ((and (consp phase) (equal (car phase) :cleanup-issued))
    (if (and (consp event) (equal (car event) :cleanup-result)
             (fn-anchor-rp-resultp
              (fn-native-auth-admin-recovery-event-value event)))
        (cond
         ((equal (fn-native-auth-admin-recovery-event-value event) :ok)
          (list :cleanup-visible
                (fn-native-auth-admin-recovery-phase-value phase)))
         ((equal (fn-native-auth-admin-recovery-event-value event) :known-fail)
          :faulted)
         (t :fenced))
      phase))
   ((and (consp phase) (equal (car phase) :cleanup-visible))
    (if (and (consp event) (equal (car event) :cleanup-directory-result)
             (fn-anchor-rp-resultp
              (fn-native-auth-admin-recovery-event-value event)))
        (if (equal (fn-native-auth-admin-recovery-event-value event) :ok)
            (list :replace-recovery
                  (fn-native-auth-admin-rp-recover-start
                   (fn-native-auth-admin-recovery-phase-value phase)))
          :fenced)
      phase))
   ((and (consp phase) (equal (car phase) :replace-recovery))
    (list :replace-recovery
          (fn-native-auth-admin-rp-step
           (fn-native-auth-admin-recovery-phase-value phase) event)))
   (t phase)))

(defun fn-native-auth-admin-recovery-outcome (phase)
  (declare (xargs :guard t))
  (cond ((equal phase :faulted) :fault)
        ((equal phase :fenced) :uncertain)
        ((and (consp phase) (equal (car phase) :replace-recovery))
         (fn-native-auth-admin-rp-outcome
          (fn-native-auth-admin-recovery-phase-value phase)))
        (t :pending)))

(defun fn-native-auth-admin-recovery-trace (phase events)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-native-auth-admin-recovery-trace
       (fn-native-auth-admin-recovery-step phase (car events))
       (cdr events))
    phase))

(defun fn-native-auth-admin-recovery-has-cleanup-directory-okp (events)
  (declare (xargs :guard t))
  (if (atom events)
      nil
    (or (and (consp (car events))
             (equal (car (car events)) :cleanup-directory-result)
             (equal (fn-native-auth-admin-recovery-event-value
                     (car events)) :ok))
        (fn-native-auth-admin-recovery-has-cleanup-directory-okp
         (cdr events)))))

(defthm fn-native-auth-admin-recovery-step-enters-final-recovery-after-cleanup-barrier
  (implies
   (and (not (and (consp phase) (equal (car phase) :replace-recovery)))
        (consp (fn-native-auth-admin-recovery-step phase event))
        (equal (car (fn-native-auth-admin-recovery-step phase event))
               :replace-recovery))
   (and (consp phase)
        (equal (car phase) :cleanup-visible)
        (consp event)
        (equal (car event) :cleanup-directory-result)
        (equal (fn-native-auth-admin-recovery-event-value event) :ok)))
  :rule-classes nil)

(local
 (defthm fn-native-auth-admin-recovery-trace-introduces-final-recovery
   (implies
    (and (not (and (consp phase)
                   (equal (car phase) :replace-recovery)))
         (consp (fn-native-auth-admin-recovery-trace phase events))
         (equal (car (fn-native-auth-admin-recovery-trace phase events))
                :replace-recovery))
    (fn-native-auth-admin-recovery-has-cleanup-directory-okp events))))

; KEYSTONE for the exact recovery step/trace the native administrator calls:
; if a stage was observed at invocation start, finite execution cannot begin
; final-name recovery without a successful cleanup directory barrier.
(defthm fn-native-auth-admin-recovery-trace-cleans-stage-before-final-recovery
  (implies
   (and (consp (fn-native-auth-admin-recovery-trace
                (fn-native-auth-admin-recovery-start t final-presentp)
                events))
        (equal (car (fn-native-auth-admin-recovery-trace
                     (fn-native-auth-admin-recovery-start t final-presentp)
                     events))
               :replace-recovery))
   (fn-native-auth-admin-recovery-has-cleanup-directory-okp events))
  :hints
  (("Goal"
    :use ((:instance
           fn-native-auth-admin-recovery-trace-introduces-final-recovery
           (phase (fn-native-auth-admin-recovery-start t final-presentp)))))))

;; When a durable credential change reaches service (PKT-102).  An owner
;; reads the credential file once, at start (host/native/auth.lisp
;; fnn-native-auth-startup-hook), so a change is served only after a
;; (re)start.  OBSERVATION is what the host saw of the configured store's
;; writer lock AFTER the change was durable (host/native/io.lisp
;; fnn-store-owner-observation): :held (another process holds it: an owner
;; runs and still serves the old credentials), :free, :absent (no store), or
;; anything else when the probe failed.  Only a lock seen free or absent says
;; the change takes effect at the next start with nothing to restart; an
;; owner starting after the probe reads the durable file.  An unknown
;; observation is answered as a running owner.
(defun fn-native-auth-admin-effect-word (observation)
  (declare (xargs :guard t))
  (if (member-equal observation '(:free :absent))
      :effective-at-next-start
    :restart-required))

; KEYSTONE.  The answer never says `effective-at-next-start' while an owner
; may hold the store: only a probe that saw the lock free or the store absent
; gives it.
(defthm fn-native-auth-admin-effect-word-restart-unless-no-owner
  (equal (equal (fn-native-auth-admin-effect-word observation)
                :restart-required)
         (not (member-equal observation '(:free :absent)))))

(in-theory
 (disable (:d fn-native-auth-admin-plan-result)
          (:d fn-native-auth-admin-plan-status)
          (:d fn-native-auth-admin-plan-reason)
          (:d fn-native-auth-admin-plan-action)
          (:d fn-native-auth-admin-parse-set-options)
          (:d fn-native-auth-admin-parse-argv)
          (:d fn-native-auth-admin-action-kind)
          (:d fn-native-auth-admin-action-name)
          (:d fn-native-auth-admin-action-signing-text)
          (:d fn-native-auth-admin-binding)
          (:d fn-native-auth-admin-signing-field)
          (:d fn-native-auth-admin-rebind)
          (:d fn-native-auth-admin-bind)
          (:d fn-native-auth-admin-action-principal-text)
          (:d fn-native-auth-admin-action-principal-presentp)
          (:d fn-native-auth-admin-action-postingp)
          (:d fn-native-auth-admin-secretp)
          (:d fn-native-auth-admin-principal)
          (:d fn-native-auth-admin-upsert)
          (:d fn-native-auth-admin-octets-lessp)
          (:d fn-native-auth-admin-insert-credential)
          (:d fn-native-auth-admin-sort-credentials)
          (:d fn-native-auth-admin-quoted)
          (:d fn-native-auth-admin-field)
          (:d fn-native-auth-admin-serialize-cred)
          (:d fn-native-auth-admin-serialize-creds)
          (:d fn-native-auth-admin-serialize)
          (:d fn-native-auth-admin-public-row)
          (:d fn-native-auth-admin-public-report)
          (:d fn-native-auth-admin-list)
          (:d fn-native-auth-admin-set-password)
          (:d fn-native-auth-admin-result-status)
          (:d fn-native-auth-admin-result-reason)
          (:d fn-native-auth-admin-result-octets)
          (:d fn-native-auth-admin-result-report)
          (:d fn-native-auth-admin-recovery-start)
          (:d fn-native-auth-admin-recovery-phase-value)
          (:d fn-native-auth-admin-recovery-action)
          (:d fn-native-auth-admin-recovery-event-value)
          (:d fn-native-auth-admin-recovery-step)
          (:d fn-native-auth-admin-recovery-outcome)
          (:d fn-native-auth-admin-recovery-trace)
          (:d fn-native-auth-admin-recovery-has-cleanup-directory-okp)))
