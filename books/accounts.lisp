; Invitation-code accounts (PRF-164; specs/nntp.md, "Invitation-code
; accounts (NNT-034)").
;
; An operator hands a friend one code.  The configuration's tenth slot
; (books/config.lisp `fn-cfg-accounts') keeps a pending row keyed on the
; crypto seam's tagged SHA-256 digest of the code, never the code; the
; friend's XREDEEM (books/nntp-auth.lisp) turns it into a redeemed row
; carrying a login and the books/auth-secret.lisp verifier of the friend's
; password, published through the owner's live reconfiguration exactly as
; `peer add' is.  The redeemed rows are the second producer of the reader's
; credential table: auth.toml's credentials at start, then these.
;
; This book owns three decisions:
;   - the digest of a code and the text a verifier is kept as in a row
;     (`fn-acct-code-digest-text', `fn-acct-verifier-text' and its inverse
;     `fn-acct-text-verifier', with the round trip that makes the text a
;     representation and not a second verifier);
;   - the redeem plan, a pure function of the configuration value and the
;     request (`fn-acct-redeem-plan'), whose :redeem delta is exactly one the
;     configuration admits;
;   - the login's local principal (`fn-acct-local-principal'), the one
;     function `fn principal set-password' without --principal also uses.
;
; Once only, PRF-097's pattern: a redeemed row stays the same row across
; every admitted delta and across the replay the owner runs at open
; (`fn-acct-redeemed-row-stays-across-replay'); a second redeem of the same
; digest is refused unless it is the identical delta
; (`fn-acct-redeemed-refuses-another-redeem'); and after the owner published
; a redeem, the same request plans "already redeemed by this login" and
; stages nothing (`fn-acct-redeem-plan-after-its-redeem-is-already-redeemed'),
; which is the crash cut after `fn-ocl-publish''s root barrier and before the
; reply.  That a guessed code finds a row is the crypto seam's preimage
; resistance (A-CRYPTO), never claimed here.
(in-package "ACL2")
(include-book "config")
(include-book "auth-secret")
(include-book "identity")
(include-book "native-admin-shape")
(local (include-book "identity-invariants"))
(local (include-book "records-canonicality"))

(defconst *fn-acct-code-tag* (fn-record-string-octets "fn-account-code-v1"))
(defconst *fn-acct-local-principal-tag*
  (fn-record-string-octets "fn-principal-local-v1"))

; -----------------------------------------------------------------------------
; Representations

(defun fn-acct-text (octets)
  ; The configuration text of wire octets (a login).
  (declare (xargs :guard t))
  (fn-record-octets-string (fn-authsec-octets octets)))

(defun fn-acct-hex-text (octets)
  (declare (xargs :guard t))
  (fn-record-octets-string (fn-id-hex-octets (fn-authsec-octets octets))))

(defun fn-acct-code-digest (code)
  ; The crypto seam's tagged digest (SHA-256 under crypto-attach) of the
  ; code's octets.
  (declare (xargs :guard t))
  (fn-digest-tagged *fn-acct-code-tag* (fn-authsec-octets code)))

(defun fn-acct-code-digest-text (code)
  (declare (xargs :guard t))
  (fn-acct-hex-text (fn-acct-code-digest code)))

(defun fn-acct-verifier-text (ver)
  ; 96 hexadecimal characters: the verifier's 16-octet salt, then its
  ; 32-octet digest.  The tag is not stored; `fn-acct-text-verifier' rebuilds
  ; the verifier through `fn-authsec-verifier', the one reassembly.
  (declare (xargs :guard t))
  (fn-acct-hex-text (append (fn-authsec-octets (fn-authsec-ver-salt ver))
                            (fn-authsec-octets (fn-authsec-ver-digest ver)))))

(defun fn-acct-text-verifier (text)
  (declare (xargs :guard t))
  (let ((hex (fn-record-string-octets text)))
    (if (and (stringp text) (fn-id-hex-listp hex) (evenp (len hex)))
        (let ((o (fn-id-unhex hex)))
          (fn-authsec-verifier (take (min 16 (len o)) o) (nthcdr 16 o)))
      nil)))

(defun fn-acct-local-principal (name)
  ; A login's local principal: the tagged digest of its octets.  The
  ; principal a credential enrolled without --principal carries
  ; (books/native-auth-admin.lisp `fn-native-auth-admin-principal').
  (declare (xargs :guard t))
  (fn-digest-tagged *fn-acct-local-principal-tag* (fn-authsec-octets name)))

; The representation boundary: a verifier kept as text in a row is the
; verifier.
(local (defthm fn-acct-cbor-octet-listp-of-hex-octets
  (implies (fn-cbor-octet-listp x)
           (and (fn-cbor-octet-listp (fn-id-hex-octets x))
                (fn-id-hex-listp (fn-id-hex-octets x))))
  :hints (("Goal" :in-theory (enable fn-id-hex-octets fn-id-hex-digit
                                     fn-id-hex-digitp fn-cbor-octet-listp
                                     fn-cbor-octetp)))))

(local (defthm fn-acct-evenp-len-hex-octets
  (evenp (len (fn-id-hex-octets x)))
  :hints (("Goal" :in-theory (enable fn-id-hex-octets evenp)))))

(local (defthm fn-acct-cbor-octet-listp-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local (defthm fn-acct-len-of-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-acct-take-of-append
  (implies (and (equal (len a) n) (true-listp a))
           (equal (take n (append a b)) a))))

(local (defthm fn-acct-nthcdr-of-append
  (implies (equal (len a) n)
           (equal (nthcdr n (append a b)) b))))

(local (defthm fn-acct-cbor-octet-listp-true-listp
  (implies (fn-cbor-octet-listp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))
  :rule-classes :forward-chaining))

(local (defthm fn-acct-len-one-true-list
  (implies (and (true-listp x) (equal (len x) 1))
           (equal (list (car x)) x))
  :rule-classes nil
  :hints (("Goal" :expand ((len x) (len (cdr x)))))))

(local (defthm fn-acct-verifier-decomposes
  (implies (fn-authsec-verifierp ver)
           (equal (list :fn-authsec-v1 (cadr ver) (caddr ver)) ver))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-authsec-verifierp)
                                  (fn-authsec-saltp fn-cbor-octet-listp))
           :use ((:instance fn-acct-len-one-true-list (x (cddr ver))))))))

(defthm fn-acct-text-verifier-of-verifier-text
  (implies (fn-authsec-verifierp ver)
           (equal (fn-acct-text-verifier (fn-acct-verifier-text ver)) ver))
  :hints (("Goal" :in-theory (e/d (fn-authsec-verifierp fn-authsec-saltp
                                   fn-record-string-octets-of-octets-string
                                   fn-authsec-verifier
                                   fn-authsec-ver-salt fn-authsec-ver-digest)
                                  (fn-record-string-octets
                                   fn-record-octets-string fn-id-hex-octets
                                   fn-id-unhex fn-id-hex-listp evenp
                                   fn-id-hex-octets-length))
           :use ((:instance fn-acct-verifier-decomposes)))))

; -----------------------------------------------------------------------------
; The redeem plan
;
;   (:already-redeemed)   the code's row is redeemed by this login and the
;                         password checks against its verifier: the resume
;                         after a crash between publication and reply
;   (:redeem D)           D is the :account-redeem delta the owner publishes
;   (:refused REASON)     the reason class; never the digest or the code
;   (:fault :salt-observation)  the host's salt was not 16 octets
;
; TAKENP is whether the login already names a credential in the connection's
; snapshot (auth.toml's rows and the redeemed rows), decided by
; books/nntp-auth.lisp with `fn-auth-find-cred'.

(defun fn-acct-redeem-plan (v stamp code login password salt takenp)
  (declare (xargs :guard t))
  (let* ((digest (fn-acct-code-digest-text code))
         (name (fn-acct-text login))
         (row (fn-cfg-account-row (fn-cfg-accounts v) digest)))
    (cond
     ((and (consp row) (equal (fn-cfg-row-n row) 1))
      (if (and (equal (fn-cfg-row-b row) name)
               (fn-authsec-checkp (fn-acct-text-verifier (fn-cfg-row-c row))
                                  password))
          (list :already-redeemed)
        (list :refused :account-redeemed)))
     (takenp (list :refused :account-login-taken))
     ((not (fn-authsec-saltp salt)) (list :fault :salt-observation))
     (t
      (let* ((d (fn-cfg-account-redeem
                 digest name
                 (fn-acct-verifier-text (fn-authsec-enrol salt password))))
             (reason (fn-cfg-delta-reason v 0 stamp 0 0 d)))
        (if reason (list :refused reason) (list :redeem d)))))))

(defun fn-acct-plan-delta (plan)
  (declare (xargs :guard t))
  (if (and (consp plan) (consp (cdr plan))) (car (cdr plan)) nil))

; -----------------------------------------------------------------------------
; Row algebra (the slot's rows are keyed; PRF-097's lemmas, for this slot)

(local (defthm fn-acct-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local (defthm fn-acct-rows-with-key-of-rows-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-key)))))

(local (defthm fn-acct-rows-with-other-key-of-rows-without-key
  (implies (not (equal j k))
           (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows j) k)
                  (fn-cfg-rows-with-key rows k)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-key)))))

(local (defthm fn-acct-first-row-kept-by-append
  (implies (consp (fn-cfg-rows-with-key a k))
           (equal (fn-cfg-ag-car (append (fn-cfg-rows-with-key a k) b))
                  (fn-cfg-ag-car (fn-cfg-rows-with-key a k))))
  :hints (("Goal" :in-theory (enable fn-cfg-ag-car)))))

(local (defthm fn-acct-first-row-with-key-has-the-key
  (implies (consp (fn-cfg-rows-with-key rows k))
           (equal (fn-cfg-row-a (car (fn-cfg-rows-with-key rows k))) k))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local (defthm fn-acct-rows-with-key-of-singleton
  (equal (fn-cfg-rows-with-key (list r) k)
         (if (equal (fn-cfg-row-a r) k) (list r) nil))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local (defthm fn-acct-rows-with-key-when-singleton
  (implies (equal (list r) rows)
           (equal (fn-cfg-rows-with-key rows k)
                  (if (equal (fn-cfg-row-a r) k) (list r) nil)))))

(defthm fn-acct-accounts-of-apply-delta-unfolds
  (equal (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d))
         (if (or (equal (fn-cfg-delta-kind d) :account-invite)
                 (equal (fn-cfg-delta-kind d) :account-redeem))
             (append (fn-cfg-rows-without-key (fn-cfg-accounts v)
                                              (fn-cfg-delta-a d))
                     (fn-cfg-delta-rows d))
           (fn-cfg-accounts v)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups))))

; -----------------------------------------------------------------------------
; Once only

; An admitted delta keeps a redeemed row the same row: invite and redeem of
; another digest touch another key, an invite of this digest is refused as
; reused, a redeem of it is admitted only as the identical row, and no other
; kind writes the slot.
(defthm fn-acct-redeemed-row-stays-by-a-delta
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts v) digest)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (equal (fn-cfg-account-row
                   (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d)) digest)
                  (fn-cfg-account-row (fn-cfg-accounts v) digest)))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-account-redeemedp
                                     fn-cfg-account-row
                                     fn-cfg-ag-car)
           :cases ((equal (fn-cfg-delta-a d) digest)))))

(local (defthm fn-acct-redeemed-stays-redeemed-by-a-delta
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts v) digest)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-cfg-account-redeemedp
            (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d)) digest))
  :hints (("Goal" :in-theory (e/d (fn-cfg-account-redeemedp)
                                  (fn-cfg-account-row fn-cfg-delta-reason
                                   fn-cfg-apply-delta
                                   fn-acct-accounts-of-apply-delta-unfolds))
           :use ((:instance fn-acct-redeemed-row-stays-by-a-delta))))))

(defthm fn-acct-redeemed-row-stays
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts v) digest)
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (equal (fn-cfg-account-row
                   (fn-cfg-accounts (fn-cfg-apply v gen stamp deltas)) digest)
                  (fn-cfg-account-row (fn-cfg-accounts v) digest)))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-admissiblep fn-cfg-admissible-reason
                                               fn-cfg-apply)
                           (fn-cfg-account-redeemedp fn-cfg-account-row
                                                     fn-cfg-delta-reason
                                                     fn-cfg-apply-delta
                                                     fn-acct-accounts-of-apply-delta-unfolds)))))

;; One acceptable record keeps a redeemed row the same row.
(local (defthm fn-acct-redeemed-row-stays-by-a-record
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts (fn-cfg-value cfg))
                                          digest)
                (fn-cfg-record-acceptablep cfg r reserved ceiling))
           (and (equal (fn-cfg-account-row
                        (fn-cfg-accounts (fn-cfg-value (fn-cfg-apply-record cfg r)))
                        digest)
                       (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg))
                                           digest))
                (fn-cfg-account-redeemedp
                 (fn-cfg-accounts (fn-cfg-value (fn-cfg-apply-record cfg r)))
                 digest)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-record fn-cfg-record-acceptablep)
                                  (fn-cfg-account-row fn-cfg-apply fn-cfgp
                                   fn-cfg-recordp fn-cfg-admissiblep))
           :use ((:instance fn-acct-redeemed-row-stays
                            (v (fn-cfg-value cfg))
                            (gen (fn-cfg-record-generation r))
                            (stamp (fn-cfg-record-stamp r))
                            (deltas (fn-cfg-record-change r))))))))

; KEYSTONE (once only, across the history).  Across the configuration
; records the owner replays at open (`fn-config-replay-loop', the fold
; fn-owner-reconfigure-complete's published records are read back through),
; a code's redeemed row is the same row after every later acceptable record:
; the login and the verifier it bound never change and no second login is
; ever bound to the code.
(defthm fn-acct-redeemed-row-stays-across-replay
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts (fn-cfg-value cfg))
                                          digest)
                (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                            :fault)))
           (equal (fn-cfg-account-row
                   (fn-cfg-accounts
                    (fn-cfg-value (fn-config-replay-loop cfg reserved ceiling
                                                         records)))
                   digest)
                  (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg))
                                      digest)))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (e/d (fn-config-replay-loop)
                           (fn-cfg-account-redeemedp fn-cfg-account-row
                            fn-cfg-apply-record fn-cfg-record-acceptablep)))))

; KEYSTONE (a second redeem).  A redeem of a redeemed digest is refused
; unless it carries exactly the redeemed row: the same login and the same
; verifier.
(defthm fn-acct-redeemed-refuses-another-redeem
  (implies (and (fn-cfg-account-redeemedp (fn-cfg-accounts v)
                                          (fn-cfg-delta-a d))
                (equal (fn-cfg-delta-kind d) :account-redeem)
                (not (equal (fn-cfg-delta-rows d)
                            (list (fn-cfg-account-row (fn-cfg-accounts v)
                                                      (fn-cfg-delta-a d))))))
           (fn-cfg-delta-reason v gen stamp reserved ceiling d))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-account-redeemedp))))

; -----------------------------------------------------------------------------
; The plan

(local (defthm fn-acct-delta-reason-of-account-redeem-ignores-ledger
  (implies (equal (fn-cfg-delta-kind d) :account-redeem)
           (equal (fn-cfg-delta-reason v gen stamp reserved ceiling d)
                  (fn-cfg-delta-reason v 0 stamp 0 0 d)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason)))))

(defmacro fn-acct-plan-redeem-delta-term ()
  '(fn-cfg-account-redeem (fn-acct-code-digest-text code)
                          (fn-acct-text login)
                          (fn-acct-verifier-text
                           (fn-authsec-enrol salt password))))

; KEYSTONE (the plan agrees with admission).  A :redeem plan's delta is one
; the configuration admits at any generation and ledger, so the owner's
; publish of it cannot be refused by `fn-cfg-admissiblep' for a reason the
; plan did not see; and it redeems the code under the login it names.
(defthm fn-acct-redeem-plan-is-admitted-and-redeems
  (let ((plan (fn-acct-redeem-plan v stamp code login password salt takenp)))
    (implies (equal (car plan) :redeem)
             (and (not (fn-cfg-delta-reason v gen stamp reserved ceiling
                                            (fn-acct-plan-delta plan)))
                  (equal (fn-cfg-account-row
                          (fn-cfg-accounts
                           (fn-cfg-apply-delta v gen stamp
                                               (fn-acct-plan-delta plan)))
                          (fn-acct-code-digest-text code))
                         (fn-cfg-row-make
                          (fn-acct-code-digest-text code)
                          (fn-acct-text login)
                          (fn-acct-verifier-text
                           (fn-authsec-enrol salt password))
                          1)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-account-redeem fn-cfg-account-row
                                   fn-cfg-rows-with-key fn-cfg-ag-car
                                   fn-cfg-ag-cdr)
                                  (fn-cfg-delta-reason fn-acct-text
                                   fn-acct-code-digest-text
                                   fn-acct-verifier-text fn-authsec-enrol))
           :use ((:instance fn-acct-delta-reason-of-account-redeem-ignores-ledger
                            (d (fn-acct-plan-redeem-delta-term)))))))

; KEYSTONE (crash between publication and reply).  Once the owner's
; publication of a redeem is durable (after fn-ocl-publish's root barrier),
; the same request -- the same code, login and password, under any later
; stamp, salt and snapshot -- plans "already redeemed by this login" and
; stages nothing: a retried XREDEEM answers 281 and never binds a second row.
(defthm fn-acct-redeem-plan-after-its-redeem-is-already-redeemed
  (let ((plan (fn-acct-redeem-plan v stamp code login password salt takenp)))
    (implies (equal (car plan) :redeem)
             (equal (fn-acct-redeem-plan
                     (fn-cfg-apply-delta v gen stamp (fn-acct-plan-delta plan))
                     stamp2 code login password salt2 takenp2)
                    (list :already-redeemed))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-account-redeem fn-cfg-account-row
                                   fn-cfg-rows-with-key fn-cfg-ag-car
                                   fn-cfg-ag-cdr)
                                  (fn-cfg-delta-reason fn-acct-text
                                   fn-acct-code-digest-text
                                   fn-acct-verifier-text fn-authsec-enrol
                                   fn-acct-text-verifier fn-authsec-checkp)))))

; KEYSTONE (another login).  A code redeemed by one login is refused to
; every other login, whatever password it sends.
(defthm fn-acct-redeem-plan-refuses-another-login
  (implies (and (fn-cfg-account-redeemedp
                 (fn-cfg-accounts v) (fn-acct-code-digest-text code))
                (not (equal (fn-cfg-row-b
                             (fn-cfg-account-row
                              (fn-cfg-accounts v)
                              (fn-acct-code-digest-text code)))
                            (fn-acct-text login))))
           (equal (fn-acct-redeem-plan v stamp code login password salt takenp)
                  (list :refused :account-redeemed)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-account-redeemedp)
                                  (fn-acct-code-digest-text fn-acct-text
                                   fn-cfg-account-row)))))

; KEYSTONE (an unknown code).  A code whose digest keys no row plans neither
; a redeem nor a resume: it stages nothing.
(defthm fn-acct-redeem-plan-of-an-unknown-code-stages-nothing
  (implies (not (consp (fn-cfg-account-row (fn-cfg-accounts v)
                                           (fn-acct-code-digest-text code))))
           (and (not (equal (car (fn-acct-redeem-plan v stamp code login
                                                      password salt takenp))
                            :redeem))
                (not (equal (car (fn-acct-redeem-plan v stamp code login
                                                      password salt takenp))
                            :already-redeemed))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason fn-cfg-account-redeem)
                                  (fn-acct-code-digest-text fn-acct-text
                                   fn-acct-verifier-text fn-authsec-enrol)))))

; -----------------------------------------------------------------------------
; The owner's plan and the word the wire answers (PKT-439)
;
; host/native-admin-host.lisp `fn-acct-host-owner-redeem-stage' runs this plan
; over the LIVE configuration value, under the owner mutex, with the code,
; login and password a holding session keeps (books/nntp-auth.lisp
; `fn-auth-redeem-request'), the host's CSPRNG salt, TAKENP from the
; connection-independent credential table (auth.toml's rows and the
; redeemed rows), USED the number of credentials in that table and BOUND the
; store profile's max-credentials (field 12, the bound auth.toml's table is
; loaded under, D27): a redeem that would take the table past the operator's
; bound is refused; a resume is never refused by it, since it adds no row.

(defun fn-acct-redeem-bounded-plan (v stamp code login password salt takenp
                                      used bound)
  (declare (xargs :guard t))
  (let ((plan (fn-acct-redeem-plan v stamp code login password salt takenp)))
    (if (and (equal (car plan) :redeem)
             (not (< (nfix used) (nfix bound))))
        (list :refused :account-credential-bound)
      plan)))

; The word the owner feeds the holding connection (books/nntp-auth.lisp
; `fn-auth-redeem-outcome'): :bound only for a resume, or for a redeem the
; owner's publication answered :accepted (host/native/admin.lisp
; `fnn-owner-live-reconfigure-locked' answers :accepted only after
; `fn-owner-reconfigure-complete' installed the durable record).
(defun fn-acct-redeem-word (plan published)
  (declare (xargs :guard t))
  (let ((head (if (consp plan) (car plan) nil)))
    (if (or (equal head :already-redeemed)
            (and (equal head :redeem) (equal published :accepted)))
        :bound
      :refused)))

; KEYSTONE (the admission limit, community-bounds' shape).  Where the plan
; would redeem, the bounded plan redeems exactly when the table is under the
; operator's bound, and otherwise refuses with the bound's own reason.
(defthm fn-acct-redeem-bounded-plan-refuses-exactly-past-the-operator-bound
  (implies (and (natp used) (natp bound)
                (equal (car (fn-acct-redeem-plan v stamp code login password
                                                 salt takenp))
                       :redeem))
           (equal (fn-acct-redeem-bounded-plan v stamp code login password salt
                                               takenp used bound)
                  (if (< used bound)
                      (fn-acct-redeem-plan v stamp code login password salt
                                           takenp)
                    (list :refused :account-credential-bound))))
  :hints (("Goal" :in-theory (disable fn-acct-redeem-plan))))

; The bound never refuses a resume or changes any plan but a redeem.
(defthm fn-acct-redeem-bounded-plan-is-the-plan-unless-it-redeems
  (implies (not (equal (car (fn-acct-redeem-plan v stamp code login password
                                                 salt takenp))
                       :redeem))
           (equal (fn-acct-redeem-bounded-plan v stamp code login password salt
                                               takenp used bound)
                  (fn-acct-redeem-plan v stamp code login password salt
                                       takenp)))
  :hints (("Goal" :in-theory (disable fn-acct-redeem-plan))))

; KEYSTONE (281 only after durability).  The owner's word is :bound only
; for a resume of a redeem already durable for this login and password, or
; for a :redeem plan whose publication answered :accepted.
(defthm fn-acct-redeem-word-is-bound-only-after-a-durable-redeem
  (implies (equal (fn-acct-redeem-word plan published) :bound)
           (or (equal (car plan) :already-redeemed)
               (and (equal (car plan) :redeem)
                    (equal published :accepted)))))

; KEYSTONE (an unknown code, on the wire).  A code whose digest keys no row
; stages nothing and answers :refused, i.e. 482 (books/nntp-auth.lisp
; fn-auth-step-pinned-redeem-outcome-answers-the-word), whatever the
; publication step reported.
(defthm fn-acct-redeem-word-of-an-unknown-code-is-refused
  (implies (not (consp (fn-cfg-account-row (fn-cfg-accounts v)
                                           (fn-acct-code-digest-text code))))
           (and (not (equal (car (fn-acct-redeem-bounded-plan
                                  v stamp code login password salt takenp
                                  used bound))
                            :redeem))
                (equal (fn-acct-redeem-word
                        (fn-acct-redeem-bounded-plan v stamp code login password
                                                     salt takenp used bound)
                        published)
                       :refused)))
  :hints (("Goal" :in-theory (disable fn-acct-redeem-plan)
           :use ((:instance fn-acct-redeem-plan-of-an-unknown-code-stages-nothing)))))

; KEYSTONE (the crash cut, through the bound).  After the owner published a
; bounded plan's redeem, the same request under any later stamp, salt,
; snapshot, count and bound answers :bound and stages nothing: a client
; whose 281 was lost to a crash after the root barrier is told 281 on retry.
(defthm fn-acct-redeem-bounded-plan-after-its-redeem-is-bound
  (let ((plan (fn-acct-redeem-bounded-plan v stamp code login password salt
                                           takenp used bound)))
    (implies (equal (car plan) :redeem)
             (let ((again (fn-acct-redeem-bounded-plan
                           (fn-cfg-apply-delta v gen stamp
                                               (fn-acct-plan-delta plan))
                           stamp2 code login password salt2 takenp2 used2
                           bound2)))
               (and (equal again (list :already-redeemed))
                    (equal (fn-acct-redeem-word again published2) :bound)))))
  :hints (("Goal" :in-theory (disable fn-acct-redeem-plan fn-cfg-apply-delta
                                      fn-acct-plan-delta)
           :use ((:instance fn-acct-redeem-plan-after-its-redeem-is-already-redeemed)))))

; -----------------------------------------------------------------------------
; The operator's verbs (PKT-439): `account invite' and `account list'
;
; The code is the hexadecimal text of 16 CSPRNG octets the host read; ACL2
; renders it and its digest, and the configuration keeps only the digest.
; The expiry is in the unit of the record's clock (books/clock.lisp: wall
; milliseconds since 2000-01-01, DTN time), which is what
; `fn-cfg-account-livep' compares it with: the upper end of the issuing
; observation's error interval plus SECONDS.

(defconst *fn-acct-code-entropy-octets* 16)
(defconst *fn-acct-default-expiry-seconds* 604800)
(defconst *fn-acct-issuer* "operator")

(defun fn-acct-code-text (entropy)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp entropy)
           (equal (len entropy) *fn-acct-code-entropy-octets*))
      (fn-acct-hex-text entropy)
    nil))

; `explode-nonnegative-integer' is the tree's decimal renderer
; (books/provenance.lisp `fn-prov-nat-string' proves the same two facts).
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-acct-explode-characters-aux
   (implies (and (natp number) (character-listp accumulator))
            (character-listp
             (explode-nonnegative-integer number 10 accumulator)))))

(defun fn-acct-decimal-text (n)
  (declare (xargs :guard t))
  (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))

(defun fn-acct-invite-expiry (seconds stamp)
  (declare (xargs :guard t))
  (if (and (posp seconds)
           (fn-clock-has-wall stamp)
           (natp (fn-clock-wall stamp))
           (natp (fn-clock-wall-error stamp)))
      (+ (fn-clock-wall stamp) (fn-clock-wall-error stamp) (* 1000 seconds))
    nil))

; The pending row's delta for a code's digest text, or nil when the stamp
; carries no usable wall clock (an invite cannot expire without one).
(defun fn-acct-invite-delta (digest seconds stamp)
  (declare (xargs :guard t))
  (let ((expiry (fn-acct-invite-expiry seconds stamp)))
    (if expiry
        (fn-cfg-account-invite digest *fn-acct-issuer*
                               (fn-acct-decimal-text expiry))
      nil)))

; A pending row's code is live at the issuing stamp and at every later stamp
; whose error interval ends before SECONDS have passed.
(defthm fn-acct-invite-delta-is-live-at-its-stamp
  (implies (fn-acct-invite-expiry seconds stamp)
           (< (+ (fn-clock-wall stamp) (fn-clock-wall-error stamp))
              (fn-acct-invite-expiry seconds stamp))))

; `account list': one line per row, never a digest or a verifier.
;   pending LOGIN-FREE expires EXPIRY
;   redeemed LOGIN PRINCIPAL-HEX
(defun fn-acct-list-lines (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((row (car rows)))
        (cons (if (equal (fn-cfg-row-n row) 1)
                  (concatenate 'string "redeemed "
                               (if (stringp (fn-cfg-row-b row))
                                   (fn-cfg-row-b row) "")
                               " "
                               (fn-acct-hex-text
                                (fn-acct-local-principal
                                 (fn-record-string-octets (fn-cfg-row-b row))))
                               (string #\Newline))
                (concatenate 'string "pending expires "
                             (if (stringp (fn-cfg-row-c row))
                                 (fn-cfg-row-c row) "")
                             (string #\Newline)))
              (fn-acct-list-lines (cdr rows))))
    nil))

(defun fn-acct-string-join (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (concatenate 'string (if (stringp (car xs)) (car xs) "")
                   (fn-acct-string-join (cdr xs)))
    ""))

(defun fn-acct-list-report (v)
  (declare (xargs :guard t))
  (fn-record-string-octets (fn-acct-string-join
                            (fn-acct-list-lines (fn-cfg-accounts v)))))

; The pending row an accepted `account invite DIGEST SECONDS' plan stages at
; STAMP (the live owner's clock, or the offline record's), or nil.
(defun fn-acct-admin-deltas (plan stamp)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-admin-result-status plan) :accepted)
           (equal (fn-native-admin-result-kind plan) :account-invite))
      (let ((d (fn-acct-invite-delta
                (fn-record-octets-string (fn-native-admin-result-name plan))
                (fn-native-admin-result-capacity plan) stamp)))
        (if d (list d) nil))
    nil))
