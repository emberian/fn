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
(include-book "clock-unit")
(include-book "article")
(include-book "consumer-position")
(local (include-book "identity-invariants"))
(local (include-book "records-canonicality"))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

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
  ; 224 hexadecimal characters: the verifier's 16-octet salt, its 32-octet
  ; digest, then SCRAM's 32-octet StoredKey and 32-octet ServerKey
  ; (books/auth-secret.lisp, verifier v2).  The tag is not stored;
  ; `fn-acct-text-verifier' rebuilds the verifier through
  ; `fn-authsec-verifier', the one reassembly.
  (declare (xargs :guard t))
  (fn-acct-hex-text (append (fn-authsec-octets (fn-authsec-ver-salt ver))
                            (fn-authsec-octets (fn-authsec-ver-digest ver))
                            (fn-authsec-octets (fn-authsec-ver-stored-key ver))
                            (fn-authsec-octets (fn-authsec-ver-server-key ver)))))

(defun fn-acct-slice (start n o)
  ; Octets START .. START+N-1 of O, as many as there are.
  (declare (xargs :guard (and (natp start) (natp n))))
  (let ((rest (nthcdr start (fn-authsec-octets o))))
    (take (min n (len rest)) rest)))

(defun fn-acct-text-verifier (text)
  (declare (xargs :guard t))
  (let ((hex (fn-record-string-octets text)))
    (if (and (stringp text) (fn-id-hex-listp hex) (evenp (len hex)))
        (let ((o (fn-id-unhex hex)))
          (fn-authsec-verifier (fn-acct-slice 0 16 o) (fn-acct-slice 16 32 o)
                               (fn-acct-slice 48 32 o)
                               (nthcdr 80 (fn-authsec-octets o))))
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
           (equal (list :fn-authsec-v2 (cadr ver) (caddr ver) (cadddr ver)
                        (car (cddddr ver)))
                  ver))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-authsec-verifierp)
                                  (fn-authsec-saltp fn-cbor-octet-listp
                                   fn-authsec-32p))
           :use ((:instance fn-acct-len-one-true-list (x (cddddr ver))))))))

(local (defthm fn-acct-nthcdr-of-append-assoc
  (implies (and (true-listp a) (equal (len a) n))
           (equal (nthcdr n (append a b)) b))))

(local (defun fn-acct-nthcdr-induct (a k)
  (if (and (consp a) (posp k))
      (fn-acct-nthcdr-induct (cdr a) (- k 1))
    (list a k))))

(local (defthm fn-acct-nthcdr-past-append-head
  (implies (and (true-listp a) (natp k) (<= (len a) k))
           (equal (nthcdr k (append a b)) (nthcdr (- k (len a)) b)))
  :hints (("Goal" :induct (fn-acct-nthcdr-induct a k)))))

(local (defthm fn-acct-slice-of-append
  (implies (and (fn-cbor-octet-listp a) (equal (len a) n)
                (fn-cbor-octet-listp b) (natp m) (<= m (len b)))
           (equal (fn-acct-slice n m (append a b))
                  (take m b)))
  :hints (("Goal" :in-theory (e/d (fn-acct-slice) (fn-authsec-octets))))))

(local (defthm fn-acct-take-all
  (implies (and (true-listp x) (equal (len x) n))
           (equal (take n x) x))))

(defthm fn-acct-text-verifier-of-verifier-text
  (implies (fn-authsec-verifierp ver)
           (equal (fn-acct-text-verifier (fn-acct-verifier-text ver)) ver))
  :hints (("Goal" :in-theory (e/d (fn-authsec-verifierp fn-authsec-saltp
                                   fn-authsec-32p
                                   fn-record-string-octets-of-octets-string
                                   fn-authsec-verifier
                                   fn-authsec-ver-salt fn-authsec-ver-digest
                                   fn-authsec-ver-stored-key
                                   fn-authsec-ver-server-key fn-acct-slice)
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

; The slot's third writer is the login binding (PKT-221,
; books/login-binding.lisp): it removes only binding rows (mark 2).
(defthm fn-acct-accounts-of-apply-delta-unfolds
  (equal (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d))
         (cond ((or (equal (fn-cfg-delta-kind d) :account-invite)
                    (equal (fn-cfg-delta-kind d) :account-redeem))
                (append (fn-cfg-rows-without-key (fn-cfg-accounts v)
                                                 (fn-cfg-delta-a d))
                        (fn-cfg-delta-rows d)))
               ((equal (fn-cfg-delta-kind d) :login-binding)
                (append (fn-cfg-rows-without-binding (fn-cfg-accounts v)
                                                     (fn-cfg-delta-a d))
                        (fn-cfg-delta-rows d)))
               ((equal (fn-cfg-delta-kind d) :account-access)
                (append (fn-cfg-rows-without-access (fn-cfg-accounts v)
                                                    (fn-cfg-delta-a d))
                        (fn-cfg-delta-rows d)))
               ((equal (fn-cfg-delta-kind d) :set-group-moderation)
                (append (fn-cfg-rows-without-moderation (fn-cfg-accounts v)
                                                        (fn-cfg-delta-a d))
                        (fn-cfg-delta-rows d)))
               ((equal (fn-cfg-delta-kind d) :consumer-bind)
                (append (fn-cfg-rows-without-consumer-bind (fn-cfg-accounts v)
                                                           (fn-cfg-delta-a d))
                        (fn-cfg-delta-rows d)))
               ((equal (fn-cfg-delta-kind d) :account-delete)
                (fn-cfg-rows-deleting-account (fn-cfg-accounts v)
                                              (fn-cfg-delta-a d)))
               (t (fn-cfg-accounts v))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups))))

; Removing binding rows keeps the first row a key names when that row is an
; account row.
(local (defthm fn-acct-rows-with-key-of-rows-without-binding
  (implies (and (consp (fn-cfg-rows-with-key rows k))
                (not (fn-cfg-binding-rowp (car (fn-cfg-rows-with-key rows k)))))
           (and (consp (fn-cfg-rows-with-key
                        (fn-cfg-rows-without-binding rows l) k))
                (equal (car (fn-cfg-rows-with-key
                             (fn-cfg-rows-without-binding rows l) k))
                       (car (fn-cfg-rows-with-key rows k)))))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-binding)))))

; The slot's fourth writer is the access rule (PRF-222,
; books/group-access.lisp): it removes only access rows (mark 3).
(local (defthm fn-acct-rows-with-key-of-rows-without-access
  (implies (and (consp (fn-cfg-rows-with-key rows k))
                (not (fn-cfg-access-rowp (car (fn-cfg-rows-with-key rows k)))))
           (and (consp (fn-cfg-rows-with-key
                        (fn-cfg-rows-without-access rows l) k))
                (equal (car (fn-cfg-rows-with-key
                             (fn-cfg-rows-without-access rows l) k))
                       (car (fn-cfg-rows-with-key rows k)))))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-access)))))
; The slot's moderation writer (P3, PRF-228, code 23): it removes only
; moderation and moderator rows (marks 5 and 4).
(local (defthm fn-acct-rows-with-key-of-rows-without-moderation
  (implies (and (consp (fn-cfg-rows-with-key rows k))
                (not (fn-cfg-moderation-rowp (car (fn-cfg-rows-with-key rows k))))
                (not (fn-cfg-moderator-rowp (car (fn-cfg-rows-with-key rows k)))))
           (and (consp (fn-cfg-rows-with-key
                        (fn-cfg-rows-without-moderation rows l) k))
                (equal (car (fn-cfg-rows-with-key
                             (fn-cfg-rows-without-moderation rows l) k))
                       (car (fn-cfg-rows-with-key rows k)))))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-moderation)))))

; The slot's fifth writer is the consumer binding (PRF-234,
; books/consumer-bound.lisp): it removes only consumer binding rows (mark 6).
(local (defthm fn-acct-rows-with-key-of-rows-without-consumer-bind
  (implies (and (consp (fn-cfg-rows-with-key rows k))
                (not (fn-cfg-consumer-bind-rowp
                      (car (fn-cfg-rows-with-key rows k)))))
           (and (consp (fn-cfg-rows-with-key
                        (fn-cfg-rows-without-consumer-bind rows l) k))
                (equal (car (fn-cfg-rows-with-key
                             (fn-cfg-rows-without-consumer-bind rows l) k))
                       (car (fn-cfg-rows-with-key rows k)))))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-consumer-bind)))))

;; The account deletion (public-node-2, code 27) rewrites a redeemed row in
;; place as its tombstone: the digest a row is keyed on never changes, and
;; the key's first row is the rewritten first row.
(local (defthm fn-acct-rows-with-key-of-rows-deleting-account
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-deleting-account rows l) k)
         (fn-cfg-rows-deleting-account (fn-cfg-rows-with-key rows k) l))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-account-deleted-row)))))

(local (defthm fn-acct-ag-car-of-rows-deleting-account
  (equal (fn-cfg-ag-car (fn-cfg-rows-deleting-account rows l))
         (if (consp rows)
             (if (and (equal (fn-cfg-row-n (car rows)) 1)
                      (fn-cfg-same-login-p (fn-cfg-row-b (car rows)) l))
                 (fn-cfg-account-deleted-row (car rows))
               (car rows))
           nil))
  :hints (("Goal" :in-theory (enable fn-cfg-ag-car)))))

; -----------------------------------------------------------------------------
; Once only
;
; A code binds at most one login, ever.  A code's row is BOUND once it is
; redeemed (mark 1) or its account deleted (mark 7, the tombstone); a bound
; row's successor under an admitted delta is the row itself or, only for a
; redeemed row, its tombstone: the digest and the login never change, the
; verifier is only ever dropped, and a tombstone never changes again.

(defun fn-acct-boundp (rows digest)
  (declare (xargs :guard t))
  (let ((row (fn-cfg-account-row rows digest)))
    (and (consp row)
         (member-equal (fn-cfg-row-n row) '(1 7))
         t)))

(defun fn-acct-row-successorp (old new)
  (declare (xargs :guard t))
  (or (equal new old)
      (and (equal (fn-cfg-row-n old) 1)
           (equal new (fn-cfg-account-deleted-row old)))))

; An admitted delta keeps a bound row or tombstones a redeemed one: invite
; and redeem of another digest touch another key, an invite of this digest
; is refused as reused, a redeem of it is admitted only as the identical
; redeemed row, an account deletion tombstones exactly the redeemed rows of
; its login, and no other kind writes the slot's account rows.
(defthm fn-acct-bound-row-succeeds-by-a-delta
  (implies (and (fn-acct-boundp (fn-cfg-accounts v) digest)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-acct-row-successorp
            (fn-cfg-account-row (fn-cfg-accounts v) digest)
            (fn-cfg-account-row
             (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d)) digest)))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-account-row
                                     fn-cfg-binding-rowp
                                     fn-cfg-access-rowp
                                     fn-cfg-moderation-rowp
                                     fn-cfg-moderator-rowp
                                     fn-cfg-consumer-bind-rowp
                                     fn-cfg-ag-car)
           :cases ((equal (fn-cfg-delta-a d) digest)))))

(local (defthm fn-acct-row-successorp-is-reflexive
  (fn-acct-row-successorp x x)))

(local (defthm fn-acct-successor-of-bound-is-bound
  (implies (and (fn-acct-boundp rows digest)
                (fn-acct-row-successorp (fn-cfg-account-row rows digest)
                                        (fn-cfg-account-row rows2 digest)))
           (fn-acct-boundp rows2 digest))
  :hints (("Goal" :in-theory (enable fn-cfg-account-deleted-row)))))

(local (defthm fn-acct-row-successorp-is-transitive
  (implies (and (fn-acct-row-successorp a b) (fn-acct-row-successorp b c))
           (fn-acct-row-successorp a c))
  :hints (("Goal" :in-theory (enable fn-cfg-account-deleted-row)))))

(local (defthm fn-acct-bound-stays-bound-by-a-delta
  (implies (and (fn-acct-boundp (fn-cfg-accounts v) digest)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-acct-boundp
            (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp d)) digest))
  :hints (("Goal" :in-theory (disable fn-acct-boundp fn-acct-row-successorp
                                      fn-cfg-account-row fn-cfg-delta-reason
                                      fn-cfg-apply-delta
                                      fn-acct-accounts-of-apply-delta-unfolds)
           :use ((:instance fn-acct-bound-row-succeeds-by-a-delta)
                 (:instance fn-acct-successor-of-bound-is-bound
                            (rows (fn-cfg-accounts v))
                            (rows2 (fn-cfg-accounts
                                    (fn-cfg-apply-delta v gen stamp d)))))))))

(local (defthm fn-acct-bound-row-succeeds-from
  (implies (and (fn-acct-boundp (fn-cfg-accounts v) digest)
                (fn-acct-row-successorp orig (fn-cfg-account-row (fn-cfg-accounts v) digest))
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (fn-acct-row-successorp
            orig
            (fn-cfg-account-row
             (fn-cfg-accounts (fn-cfg-apply v gen stamp deltas)) digest)))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-admissiblep fn-cfg-admissible-reason
                                               fn-cfg-apply)
                           (fn-acct-boundp fn-cfg-account-row
                            fn-acct-row-successorp
                            fn-cfg-delta-reason
                            fn-cfg-apply-delta
                            fn-acct-accounts-of-apply-delta-unfolds)))
          ("Subgoal *1/1" :use ((:instance fn-acct-bound-row-succeeds-by-a-delta
                                           (d (car deltas)))
                                (:instance fn-acct-bound-stays-bound-by-a-delta
                                           (d (car deltas)))
                                (:instance fn-acct-row-successorp-is-transitive
                                           (a orig)
                                           (b (fn-cfg-account-row (fn-cfg-accounts v) digest))
                                           (c (fn-cfg-account-row
                                               (fn-cfg-accounts
                                                (fn-cfg-apply-delta v gen stamp (car deltas)))
                                               digest))))))))

(defthm fn-acct-bound-row-succeeds
  (implies (and (fn-acct-boundp (fn-cfg-accounts v) digest)
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (fn-acct-row-successorp
            (fn-cfg-account-row (fn-cfg-accounts v) digest)
            (fn-cfg-account-row
             (fn-cfg-accounts (fn-cfg-apply v gen stamp deltas)) digest)))
  :hints (("Goal" :in-theory (disable fn-acct-boundp fn-cfg-account-row
                                      fn-acct-row-successorp
                                      fn-acct-bound-row-succeeds-from
                                      fn-cfg-admissiblep fn-cfg-apply)
           :use ((:instance fn-acct-bound-row-succeeds-from
                            (orig (fn-cfg-account-row (fn-cfg-accounts v)
                                                      digest)))))))

(local (defthm fn-acct-bound-stays-bound
  (implies (and (fn-acct-boundp (fn-cfg-accounts v) digest)
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (fn-acct-boundp (fn-cfg-accounts (fn-cfg-apply v gen stamp deltas))
                           digest))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-admissiblep fn-cfg-admissible-reason
                                               fn-cfg-apply)
                           (fn-acct-boundp fn-cfg-account-row
                            fn-acct-row-successorp
                            fn-cfg-delta-reason
                            fn-cfg-apply-delta
                            fn-acct-accounts-of-apply-delta-unfolds))))))

;; One acceptable record: a bound row succeeds and stays bound.
(local (defthm fn-acct-bound-row-succeeds-by-a-record
  (implies (and (fn-acct-boundp (fn-cfg-accounts (fn-cfg-value cfg)) digest)
                (fn-cfg-record-acceptablep cfg r reserved ceiling))
           (and (fn-acct-row-successorp
                 (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg)) digest)
                 (fn-cfg-account-row
                  (fn-cfg-accounts (fn-cfg-value (fn-cfg-apply-record cfg r)))
                  digest))
                (fn-acct-boundp
                 (fn-cfg-accounts (fn-cfg-value (fn-cfg-apply-record cfg r)))
                 digest)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-record fn-cfg-record-acceptablep)
                                  (fn-acct-boundp fn-acct-row-successorp
                                   fn-cfg-account-row fn-cfg-apply fn-cfgp
                                   fn-cfg-recordp fn-cfg-admissiblep))
           :use ((:instance fn-acct-bound-row-succeeds
                            (v (fn-cfg-value cfg))
                            (gen (fn-cfg-record-generation r))
                            (stamp (fn-cfg-record-stamp r))
                            (deltas (fn-cfg-record-change r)))
                 (:instance fn-acct-bound-stays-bound
                            (v (fn-cfg-value cfg))
                            (gen (fn-cfg-record-generation r))
                            (stamp (fn-cfg-record-stamp r))
                            (deltas (fn-cfg-record-change r))))))))

; KEYSTONE (once only, across the history).  Across the configuration
; records the owner replays at open (`fn-config-replay-loop', the fold
; fn-owner-reconfigure-complete's published records are read back through),
; a code's bound row is, after every later acceptable record, the same row
; or -- only if it was redeemed -- its tombstone: the digest and the login it
; bound never change, so no second login is ever bound to the code, and a
; deleted account's code is never bound again.  (Restated by public-node-2
; from fn-acct-redeemed-row-stays-across-replay, the row's EQUALITY, which
; `account delete' falsifies by design.)
(local (defthm fn-acct-bound-row-succeeds-across-replay-from
  (implies (and (fn-acct-boundp (fn-cfg-accounts (fn-cfg-value cfg)) digest)
                (fn-acct-row-successorp
                 orig (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg)) digest))
                (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                            :fault)))
           (fn-acct-row-successorp
            orig
            (fn-cfg-account-row
             (fn-cfg-accounts
              (fn-cfg-value (fn-config-replay-loop cfg reserved ceiling records)))
             digest)))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (e/d (fn-config-replay-loop)
                           (fn-acct-boundp fn-acct-row-successorp
                            fn-cfg-account-row
                            fn-cfg-apply-record fn-cfg-record-acceptablep)))
          ("Subgoal *1/3"
           :use ((:instance fn-acct-bound-row-succeeds-by-a-record
                            (r (car records)))
                 (:instance fn-acct-row-successorp-is-transitive
                            (a orig)
                            (b (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg)) digest))
                            (c (fn-cfg-account-row
                                (fn-cfg-accounts (fn-cfg-value (fn-cfg-apply-record cfg (car records))))
                                digest))))))))

(defthm fn-acct-bound-row-succeeds-across-replay
  (implies (and (fn-acct-boundp (fn-cfg-accounts (fn-cfg-value cfg)) digest)
                (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                            :fault)))
           (fn-acct-row-successorp
            (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg)) digest)
            (fn-cfg-account-row
             (fn-cfg-accounts
              (fn-cfg-value (fn-config-replay-loop cfg reserved ceiling records)))
             digest)))
  :hints (("Goal" :in-theory (disable fn-acct-boundp fn-cfg-account-row
                                      fn-acct-row-successorp
                                      fn-acct-bound-row-succeeds-across-replay-from
                                      fn-config-replay-loop)
           :use ((:instance fn-acct-bound-row-succeeds-across-replay-from
                            (orig (fn-cfg-account-row
                                   (fn-cfg-accounts (fn-cfg-value cfg))
                                   digest)))))))

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
; The expiry is in milliseconds of DTN time (books/clock.lisp: wall
; milliseconds since 2000-01-01), the unit of the owner's clock that
; `fn-cfg-account-livep' compares it with when the redeem plan runs
; (host/native-admin-host.lisp fn-acct-host-owner-redeem-stage passes
; fn-own-clock): the upper end of the issuing reading's error interval plus
; SECONDS, both converted to milliseconds from the reading's own unit
; (books/clock-unit.lisp).  The running node issues from the owner's clock;
; the stopped node from its configuration record's stamp; both are
; milliseconds since PRF-378.  Bug M1 (PRF-374): the stopped path's stamp,
; then seconds, was added to milliseconds, so its codes were already
; expired.

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

(defun fn-acct-invite-expiry (seconds reading)
  (declare (xargs :guard t))
  (let ((latest (fn-clock-reading-latest-milliseconds reading)))
    (if (and (posp seconds) latest)
        (+ latest (fn-clock-seconds-in-milliseconds seconds))
      nil)))

; The pending row's delta for a code's digest text, or nil when the reading
; carries no usable wall clock (an invite cannot expire without one).
(defun fn-acct-invite-delta (digest seconds reading)
  (declare (xargs :guard t))
  (let ((expiry (fn-acct-invite-expiry seconds reading)))
    (if expiry
        (fn-cfg-account-invite digest *fn-acct-issuer*
                               (fn-acct-decimal-text expiry))
      nil)))

; The two readings an invitation is issued at.  Running: the live owner's
; clock.  Stopped: the offline configuration record's stamp, the very
; observation the record carries (host/native/admin.lisp
; fnn-admin-clock-plan, books/native-admin.lisp
; fn-native-admin-clock-observation, host/store-node-host.lisp
; fn-store-cfg-peer-delta-record), wall claim included: a stopped node whose
; wall clock is unreadable stamps a record with no wall claim, and its
; invitation refuses (fn-acct-offline-invite-refusal, PRF-379).
(defun fn-acct-live-invite-reading (clock)
  (declare (xargs :guard t))
  (fn-clock-reading *fn-clock-owner-unit* clock))

(defun fn-acct-offline-invite-reading (stamp)
  (declare (xargs :guard t))
  (fn-clock-reading *fn-clock-record-stamp-unit* stamp))

; A pending row's code is live at the issuing reading and at every later
; reading whose error interval ends before SECONDS have passed.
(defthm fn-acct-invite-delta-is-live-at-its-stamp
  (implies (fn-acct-invite-expiry seconds reading)
           (< (fn-clock-reading-latest-milliseconds reading)
              (fn-acct-invite-expiry seconds reading))))

; `account list' is books/account-list.lisp's report (PKT-391); the older
; fn-acct-list-report, which listed a binding row as pending, was removed
; with its last caller (PKT-473).

; The pending row an accepted `account invite DIGEST SECONDS' plan stages at
; READING (fn-acct-live-invite-reading of the live owner's clock, or
; fn-acct-offline-invite-reading of the offline record's stamp), or nil.
(defun fn-acct-admin-deltas (plan reading)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-admin-result-status plan) :accepted)
           (equal (fn-native-admin-result-kind plan) :account-invite))
      (let ((d (fn-acct-invite-delta
                (fn-record-octets-string (fn-native-admin-result-name plan))
                (fn-native-admin-result-capacity plan) reading)))
        (if d (list d) nil))
    nil))

; KEYSTONE (PRF-374, bug M1).  The host calls fn-acct-admin-deltas from
; host/native-admin-host.lisp: fn-native-admin-host-owner-reconfigure (the
; running node, at fn-acct-live-invite-reading of fn-own-clock) and
; fn-native-admin-host-apply (the stopped node, at
; fn-acct-offline-invite-reading of the record's stamp).  On both paths an
; accepted invite plan stages exactly one pending row whose expiry is
; now + expires in MILLISECONDS: the upper end of the reading's error
; interval plus 1000 x expires.
(defthm fn-acct-admin-deltas-expire-at-now-plus-expires-on-both-paths
  (implies (and (equal (fn-native-admin-result-status plan) :accepted)
                (equal (fn-native-admin-result-kind plan) :account-invite)
                (posp (fn-native-admin-result-capacity plan))
                (natp wall)
                (natp err))
           (let ((row (list (fn-cfg-account-invite
                             (fn-record-octets-string
                              (fn-native-admin-result-name plan))
                             *fn-acct-issuer*
                             (fn-acct-decimal-text
                              (+ wall err
                                 (* 1000 (fn-native-admin-result-capacity
                                          plan))))))))
             (and (equal (fn-acct-admin-deltas
                          plan (fn-acct-live-invite-reading
                                (fn-clock-observation monotonic wall err t)))
                         row)
                  (equal (fn-acct-admin-deltas
                          plan (fn-acct-offline-invite-reading
                                (fn-clock-observation monotonic wall err t)))
                         row))))
  :hints (("Goal" :in-theory (enable fn-clock-reading-latest-milliseconds
                                     fn-clock-reading fn-clock-readingp
                                     fn-clock-reading-unit
                                     fn-clock-reading-observation))))

; KEYSTONE (PRF-374, PRF-378).  The two paths agree exactly: at one
; observation the stopped node's expiry is the running node's.  Bug M1's
; factor of 1000, and the one-second truncation of the seconds stamp that
; followed it, are what this refutes.
(defthm fn-acct-invite-expiry-agrees-across-the-running-and-stopped-paths
  (equal (fn-acct-invite-expiry seconds (fn-acct-offline-invite-reading obs))
         (fn-acct-invite-expiry seconds (fn-acct-live-invite-reading obs)))
  :hints (("Goal" :in-theory (enable fn-clock-reading))))

; The stopped node's `account invite' outcome (PRF-379): nil when the plan
; stages its pending row at STAMP, else the reason the host reports.  An
; unreadable wall clock (a stamp with no wall claim) cannot date an expiry,
; so the verb refuses by name rather than print a code that is born
; expired.  The host calls it from host/native-admin-host.lisp
; fn-native-admin-host-apply.
(defun fn-acct-offline-invite-refusal (plan stamp)
  (declare (xargs :guard t))
  (if (fn-acct-admin-deltas plan (fn-acct-offline-invite-reading stamp))
      nil
    :no-clock))

; KEYSTONE (PRF-379).  An accepted `account invite' plan on a stopped node
; refuses :no-clock exactly when the record's stamp claims no usable wall
; clock; otherwise it stages its row.
(defthm fn-acct-offline-invite-refusal-is-no-clock-exactly-without-a-wall
  (implies (and (equal (fn-native-admin-result-status plan) :accepted)
                (equal (fn-native-admin-result-kind plan) :account-invite)
                (posp (fn-native-admin-result-capacity plan))
                (fn-clock-observationp stamp))
           (equal (fn-acct-offline-invite-refusal plan stamp)
                  (if (fn-clock-has-wall stamp) nil :no-clock)))
  :hints (("Goal" :in-theory (enable fn-clock-reading-latest-milliseconds
                                     fn-clock-reading fn-clock-readingp
                                     fn-clock-reading-unit
                                     fn-clock-reading-observation
                                     fn-clock-observationp))))

; -----------------------------------------------------------------------------
; Expiry at admission and replay (PRF-378)
;
; `fn-cfg-account-livep' reads a record's stamp in milliseconds, the unit
; of the expiry, so a redeem record stamped at or after its row's expiry is
; refused at admission (host/store-node-host.lisp
; fn-store-cfg-peer-delta-record and books/owner-config.lisp's live path
; call fn-cfg-record-acceptablep through fn-cnode-record-acceptablep) and
; faults the replay (fn-config-replay-loop, which every open folds).

(defthm fn-cfg-account-livep-unfolds
  (implies (and (natp (fn-clock-wall stamp))
                (natp (fn-clock-wall-error stamp))
                (fn-clock-observation-shapep stamp))
           (equal (fn-cfg-account-livep row stamp)
                  (and (fn-clock-has-wall stamp)
                       (< (+ (fn-clock-wall stamp) (fn-clock-wall-error stamp))
                          (fn-cfg-account-expiry (fn-cfg-row-c row))))))
  :hints (("Goal" :in-theory (enable fn-clock-reading-latest-milliseconds
                                     fn-clock-reading fn-clock-readingp
                                     fn-clock-reading-unit
                                     fn-clock-reading-observation))))

; The redeem's own branch of fn-cfg-delta-reason, and the time test in
; the stamp's milliseconds.
(defthm fn-cfg-delta-reason-of-a-redeem-past-its-expiry
  (let ((row (fn-cfg-account-row (fn-cfg-accounts v) (fn-cfg-delta-a d))))
    (implies (and (fn-cfg-deltap d)
                  (equal (fn-cfg-delta-kind d) :account-redeem)
                  (fn-cfg-account-digestp (fn-cfg-delta-a d))
                  (fn-cfg-account-loginp (fn-cfg-delta-b d))
                  (fn-cfg-account-delta-rowp d 1)
                  (consp row)
                  (equal (fn-cfg-row-n row) 0)
                  (not (fn-cfg-account-livep row stamp)))
             (equal (fn-cfg-delta-reason v gen stamp reserved ceiling d)
                    :account-expired)))
  :hints (("Goal" :in-theory (disable fn-cfg-account-livep fn-cfg-account-digestp
                                      fn-cfg-account-loginp fn-cfg-account-delta-rowp
                                      fn-cfg-account-row fn-cfg-deltap)
           :expand ((fn-cfg-delta-reason v gen stamp reserved ceiling d)))))
(defthm fn-cfg-account-livep-fails-at-or-past-the-expiry
  (implies (or (not (fn-clock-has-wall stamp))
               (<= (fn-cfg-account-expiry (fn-cfg-row-c row))
                   (+ (fn-clock-wall stamp) (fn-clock-wall-error stamp))))
           (not (fn-cfg-account-livep row stamp)))
  :hints (("Goal" :in-theory (enable fn-clock-reading-latest-milliseconds
                                     fn-clock-reading fn-clock-readingp
                                     fn-clock-reading-unit
                                     fn-clock-reading-observation))))

; KEYSTONE (PRF-378).  A record whose first delta redeems a pending code,
; stamped when the upper end of its wall interval (milliseconds) is at or
; past the code's expiry (milliseconds), or with no wall claim, is refused
; :account-expired, is not acceptable, and faults a replay reaching it.
(defthm fn-cfg-record-redeeming-an-expired-code-is-refused-and-faults-replay
  (let* ((d (car (fn-cfg-record-change r)))
         (stamp (fn-cfg-record-stamp r))
         (row (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value cfg))
                                  (fn-cfg-delta-a d))))
    (implies (and (fn-cfg-deltap d)
                  (equal (fn-cfg-delta-kind d) :account-redeem)
                  (fn-cfg-account-digestp (fn-cfg-delta-a d))
                  (fn-cfg-account-loginp (fn-cfg-delta-b d))
                  (fn-cfg-account-delta-rowp d 1)
                  (consp row)
                  (equal (fn-cfg-row-n row) 0)
                  (or (not (fn-clock-has-wall stamp))
                      (<= (fn-cfg-account-expiry (fn-cfg-row-c row))
                          (+ (fn-clock-wall stamp)
                             (fn-clock-wall-error stamp)))))
             (and (equal (fn-cfg-admissible-reason
                          (fn-cfg-value cfg) (fn-cfg-record-generation r)
                          stamp reserved ceiling (fn-cfg-record-change r))
                         :account-expired)
                  (not (fn-cfg-record-acceptablep cfg r reserved ceiling))
                  (equal (fn-config-replay-loop cfg reserved ceiling
                                                (cons r rest))
                         :fault))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-admissiblep fn-cfg-record-acceptablep)
                                  (fn-cfg-account-livep
                                   fn-cfg-account-digestp
                                   fn-cfg-account-loginp
                                   fn-cfg-account-delta-rowp
                                   fn-cfg-account-row fn-cfg-deltap
                                   fn-cfg-delta-reason fn-cfg-account-expiry
                                   fn-cfg-apply-record fn-cfg-apply-delta))
           :expand ((fn-cfg-admissible-reason
                     (fn-cfg-value cfg) (fn-cfg-record-generation r)
                     (fn-cfg-record-stamp r) reserved ceiling
                     (fn-cfg-record-change r))
                    (fn-config-replay-loop cfg reserved ceiling (cons r rest))))))

; -----------------------------------------------------------------------------
; Account deletion (public-node-2): `account delete LOGIN', delta code 27
;
; books/config.lisp owns the record (fn-cfg-account-delete) and its
; admission (fn-cfg-account-delete-reason); the verb's plan is
; books/native-admin.lisp's and its delta is exactly this record
; (fn-native-admin-plan-deltas-of-account-delete-unfolds).  The credential
; half is books/nntp-auth.lisp's
; fn-auth-config-with-accounts-after-an-account-delete-offers-only-the-operators-credential.

; KEYSTONE (refuses with an obligation).  The deletion is admitted exactly
; when the login is well formed, a redeemed row or a tombstone holds it, and
; no row names it in a role (a signing binding, a moderator role, a consumer
; binding): an account with an unresolved obligation is refused, whatever
; else holds.
(local (defthm fn-acct-account-delete-is-a-delta
  (implies (fn-cfg-account-loginp login)
           (fn-cfg-deltap (fn-cfg-account-delete login)))
  :hints (("Goal" :in-theory (enable fn-cfg-deltap fn-cfg-account-delete
                                     fn-cfg-account-loginp)))))

(defthm fn-acct-delete-is-admitted-exactly-when-held-and-unobligated
  (iff (fn-cfg-delta-reason v gen stamp reserved ceiling
                            (fn-cfg-account-delete login))
       (not (and (fn-cfg-account-loginp login)
                 (fn-cfg-account-heldp (fn-cfg-accounts v) login)
                 (not (fn-cfg-account-obligation (fn-cfg-accounts v) login)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason
                                   fn-cfg-account-delete-reason)
                                  (fn-cfg-account-loginp
                                   fn-cfg-account-heldp
                                   fn-cfg-account-obligation fn-cfg-deltap))
           :use ((:instance fn-acct-account-delete-is-a-delta))
           :expand ((fn-cfg-account-delete login)))))

; The deletion writes only the accounts slot: groups, articles' withdrawal
; rows (the authorities slot), peers and every other slot are the value's.
; Nothing is withdrawn.  An unfold of the arm, named for that.
(defthm fn-acct-delete-apply-unfolds
  (equal (fn-cfg-apply-delta v gen stamp (fn-cfg-account-delete login))
         (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v)
                                 (fn-cfg-quotas v) (fn-cfg-policies v)
                                 (fn-cfg-listeners v) (fn-cfg-peers v)
                                 (fn-cfg-limits v) (fn-cfg-authorities v)
                                 (fn-cfg-invitations v)
                                 (fn-cfg-rows-deleting-account
                                  (fn-cfg-accounts v) login)
                                 (fn-cfg-descriptions v)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-account-delete))))

; A deleted login is not redeemed again: a second code's redeem under it is
; refused :account-login-taken, since its tombstone keeps it taken.
(defthm fn-acct-delete-keeps-the-login-taken
  (implies (fn-cfg-account-login-takenp rows login)
           (fn-cfg-account-login-takenp
            (fn-cfg-rows-deleting-account rows del) login))
  :hints (("Goal" :in-theory (enable fn-cfg-account-deleted-row))))
