; fn: AUTHINFO (RFC 4643) and STARTTLS (RFC 4642) on the served reader path.
;
; This book is the outermost wrapper of the served command chain:
;
;   fn-served-dispatch  (books/served.lisp, the byte fold's per-event step)
;     -> fn-auth-step   (here)            AUTHINFO, STARTTLS, CAPABILITIES
;       -> fn-peer-step (books/peer-inbound.lisp)  IHAVE/CHECK/TAKETHIS
;         -> fn-nntp-post-step (books/nntp-post.lisp)  POST
;           -> fn-nntp-step (books/nntp.lisp)          the reader dispatcher
;
; It has exactly fn-peer-step's signature and exports the same three facts
; the fold needs of its dispatcher, so books/served.lisp swaps one call.
; Everything it does not claim is delegated unchanged.
;
; WHAT IS AND IS NOT PROVED HERE.
;
; TLS itself is a host facility.  The book sees plaintext octets either way:
; a (:starttls) effect tells tools/run_owner.py to wrap the socket, and every
; octet after the handshake arrives at fn-served-step exactly as a plaintext
; octet would.  No theorem here says anything about confidentiality,
; integrity, certificate validation or the handshake; see the trust boundary
; in specs/nntp.md.  What is proved is the protocol state machine around it:
; the capability label is advertised only where RFC 4642 section 2.1 permits,
; 382 is emitted at most once per connection, and a second STARTTLS on a TLS
; connection is 502.
;
; THE HANDSHAKE IS A STATE OF THIS MACHINE, NOT A GAP IN IT.  RFC 4642
; section 2.2 says STARTTLS MUST NOT be pipelined and that the handshake
; begins with the first octet after the 382's CRLF, so the octets that
; arrived in the same read behind the command line are handshake bytes and
; not NNTP.  The 382 branch therefore leaves the session HANDSHAKING rather
; than immediately in TLS: `fn-auth-session-handshakingp' is a connection
; state books/served.lisp's byte fold stops on exactly as it stops on a
; closed wire (fn-served-feed), so no octet of the handshake is framed as a
; command, and partition independence survives because the stop is a
; property of the connection and not of where the network cut the read.
; The host performs the upgrade on the (:starttls) effect and re-enters the
; plaintext stream with the (:tls-established) wire event this book defines,
; which is the only transition that sets `tlsp'.  That was the "Open, and a
; real one" paragraph of specs/nntp.md and it is closed here.
;
; THE SECRET IS A SALTED DIGEST.  RFC 4643 section 2.3 AUTHINFO USER/PASS is
; a cleartext password mechanism ON THE WIRE, and nothing here changes that.
; What the configuration holds is a verifier: books/auth-secret.lisp's
; (:fn-authsec-v1 salt digest) over the tagged digest of salt || secret, and
; fn-auth-checkp is fn-authsec-checkp on it.  The digest is the crypto
; seam's, executable since books/crypto-attach.lisp attached the SHA-256 of
; books/sha256.lisp, so the comparison runs on the served path and Python
; computes nothing ACL2 compares (AGENTS.md's one-owner rule).  That closes
; OB-AUTH-DIGEST; the audit entry is updated, not deleted.
;
; The consequence is stated and not softened: AUTHINFO USER/PASS over a
; plaintext connection reveals the secret to anyone on the path, which is why
; RFC 4643 section 2.3.2 requires a protected channel and why fn-auth-config
; carries `protected-onlyp'.  A stolen configuration file no longer reveals
; the secret; a tapped connection still does.

(in-package "ACL2")
(include-book "peer-inbound")
(include-book "principal")
(include-book "accounts")
(include-book "auth-secret")

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nntp-post-vocabulary
                          fn-peer-vocabulary)))
; The record accessors below are fn-inj-nth applications, as
; books/peer-inbound.lisp's are; the accessor-of-constructor lemmas cannot
; close without it.  Local, so no includer inherits the opening.
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))
; books/nntp-effects.lisp states fn-nntp-effects-single and
; fn-nntp-effects-multi OVER fn-nntp-result-effects.  That accessor is left
; enabled by books/nntp-session.lisp, so it opens to `cdr' first and the two
; rules stop matching; every effects-well-formed proof below then fails on a
; goal about `cdr'.  Closed here, book-locally, which is where
; docs/proof-style.md section 8 says a record accessor belongs.
(local (in-theory (disable fn-nntp-result-effects)))
; Two exported rules of the NNTP books state a shape fact about a recognizer:
; fn-nntp-article-idp-is-consp (books/nntp-invariants) and
; fn-nntp-response-text-true-listp (books/nntp-effects).  With the syntax
; vocabulary open above, each is tried on every `consp' and `true-listp' term
; of a dispatch over the auth step, and relieving its hypothesis opens the
; Message-ID grammar or the response-text scan on a term that is neither.
; In the certify log's two role keystones they were the top of the profile
; (560 k and 175 k useless frames of 2.3 s); no proof here reads an article
; identifier, and none needs a response text's shape from this rule.
(local (in-theory (disable fn-nntp-article-idp-is-consp
                           fn-nntp-response-text-true-listp)))

; -----------------------------------------------------------------------------
; A credential
;
; (:fn-auth-cred name principal secret postingp).  `name' is the AUTHINFO
; USER argument as octets; `principal' is the substrate principal id
; (books/principal.lisp fn-prin-idp) this login speaks for, so an
; authenticated connection names a principal and not a string; `secret' is
; the stored VERIFIER (books/auth-secret.lisp fn-authsec-verifierp), never a
; secret --- fn-authsec-verifier-is-not-octets is what makes a cleartext
; token unrecognizable in this slot; `postingp' is whether this principal
; may POST.

(defconst *fn-auth-max-name-octets* 64)

(defun fn-auth-cred-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5) (equal (car x) :fn-auth-cred)))
(defun fn-auth-cred-name (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-auth-cred-principal (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-auth-cred-secret (x)
  (declare (xargs :guard t))
  (fn-inj-nth 3 x))
(defun fn-auth-cred-postingp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 4 x))
(defun fn-auth-make-cred (name principal secret postingp)
  (declare (xargs :guard t))
  (list :fn-auth-cred name principal secret postingp))

(defthm fn-auth-cred-shapep-of-fn-auth-make-cred
  (fn-auth-cred-shapep (fn-auth-make-cred name principal secret postingp)))
(defthm fn-auth-cred-name-of-fn-auth-make-cred
  (equal (fn-auth-cred-name (fn-auth-make-cred name principal secret postingp))
         name))
(defthm fn-auth-cred-principal-of-fn-auth-make-cred
  (equal (fn-auth-cred-principal
          (fn-auth-make-cred name principal secret postingp))
         principal))
(defthm fn-auth-cred-secret-of-fn-auth-make-cred
  (equal (fn-auth-cred-secret (fn-auth-make-cred name principal secret postingp))
         secret))
(defthm fn-auth-cred-postingp-of-fn-auth-make-cred
  (equal (fn-auth-cred-postingp
          (fn-auth-make-cred name principal secret postingp))
         postingp))
(defthm fn-auth-cred-shapep-forward-shape
  (implies (fn-auth-cred-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

; The accessor-of-nothing facts fn-defrecord generates and this hand-written
; record lacks (docs/proof-style.md section 1, "what opacity takes away"):
; a field that is there means the record is there.  Forward-chaining on the
; field term itself, never a rewrite.
(defthm fn-auth-cred-accessors-forward-consp
  (and (implies (fn-auth-cred-name x) (consp x))
       (implies (fn-auth-cred-principal x) (consp x))
       (implies (fn-auth-cred-secret x) (consp x))
       (implies (fn-auth-cred-postingp x) (consp x)))
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-auth-cred-name x) (consp x))
                      :trigger-terms ((fn-auth-cred-name x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-principal x) (consp x))
                      :trigger-terms ((fn-auth-cred-principal x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-secret x) (consp x))
                      :trigger-terms ((fn-auth-cred-secret x)))
   (:forward-chaining :corollary (implies (fn-auth-cred-postingp x) (consp x))
                      :trigger-terms ((fn-auth-cred-postingp x))))
  :hints (("Goal" :in-theory (enable fn-auth-cred-name fn-auth-cred-principal
                                     fn-auth-cred-secret fn-auth-cred-postingp
                                     fn-inj-nth))))

(in-theory (disable (:d fn-auth-cred-shapep) (:d fn-auth-make-cred)
                    (:d fn-auth-cred-name) (:d fn-auth-cred-principal)
                    (:d fn-auth-cred-secret) (:d fn-auth-cred-postingp)))

(defun fn-auth-credp (x)
  (declare (xargs :guard t))
  (and (fn-auth-cred-shapep x)
       (fn-nntp-printable-tokenp (fn-auth-cred-name x))
       (consp (fn-auth-cred-name x))
       (true-listp (fn-auth-cred-name x))
       (<= (len (fn-auth-cred-name x)) *fn-auth-max-name-octets*)
       (fn-prin-idp (fn-auth-cred-principal x))
       (fn-authsec-verifierp (fn-auth-cred-secret x))
       (booleanp (fn-auth-cred-postingp x))))

(defun fn-auth-cred-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-auth-credp (car xs)) (fn-auth-cred-listp (cdr xs)))
    (null xs)))

(defun fn-auth-find-cred (name creds)
  (declare (xargs :guard t))
  (if (consp creds)
      (if (equal (fn-auth-cred-name (car creds)) name)
          (car creds)
        (fn-auth-find-cred name (cdr creds)))
    nil))

(defthm fn-auth-find-cred-is-a-cred
  (implies (and (fn-auth-cred-listp creds) (fn-auth-find-cred name creds))
           (fn-auth-credp (fn-auth-find-cred name creds))))

; -----------------------------------------------------------------------------
; The connection's authentication configuration, pinned at open
;
; (:fn-auth-config requiredp protected-onlyp tls-availablep creds).
;   requiredp        authentication is required before a state-changing command
;   protected-onlyp  AUTHINFO USER/PASS is refused on an unprotected
;                    connection (RFC 4643 section 2.3.2's 483)
;   tls-availablep   the host holds a certificate and key, so STARTTLS can be
;                    advertised and answered 382 rather than 580
;                    (RFC 4642 section 2.2.2)

(defun fn-auth-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5) (equal (car x) :fn-auth-config)))
(defun fn-auth-config-requiredp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-auth-config-protected-onlyp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-auth-config-tls-availablep (x)
  (declare (xargs :guard t))
  (fn-inj-nth 3 x))
(defun fn-auth-config-creds (x)
  (declare (xargs :guard t))
  (fn-inj-nth 4 x))
(defun fn-auth-make-config (requiredp protected-onlyp tls-availablep creds)
  (declare (xargs :guard t))
  (list :fn-auth-config requiredp protected-onlyp tls-availablep creds))

(defthm fn-auth-config-shapep-of-fn-auth-make-config
  (fn-auth-config-shapep
   (fn-auth-make-config requiredp protected-onlyp tls-availablep creds)))
(defthm fn-auth-config-requiredp-of-fn-auth-make-config
  (equal (fn-auth-config-requiredp
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         requiredp))
(defthm fn-auth-config-protected-onlyp-of-fn-auth-make-config
  (equal (fn-auth-config-protected-onlyp
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         protected-onlyp))
(defthm fn-auth-config-tls-availablep-of-fn-auth-make-config
  (equal (fn-auth-config-tls-availablep
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         tls-availablep))
(defthm fn-auth-config-creds-of-fn-auth-make-config
  (equal (fn-auth-config-creds
          (fn-auth-make-config requiredp protected-onlyp tls-availablep creds))
         creds))

(in-theory (disable (:d fn-auth-config-shapep) (:d fn-auth-make-config)
                    (:d fn-auth-config-requiredp)
                    (:d fn-auth-config-protected-onlyp)
                    (:d fn-auth-config-tls-availablep)
                    (:d fn-auth-config-creds)))

(defun fn-auth-configp (x)
  (declare (xargs :guard t))
  (and (fn-auth-config-shapep x)
       (booleanp (fn-auth-config-requiredp x))
       (booleanp (fn-auth-config-protected-onlyp x))
       (booleanp (fn-auth-config-tls-availablep x))
       (fn-auth-cred-listp (fn-auth-config-creds x))))

; What the pinned configuration carries, and what a credential found in it
; carries.  Both forward-chaining, so the two recognizers stay closed in
; the transition proofs (docs/proof-style.md) and the 281 branch can still
; see that the principal it records is a principal id.
(local (defthm fn-auth-configp-forward
  (implies (fn-auth-configp x)
           (and (booleanp (fn-auth-config-requiredp x))
                (booleanp (fn-auth-config-protected-onlyp x))
                (booleanp (fn-auth-config-tls-availablep x))
                (fn-auth-cred-listp (fn-auth-config-creds x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-configp) (fn-auth-cred-listp))))))

(local (defthm fn-auth-find-cred-principal-is-a-prin-id
  (implies (and (fn-auth-cred-listp creds) (fn-auth-find-cred name creds))
           (and (fn-prin-idp
                 (fn-auth-cred-principal (fn-auth-find-cred name creds)))
                (booleanp
                 (fn-auth-cred-postingp (fn-auth-find-cred name creds)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-credp)
                                  (fn-prin-idp fn-authsec-verifierp
                                   fn-nntp-printable-tokenp
                                   fn-auth-find-cred fn-auth-cred-listp
                                   ; else the :use hypothesis is rewritten
                                   ; to T by this very rule and says nothing
                                   fn-auth-find-cred-is-a-cred))
           :use ((:instance fn-auth-find-cred-is-a-cred))))))

; The configuration of a connection that requires nothing and offers nothing:
; the profile books/served.lisp fn-served-open opens with, so every existing
; served theorem and transcript keeps its meaning.
(defun fn-auth-open-config ()
  (declare (xargs :guard t))
  (fn-auth-make-config nil nil nil nil))

(defthm fn-auth-open-config-is-a-config
  (fn-auth-configp (fn-auth-open-config)))

; -----------------------------------------------------------------------------
; The credential table's second producer (PRF-164)
;
; ONE credential table, two producers: the operator's auth.toml, read at
; start (fn-owner-set-auth-config), and the redeemed rows of the
; configuration's `accounts' slot, published live by the owner's
; reconfiguration (books/accounts.lisp).  A connection's snapshot is taken at
; open (books/owner-config.lisp fn-ocfg-open, against the configuration the
; connection pins): auth.toml's credentials first, so a login both producers
; name is auth.toml's, then one credential per well-formed redeemed row.  A
; redeemed row's credential is the login, its local principal
; (fn-acct-local-principal, the principal `fn principal set-password' gives a
; login without --principal), the verifier the row keeps, and the posting
; allowance.  A row whose credential would not be well formed contributes
; nothing, so the snapshot is always a configuration.

(defun fn-auth-account-cred (row)
  (declare (xargs :guard t))
  (let ((name (fn-record-string-octets (fn-cfg-row-b row))))
    (fn-auth-make-cred name (fn-acct-local-principal name)
                       (fn-acct-text-verifier (fn-cfg-row-c row)) t)))

(defun fn-auth-account-creds (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-n (car rows)) 1)
               (fn-auth-credp (fn-auth-account-cred (car rows))))
          (cons (fn-auth-account-cred (car rows))
                (fn-auth-account-creds (cdr rows)))
        (fn-auth-account-creds (cdr rows)))
    nil))

(defthm fn-auth-account-creds-are-creds
  (fn-auth-cred-listp (fn-auth-account-creds rows))
  :hints (("Goal" :in-theory (disable fn-auth-credp fn-auth-account-cred))))

(local (defthm fn-auth-cred-listp-is-true-listp
  (implies (fn-auth-cred-listp x) (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-auth-credp)))))

(defun fn-auth-config-with-accounts (acfg v)
  ; The snapshot the host-called opener pins (fn-ocfg-open).
  (declare (xargs :guard t))
  (if (fn-auth-configp acfg)
      (fn-auth-make-config (fn-auth-config-requiredp acfg)
                           (fn-auth-config-protected-onlyp acfg)
                           (fn-auth-config-tls-availablep acfg)
                           (append (fn-auth-config-creds acfg)
                                   (fn-auth-account-creds
                                    (fn-cfg-accounts v))))
    acfg))

(local (defthm fn-auth-cred-listp-of-append
  (implies (and (fn-auth-cred-listp a) (fn-auth-cred-listp b))
           (fn-auth-cred-listp (append a b)))
  :hints (("Goal" :in-theory (disable fn-auth-credp)))))

(defthm fn-auth-config-with-accounts-is-a-config
  (implies (fn-auth-configp acfg)
           (fn-auth-configp (fn-auth-config-with-accounts acfg v)))
  :hints (("Goal" :in-theory (e/d (fn-auth-configp)
                                  (fn-auth-cred-listp fn-auth-account-creds)))))

(local (defthm fn-auth-find-cred-of-append
  (implies (fn-auth-cred-listp a)
           (equal (fn-auth-find-cred name (append a b))
                  (if (fn-auth-find-cred name a)
                      (fn-auth-find-cred name a)
                    (fn-auth-find-cred name b))))
  :hints (("Goal" :in-theory (enable fn-auth-credp fn-auth-cred-shapep)))))

; KEYSTONE (the snapshot).  A login auth.toml does not name is looked up in
; the redeemed rows: the credential AUTHINFO USER/PASS checks against is the
; first redeemed row's for that login, with the login's local principal and
; the verifier the row keeps.  Composed with
; fn-auth-step-principal-login-binds-exactly-the-unique-match, a redeemed
; account's 281 installs exactly that principal.
(defthm fn-auth-config-with-accounts-finds-the-redeemed-credential
  (implies (and (fn-auth-configp acfg)
                (not (fn-auth-find-cred name (fn-auth-config-creds acfg))))
           (equal (fn-auth-find-cred
                   name (fn-auth-config-creds
                         (fn-auth-config-with-accounts acfg v)))
                  (fn-auth-find-cred name (fn-auth-account-creds
                                           (fn-cfg-accounts v)))))
  :hints (("Goal" :in-theory (disable fn-auth-configp fn-auth-account-creds))))

(defthm fn-auth-config-with-accounts-keeps-the-operators-credential
  (implies (and (fn-auth-configp acfg)
                (fn-auth-find-cred name (fn-auth-config-creds acfg)))
           (equal (fn-auth-find-cred
                   name (fn-auth-config-creds
                         (fn-auth-config-with-accounts acfg v)))
                  (fn-auth-find-cred name (fn-auth-config-creds acfg))))
  :hints (("Goal" :in-theory (disable fn-auth-configp fn-auth-account-creds))))

; A redeemed row whose credential is well formed is found under its login,
; with the login's local principal and the row's verifier, ahead of every
; later row.
(defthm fn-auth-account-creds-find-the-row
  (implies (and (equal (fn-cfg-row-n row) 1)
                (fn-auth-credp (fn-auth-account-cred row)))
           (equal (fn-auth-find-cred (fn-record-string-octets (fn-cfg-row-b row))
                                     (fn-auth-account-creds (cons row rows)))
                  (fn-auth-account-cred row)))
  :hints (("Goal" :in-theory (disable fn-auth-credp fn-record-string-octets))))

; -----------------------------------------------------------------------------
; The session: the peer session, the pinned configuration, and three bits of
; per-connection authentication state.  Opaque.
;
;   pending      nil, or the name AUTHINFO USER cached (RFC 4643 section 2.3.2)
;   subject      nil, or the principal id this connection authenticated as
;   tlsp         whether a TLS layer is active underneath (RFC 4642 2.2.2)
;   handshaking  382 has been emitted and the host owes a TLS handshake: no
;                further octet of this connection is NNTP until the host
;                re-enters the plaintext stream with (:tls-established).
;                books/served.lisp's byte fold stops on this exactly as it
;                stops on a closed wire.

(defun fn-auth-session-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)))
(defun fn-auth-session-base (x)
  (declare (xargs :guard t))
  (fn-inj-nth 0 x))
(defun fn-auth-session-config (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-auth-session-pending (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-auth-session-subject (x)
  (declare (xargs :guard t))
  (fn-inj-nth 3 x))
(defun fn-auth-session-tlsp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 4 x))
(defun fn-auth-session-handshakingp (x)
  (declare (xargs :guard t))
  (fn-inj-nth 5 x))
(defun fn-auth-make-session (base config pending subject tlsp handshaking)
  (declare (xargs :guard t))
  (list base config pending subject tlsp handshaking))

(defthm fn-auth-session-shapep-of-fn-auth-make-session
  (fn-auth-session-shapep
   (fn-auth-make-session base config pending subject tlsp handshaking)))
(defthm fn-auth-session-base-of-fn-auth-make-session
  (equal (fn-auth-session-base
          (fn-auth-make-session base config pending subject tlsp handshaking))
         base))
(defthm fn-auth-session-config-of-fn-auth-make-session
  (equal (fn-auth-session-config
          (fn-auth-make-session base config pending subject tlsp handshaking))
         config))
(defthm fn-auth-session-pending-of-fn-auth-make-session
  (equal (fn-auth-session-pending
          (fn-auth-make-session base config pending subject tlsp handshaking))
         pending))
(defthm fn-auth-session-subject-of-fn-auth-make-session
  (equal (fn-auth-session-subject
          (fn-auth-make-session base config pending subject tlsp handshaking))
         subject))
(defthm fn-auth-session-tlsp-of-fn-auth-make-session
  (equal (fn-auth-session-tlsp
          (fn-auth-make-session base config pending subject tlsp handshaking))
         tlsp))
(defthm fn-auth-session-handshakingp-of-fn-auth-make-session
  (equal (fn-auth-session-handshakingp
          (fn-auth-make-session base config pending subject tlsp handshaking))
         handshaking))
(defthm fn-auth-session-shapep-forward-shape
  (implies (fn-auth-session-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-auth-session-shapep) (:d fn-auth-make-session)
                    (:d fn-auth-session-base) (:d fn-auth-session-config)
                    (:d fn-auth-session-pending) (:d fn-auth-session-subject)
                    (:d fn-auth-session-tlsp)
                    (:d fn-auth-session-handshakingp)))

; The two deeper reaches out of an auth session, named ONCE, for the same
; reason and in the same way as `fn-peer-reader-session'
; (books/peer-inbound.lisp): the chain is auth over peer over post over the
; reader session, all three base accessors are `car', and a call that stops
; one level short is answered with a plausible value rather than an error.
; Macros, not functions: each expands to exactly the term its call sites
; spell today, so the name costs no theorem, no rule and no re-proof, and
; adding a wrapper is one edit in each of these two books.
; `tools/session_depth.py' reads this ladder out of the books and fails on a
; wrong depth; it counts a hand-spelled walk as drift.
(defmacro fn-auth-post-session (as)
  `(fn-peer-session-base (fn-auth-session-base ,as)))
(defmacro fn-auth-reader-session (as)
  `(fn-peer-reader-session (fn-auth-session-base ,as)))

(defun fn-auth-sessionp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-auth-session-shapep x)
       (fn-peer-sessionp (fn-auth-session-base x))
       (fn-auth-configp (fn-auth-session-config x))
       (or (null (fn-auth-session-pending x))
           (and (consp (fn-auth-session-pending x))
                (true-listp (fn-auth-session-pending x))
                (fn-nntp-printable-tokenp (fn-auth-session-pending x))))
       (or (null (fn-auth-session-subject x))
           (fn-prin-idp (fn-auth-session-subject x)))
       (booleanp (fn-auth-session-tlsp x))
       (booleanp (fn-auth-session-handshakingp x))))

(defthm fn-auth-sessionp-forward-shape
  (implies (fn-auth-sessionp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defun fn-auth-session-consistentp (x archive)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-auth-sessionp x)
       (fn-peer-session-consistentp (fn-auth-session-base x) archive)))

; EXPORTED, forward-chaining only: books/served.lisp carries this
; consistency as its connection invariant and needs the session facts of it
; wherever a branch test mentions fn-auth-sessionp, exactly as
; books/peer-inbound.lisp exports fn-peer-session-consistentp-forward.
(defthm fn-auth-consistent-forward
  (implies (fn-auth-session-consistentp as archive)
           (and (fn-auth-sessionp as)
                (fn-peer-session-consistentp (fn-auth-session-base as)
                                             archive)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-session-consistentp)
                                  (fn-auth-sessionp
                                   fn-peer-session-consistentp)))))

(defun fn-auth-open-session (archive peer node cfg acfg tlsp)
  (declare (xargs :guard t :verify-guards nil))
  (fn-auth-make-session (fn-peer-open-session archive peer node cfg)
                        (if (fn-auth-configp acfg) acfg (fn-auth-open-config))
                        nil nil (and tlsp t) nil))

(defthm fn-auth-open-session-is-consistent
  (fn-auth-session-consistentp (fn-auth-open-session archive peer node cfg
                                                     acfg tlsp)
                               archive)
  :hints (("Goal"
           :use ((:instance fn-peer-open-session-is-consistent))
           :in-theory (disable fn-peer-open-session
                               fn-peer-open-session-is-consistent
                               fn-peer-session-consistentp fn-peer-sessionp
                               fn-auth-configp))))

(defun fn-auth-with-base (as base)
  (declare (xargs :guard t))
  (fn-auth-make-session base (fn-auth-session-config as)
                        (fn-auth-session-pending as)
                        (fn-auth-session-subject as)
                        (fn-auth-session-tlsp as)
                        (fn-auth-session-handshakingp as)))

(defun fn-auth-principal-peer-count (hex rows)
  "How many configured peer records bind HEX as their AUTHINFO principal."
  (declare (xargs :guard t))
  (if (consp rows)
      (+ (if (and (equal (fn-cfg-row-b (car rows)) "auth-principal")
                  (equal (fn-cfg-row-c (car rows)) hex)) 1 0)
         (fn-auth-principal-peer-count hex (cdr rows)))
    0))

(defun fn-auth-principal-peer-name (hex rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-b (car rows)) "auth-principal")
               (equal (fn-cfg-row-c (car rows)) hex))
          (fn-cfg-row-a (car rows))
        (fn-auth-principal-peer-name hex (cdr rows)))
    nil))

; What AUTHINFO may assume of the peer name it reads out of the configured
; rows.  `fn-cfgp' makes the peers a `fn-cfg-row-listp', every row's first
; field is a `fn-cfg-labelp' and every label is an ASCII string, so a name
; that was found is a string -- which is what `fn-peer-sessionp' asks of a
; peer connection (books/peer-inbound.lisp).  Stated here because this book
; does not open the configuration record anywhere else.
(local
 (defthm fn-auth-cfgp-gives-peer-rows
   (implies (fn-cfgp cfg)
            (fn-cfg-row-listp (fn-cfg-peers (fn-cfg-value cfg))))
   :hints (("Goal" :in-theory (enable fn-cfgp fn-cfg-valuep)))))

(local
 (defthm fn-auth-principal-peer-name-is-a-string
   (implies (and (fn-cfg-row-listp rows)
                 (fn-auth-principal-peer-name hex rows))
            (stringp (fn-auth-principal-peer-name hex rows)))
   :hints (("Goal" :induct (fn-auth-principal-peer-name hex rows)
            :in-theory (enable fn-auth-principal-peer-name fn-cfg-row-listp
                               fn-cfg-rowp fn-cfg-labelp fn-cfg-row-a
                               fn-record-ascii-stringp)))))

; The connection's peer role: the name of the configured peer record the
; connection speaks for, or nil for a reader.  Named so the role theorems
; below read as statements about the role and not about the third wrapper.
(defun fn-auth-session-peer (as)
  (declare (xargs :guard t))
  (fn-peer-session-peer (fn-auth-session-base as)))

(defthm fn-auth-session-peer-of-fn-auth-make-session
  (equal (fn-auth-session-peer
          (fn-auth-make-session base config pending subject tlsp handshaking))
         (fn-peer-session-peer base)))

(defthm fn-auth-session-peer-of-fn-auth-with-base
  (equal (fn-auth-session-peer (fn-auth-with-base as base))
         (fn-peer-session-peer base)))

; The one peer a principal binds under a pinned configuration, or nil.  A
; match is a peer whose record, read back through `fn-cfg-peer-find' exactly
; as the transit decision reads it, authenticates by (:principal HEX) with
; HEX the principal's digest in hex; and it must be the ONLY configured
; auth-principal row naming HEX.  Zero rows is a mismatch and two are an
; ambiguity, and both bind nothing.
;
; The record check is not redundant with the row count.  `fn-cfgp' asks only
; that the peers slot be a row list, and `(:set-peers rows)' installs any
; row list, so a row group can carry an auth-principal row and yet denote no
; record, or a record whose auth is (:source-address ...) because
; `fn-cfg-peer-of-rows' reads that slot first.  A role bound from such a row
; would not be one `fn-auth-clear-principal-peer' recognizes as
; principal-derived, and it would survive STARTTLS: a role learned before
; the handshake carried across it, which RFC 4642 section 2.2.2 forbids.
; Binding only a peer whose record says (:principal HEX) is what makes
; `fn-auth-principal-rolep' true of every binding, and therefore what makes
; STARTTLS clear every binding.
(defun fn-auth-principal-match (principal cfg)
  (declare (xargs :guard t))
  (let* ((hex (and (fn-cbor-octet-listp principal)
                   (fn-digest-hex principal)))
         (rows (and (fn-cfgp cfg) (fn-cfg-peers (fn-cfg-value cfg))))
         (name (and (equal (fn-auth-principal-peer-count hex rows) 1)
                    (fn-auth-principal-peer-name hex rows)))
         (record (and name (fn-cfg-peer-find name rows))))
    (and record
         (equal (fn-cfg-peer-auth record) (list :principal hex))
         name)))

; Whether the connection's peer role came from a (:principal ...) record of
; the configuration pinned into it.  The configuration is pinned at open and
; no transition of this book or of books/owner.lisp rewrites it (the owner
; re-pins only the node, fn-own-conn-live-session), so this reads the same
; record the binding read.
(defun fn-auth-principal-rolep (as)
  (declare (xargs :guard t))
  (let* ((ps (fn-auth-session-base as))
         (peer (fn-peer-session-peer ps))
         (cfg (fn-peer-session-cfg ps))
         (record (and peer (fn-cfgp cfg)
                      (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))))
    (and record (equal (car (fn-cfg-peer-auth record)) :principal))))

(defun fn-auth-bind-principal-peer (as principal)
  "Promote a contextual reader only for one unambiguous configured principal."
  (declare (xargs :guard t))
  (let* ((ps (fn-auth-session-base as))
         (cfg (fn-peer-session-cfg ps))
         ; `fn-digest-hex' is guarded by `fn-cbor-octet-listp' and the match
         ; is `:guard t', so the check is there: a principal that is not
         ; octets names no peer and promotes nothing, which is the same
         ; refusal an unmatched principal gets.  The host passes the digest
         ; `fn-auth-principal' returned, so that branch is not reachable in
         ; the composed machine.
         (peer (fn-auth-principal-match principal cfg)))
    (if (and (null (fn-peer-session-peer ps)) peer
             (fn-node-statep (fn-peer-session-node ps)))
        (fn-auth-with-base
         as (fn-peer-make-session (fn-peer-session-base ps) peer nil 0
                                  (fn-peer-session-node ps) cfg))
      as)))

(defun fn-auth-clear-principal-peer (as)
  "Drop only a role derived from (:principal ...); legacy source peers stay peers."
  (declare (xargs :guard t))
  (let ((ps (fn-auth-session-base as)))
    (if (fn-auth-principal-rolep as)
        (fn-auth-with-base
         as (fn-peer-make-session (fn-peer-session-base ps) nil nil 0
                                  (fn-peer-session-node ps)
                                  (fn-peer-session-cfg ps)))
      as)))

; -----------------------------------------------------------------------------
; Replies and effects

(defun fn-auth-single (as text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects
   (fn-nntp-single (fn-auth-reader-session as) text)))

; The one new effect.  The host has already written the 382 line when it acts
; on this; the handshake begins with the first octet after that reply's CRLF
; (RFC 4642 section 2.2.2).  The book sees plaintext octets on both sides.
(defun fn-auth-starttls-effect ()
  (declare (xargs :guard t))
  (list :starttls))

; The 382 branch appends the effect to the reply, and `append' wants the
; reply to be a proper list.  With fn-nntp-result-effects closed (see the
; theory note at the top) that is no longer read off the term, so it is a
; lemma; `:rule-classes nil' would not do, because the fact is needed in a
; guard conjecture and not in a `:use'.
(local (defthm fn-auth-single-is-not-an-offer
  ; The 480, 440, 481 and 483 refusals are single replies, so none of them
  ; puts the wire into article mode.  With fn-nntp-result-effects closed
  ; this is no longer read off the term.
  (not (fn-post-offeredp (fn-auth-single as text)))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result
                                   fn-post-offeredp
                                   fn-nntp-begin-article-effect)
                                  nil)))))

(local (defthm fn-auth-single-has-no-starttls
  ; A single reply is one (:reply ...) effect, so the handshake instruction
  ; is not in it.  With fn-nntp-result-effects closed this is no longer
  ; read off the term, and the two STARTTLS keystones are about exactly
  ; this membership.
  (not (member-equal '(:starttls) (fn-auth-single as text)))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result
                                   fn-auth-starttls-effect)
                                  nil)))))

(local (defthm fn-auth-single-is-true-listp
  (true-listp (fn-auth-single as text))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result)
                                  nil)))))

; -----------------------------------------------------------------------------
; The capability block (RFC 3977 section 5.2, RFC 4643 section 2.1,
; RFC 4642 section 2.1)
;
; One function composes the connection's effective base list with the two
; access-dependent labels; neither the reader list nor the peer list is
; restated here.  On a transit connection the base is
; fn-peer-capability-lines, so IHAVE and STREAMING mean exactly what the
; pinned peer record currently permits.  AUTHINFO remains a reader mechanism:
; it is offered when this connection may use it for reader commands, but it
; neither creates nor changes the peer identity which authorizes transit.
;
;   STARTTLS        advertised only when a certificate is configured and no
;                   TLS layer is active.  "MUST NOT be advertised once a TLS
;                   layer is active" (RFC 4642 section 2.1).
;   AUTHINFO USER   advertised only while the connection is unauthenticated
;                   AND a credential is configured AND the channel is not
;                   the one protected-only refuses.  RFC 4643 section 2.1:
;                   the arguments are the USER/PASS and SASL variants the
;                   server will accept NOW, and with no credential in the
;                   configuration every PASS is 481.
;   POST            the reader's own label, which fn-nntp-capability-lines
;                   already gates on the posting bit.  On an authenticating
;                   connection that bit is the CONJUNCTION of the pinned
;                   injection configuration (what fn-nntp-env-posting carries
;                   to fn-nntp-session-command, books/nntp.lisp) and
;                   fn-auth-postingp, so the label, the greeting code and the
;                   440 all still say the same thing.

(defun fn-auth-access-capability-lines (acfg subject tlsp)
  (declare (xargs :guard t))
  (append
   (if (and (fn-auth-config-tls-availablep acfg) (not tlsp))
       (list (fn-nntp-string-octets "STARTTLS"))
     nil)
   ; RFC 4643 section 2.1: the arguments are the mechanisms the
   ; server will accept NOW.  With no credential configured every
   ; PASS is 481, so the label would promise a mechanism that
   ; cannot succeed; with one, it is the honest offer.
   (if (or subject
           (not (consp (fn-auth-config-creds acfg)))
           (and (fn-auth-config-protected-onlyp acfg) (not tlsp)))
       nil
     (list (fn-nntp-string-octets "AUTHINFO USER")))))

(defun fn-auth-capability-lines-for-peer (acfg subject tlsp postingp record)
  ; `record' is looked up from the peer session that the owner opened from
  ; the configured source role.  A missing record or missing inbound half
  ; therefore carries no transit promise; fn-peer-step gives the refusal.
  (declare (xargs :guard t))
  (append (fn-peer-capability-lines record postingp)
          (fn-auth-access-capability-lines acfg subject tlsp)))

(defun fn-auth-capability-lines (acfg subject tlsp postingp)
  ; The reader-facing compatibility entry.  The called path uses the peer
  ; aware function above; keeping this entry means reader facts and callers
  ; continue to name the same ordinary-reader list.
  (declare (xargs :guard t))
  (fn-auth-capability-lines-for-peer acfg subject tlsp postingp nil))

(defun fn-auth-peer-record (as)
  ; Peer identity is the source/configuration role pinned at accept, never an
  ; AUTHINFO principal.  This is a bounded record lookup, not a store scan.
  (declare (xargs :guard t))
  (let ((ps (fn-auth-session-base as)))
    (fn-cfg-peer-find (fn-peer-session-peer ps)
                      (fn-cfg-peers
                       (fn-cfg-value (fn-peer-session-cfg ps))))))

; -----------------------------------------------------------------------------
; The decision functions
;
; Each is a total function of the session and the command's tokens.  Nothing
; here reads a global and nothing re-derives a value another book owns.

(defun fn-auth-checkp (cred secret)
  ; The whole of the password comparison, in ACL2: books/auth-secret.lisp's
  ; fn-authsec-checkp against the credential's stored verifier.  The
  ; enrolled secret always passes (fn-authsec-enrolled-secret-checks); that a
  ; wrong one fails is A-CRYPTO and is not claimed here.
  (declare (xargs :guard t))
  (and (consp cred) (fn-authsec-checkp (fn-auth-cred-secret cred) secret)))

(defun fn-auth-postingp (as)
  ; The posting allowance of the connection.  Authenticated, the credential
  ; decides and nothing else: a principal enrolled without the posting flag
  ; may not POST however permissive the pinned injection configuration is.
  ; Unauthenticated, a configuration that requires authentication refuses,
  ; and one that does not leaves the decision where it was before this book
  ; existed -- with the connection's pinned injection configuration, which
  ; fn-nntp-post-step reads.
  (declare (xargs :guard t))
  (let ((acfg (fn-auth-session-config as)))
    (if (fn-auth-session-subject as)
        (let ((cred (fn-auth-find-cred (fn-auth-session-pending as)
                                       (fn-auth-config-creds acfg))))
          (and (consp cred)
               (equal (fn-auth-cred-principal cred)
                      (fn-auth-session-subject as))
               (fn-auth-cred-postingp cred)
               t))
      (not (fn-auth-config-requiredp acfg)))))

; Which commands this book refuses before delegating when the configuration
; requires authentication and the connection has not authenticated.  RFC 4643
; section 2.2 permits a server to require authentication for any command; fn
; requires it for exactly the local reader commands that can change durable
; state or disclose article content.  Transit is not reader authentication:
; IHAVE, CHECK, and TAKETHIS always delegate to fn-peer-step, which decides
; from the configured source-role record and refuses a non-peer itself.  An
; unauthenticated client can still discover the server (CAPABILITIES, HELP,
; QUIT, MODE, DATE, AUTHINFO, STARTTLS).
(defun fn-auth-restricted-keywordp (keyword)
  (declare (xargs :guard t))
  (or (fn-nntp-keywordp keyword "POST")
      (fn-nntp-keywordp keyword "GROUP")
      (fn-nntp-keywordp keyword "LISTGROUP")
      (fn-nntp-keywordp keyword "LIST")
      (fn-nntp-keywordp keyword "NEXT")
      (fn-nntp-keywordp keyword "LAST")
      (fn-nntp-keywordp keyword "ARTICLE")
      (fn-nntp-keywordp keyword "HEAD")
      (fn-nntp-keywordp keyword "BODY")
      (fn-nntp-keywordp keyword "STAT")
      (fn-nntp-keywordp keyword "OVER")
      (fn-nntp-keywordp keyword "XOVER")
      (fn-nntp-keywordp keyword "HDR")
      (fn-nntp-keywordp keyword "XHDR")
      (fn-nntp-keywordp keyword "XPAT")
      (fn-nntp-keywordp keyword "NEWGROUPS")
      ; NEWNEWS reads the archive and answers with stored identifiers, so it
      ; is gated exactly as the other archive readers are.
      (fn-nntp-keywordp keyword "NEWNEWS")))

(defun fn-auth-transit-keywordp (keyword)
  ; The three inbound-transfer verbs are peer policy, not reader policy.
  (declare (xargs :guard t))
  (or (fn-nntp-keywordp keyword "IHAVE")
      (fn-nntp-keywordp keyword "CHECK")
      (fn-nntp-keywordp keyword "TAKETHIS")))

(defthm fn-auth-transit-keyword-is-not-reader-restricted
  (implies (fn-auth-transit-keywordp keyword)
           (not (fn-auth-restricted-keywordp keyword)))
  :hints (("Goal" :in-theory (enable fn-auth-transit-keywordp
                                        fn-auth-restricted-keywordp
                                        fn-nntp-keywordp))))

(defun fn-auth-gatedp (as keyword)
  (declare (xargs :guard t))
  (and (fn-auth-config-requiredp (fn-auth-session-config as))
       (not (fn-auth-session-subject as))
       (fn-auth-restricted-keywordp keyword)
       t))

; fn-auth-authinfo tests USER before PASS, so every theorem about the PASS
; branch has to know the two words are different.  They are, by evaluation:
; fn-nntp-keywordp is one `equal' against a ground octet list.
(local (defthm fn-auth-user-is-not-pass
  (implies (fn-nntp-keywordp keyword "USER")
           (not (fn-nntp-keywordp keyword "PASS")))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

(defun fn-auth-token-argp (args)
  (declare (xargs :guard t))
  (and (consp args) (null (cdr args))
       (consp (car args))
       (true-listp (car args))
       (fn-nntp-printable-tokenp (car args))))

; What the cached name is, once the argument check has passed: the USER
; branch stores it in the session and fn-auth-sessionp asks for exactly
; these three facts of it.  Forward-chaining, so the recognizer stays
; closed in the preservation proof.
(local (defthm fn-auth-token-argp-forward
  (implies (fn-auth-token-argp args)
           (and (consp args) (null (cdr args))
                (consp (car args)) (true-listp (car args))
                (fn-nntp-printable-tokenp (car args))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-token-argp)
                                  (fn-nntp-printable-tokenp))))))

; AUTHINFO (RFC 4643 section 2.3).
(defun fn-auth-authinfo (as args)
  (declare (xargs :guard t))
  (let ((acfg (fn-auth-session-config as)))
    (cond
     ; Already authenticated: section 2.3.1 note [2], the command is not
     ; available to this client.  Never 480: section 2.3.2 forbids it.
     ((fn-auth-session-subject as)
      (fn-post-make-result as (fn-auth-single as "502 already authenticated") nil))
     ; Section 2.3.2: a cleartext mechanism on an unprotected connection is
     ; 483, and the client is told to protect the channel first.
     ((and (fn-auth-config-protected-onlyp acfg) (not (fn-auth-session-tlsp as)))
      (fn-post-make-result
       as (fn-auth-single as "483 a protected channel is required; use STARTTLS")
       nil))
     ((and (consp args) (fn-nntp-keywordp (car args) "USER"))
      (if (not (fn-auth-token-argp (cdr args)))
          (fn-post-make-result as (fn-auth-single as "501 syntax error") nil)
        ; Section 2.3.2: "MUST return a 381 response to AUTHINFO USER".
        ; Unconditionally: whether the name is known is not disclosed here.
        (fn-post-make-result
         (fn-auth-make-session (fn-auth-session-base as) acfg
                               (car (cdr args)) nil
                               (fn-auth-session-tlsp as)
                               (fn-auth-session-handshakingp as))
         (fn-auth-single as "381 password required")
         nil)))
     ((and (consp args) (fn-nntp-keywordp (car args) "PASS"))
      (if (not (fn-auth-token-argp (cdr args)))
          (fn-post-make-result as (fn-auth-single as "501 syntax error") nil)
        (if (not (fn-auth-session-pending as))
            ; Section 2.3.2: "MUST give a 482 response to AUTHINFO PASS if
            ; there is no cached username."
            (fn-post-make-result
             as (fn-auth-single as "482 authentication commands issued out of sequence")
             nil)
          (let ((cred (fn-auth-find-cred (fn-auth-session-pending as)
                                         (fn-auth-config-creds acfg))))
            (if (fn-auth-checkp cred (car (cdr args)))
                (let* ((authenticated
                         (fn-auth-make-session (fn-auth-session-base as) acfg
                                               (fn-auth-session-pending as)
                                               (fn-auth-cred-principal cred)
                                               (fn-auth-session-tlsp as)
                                               (fn-auth-session-handshakingp as)))
                       (bound (fn-auth-bind-principal-peer
                               authenticated (fn-auth-cred-principal cred))))
                (fn-post-make-result
                 bound
                 (fn-auth-single as "281 authentication accepted")
                 nil))
              ; The cached name is cleared on failure, so a failed PASS
              ; cannot be retried without a fresh USER.
              (fn-post-make-result
               (fn-auth-make-session (fn-auth-session-base as) acfg nil nil
                                     (fn-auth-session-tlsp as)
                                     (fn-auth-session-handshakingp as))
               (fn-auth-single as "481 authentication failed")
               nil))))))
     ; SASL (section 2.4) is DEFERRED, not refused: no mechanism is
     ; implemented, so section 2.4.1 note [2]'s 502 is the honest answer and
     ; the SASL capability argument is never advertised.
     ((and (consp args) (fn-nntp-keywordp (car args) "SASL"))
      (fn-post-make-result as (fn-auth-single as "502 no SASL mechanism is offered")
                           nil))
     (t (fn-post-make-result as (fn-auth-single as "501 syntax error") nil)))))

; STARTTLS (RFC 4642 section 2.2).
(defun fn-auth-starttls (as args)
  ; The guard hint keeps fn-auth-single closed so the true-listp lemma
  ; above matches: the 382 branch is the one place this book appends to a
  ; reply, and `append' wants a proper list.
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable fn-auth-single fn-nntp-single
                                               fn-nntp-result-effects)
                    :use ((:instance fn-auth-single-is-true-listp
                                     (text "382 continue with TLS negotiation")))))))
  (cond
   ((not (null args))
    (fn-post-make-result as (fn-auth-single as "501 syntax error") nil))
   ; Section 2.2.2: once a TLS layer is active, STARTTLS is not a valid
   ; command.  Never 480 or 483: the section forbids both here.
   ((fn-auth-session-tlsp as)
    (fn-post-make-result as (fn-auth-single as "502 a TLS layer is already active")
                         nil))
   ; Section 2.2.2: unable to initiate, for a configuration reason, is 580.
   ((not (fn-auth-config-tls-availablep (fn-auth-session-config as)))
    (fn-post-make-result
     as (fn-auth-single as "580 can not initiate TLS negotiation") nil))
   (t
    ; 382 and then the handshake.  The session becomes HANDSHAKING, not
    ; TLS: section 2.2 forbids pipelining STARTTLS and puts the handshake's
    ; first octet immediately after the 382's CRLF, so every octet still in
    ; this read belongs to the handshake.  books/served.lisp's fold stops on
    ; a handshaking session, the host upgrades the socket on the
    ; (:starttls) effect, and (:tls-established) is the one transition that
    ; sets `tlsp'.  Section 2.2.2 also requires the protocol state to be
    ; reset, which is why the cached name and the subject are dropped here:
    ; nothing learned before the handshake is carried across it.
    (let ((cleared (fn-auth-clear-principal-peer as)))
    (fn-post-make-result
     (fn-auth-make-session (fn-auth-session-base cleared)
                           (fn-auth-session-config as) nil nil nil t)
     (append (fn-auth-single as "382 continue with TLS negotiation")
             (list (fn-auth-starttls-effect)))
     nil)))))

; The host's re-entry after the handshake (RFC 4642 section 2.2.2).  It is a
; wire event and not a command: no client octet produces it, and it emits no
; reply.  The session leaves handshaking with a TLS layer recorded; the base
; session is untouched, because the protocol state was already reset when
; 382 was emitted.
(defun fn-auth-tls-established (as)
  (declare (xargs :guard t))
  (fn-post-make-result
   (fn-auth-make-session (fn-auth-session-base as) (fn-auth-session-config as)
                         nil nil t nil)
   nil nil))

(defun fn-auth-tls-eventp (wire-event)
  (declare (xargs :guard t))
  (and (consp wire-event)
       (equal (car wire-event) :tls-established)
       (null (cdr wire-event))))

(defun fn-auth-command (as config keyword args)
  ; The commands this book answers.  Anything else is nil: delegate.
  ;
  ; The gate is FIRST, deliberately.  With it last, every theorem about the
  ; gate would have to prove that a restricted keyword is not also AUTHINFO,
  ; STARTTLS or CAPABILITIES -- true, but an argument about string equality
  ; rather than about the gate.  First, the refusal is read directly off the
  ; branch.  AUTHINFO, STARTTLS, CAPABILITIES, HELP, QUIT, MODE and DATE are
  ; not in fn-auth-restricted-keywordp, so an unauthenticated client can
  ; still authenticate and still discover the server.
  ;
  ; `config' is the connection's pinned injection configuration, the same
  ; value fn-nntp-post-step reads; it appears here for exactly one reason,
  ; the POST capability label, and no decision below re-derives anything
  ; that book owns.
  (declare (xargs :guard t))
  (cond
   ((fn-auth-gatedp as keyword)
    ; RFC 4643 section 2.2: 480, and the command is not performed.
    (fn-post-make-result as (fn-auth-single as "480 authentication required")
                         nil))
   ; RFC 3977 section 3.2.1 / 6.3.1.1: 440 is "posting not permitted", and
   ; it is the answer when the authenticated principal was enrolled without
   ; the posting flag.  A configuration that forbids posting outright is
   ; still fn-nntp-post-step's 440 and is not decided twice.  This arm sits
   ; SECOND, immediately behind the gate and ahead of AUTHINFO, for the
   ; reason the gate sits first: a theorem about it then reads the refusal
   ; off the branch instead of having to prove that POST is not also
   ; AUTHINFO, STARTTLS or CAPABILITIES.
   ((and (fn-nntp-keywordp keyword "POST") (not (fn-auth-postingp as)))
    (fn-post-make-result
     as (fn-auth-single as "440 posting not permitted for this principal") nil))
   ((fn-nntp-keywordp keyword "AUTHINFO") (fn-auth-authinfo as args))
   ((fn-nntp-keywordp keyword "STARTTLS") (fn-auth-starttls as args))
   ((and (fn-nntp-keywordp keyword "CAPABILITIES")
         (or (null args)
             (and (consp args) (null (cdr args))
                  (fn-nntp-keyword-tokenp (car args)))))
    (fn-post-make-result
     as
      (fn-nntp-result-effects
      (fn-nntp-multi (fn-auth-reader-session as)
                     "101 capability list follows"
                     (fn-auth-capability-lines-for-peer
                      (fn-auth-session-config as)
                      (fn-auth-session-subject as)
                      (fn-auth-session-tlsp as)
                      (and (fn-inj-config-allow config)
                           (fn-auth-postingp as))
                      (fn-auth-peer-record as))))
     nil))
   (t nil)))

(defun fn-auth-delegate (as archive config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-peer-step (fn-auth-session-base as) archive config observation
                         injection wire-event)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

; The step.  Exactly fn-peer-step's signature.
(defun fn-auth-step (as archive config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-auth-sessionp as)) (fn-post-make-result as nil nil))
   ; RFC 4642 section 2.2.2: the host's re-entry after the handshake.
   ((fn-auth-tls-eventp wire-event) (fn-auth-tls-established as))
   ; A handshaking connection serves nothing: every octet belongs to the
   ; handshake, and books/served.lisp's fold does not even frame them.  The
   ; branch is here so that the property holds of the step itself and not
   ; only of its caller.
   ((fn-auth-session-handshakingp as) (fn-post-make-result as nil nil))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-auth-command as config (car tokens) (cdr tokens))))
            (if r r
              (fn-auth-delegate as archive config observation injection
                                wire-event)))
        (fn-auth-delegate as archive config observation injection wire-event))))
   (t (fn-auth-delegate as archive config observation injection wire-event))))

(verify-guards fn-auth-cred-shapep)
(verify-guards fn-auth-make-cred)
(verify-guards fn-auth-credp)
(verify-guards fn-auth-cred-listp)
(verify-guards fn-auth-find-cred)
(verify-guards fn-auth-config-shapep)
(verify-guards fn-auth-make-config)
(verify-guards fn-auth-configp)
(verify-guards fn-auth-open-config)
(verify-guards fn-auth-session-shapep)
(verify-guards fn-auth-make-session)
(verify-guards fn-auth-sessionp)
(verify-guards fn-auth-open-session)
(verify-guards fn-auth-with-base)
(verify-guards fn-auth-principal-peer-count)
(verify-guards fn-auth-principal-peer-name)
(verify-guards fn-auth-session-peer)
(verify-guards fn-auth-principal-match)
(verify-guards fn-auth-principal-rolep)
(verify-guards fn-auth-bind-principal-peer)
(verify-guards fn-auth-clear-principal-peer)
(verify-guards fn-auth-single)
(verify-guards fn-auth-starttls-effect)
(verify-guards fn-auth-access-capability-lines)
(verify-guards fn-auth-capability-lines-for-peer)
(verify-guards fn-auth-capability-lines)
(verify-guards fn-auth-peer-record)
(verify-guards fn-auth-checkp)
(verify-guards fn-auth-postingp)
(verify-guards fn-auth-restricted-keywordp)
(verify-guards fn-auth-transit-keywordp)
(verify-guards fn-auth-gatedp)
(verify-guards fn-auth-token-argp)
(verify-guards fn-auth-authinfo)
(verify-guards fn-auth-starttls)
(verify-guards fn-auth-tls-established)
(verify-guards fn-auth-tls-eventp)
(verify-guards fn-auth-command)
(verify-guards fn-auth-delegate)
(verify-guards fn-auth-step)

; -----------------------------------------------------------------------------
; What the step preserves and emits
;
; The three facts books/served.lisp's fold needs of its dispatcher, stated as
; books/peer-inbound.lisp states them of fn-peer-step, and lifted from them.

(local (defthm fn-auth-effectsp-of-append
  (implies (and (fn-nntp-effectsp a) (fn-nntp-effectsp b))
           (fn-nntp-effectsp (append a b)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-effectsp) (fn-nntp-effectp))))))

(defthm fn-auth-single-effects-well-formed
  (implies (and (fn-nntp-response-textp (fn-nntp-string-octets text))
                (fn-nntp-initial-status-linep (fn-nntp-string-octets text))
                (<= (+ (len (fn-nntp-string-octets text)) 2)
                    *fn-nntp-max-response-octets*))
           (fn-nntp-effectsp (fn-auth-single as text)))
  :hints (("Goal" :in-theory (e/d (fn-auth-single)
                                  (fn-nntp-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep)))))

; The closed enumeration of what THIS book may emit: everything
; books/nntp-effects.lisp enumerates, plus the one new effect.  A separate
; recognizer rather than a new arm of fn-nntp-effectp, because (:starttls)
; is not an NNTP effect -- it is an instruction to the host's transport --
; and because widening fn-nntp-effectp would invalidate the certificate of
; every book above books/nntp-effects.  books/served.lisp accepts it the
; same way it accepts the :submit effect.

(defun fn-auth-effectp (effect)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-nntp-effectp effect)
      (equal effect (fn-auth-starttls-effect))))

(defun fn-auth-effectsp (effects)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp effects)
      (and (fn-auth-effectp (car effects))
           (fn-auth-effectsp (cdr effects)))
    (null effects)))

(defthm fn-auth-nntp-effects-are-auth-effects
  (implies (fn-nntp-effectsp effects)
           (fn-auth-effectsp effects))
  :hints (("Goal" :induct (fn-auth-effectsp effects)
           :in-theory (e/d (fn-nntp-effectsp fn-auth-effectp)
                           (fn-nntp-effectp)))))

(defthm fn-auth-effectsp-of-append-auth
  (implies (and (fn-auth-effectsp a) (fn-auth-effectsp b))
           (fn-auth-effectsp (append a b)))
  ; fn-auth-nntp-effects-are-auth-effects is closed: it is tried on every
  ; fn-auth-effectsp term of the induction and opens fn-nntp-effectsp to
  ; relieve its hypothesis, 277 k useless frames of the 0.87 s.
  :hints (("Goal" :induct (fn-auth-effectsp a)
           :in-theory (disable fn-auth-effectp
                               fn-auth-nntp-effects-are-auth-effects))))

(defthm fn-auth-starttls-effect-is-typed
  (fn-auth-effectsp (list (fn-auth-starttls-effect)))
  :hints (("Goal" :in-theory (enable fn-auth-effectsp fn-auth-effectp))))

(defthm fn-auth-capability-lines-are-block-text
  (fn-nntp-block-textp
   (fn-auth-capability-lines acfg subject tlsp postingp))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

(defthm fn-auth-capability-lines-for-peer-are-block-text
  (fn-nntp-block-textp
   (fn-auth-capability-lines-for-peer acfg subject tlsp postingp record))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-capability-lines-for-peer
                            fn-auth-access-capability-lines
                            fn-peer-capability-lines
                            fn-nntp-capability-lines
                            fn-nntp-block-textp)
                           ((:d fn-cfg-peer-inbound))))))

(defthm fn-auth-authinfo-effects-well-formed
  (fn-auth-effectsp (fn-post-result-effects (fn-auth-authinfo as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo)
                                  (fn-auth-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-keywordp fn-auth-token-argp
                                   fn-auth-find-cred fn-auth-checkp)))))

(defthm fn-auth-starttls-effects-well-formed
  (fn-auth-effectsp (fn-post-result-effects (fn-auth-starttls as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls)
                                  (fn-auth-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep)))))


(defthm fn-auth-tls-established-effects-well-formed
  (fn-auth-effectsp (fn-post-result-effects (fn-auth-tls-established as)))
  :hints (("Goal" :in-theory (e/d (fn-auth-tls-established fn-auth-effectsp)
                                  nil))))

(defthm fn-auth-command-effects-well-formed
  (implies (fn-auth-command as config keyword args)
           (fn-auth-effectsp (fn-post-result-effects
                              (fn-auth-command as config keyword args))))
  :hints (("Goal" :in-theory (e/d (fn-auth-command)
                                  (fn-auth-single fn-auth-authinfo
                                   fn-auth-starttls fn-auth-gatedp
                                   fn-nntp-effectsp fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-multi
                                   fn-auth-capability-lines-for-peer
                                   fn-auth-peer-record
                                   fn-inj-config-allow
                                   fn-auth-postingp))
           :use ((:instance fn-nntp-effects-multi
                            (session (fn-auth-reader-session as))
                            (initial "101 capability list follows")
                            (lines (fn-auth-capability-lines-for-peer
                                    (fn-auth-session-config as)
                                    (fn-auth-session-subject as)
                                    (fn-auth-session-tlsp as)
                                    (and (fn-inj-config-allow config)
                                         (fn-auth-postingp as))
                                    (fn-auth-peer-record as))))))))

(defthm fn-auth-step-effects-well-formed
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-effectsp
            (fn-post-result-effects
             (fn-auth-step as archive config observation injection
                           wire-event))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-delegate
                                   fn-auth-session-consistentp)
                                  (fn-auth-command fn-peer-step
                                   fn-auth-sessionp fn-nntp-effectsp
                                   fn-auth-single fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-keyword-tokenp
                                   fn-auth-tls-eventp fn-auth-tls-established
                                   fn-nntp-command-arguments-at-mostp
                                   fn-peer-session-consistentp)))))

; One preservation lemma per transition, each opening the recognizer over
; that transition's branches ALONE, then the step lifted with the recognizer
; closed (docs/proof-style.md, "Never open a recognizer to prove a property
; of a transition").  Opened over the whole step the same proof costs more
; than 2,000,000 prover steps across 182 subgoals and does not close.

; The two facts about fn-auth-principal-match that a consistency proof reads:
; a match is a name, and a match was read out of a checked configuration.
; With them the match stays closed, instead of opening the row count, the
; name scan and the record lookup under every branch of AUTHINFO.
(local (defthm fn-auth-principal-match-is-a-string
  (or (null (fn-auth-principal-match principal cfg))
      (stringp (fn-auth-principal-match principal cfg)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-auth-principal-match)
                                  (fn-cfg-peer-find fn-digest-hex fn-cfgp))))))

(local (defthm fn-auth-principal-match-means-a-configuration
  (implies (fn-auth-principal-match principal cfg)
           (fn-cfgp cfg))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-principal-match)
                                  (fn-cfg-peer-find fn-digest-hex fn-cfgp))))))

(local (defthm fn-auth-authinfo-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-authinfo as args)) archive))
  ; The POST and NNTP session recognizers stay closed too: AUTHINFO's
  ; promotion branch builds a peer session, and the constructor rules
  ; books/peer-inbound.lisp exports for it reduce that to the consistency of
  ; the POST base this session already carried.  Opened, that base's
  ; recognizer unfolds into a `true-listp' obligation on the NNTP session
  ; instead (hbox certify-20260922T084314Z-2803863).
  :hints (("Goal"
           :in-theory (e/d (fn-auth-authinfo fn-auth-session-consistentp
                            fn-auth-sessionp)
                           (fn-peer-sessionp fn-peer-session-consistentp
                            fn-post-sessionp fn-post-session-consistentp
                            fn-nntp-sessionp fn-nntp-session-consistentp
                            fn-auth-configp fn-auth-single fn-nntp-single
                            fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-printable-tokenp fn-prin-idp
                            fn-auth-principal-match))))))

(local (defthm fn-auth-starttls-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-starttls as args)) archive))
  ; The POST and NNTP session recognizers stay closed, as they do for
  ; AUTHINFO above: STARTTLS drops a principal-derived peer role back to the
  ; configured reader shape, and the constructor rules books/peer-inbound.lisp
  ; exports carry it.
  :hints (("Goal"
           :in-theory (e/d (fn-auth-starttls fn-auth-session-consistentp
                            fn-auth-sessionp)
                           (fn-peer-sessionp fn-peer-session-consistentp
                            fn-post-sessionp fn-post-session-consistentp
                            fn-nntp-sessionp fn-nntp-session-consistentp
                            fn-auth-configp fn-auth-single fn-nntp-single
                            fn-nntp-printable-tokenp fn-prin-idp))))))

(local (defthm fn-auth-tls-established-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-tls-established as)) archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-tls-established
                            fn-auth-session-consistentp fn-auth-sessionp)
                           (fn-peer-sessionp fn-peer-session-consistentp
                            fn-auth-configp fn-nntp-printable-tokenp
                            fn-prin-idp))))))

(local (defthm fn-auth-command-preserves-consistentp
  (implies (and (fn-auth-session-consistentp as archive)
                (fn-auth-command as config keyword args))
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-command as config keyword args))
            archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-command)
                           (fn-auth-authinfo fn-auth-starttls fn-auth-single
                            fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                            fn-nntp-keyword-tokenp fn-nntp-multi
                            fn-auth-capability-lines
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-inj-config-allow
                            fn-auth-sessionp fn-auth-session-consistentp))))))

(local (defthm fn-auth-delegate-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session
             (fn-auth-delegate as archive config observation injection
                               wire-event))
            archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-delegate fn-auth-with-base
                            fn-auth-session-consistentp fn-auth-sessionp)
                           (fn-peer-step fn-peer-sessionp
                            fn-peer-session-consistentp fn-auth-configp
                            ; else the :use hypothesis is rewritten to T by
                            ; this very rule and says nothing
                            fn-peer-step-preserves-consistent-session
                            fn-nntp-printable-tokenp fn-prin-idp))
           :use ((:instance fn-peer-step-preserves-consistent-session
                            (ps (fn-auth-session-base as))))))))

(defthm fn-auth-step-preserves-consistent-session
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session
             (fn-auth-step as archive config observation injection wire-event))
            archive))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step)
                           (fn-peer-step fn-auth-delegate fn-auth-command
                            fn-auth-tls-established fn-auth-tls-eventp
                            fn-auth-sessionp fn-auth-session-consistentp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp fn-nntp-tokenize
                            fn-nntp-command-arguments-at-mostp)))))

; KEYSTONE.  The operator's policy is pinned, and the step never moves it.
;
; books/served.lisp fn-served-open and fn-served-open-peer pin the
; operator's AUTHINFO configuration into the session at OPEN, and
; fn-served-peer-and-reader-open-under-the-same-policy (PRF-039) says both
; entries pin the same value.  That is a statement about one transition;
; what makes it a statement about the connection is this one, which says
; the field those theorems are about is not written by any branch of the
; step: not by a login, not by the handshake, not by a delegated reader
; command, and not by a command this book does not answer.  Every decision
; in this book -- the credential fn-auth-authinfo searches, the two
; capability labels, the 480 gate and the posting allowance -- reads that
; field, so with it fixed the policy a client meets on its hundredth
; command is the one the operator configured before the connection opened.
;
; No hypothesis: the non-session branch returns its argument, so it holds
; there too.  books/nntp-auth-invariants.lisp asked for this by name as the
; first of the three facts OB-AUTH-FOLD (K2) waits on; the other two are a
; wire lemma and a reader lemma in books that this one does not own.

; The config field one transition at a time.  Opened over the whole step
; with every arm open, the keystone below split 180 ways on the AUTHINFO,
; STARTTLS and binding arms together (2.4 s in the certify log); each arm
; rebuilds the session from the config it was given, and that is the fact.
(local (defthm fn-auth-authinfo-keeps-the-config
  (equal (fn-auth-session-config
          (fn-post-result-session (fn-auth-authinfo as args)))
         (fn-auth-session-config as))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                                   fn-auth-with-base)
                                  (fn-auth-single fn-auth-find-cred fn-auth-checkp
                                   fn-auth-token-argp fn-nntp-keywordp
                                   fn-auth-principal-match fn-node-statep))))))

(local (defthm fn-auth-starttls-keeps-the-config
  (equal (fn-auth-session-config
          (fn-post-result-session (fn-auth-starttls as args)))
         (fn-auth-session-config as))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                                   fn-auth-with-base)
                                  (fn-auth-single fn-auth-principal-rolep))))))

(local (defthm fn-auth-command-keeps-the-config
  (implies (fn-auth-command as config keyword args)
           (equal (fn-auth-session-config
                   (fn-post-result-session
                    (fn-auth-command as config keyword args)))
                  (fn-auth-session-config as)))
  :hints (("Goal" :in-theory (e/d (fn-auth-command)
                                  (fn-auth-authinfo fn-auth-starttls fn-auth-single
                                   fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                                   fn-nntp-keyword-tokenp fn-nntp-multi
                                   fn-auth-capability-lines-for-peer
                                   fn-auth-peer-record fn-inj-config-allow))))))

(local (defthm fn-auth-delegate-keeps-the-config
  (equal (fn-auth-session-config
          (fn-post-result-session
           (fn-auth-delegate as archive config observation injection
                             wire-event)))
         (fn-auth-session-config as))
  :hints (("Goal" :in-theory (e/d (fn-auth-delegate fn-auth-with-base)
                                  (fn-peer-step))))))

(defthm fn-auth-step-preserves-the-config
  (equal (fn-auth-session-config
          (fn-post-result-session
           (fn-auth-step as archive config observation injection wire-event)))
         (fn-auth-session-config as))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-tls-eventp
                            fn-auth-tls-established)
                           (fn-peer-step fn-auth-command fn-auth-delegate
                            fn-auth-sessionp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp)))))

; The third fact the fold needs: a submission that leaves this step is the
; one fn-peer-step produced, so books/peer-inbound.lisp's
; fn-peer-step-submission-is-typed is the whole of its typing.  Only the
; delegate branch has a submission at all: every branch this book answers
; builds its result with a NIL third field.

; No branch this book answers has a submission, one arm at a time, so the
; theorem below reads the step's dispatch with fn-auth-command closed instead
; of opening all of its arms (221-way split, 2.2 s in the certify log).
(local (defthm fn-auth-authinfo-has-no-submission
  (not (fn-post-result-submission (fn-auth-authinfo as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer)
                                  (fn-auth-single fn-auth-find-cred fn-auth-checkp
                                   fn-auth-token-argp fn-nntp-keywordp
                                   fn-auth-principal-match fn-node-statep))))))

(local (defthm fn-auth-starttls-has-no-submission
  (not (fn-post-result-submission (fn-auth-starttls as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls)
                                  (fn-auth-single fn-auth-clear-principal-peer))))))

(local (defthm fn-auth-command-has-no-submission
  (not (fn-post-result-submission (fn-auth-command as config keyword args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-command)
                                  (fn-auth-authinfo fn-auth-starttls fn-auth-single
                                   fn-auth-gatedp fn-auth-postingp fn-nntp-keywordp
                                   fn-nntp-keyword-tokenp fn-nntp-multi
                                   fn-auth-capability-lines-for-peer
                                   fn-auth-peer-record fn-inj-config-allow))))))

(defthm fn-auth-submission-is-the-delegated-submission
  (implies (fn-post-result-submission
            (fn-auth-step as archive config observation injection wire-event))
           (equal (fn-post-result-submission
                   (fn-auth-step as archive config observation injection
                                 wire-event))
                  (fn-post-result-submission
                   (fn-peer-step (fn-auth-session-base as) archive config
                                 observation injection wire-event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-delegate
                                   fn-auth-tls-established)
                                  (fn-peer-step fn-auth-command
                                   fn-auth-sessionp fn-nntp-tokenize
                                   fn-nntp-command-inputp
                                   fn-auth-tls-eventp
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp)))))

; KEYSTONE.  The outer auth dispatcher is transparent for the three inbound
; transit verbs.  The peer step is therefore the sole authorization decision:
; a configured peer's pinned record reaches its offer logic, and a reader
; connection reaches its own not-permitted refusal.  In particular no
; AUTHINFO subject is a hypothesis of this equality.
(defthm fn-auth-step-transit-command-delegates-to-peer
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-transit-keywordp
                 (car (fn-nntp-tokenize line))))
           (equal (fn-auth-step as archive config observation injection
                                (list :command line))
                  (fn-auth-delegate as archive config observation injection
                                    (list :command line))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-transit-keywordp fn-nntp-keywordp)
                           (fn-auth-delegate fn-peer-step fn-auth-sessionp
                            fn-auth-transit-keyword-is-not-reader-restricted
                            fn-auth-restricted-keywordp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-transit-keyword-is-not-reader-restricted
                            (keyword (car (fn-nntp-tokenize line))))))))

(defthm fn-auth-step-submission-is-typed
  (implies (and (fn-auth-sessionp as)
                (fn-post-result-submission
                 (fn-auth-step as archive config observation injection
                               wire-event)))
           (or (fn-inj-injectedp
                (fn-post-result-submission
                 (fn-auth-step as archive config observation injection
                               wire-event)))
               (fn-peer-submissionp
                (fn-post-result-submission
                 (fn-auth-step as archive config observation injection
                               wire-event)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-sessionp)
                           (fn-auth-step fn-peer-step fn-peer-sessionp
                            fn-inj-injectedp fn-peer-submissionp
                            ; fn-auth-submission-is-the-delegated-submission
                            ; is :rule-classes nil and names no rune
                            fn-peer-step-submission-is-typed))
           :use ((:instance fn-auth-submission-is-the-delegated-submission)
                 (:instance fn-peer-step-submission-is-typed
                            (ps (fn-auth-session-base as))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; A restricted keyword is a keyword token, and so is every token this book
; compares against a keyword.
;
; This pair exists because of the teeth.  The keystone below used to carry
; `(consp (fn-nntp-tokenize line))' and
; `(fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))' beside
; `fn-auth-restricted-keywordp' of the same token, and neither can be
; violated while the third holds: `fn-auth-restricted-keywordp' is a
; disjunction of `fn-nntp-keywordp' against ground keyword texts, and
; `fn-nntp-keywordp' is one `equal' between the token's upcasing and those
; octets.  A hypothesis no value can violate has no `must-fail' case
; (AGENTS.md, teeth), so it is removed and the reason is proved here rather
; than asserted in a comment.
;
; The work is one direction of `fn-nntp-upcase-keyword': upcasing maps
; 97..122 onto 65..90 and fixes everything else, so an upcased token that is
; a keyword token came from a keyword token.

(local (defthm fn-auth-upcase-keeps-a-rest-byte
  (implies (fn-nntp-keyword-rest-bytep (fn-nntp-upcase-byte b))
           (fn-nntp-keyword-rest-bytep b))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-rest-bytep
                                     fn-nntp-keyword-first-bytep
                                     fn-nntp-upcase-byte)))))

(local (defthm fn-auth-upcase-keyword-is-consp-exactly-when-its-argument-is
  (equal (consp (fn-nntp-upcase-keyword x)) (consp x))
  :hints (("Goal" :in-theory (enable fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-upcase-keeps-a-keyword-tail
  (implies (fn-nntp-keyword-tailp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tailp x))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tailp
                                     fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-upcase-keeps-a-keyword-token
  (implies (fn-nntp-keyword-tokenp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tokenp x))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-first-bytep
                                   fn-nntp-upcase-byte)
                                  (fn-nntp-keyword-tailp))))))

(local (defthm fn-auth-keyword-match-is-a-keyword-token
  (implies (and (fn-nntp-keywordp keyword text)
                (fn-nntp-keyword-tokenp (fn-nntp-string-octets text)))
           (fn-nntp-keyword-tokenp keyword))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-string-octets))
           :use ((:instance fn-auth-upcase-keeps-a-keyword-token
                            (x keyword)))))))

; Exported: every keyword the reader gate refuses is a keyword token, so the
; two syntactic hypotheses the keystone used to carry are consequences of
; its last one.  Each of the eighteen texts is a ground keyword token, which
; the prover checks by evaluation.
(defthm fn-auth-restricted-keyword-is-a-keyword-token
  (implies (fn-auth-restricted-keywordp keyword)
           (fn-nntp-keyword-tokenp keyword))
  :hints (("Goal" :in-theory (e/d (fn-auth-restricted-keywordp)
                                  (fn-nntp-keywordp fn-nntp-keyword-tokenp)))))

(local (defthm fn-auth-a-keyword-token-car-has-a-cons
  (implies (fn-nntp-keyword-tokenp (car x)) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tokenp)))))

; -----------------------------------------------------------------------------
; KEYSTONE.  No restricted command runs unauthenticated when the
; configuration requires authentication.
;
; RFC 4643 section 2.2: a 480 response says the command was NOT performed.
; The three conjuncts are what "not performed" means on this path: nothing
; was submitted for durable acceptance, the wire was not put into article
; mode (so no body can follow), and the session is the one the command
; arrived on -- no cursor moved, no group was selected, nothing was cached.
;
; Seven hypotheses, and each one has a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.

(defthm fn-auth-gated-command-is-refused-and-not-performed
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-auth-config-requiredp (fn-auth-session-config as))
                (not (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
           (and (null (fn-post-result-submission
                       (fn-auth-step as archive config observation injection
                                     (list :command line))))
                (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-step as archive config observation injection
                                     (list :command line)))))
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       as)
                (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       (fn-auth-single as "480 authentication required"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-tls-eventp fn-post-offeredp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-restricted-keywordp fn-auth-sessionp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-nntp-begin-article-effect)))))

; -----------------------------------------------------------------------------
; KEYSTONE.  POST is never offered to a connection whose posting allowance
; is false, whatever the pinned injection configuration says.
;
; This is the half of the authorization the 480 gate does not cover: an
; authenticated principal enrolled WITHOUT the posting flag passes the gate
; and must still be refused.  "Not offered" is the load-bearing conjunct:
; fn-served-dispatch switches the wire into article mode on exactly the
; begin-article effect (books/served.lisp), so no offer is no body, and no
; body is no submission.  fn-auth-postingp is false for both reasons at
; once -- gated or unflagged -- so this theorem covers the gate's POST case
; as well and the two are not independent claims.

(defthm fn-auth-post-without-permission-is-not-offered
  (implies (and (not (fn-auth-postingp as))
                (fn-nntp-keywordp keyword "POST"))
           (and (fn-auth-command as config keyword args)
                (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-command as config keyword args))))
                (null (fn-post-result-submission
                       (fn-auth-command as config keyword args)))
                (equal (fn-post-result-session
                        (fn-auth-command as config keyword args))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-post-offeredp)
                           (fn-auth-single fn-auth-authinfo fn-auth-starttls
                            fn-auth-postingp fn-nntp-keywordp
                            fn-nntp-keyword-tokenp fn-nntp-multi
                            fn-auth-capability-lines fn-inj-config-allow
                            fn-nntp-begin-article-effect)))))

(defthm fn-auth-step-post-without-permission-is-not-offered
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-postingp as))
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))
           (and (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-step as archive config observation injection
                                     (list :command line)))))
                (null (fn-post-result-submission
                       (fn-auth-step as archive config observation injection
                                     (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-tls-eventp)
                           (fn-peer-step fn-auth-delegate fn-auth-command
                            fn-auth-sessionp fn-auth-postingp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-post-offeredp
                            fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-post-without-permission-is-not-offered
                            (keyword (car (fn-nntp-tokenize line)))
                            (args (cdr (fn-nntp-tokenize line))))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  The two capability labels appear exactly where their RFCs allow,
; on every connection and not only on a reader's.
;
; RFC 4642 section 2.1: "MUST NOT be advertised once a TLS layer is active".
; RFC 4643 section 2.1: the AUTHINFO arguments are what the server will
; accept now, and after a 281 it will accept nothing.
;
; The subject is fn-auth-capability-lines-for-peer, because that is the
; function fn-auth-command calls for the 101 block (the CAPABILITIES arm
; below, and fn-auth-step-capability-block-unfolds-to-the-peer-aware-lines
; names that equality).  fn-auth-capability-lines is its `record' = nil
; instance and the reader-facing pair beneath each keystone is exactly that
; instance: stating the keystone over the reader entry alone would have left
; a client the owner resolved to a peer record -- which on one box is every
; client (PRF-039) -- outside the claim.

(defthm fn-auth-starttls-is-not-advertised-under-tls-on-any-connection
  (implies tlsp
           (not (member-equal (fn-nntp-string-octets "STARTTLS")
                              (fn-auth-capability-lines-for-peer
                               acfg subject tlsp postingp record))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines-for-peer
                                   fn-auth-access-capability-lines
                                   fn-peer-capability-lines
                                   fn-nntp-capability-lines)
                                  (fn-auth-config-tls-availablep
                                   fn-auth-config-protected-onlyp
                                   fn-auth-config-creds
                                   fn-cfg-peer-inbound)))))

(defthm fn-auth-starttls-is-not-advertised-under-tls
  (implies tlsp
           (not (member-equal (fn-nntp-string-octets "STARTTLS")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines) nil))))

(defthm fn-auth-authinfo-is-not-advertised-once-authenticated-on-any-connection
  (implies subject
           (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                              (fn-auth-capability-lines-for-peer
                               acfg subject tlsp postingp record))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines-for-peer
                                   fn-auth-access-capability-lines
                                   fn-peer-capability-lines
                                   fn-nntp-capability-lines)
                                  (fn-auth-config-tls-availablep
                                   fn-auth-config-protected-onlyp
                                   fn-auth-config-creds
                                   fn-cfg-peer-inbound)))))

(defthm fn-auth-authinfo-is-not-advertised-once-authenticated
  (implies subject
           (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines) nil))))

; The other half of protected-only, on the label rather than on the command:
; while the channel is the one section 2.3.2 refuses a cleartext mechanism
; on, the mechanism is not offered either, so a client is never invited to
; send a secret that would be answered 483.
(defthm fn-auth-authinfo-is-not-advertised-before-tls-under-protected-only
  (implies (and (fn-auth-config-protected-onlyp acfg) (not tlsp))
           (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                              (fn-auth-capability-lines-for-peer
                               acfg subject tlsp postingp record))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines-for-peer
                                   fn-auth-access-capability-lines
                                   fn-peer-capability-lines
                                   fn-nntp-capability-lines)
                                  (fn-auth-config-tls-availablep
                                   fn-auth-config-creds
                                   fn-cfg-peer-inbound)))))

(defthm fn-auth-starttls-is-not-advertised-without-a-certificate
  (implies (not (fn-auth-config-tls-availablep acfg))
           (not (member-equal (fn-nntp-string-octets "STARTTLS")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-auth-capability-lines-for-peer
                                   fn-auth-access-capability-lines
                                   fn-peer-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

; The block the step emits is that list, and this equality is what makes the
; three keystones above claims about what a client sees rather than about a
; helper beside it (AGENTS.md: the theorem subject is the function the host
; calls).  It is an unfold of fn-auth-step and fn-auth-command on the
; CAPABILITIES arm and does no work of its own; it is named for that.
(defthm fn-auth-step-capability-block-unfolds-to-the-peer-aware-lines
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "CAPABILITIES")
                (null (cdr (fn-nntp-tokenize line))))
           (equal (fn-post-result-effects
                   (fn-auth-step as archive config observation injection
                                 (list :command line)))
                  (fn-nntp-result-effects
                   (fn-nntp-multi (fn-auth-reader-session as)
                                  "101 capability list follows"
                                  (fn-auth-capability-lines-for-peer
                                   (fn-auth-session-config as)
                                   (fn-auth-session-subject as)
                                   (fn-auth-session-tlsp as)
                                   (and (fn-inj-config-allow config)
                                        (fn-auth-postingp as))
                                   (fn-auth-peer-record as))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-tls-eventp fn-auth-restricted-keywordp
                            fn-nntp-keywordp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-postingp
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record
                            fn-nntp-multi fn-inj-config-allow
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp)))))

; -----------------------------------------------------------------------------
; KEYSTONE.  382 is emitted at most once per connection, from the one branch
; that also puts the session into the handshake, and the handshake is the
; only way a TLS layer is recorded.

(defthm fn-auth-starttls-effect-only-with-382
  (implies (member-equal (fn-auth-starttls-effect)
                         (fn-post-result-effects (fn-auth-starttls as args)))
           (and (null args)
                (not (fn-auth-session-tlsp as))
                (fn-auth-config-tls-availablep (fn-auth-session-config as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session (fn-auth-starttls as args)))
                (not (fn-auth-session-tlsp
                      (fn-post-result-session (fn-auth-starttls as args))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls fn-auth-starttls-effect)
                                  (fn-nntp-single fn-auth-single))))
  :rule-classes nil)

(defthm fn-auth-second-starttls-is-refused
  (implies (fn-auth-session-tlsp as)
           (and (equal (fn-post-result-effects (fn-auth-starttls as nil))
                       (fn-auth-single as "502 a TLS layer is already active"))
                (not (member-equal (fn-auth-starttls-effect)
                                   (fn-post-result-effects
                                    (fn-auth-starttls as nil))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls fn-auth-starttls-effect)
                                  (fn-nntp-single fn-auth-single)))))

; A handshaking connection answers nothing at all: no reply, no submission,
; no change of session.  With the fold's stopping condition
; (fn-served-tls-handshakingp, books/served.lisp) this is what makes the
; octets behind a STARTTLS command line handshake bytes rather than NNTP,
; which is RFC 4642 section 2.2's "MUST NOT be pipelined".

(defthm fn-auth-handshaking-session-serves-nothing
  (implies (and (fn-auth-sessionp as)
                (fn-auth-session-handshakingp as)
                (not (fn-auth-tls-eventp wire-event)))
           (and (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      wire-event))
                       nil)
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event))
                       as)
                (null (fn-post-result-submission
                       (fn-auth-step as archive config observation injection
                                     wire-event)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step)
                                  (fn-peer-step fn-auth-delegate
                                   fn-auth-command fn-auth-sessionp
                                   fn-auth-tls-eventp fn-auth-tls-established
                                   fn-nntp-tokenize fn-nntp-command-inputp
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp)))))

; The one transition that records a TLS layer, and it is the host's re-entry
; after the handshake: no client octet reaches it, because it is a wire
; event and fn-nntp-tokenize never produces one.

(defthm fn-auth-tls-established-sets-the-layer
  (implies (fn-auth-sessionp as)
           (and (fn-auth-session-tlsp
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                (list :tls-established))))
                (not (fn-auth-session-handshakingp
                      (fn-post-result-session
                       (fn-auth-step as archive config observation injection
                                     (list :tls-established)))))
                (null (fn-post-result-effects
                       (fn-auth-step as archive config observation injection
                                     (list :tls-established))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-tls-eventp
                                   fn-auth-tls-established)
                                  (fn-auth-sessionp fn-peer-step
                                   fn-auth-delegate fn-auth-command)))))

; -----------------------------------------------------------------------------
; KEYSTONE.  AUTHINFO PASS accepts only octets that check against the stored
; verifier, and only after a cached AUTHINFO USER.
;
; The comparison is books/auth-secret.lisp's fn-authsec-checkp and this
; theorem says the accepting branch ran it: it does NOT say a wrong secret
; fails, which is second-preimage resistance of the attached SHA-256
; (A-CRYPTO, specs/failures.md) and is exhibited by witness in the test book.

(defthm fn-auth-pass-accepts-only-a-checking-secret
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-auth-token-argp (list secret))
                (fn-nntp-keywordp keyword "PASS")
                (fn-auth-session-subject
                 (fn-post-result-session
                  (fn-auth-authinfo as (list keyword secret)))))
           (and (fn-auth-session-pending as)
                (fn-authsec-checkp
                 (fn-auth-cred-secret
                  (fn-auth-find-cred (fn-auth-session-pending as)
                                     (fn-auth-config-creds
                                      (fn-auth-session-config as))))
                 secret)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-checkp)
                           (fn-auth-single fn-auth-find-cred
                            fn-authsec-checkp
                            fn-auth-token-argp fn-auth-sessionp
                            fn-nntp-keywordp fn-nntp-single))))
  :rule-classes nil)

; A failed PASS leaves the connection unauthenticated AND uncached, so it
; cannot be retried without a fresh USER (RFC 4643 section 2.3.2).

(defthm fn-auth-failed-pass-leaves-the-session-unauthenticated
  (implies (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-auth-token-argp (list secret))
                (fn-nntp-keywordp keyword "PASS")
                (fn-auth-session-pending as)
                (not (fn-auth-checkp
                      (fn-auth-find-cred (fn-auth-session-pending as)
                                         (fn-auth-config-creds
                                          (fn-auth-session-config as)))
                      secret)))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session
                        (fn-auth-authinfo as (list keyword secret)))))
                (null (fn-auth-session-pending
                       (fn-post-result-session
                        (fn-auth-authinfo as (list keyword secret)))))
                (equal (fn-post-result-effects
                        (fn-auth-authinfo as (list keyword secret)))
                       (fn-auth-single as "481 authentication failed"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-auth-sessionp
                            fn-nntp-keywordp fn-nntp-single))))
  :rule-classes nil)

; AUTHINFO PASS before AUTHINFO USER is 482 and changes nothing
; (RFC 4643 section 2.3.2: "MUST give a 482 response ... if there is no
; cached username").

(defthm fn-auth-pass-before-user-is-482
  (implies (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-auth-token-argp (list secret))
                (fn-nntp-keywordp keyword "PASS")
                (not (fn-auth-session-pending as)))
           (and (equal (fn-post-result-effects
                        (fn-auth-authinfo as (list keyword secret)))
                       (fn-auth-single
                        as
                        "482 authentication commands issued out of sequence"))
                (equal (fn-post-result-session
                        (fn-auth-authinfo as (list keyword secret)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single)))))

; RFC 4643 section 2.3.2: a cleartext mechanism on an unprotected connection
; is 483 and the credentials are never even looked at.

(defthm fn-auth-protected-only-refuses-authinfo-before-tls
  (implies (and (not (fn-auth-session-subject as))
                (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                (not (fn-auth-session-tlsp as)))
           (and (equal (fn-post-result-effects (fn-auth-authinfo as args))
                       (fn-auth-single
                        as
                        "483 a protected channel is required; use STARTTLS"))
                (equal (fn-post-result-session (fn-auth-authinfo as args)) as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single)))))

; No branch of AUTHINFO submits anything; it is the fact the lift below needs
; for its "and not performed" conjunct, and it is stated as `not' rather
; than `null' so the rule survives the prover's normalization of
; (equal x nil) into (not x).
(defthm fn-auth-authinfo-carries-no-submission
  (not (fn-post-result-submission (fn-auth-authinfo as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo)
                                  (fn-auth-single fn-auth-find-cred
                                   fn-auth-checkp fn-auth-token-argp
                                   fn-nntp-keywordp fn-nntp-single)))))

; KEYSTONE.  The 483 over the function the served path calls.
;
; The theorem above is about fn-auth-authinfo, which no host line calls.
; books/served.lisp fn-served-dispatch calls fn-auth-step, and
; host/owner-host.lisp fn-owner-chunk reaches it through fn-own-read and
; fn-served-step (the native host's socket read is host/native/owner.lisp
; fnn-owner-read-chunk over the same entry).  This lift says it of that
; subject: while the operator's policy is protected-only and the connection
; carries no TLS layer, an AUTHINFO command line -- USER or PASS, with any
; arguments, known name or not -- is answered with RFC 4643 section 2.3.2's
; 483 and nothing else happens: the session is the one the command arrived
; on, so no name is cached and no subject is installed, and no submission
; leaves.  The secret is never compared, because the branch that would
; compare it is not reached.
;
; It is stated for the whole AUTHINFO keyword rather than for PASS alone
; because USER is where a client would otherwise be told 381 and send the
; secret next.
;
; Eight hypotheses, and each one has a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.  `fn-nntp-keyword-tokenp' of the
; same token is not among them, for the reason the gate keystone above gives:
; the AUTHINFO match already forces it.

(defthm fn-auth-step-protected-only-refuses-authinfo-before-tls
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-session-subject as))
                (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                (not (fn-auth-session-tlsp as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
           (and (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       (fn-auth-single
                        as
                        "483 a protected channel is required; use STARTTLS"))
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       as)
                (null (fn-post-result-submission
                       (fn-auth-step as archive config observation injection
                                     (list :command line))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-tls-eventp fn-auth-restricted-keywordp
                            fn-nntp-keywordp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-protected-only-refuses-authinfo-before-tls
                            (args (cdr (fn-nntp-tokenize line))))))))

; -----------------------------------------------------------------------------
; THE PEER ROLE A LOGIN BINDS (PRF-049).
;
; A connection the owner opens through fn-ocfg-open (host/owner-host.lisp
; fn-owner-open) is a reader; books/owner-config.lisp
; fn-ocfg-open-begins-unbound says so of every open, whatever the owner's
; other connections have done.  The only transition that gives a reader a
; peer role is AUTHINFO PASS, and only for a principal the pinned
; configuration binds to exactly one peer record (fn-auth-principal-match).
; Three keystones over fn-auth-step, the function books/served.lisp
; fn-served-dispatch calls and host/owner-host.lisp fn-owner-chunk reaches
; through fn-own-read and fn-served-step:
;
;   fn-auth-step-binds-a-peer-role-only-by-a-principal-login   (only way in)
;   fn-auth-step-principal-login-binds-exactly-the-unique-match (the way in)
;   fn-auth-step-starttls-clears-a-principal-role               (the way out)
;
; Protected-only is not restated here: fn-auth-step-protected-only-refuses-
; authinfo-before-tls (PRF-031) says the session is unchanged by any AUTHINFO
; before TLS, and the first keystone's fourth conjunct says the same thing
; from the other side -- no step whatever binds a role on a cleartext
; connection under that policy.

; The peer half of fn-peer-step never moves the peer name: every branch
; rebuilds the session with fn-peer-with-base or fn-peer-with-transfer.
(local (defthm fn-auth-peer-step-keeps-the-peer
  (equal (fn-peer-session-peer
          (fn-post-result-session
           (fn-peer-step ps archive config observation injection wire-event)))
         (fn-peer-session-peer ps))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-peer-step fn-peer-command fn-peer-delegate
                            fn-peer-with-base fn-peer-with-transfer)
                           (fn-nntp-post-step fn-peer-sessionp
                            fn-peer-decide-offer fn-peer-single
                            fn-peer-echo-reply fn-peer-msgid-argp
                            fn-peer-capability-lines fn-peer-check-code
                            fn-peer-ihave-offer-line
                            fn-nntp-multi fn-nntp-keywordp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp))))))

(local (defthm fn-auth-authinfo-binds-only-on-an-accepted-pass
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-authinfo as args))))
           (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-keywordp (car args) "PASS")
                (fn-auth-token-argp (cdr args))
                (fn-auth-session-pending as)
                (fn-auth-checkp (fn-auth-find-cred
                                 (fn-auth-session-pending as)
                                 (fn-auth-config-creds
                                  (fn-auth-session-config as)))
                                (car (cdr args)))
                (equal (fn-auth-session-subject
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))
                (fn-auth-principal-rolep
                 (fn-post-result-session (fn-auth-authinfo as args)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-cfg-peer-find fn-cfgp
                            
                            fn-digest-hex
                            fn-node-statep))))))

(local (defthm fn-auth-configured-session-has-a-node
  (implies (and (fn-peer-sessionp x)
                (fn-cfgp (fn-peer-session-cfg x)))
           (fn-node-statep (fn-peer-session-node x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

(local (defthm fn-auth-authinfo-accepted-pass-binds-the-match
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-peer as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-keywordp (car args) "PASS")
                (fn-auth-token-argp (cdr args))
                (fn-auth-session-pending as)
                (fn-auth-checkp (fn-auth-find-cred
                                 (fn-auth-session-pending as)
                                 (fn-auth-config-creds
                                  (fn-auth-session-config as)))
                                (car (cdr args))))
           (and (equal (fn-post-result-effects (fn-auth-authinfo as args))
                       (fn-auth-single as "281 authentication accepted"))
                (equal (fn-auth-session-subject
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))))
  :hints (("Goal"
           :do-not-induct t
           ; The match stays closed: the conclusion names it, and the node
           ; the binding tests comes from the configuration a match was
           ; read out of (fn-auth-principal-match-means-a-configuration).
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-sessionp)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-cfg-peer-find fn-cfgp
                            fn-auth-principal-match
                            fn-digest-hex fn-peer-sessionp fn-auth-configp
                            fn-nntp-printable-tokenp fn-prin-idp
                            fn-node-statep))))))

(local (defthm fn-auth-starttls-handshake-clears-a-principal-role
  (implies (and (not (fn-auth-session-handshakingp as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session (fn-auth-starttls as args))))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session (fn-auth-starttls as args))))
                (null (fn-auth-session-pending
                       (fn-post-result-session (fn-auth-starttls as args))))
                (not (fn-auth-principal-rolep
                      (fn-post-result-session (fn-auth-starttls as args))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-starttls as args)))
                       (if (fn-auth-principal-rolep as)
                           nil
                         (fn-auth-session-peer as)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep)
                           (fn-auth-single fn-nntp-single fn-cfg-peer-find
                            fn-cfgp))))))

(local (defthm fn-auth-starttls-keeps-a-reader
  (implies (not (fn-auth-session-peer as))
           (not (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-starttls as args)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep)
                           (fn-auth-single fn-nntp-single fn-cfg-peer-find
                            fn-cfgp))))))

(local (defthm fn-auth-delegate-keeps-the-role-and-the-handshake
  (and (equal (fn-auth-session-peer
               (fn-post-result-session
                (fn-auth-delegate as archive config observation injection
                                  wire-event)))
              (fn-auth-session-peer as))
       (equal (fn-auth-session-handshakingp
               (fn-post-result-session
                (fn-auth-delegate as archive config observation injection
                                  wire-event)))
              (fn-auth-session-handshakingp as)))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-delegate fn-auth-with-base
                            fn-auth-session-peer)
                           (fn-peer-step))))))

(local (defthm fn-auth-authinfo-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-authinfo as args)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-auth-principal-match
                            fn-node-statep))))))

(local (defthmd fn-auth-session-peer-folds
  (equal (fn-peer-session-peer (fn-auth-session-base as))
         (fn-auth-session-peer as))))


; KEYSTONE.  The only way a reader becomes a peer.
;
; No hypothesis about the session or the event beyond the role change
; itself: for ANY session and ANY wire event, if the step's session has a
; peer role and the session it was given had none, then the event was an
; AUTHINFO PASS command line, sent on a well-formed, non-handshaking,
; unauthenticated connection whose channel the policy accepts, after a
; USER, whose one-token secret checks against the cached name's stored
; verifier; the step installed that credential's principal as the subject;
; the role it bound is fn-auth-principal-match of that principal under the
; configuration pinned into the connection -- the one peer whose record says
; (:principal HEX) and the only auth-principal row naming HEX -- and the role
; is principal-derived, so the next keystone's STARTTLS clears it.
;
; Consequences read straight off it: a principal with no matching row
; (mismatch) or two (duplicate) never gains a role on any step, since the
; match is then nil; a protected-only connection without TLS never gains
; one; a delegated reader command, a CAPABILITIES, a USER, a failed PASS, a
; STARTTLS and the handshake re-entry never do.
;
; Two hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-binds-a-peer-role-only-by-a-principal-login
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event))))
           (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (equal (car wire-event) :command)
                (fn-nntp-keywordp (car (fn-nntp-tokenize (cadr wire-event)))
                                  "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize (cadr wire-event)))
                                  "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize (cadr wire-event))))
                (fn-auth-session-pending as)
                (fn-auth-checkp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as)))
                 (caddr (fn-nntp-tokenize (cadr wire-event))))
                (equal (fn-auth-session-subject
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))
                (fn-auth-principal-rolep
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp fn-auth-session-peer-folds
                            fn-auth-tls-established)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match
                            fn-auth-gatedp fn-auth-postingp
                            fn-auth-find-cred fn-auth-checkp
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-authinfo-binds-only-on-an-accepted-pass))
           :use ((:instance fn-auth-authinfo-binds-only-on-an-accepted-pass
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))))))

; The line-length fact the next keystone needs so that it does not carry
; `fn-nntp-command-arguments-at-mostp' as a hypothesis no value could
; violate: a command line inside RFC 3977 section 3.1's 510 octets that
; tokenizes to AUTHINFO PASS <one token> has a secret of at most 496
; octets, inside the 497-octet argument bound.  `fn-auth-token-span' counts
; each token with one separator; the tokenizer consumes at least that.
(local (defun fn-auth-token-span (toks)
  (if (consp toks)
      (+ 1 (len (car toks)) (fn-auth-token-span (cdr toks)))
    0)))

(local (defthm fn-auth-token-span-of-append
  (equal (fn-auth-token-span (append a b))
         (+ (fn-auth-token-span a) (fn-auth-token-span b)))))

(local (defthm fn-auth-token-span-of-rev
  (equal (fn-auth-token-span (rev a)) (fn-auth-token-span a))))

(local (defthm fn-auth-token-span-of-reverse
  (equal (fn-auth-token-span (reverse a)) (fn-auth-token-span a))))

(local (defthm fn-auth-tokenize-aux-span
  (<= (fn-auth-token-span (fn-nntp-tokenize-aux xs word-rev words-rev))
      (+ 1 (len xs) (len word-rev) (fn-auth-token-span words-rev)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nntp-tokenize-aux xs word-rev words-rev)
           :in-theory (enable fn-nntp-tokenize-aux)))))

(local (defthm fn-auth-tokenize-span
  (<= (fn-auth-token-span (fn-nntp-tokenize line)) (+ 1 (len line)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-tokenize)))))

(local (defthm fn-auth-len-of-upcase-keyword
  (equal (len (fn-nntp-upcase-keyword x)) (len x))
  :hints (("Goal" :in-theory (enable fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-keyword-len
  (implies (fn-nntp-keywordp k text)
           (equal (len k) (len (fn-nntp-string-octets text))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-upcase-keyword
                                   fn-auth-len-of-upcase-keyword))
           :use ((:instance fn-auth-len-of-upcase-keyword (x k)))))))

(local (defthm fn-auth-cbor-at-mostp-len
  (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local (defthmd fn-auth-pass-line-arguments-are-in-bounds
  (implies (and (fn-nntp-command-inputp line)
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize line)) "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize line))))
           (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-auth-tokenize-span))
           :expand ((fn-auth-token-span (fn-nntp-tokenize line))
                    (fn-auth-token-span (cdr (fn-nntp-tokenize line)))
                    (fn-auth-token-span (cddr (fn-nntp-tokenize line))))
           :in-theory (e/d (fn-nntp-command-arguments-at-mostp
                            fn-nntp-argument-tokens
                            fn-nntp-each-token-at-mostp
                            fn-nntp-command-inputp fn-auth-token-argp)
                           (fn-nntp-tokenize fn-nntp-keywordp
                            fn-auth-tokenize-span fn-nntp-command-linep
                            fn-nntp-contains-bomp fn-cbor-at-mostp
                            fn-nntp-printable-tokenp))))))

; KEYSTONE.  The way in: an accepted PASS binds exactly the unique match.
;
; On a reader connection that is well-formed, not handshaking,
; unauthenticated and whose channel the policy accepts, an AUTHINFO PASS
; line after a USER whose secret checks is answered 281, installs the
; credential's principal, and leaves the connection with the peer role
; fn-auth-principal-match computes: the configured peer when exactly one
; auth-principal row names the principal's digest and that peer's record
; says (:principal digest), and no role -- a reader, still authenticated --
; when there are none (mismatch) or several (duplicate).  RFC 4643 section
; 2.3.2's 281 is the same in every case: whether the login also names a
; peer is not disclosed on the wire.
;
; Eleven hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-principal-login-binds-exactly-the-unique-match
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-session-peer as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-command-inputp line)
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize line)) "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize line)))
                (fn-auth-session-pending as)
                (fn-auth-checkp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as)))
                 (caddr (fn-nntp-tokenize line))))
           (and (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      (list :command line)))
                       (fn-auth-single as "281 authentication accepted"))
                (equal (fn-auth-session-subject
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       (list :command line))))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       (list :command line))))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-tls-eventp fn-auth-restricted-keywordp
                            fn-nntp-keywordp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-match fn-auth-find-cred
                            fn-auth-checkp fn-auth-token-argp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-authinfo-accepted-pass-binds-the-match))
           :use ((:instance fn-auth-authinfo-accepted-pass-binds-the-match
                            (args (cdr (fn-nntp-tokenize line))))
                 (:instance fn-auth-pass-line-arguments-are-in-bounds)))))

; KEYSTONE.  The way out: STARTTLS clears a principal-derived role.
;
; For ANY session and ANY wire event: if the step entered the TLS handshake
; (the session was not handshaking and is now), the new session carries no
; subject, no cached name and no principal-derived role, and its peer role
; is the old one exactly when that role was NOT principal-derived.  So a
; peer the operator configured by source address (fn-own-open-peer) keeps
; its role across the handshake, and a role a login bound -- principal-
; derived by the first keystone -- is gone before the first octet of the
; handshake, as RFC 4642 section 2.2.2's reset of the protocol state
; requires.  The (:tls-established) re-entry keeps the base session
; (fn-auth-tls-established), so the connection comes out of the handshake
; a reader, and only a fresh AUTHINFO over TLS can bind again.
;
; Two hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-starttls-clears-a-principal-role
  (implies (and (not (fn-auth-session-handshakingp as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event))))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event))))
                (null (fn-auth-session-pending
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event))))
                (not (fn-auth-principal-rolep
                      (fn-post-result-session
                       (fn-auth-step as archive config observation injection
                                     wire-event))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event)))
                       (if (fn-auth-principal-rolep as)
                           nil
                         (fn-auth-session-peer as)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp
                            fn-auth-tls-established)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-gatedp
                            fn-auth-postingp fn-auth-find-cred
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-starttls-handshake-clears-a-principal-role))
           :use ((:instance fn-auth-starttls-handshake-clears-a-principal-role
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))))))


; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  The keystones and the
; record lemmas leave enabled; the transitions and the recognizers are
; withdrawn, so a book above computes with them and never inherits their
; unfolding.

(deftheory fn-auth-vocabulary
  '((:d fn-auth-cred-shapep) (:d fn-auth-credp) (:d fn-auth-cred-listp)
    (:d fn-auth-find-cred) (:d fn-auth-config-shapep) (:d fn-auth-configp)
    (:d fn-auth-open-config) (:d fn-auth-session-shapep)
    (:d fn-auth-sessionp) (:d fn-auth-session-consistentp)
    (:d fn-auth-open-session) (:d fn-auth-with-base) (:d fn-auth-single)
    (:d fn-auth-starttls-effect) (:d fn-auth-effectp) (:d fn-auth-effectsp)
    (:d fn-auth-access-capability-lines)
    (:d fn-auth-capability-lines-for-peer) (:d fn-auth-capability-lines)
    (:d fn-auth-peer-record)
    (:d fn-auth-checkp) (:d fn-auth-postingp)
    (:d fn-auth-restricted-keywordp) (:d fn-auth-transit-keywordp)
    (:d fn-auth-gatedp)
    (:d fn-auth-token-argp) (:d fn-auth-authinfo) (:d fn-auth-starttls)
    (:d fn-auth-tls-established) (:d fn-auth-tls-eventp)
    (:d fn-auth-command) (:d fn-auth-delegate) (:d fn-auth-step)
    (:d fn-auth-session-peer) (:d fn-auth-principal-match)
    (:d fn-auth-principal-rolep)))

(in-theory (disable fn-auth-vocabulary))

(defun fn-auth-delegate-pinned
    (as archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-peer-step-pinned
            (fn-auth-session-base as) archive index verdicts config
            observation injection wire-event)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

; Authentication and STARTTLS decisions remain the same.  Only a command
; delegated past that gate can reach the trie or historical verdict pin.
(defun fn-auth-step-pinned
    (as archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-auth-sessionp as)) (fn-post-make-result as nil nil))
   ((fn-auth-tls-eventp wire-event) (fn-auth-tls-established as))
   ((fn-auth-session-handshakingp as) (fn-post-make-result as nil nil))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-auth-command as config (car tokens) (cdr tokens))))
            (if r r
              (fn-auth-delegate-pinned as archive index verdicts config
                                        observation injection wire-event)))
        (fn-auth-delegate-pinned as archive index verdicts config observation
                                  injection wire-event))))
   (t (fn-auth-delegate-pinned as archive index verdicts config observation
                                injection wire-event))))

(verify-guards fn-auth-delegate-pinned)
(verify-guards fn-auth-step-pinned)

(defthm fn-auth-delegate-pinned-preserves-consistentp
  (implies (and (fn-auth-session-consistentp as archive)
                (fn-gidx-pin-correspondencep index archive))
           (fn-auth-session-consistentp
            (fn-post-result-session
             (fn-auth-delegate-pinned as archive index verdicts config
                                      observation injection wire-event))
            archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-delegate-pinned fn-auth-with-base
                            fn-auth-session-consistentp fn-auth-sessionp)
                           (fn-peer-step-pinned fn-peer-sessionp
                            fn-peer-session-consistentp fn-auth-configp
                            fn-peer-step-pinned-preserves-consistent-session
                            fn-nntp-printable-tokenp fn-prin-idp))
           :use ((:instance fn-peer-step-pinned-preserves-consistent-session
                            (ps (fn-auth-session-base as)))))))

(defthm fn-auth-step-pinned-preserves-consistent-session
  (implies (and (fn-auth-session-consistentp as archive)
                (fn-gidx-pin-correspondencep index archive))
           (fn-auth-session-consistentp
            (fn-post-result-session
             (fn-auth-step-pinned as archive index verdicts config observation
                                  injection wire-event))
            archive))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned)
                           (fn-peer-step-pinned fn-auth-delegate-pinned
                            fn-auth-command fn-auth-tls-established
                            fn-auth-tls-eventp fn-auth-sessionp
                            fn-auth-session-consistentp fn-nntp-keywordp
                            fn-nntp-keyword-tokenp fn-nntp-command-inputp
                            fn-nntp-tokenize
                            fn-nntp-command-arguments-at-mostp)))))

(defthm fn-auth-delegate-pinned-effects-well-formed
  (implies (and (fn-auth-session-consistentp as archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-auth-effectsp
            (fn-post-result-effects
             (fn-auth-delegate-pinned as archive index verdicts config
                                      observation injection wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-delegate-pinned fn-auth-session-consistentp)
                (fn-peer-step-pinned fn-peer-session-consistentp
                 fn-nntp-effectsp fn-auth-effectsp fn-post-result-effects
                 fn-midx-correspondencep)))))

(defthm fn-auth-step-pinned-effects-well-formed
  (implies (and (fn-auth-session-consistentp as archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-gidx-pin-correspondencep index archive))
           (fn-auth-effectsp
            (fn-post-result-effects
             (fn-auth-step-pinned as archive index verdicts config observation
                                  injection wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-auth-step-pinned)
                (fn-auth-delegate-pinned fn-auth-command
                 fn-auth-tls-established fn-auth-tls-eventp
                 fn-auth-sessionp fn-auth-session-consistentp
                 fn-auth-effectsp fn-post-result-effects
                 fn-midx-correspondencep fn-nntp-keywordp
                 fn-nntp-keyword-tokenp fn-nntp-command-inputp
                 fn-nntp-tokenize fn-nntp-command-arguments-at-mostp)))))

(defthm fn-auth-pinned-submission-is-the-delegated-submission
  (implies (fn-post-result-submission
            (fn-auth-step-pinned as archive index verdicts config observation
                                 injection wire-event))
           (equal (fn-post-result-submission
                   (fn-auth-step-pinned as archive index verdicts config
                                        observation injection wire-event))
                  (fn-post-result-submission
                   (fn-peer-step-pinned
                    (fn-auth-session-base as) archive index verdicts config
                    observation injection wire-event))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-auth-step-pinned fn-auth-delegate-pinned
                  fn-auth-tls-established)
                (fn-peer-step-pinned fn-auth-command fn-auth-sessionp
                 fn-nntp-tokenize fn-nntp-command-inputp
                 fn-auth-tls-eventp fn-nntp-keyword-tokenp
                 fn-nntp-command-arguments-at-mostp)))))

(defthm fn-auth-step-pinned-submission-is-typed
  (implies (and (fn-auth-sessionp as)
                (fn-post-result-submission
                 (fn-auth-step-pinned as archive index verdicts config
                                      observation injection wire-event)))
           (or (fn-inj-injectedp
                (fn-post-result-submission
                 (fn-auth-step-pinned as archive index verdicts config
                                      observation injection wire-event)))
               (fn-peer-submissionp
                (fn-post-result-submission
                 (fn-auth-step-pinned as archive index verdicts config
                                      observation injection wire-event)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-auth-sessionp)
                           (fn-auth-step-pinned fn-peer-step-pinned
                            fn-peer-sessionp fn-inj-injectedp
                            fn-peer-submissionp
                            fn-peer-step-pinned-submission-is-typed))
           :use ((:instance
                  fn-auth-pinned-submission-is-the-delegated-submission)
                 (:instance fn-peer-step-pinned-submission-is-typed
                            (ps (fn-auth-session-base as))))))
  :rule-classes nil)
