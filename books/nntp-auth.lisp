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

(defun fn-auth-bind-principal-peer (as principal)
  "Promote a contextual reader only for one unambiguous configured principal."
  (declare (xargs :guard t))
  (let* ((ps (fn-auth-session-base as))
         (cfg (fn-peer-session-cfg ps))
         (hex (fn-digest-hex principal))
         (rows (and (fn-cfgp cfg) (fn-cfg-peers (fn-cfg-value cfg))))
         (count (fn-auth-principal-peer-count hex rows))
         (peer (and (equal count 1) (fn-auth-principal-peer-name hex rows))))
    (if (and (null (fn-peer-session-peer ps)) peer
             (fn-node-statep (fn-peer-session-node ps)))
        (fn-auth-with-base
         as (fn-peer-make-session (fn-peer-session-base ps) peer nil 0
                                  (fn-peer-session-node ps) cfg))
      as)))

(defun fn-auth-clear-principal-peer (as)
  "Drop only a role derived from (:principal ...); legacy source peers stay peers."
  (declare (xargs :guard t))
  (let* ((ps (fn-auth-session-base as))
         (peer (fn-peer-session-peer ps))
         (cfg (fn-peer-session-cfg ps))
         (record (and peer (fn-cfgp cfg)
                      (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))))
    (if (and record (equal (car (fn-cfg-peer-auth record)) :principal))
        (fn-auth-with-base
         as (fn-peer-make-session (fn-peer-session-base ps) nil nil 0
                                  (fn-peer-session-node ps) cfg))
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
      (fn-nntp-keywordp keyword "NEWGROUPS")))

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
  :hints (("Goal" :induct (fn-auth-effectsp a)
           :in-theory (disable fn-auth-effectp))))

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

(local (defthm fn-auth-authinfo-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-authinfo as args)) archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-authinfo fn-auth-session-consistentp
                            fn-auth-sessionp)
                           (fn-peer-sessionp fn-peer-session-consistentp
                            fn-auth-configp fn-auth-single fn-nntp-single
                            fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-printable-tokenp fn-prin-idp))))))

(local (defthm fn-auth-starttls-preserves-consistentp
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session (fn-auth-starttls as args)) archive))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-starttls fn-auth-session-consistentp
                            fn-auth-sessionp)
                           (fn-peer-sessionp fn-peer-session-consistentp
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
                            fn-auth-capability-lines fn-inj-config-allow
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

; The third fact the fold needs: a submission that leaves this step is the
; one fn-peer-step produced, so books/peer-inbound.lisp's
; fn-peer-step-submission-is-typed is the whole of its typing.  Only the
; delegate branch has a submission at all: every branch this book answers
; builds its result with a NIL third field.

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
                                   fn-nntp-command-arguments-at-mostp))
           :expand ((fn-auth-command
                     as config
                     (car (fn-nntp-tokenize (car (cdr wire-event))))
                     (cdr (fn-nntp-tokenize (car (cdr wire-event)))))))))

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
; KEYSTONE.  No restricted command runs unauthenticated when the
; configuration requires authentication.
;
; RFC 4643 section 2.2: a 480 response says the command was NOT performed.
; The three conjuncts are what "not performed" means on this path: nothing
; was submitted for durable acceptance, the wire was not put into article
; mode (so no body can follow), and the session is the one the command
; arrived on -- no cursor moved, no group was selected, nothing was cached.

(defthm fn-auth-gated-command-is-refused-and-not-performed
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-auth-config-requiredp (fn-auth-session-config as))
                (not (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
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
; KEYSTONE.  The two capability labels appear exactly where their RFCs allow.
;
; RFC 4642 section 2.1: "MUST NOT be advertised once a TLS layer is active".
; RFC 4643 section 2.1: the AUTHINFO arguments are what the server will
; accept now, and after a 281 it will accept nothing.  Both are stated of
; fn-auth-capability-lines, which is the list fn-auth-command puts in the
; 101 block, which is the block fn-served-dispatch emits.

(defthm fn-auth-starttls-is-not-advertised-under-tls
  (implies tlsp
           (not (member-equal (fn-nntp-string-octets "STARTTLS")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

(defthm fn-auth-authinfo-is-not-advertised-once-authenticated
  (implies subject
           (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

(defthm fn-auth-starttls-is-not-advertised-without-a-certificate
  (implies (not (fn-auth-config-tls-availablep acfg))
           (not (member-equal (fn-nntp-string-octets "STARTTLS")
                              (fn-auth-capability-lines acfg subject tlsp
                                                        postingp))))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

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
    (:d fn-auth-command) (:d fn-auth-delegate) (:d fn-auth-step)))

(in-theory (disable fn-auth-vocabulary))
