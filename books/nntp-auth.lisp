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
; THE SECRET IS NOT A DIGEST, AND WHY.  RFC 4643 section 2.3 AUTHINFO
; USER/PASS is a cleartext password mechanism.  fn's configuration holds the
; shared secret in the clear and fn-auth-checkp compares the supplied octets
; to it with `equal'.  A stored digest was the intended design and is NOT
; implemented, for a reason that is a fact about this tree rather than a
; preference: the only digest fn has is the constrained `fn-digest' of
; books/crypto-seam.lisp, which is an encapsulated function with no
; attachment and therefore CANNOT BE EVALUATED.  Calling it on the served
; path would make fn-served-step non-executable and the reader would stop
; serving.  Deriving the digest in Python instead is refused by the
; one-owner rule (AGENTS.md): Python may not compute a value ACL2 compares.
; Recorded open as OB-AUTH-DIGEST in specs/nntp-audit.md; closing it needs an
; executable digest in ACL2, not a change here.
;
; The consequence is stated and not softened: AUTHINFO USER/PASS over a
; plaintext connection reveals the secret to anyone on the path, which is why
; RFC 4643 section 2.3.2 requires a protected channel and why fn-auth-config
; carries `protected-onlyp'.

(in-package "ACL2")
(include-book "peer-inbound")
(include-book "principal")

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nntp-post-vocabulary
                          fn-peer-vocabulary)))

; -----------------------------------------------------------------------------
; A credential
;
; (:fn-auth-cred name principal secret postingp).  `name' is the AUTHINFO
; USER argument as octets; `principal' is the substrate principal id
; (books/principal.lisp fn-prin-idp) this login speaks for, so an
; authenticated connection names a principal and not a string; `secret' is
; the shared secret; `postingp' is whether this principal may POST.

(defconst *fn-auth-max-name-octets* 64)
(defconst *fn-auth-max-secret-octets* 256)

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
       (fn-nntp-printable-tokenp (fn-auth-cred-secret x))
       (true-listp (fn-auth-cred-secret x))
       (<= (len (fn-auth-cred-secret x)) *fn-auth-max-secret-octets*)
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
;   pending   nil, or the name AUTHINFO USER cached (RFC 4643 section 2.3.2)
;   subject   nil, or the principal id this connection authenticated as
;   tlsp      whether a TLS layer is active underneath (RFC 4642 section 2.2.2)

(defun fn-auth-session-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))
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
(defun fn-auth-make-session (base config pending subject tlsp)
  (declare (xargs :guard t))
  (list base config pending subject tlsp))

(defthm fn-auth-session-shapep-of-fn-auth-make-session
  (fn-auth-session-shapep (fn-auth-make-session base config pending subject tlsp)))
(defthm fn-auth-session-base-of-fn-auth-make-session
  (equal (fn-auth-session-base
          (fn-auth-make-session base config pending subject tlsp))
         base))
(defthm fn-auth-session-config-of-fn-auth-make-session
  (equal (fn-auth-session-config
          (fn-auth-make-session base config pending subject tlsp))
         config))
(defthm fn-auth-session-pending-of-fn-auth-make-session
  (equal (fn-auth-session-pending
          (fn-auth-make-session base config pending subject tlsp))
         pending))
(defthm fn-auth-session-subject-of-fn-auth-make-session
  (equal (fn-auth-session-subject
          (fn-auth-make-session base config pending subject tlsp))
         subject))
(defthm fn-auth-session-tlsp-of-fn-auth-make-session
  (equal (fn-auth-session-tlsp
          (fn-auth-make-session base config pending subject tlsp))
         tlsp))
(defthm fn-auth-session-shapep-forward-shape
  (implies (fn-auth-session-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-auth-session-shapep) (:d fn-auth-make-session)
                    (:d fn-auth-session-base) (:d fn-auth-session-config)
                    (:d fn-auth-session-pending) (:d fn-auth-session-subject)
                    (:d fn-auth-session-tlsp)))

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
       (booleanp (fn-auth-session-tlsp x))))

(defthm fn-auth-sessionp-forward-shape
  (implies (fn-auth-sessionp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(defun fn-auth-session-consistentp (x archive)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-auth-sessionp x)
       (fn-peer-session-consistentp (fn-auth-session-base x) archive)))

(defun fn-auth-open-session (archive peer node cfg acfg tlsp)
  (declare (xargs :guard t :verify-guards nil))
  (fn-auth-make-session (fn-peer-open-session archive peer node cfg)
                        (if (fn-auth-configp acfg) acfg (fn-auth-open-config))
                        nil nil (and tlsp t)))

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
                        (fn-auth-session-tlsp as)))

; -----------------------------------------------------------------------------
; Replies and effects

(defun fn-auth-single (as text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects
   (fn-nntp-single (fn-post-session-base
                    (fn-peer-session-base (fn-auth-session-base as)))
                   text)))

; The one new effect.  The host has already written the 382 line when it acts
; on this; the handshake begins with the first octet after that reply's CRLF
; (RFC 4642 section 2.2.2).  The book sees plaintext octets on both sides.
(defun fn-auth-starttls-effect ()
  (declare (xargs :guard t))
  (list :starttls))

; -----------------------------------------------------------------------------
; The capability block (RFC 3977 section 5.2, RFC 4643 section 2.1,
; RFC 4642 section 2.1)
;
; One function composes the reader's own list with the two access-dependent
; labels; the reader list is not restated here.
;
;   STARTTLS        advertised only when a certificate is configured and no
;                   TLS layer is active.  "MUST NOT be advertised once a TLS
;                   layer is active" (RFC 4642 section 2.1).
;   AUTHINFO USER   advertised only while the connection is unauthenticated.
;                   RFC 4643 section 2.1: the arguments are the USER/PASS and
;                   SASL variants the server will accept NOW.
;   POST            the reader's own label, which fn-nntp-capability-lines
;                   already gates on the posting bit; fn-auth-postingp is
;                   what that bit is on an authenticating connection.

(defun fn-auth-capability-lines (acfg subject tlsp postingp)
  (declare (xargs :guard t))
  (append (fn-nntp-capability-lines postingp)
          (append
           (if (and (fn-auth-config-tls-availablep acfg) (not tlsp))
               (list (fn-nntp-string-octets "STARTTLS"))
             nil)
           (if (or subject
                   (and (fn-auth-config-protected-onlyp acfg) (not tlsp)))
               nil
             (list (fn-nntp-string-octets "AUTHINFO USER"))))))

; -----------------------------------------------------------------------------
; The decision functions
;
; Each is a total function of the session and the command's tokens.  Nothing
; here reads a global and nothing re-derives a value another book owns.

(defun fn-auth-checkp (cred secret)
  ; The whole of the password comparison, in ACL2.  See the header: the
  ; configuration holds the secret, not a digest, because fn's only digest
  ; cannot be evaluated.
  (declare (xargs :guard t))
  (and (consp cred) (equal (fn-auth-cred-secret cred) secret) t))

(defun fn-auth-postingp (as)
  ; The posting allowance of the connection, tied to the authenticated
  ; principal.  With authentication not required, the connection's pinned
  ; injection configuration decides, exactly as before this book existed.
  (declare (xargs :guard t))
  (let ((acfg (fn-auth-session-config as)))
    (if (not (fn-auth-config-requiredp acfg))
        t
      (let ((cred (fn-auth-find-cred (fn-auth-session-pending as)
                                     (fn-auth-config-creds acfg))))
        (and (fn-auth-session-subject as)
             (consp cred)
             (equal (fn-auth-cred-principal cred)
                    (fn-auth-session-subject as))
             (fn-auth-cred-postingp cred)
             t)))))

; Which commands this book refuses before delegating when the configuration
; requires authentication and the connection has not authenticated.  RFC 4643
; section 2.2 permits a server to require authentication for any command; fn
; requires it for exactly the commands that can change durable state or
; disclose article content, and never for the four the reader answers without
; touching the archive, so an unauthenticated client can still discover the
; server (CAPABILITIES, HELP, QUIT, MODE, DATE, AUTHINFO, STARTTLS).
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
      (fn-nntp-keywordp keyword "IHAVE")
      (fn-nntp-keywordp keyword "CHECK")
      (fn-nntp-keywordp keyword "TAKETHIS")))

(defun fn-auth-gatedp (as keyword)
  (declare (xargs :guard t))
  (and (fn-auth-config-requiredp (fn-auth-session-config as))
       (not (fn-auth-session-subject as))
       (fn-auth-restricted-keywordp keyword)
       t))

(defun fn-auth-token-argp (args)
  (declare (xargs :guard t))
  (and (consp args) (null (cdr args))
       (consp (car args))
       (true-listp (car args))
       (fn-nntp-printable-tokenp (car args))))

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
                               (fn-auth-session-tlsp as))
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
                (fn-post-make-result
                 (fn-auth-make-session (fn-auth-session-base as) acfg
                                       (fn-auth-session-pending as)
                                       (fn-auth-cred-principal cred)
                                       (fn-auth-session-tlsp as))
                 (fn-auth-single as "281 authentication accepted")
                 nil)
              ; The cached name is cleared on failure, so a failed PASS
              ; cannot be retried without a fresh USER.
              (fn-post-make-result
               (fn-auth-make-session (fn-auth-session-base as) acfg nil nil
                                     (fn-auth-session-tlsp as))
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
  (declare (xargs :guard t))
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
    ; 382 and then the handshake.  The session records that a TLS layer is
    ; active from the next octet on; the host performs the upgrade on the
    ; (:starttls) effect.  Section 2.2.2 also requires the protocol state to
    ; be reset, which is why the base session is reopened rather than kept:
    ; nothing learned before the handshake is carried across it.
    (fn-post-make-result
     (fn-auth-make-session (fn-auth-session-base as)
                           (fn-auth-session-config as) nil nil t)
     (append (fn-auth-single as "382 continue with TLS negotiation")
             (list (fn-auth-starttls-effect)))
     nil))))

(defun fn-auth-command (as keyword args)
  ; The commands this book answers.  Anything else is nil: delegate.
  ;
  ; The gate is FIRST, deliberately.  With it last, every theorem about the
  ; gate would have to prove that a restricted keyword is not also AUTHINFO,
  ; STARTTLS or CAPABILITIES -- true, but an argument about string equality
  ; rather than about the gate.  First, the refusal is read directly off the
  ; branch.  AUTHINFO, STARTTLS, CAPABILITIES, HELP, QUIT, MODE and DATE are
  ; not in fn-auth-restricted-keywordp, so an unauthenticated client can
  ; still authenticate and still discover the server.
  (declare (xargs :guard t))
  (cond
   ((fn-auth-gatedp as keyword)
    ; RFC 4643 section 2.2: 480, and the command is not performed.
    (fn-post-make-result as (fn-auth-single as "480 authentication required")
                         nil))
   ((fn-nntp-keywordp keyword "AUTHINFO") (fn-auth-authinfo as args))
   ((fn-nntp-keywordp keyword "STARTTLS") (fn-auth-starttls as args))
   ((and (fn-nntp-keywordp keyword "CAPABILITIES")
         (or (null args)
             (and (consp args) (null (cdr args))
                  (fn-nntp-keyword-tokenp (car args)))))
    (fn-post-make-result
     as
     (fn-nntp-result-effects
      (fn-nntp-multi (fn-post-session-base
                      (fn-peer-session-base (fn-auth-session-base as)))
                     "101 capability list follows"
                     (fn-auth-capability-lines (fn-auth-session-config as)
                                               (fn-auth-session-subject as)
                                               (fn-auth-session-tlsp as)
                                               (fn-auth-postingp as))))
     nil))
   (t nil)))

(defun fn-auth-delegate (as archive config observation wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-peer-step (fn-auth-session-base as) archive config observation
                         wire-event)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

; The step.  Exactly fn-peer-step's signature.
(defun fn-auth-step (as archive config observation wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-auth-sessionp as)) (fn-post-make-result as nil nil))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-auth-command as (car tokens) (cdr tokens))))
            (if r r (fn-auth-delegate as archive config observation wire-event)))
        (fn-auth-delegate as archive config observation wire-event))))
   (t (fn-auth-delegate as archive config observation wire-event))))

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
(verify-guards fn-auth-single)
(verify-guards fn-auth-starttls-effect)
(verify-guards fn-auth-capability-lines)
(verify-guards fn-auth-checkp)
(verify-guards fn-auth-postingp)
(verify-guards fn-auth-restricted-keywordp)
(verify-guards fn-auth-gatedp)
(verify-guards fn-auth-token-argp)
(verify-guards fn-auth-authinfo)
(verify-guards fn-auth-starttls)
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

(defthm fn-auth-starttls-effect-is-typed
  (fn-nntp-effectsp (list (fn-auth-starttls-effect)))
  :hints (("Goal" :in-theory (enable fn-nntp-effectsp fn-nntp-effectp
                                     fn-auth-starttls-effect))))

(defthm fn-auth-capability-lines-are-block-text
  (fn-nntp-block-textp
   (fn-auth-capability-lines acfg subject tlsp postingp))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines
                                   fn-nntp-capability-lines)
                                  nil))))

(defthm fn-auth-authinfo-effects-well-formed
  (fn-nntp-effectsp (fn-post-result-effects (fn-auth-authinfo as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo)
                                  (fn-auth-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-keywordp fn-auth-token-argp
                                   fn-auth-find-cred fn-auth-checkp)))))

(defthm fn-auth-starttls-effects-well-formed
  (fn-nntp-effectsp (fn-post-result-effects (fn-auth-starttls as args)))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls)
                                  (fn-auth-single fn-nntp-effectsp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep)))))

(defthm fn-auth-command-effects-well-formed
  (implies (fn-auth-command as keyword args)
           (fn-nntp-effectsp (fn-post-result-effects
                              (fn-auth-command as keyword args))))
  :hints (("Goal" :in-theory (e/d (fn-auth-command)
                                  (fn-auth-single fn-auth-authinfo
                                   fn-auth-starttls fn-auth-gatedp
                                   fn-nntp-effectsp fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-multi fn-auth-capability-lines
                                   fn-auth-postingp))
           :use ((:instance fn-nntp-effects-multi
                            (session (fn-post-session-base
                                      (fn-peer-session-base
                                       (fn-auth-session-base as))))
                            (initial "101 capability list follows")
                            (lines (fn-auth-capability-lines
                                    (fn-auth-session-config as)
                                    (fn-auth-session-subject as)
                                    (fn-auth-session-tlsp as)
                                    (fn-auth-postingp as))))))))

(defthm fn-auth-step-effects-well-formed
  (implies (fn-auth-session-consistentp as archive)
           (fn-nntp-effectsp
            (fn-post-result-effects
             (fn-auth-step as archive config observation wire-event))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-delegate
                                   fn-auth-session-consistentp)
                                  (fn-auth-command fn-peer-step
                                   fn-auth-sessionp fn-nntp-effectsp
                                   fn-auth-single fn-nntp-response-textp
                                   fn-nntp-initial-status-linep
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp
                                   fn-peer-session-consistentp)))))

(defthm fn-auth-step-preserves-consistent-session
  (implies (fn-auth-session-consistentp as archive)
           (fn-auth-session-consistentp
            (fn-post-result-session
             (fn-auth-step as archive config observation wire-event))
            archive))
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-delegate
                                   fn-auth-command fn-auth-authinfo
                                   fn-auth-starttls fn-auth-with-base
                                   fn-auth-session-consistentp
                                   fn-auth-sessionp)
                                  (fn-peer-step fn-peer-sessionp
                                   fn-peer-session-consistentp
                                   fn-nntp-keywordp fn-nntp-keyword-tokenp
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-command-arguments-at-mostp
                                   fn-auth-single fn-auth-gatedp
                                   fn-auth-find-cred fn-auth-checkp
                                   fn-auth-token-argp fn-auth-configp
                                   fn-nntp-multi fn-auth-capability-lines
                                   fn-auth-postingp))
           :use ((:instance fn-peer-step-preserves-consistent-session
                            (ps (fn-auth-session-base as)))))))

(defthm fn-auth-submission-is-the-delegated-submission
  (implies (fn-post-result-submission
            (fn-auth-step as archive config observation wire-event))
           (equal (fn-post-result-submission
                   (fn-auth-step as archive config observation wire-event))
                  (fn-post-result-submission
                   (fn-peer-step (fn-auth-session-base as) archive config
                                 observation wire-event))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step fn-auth-delegate)
                                  (fn-peer-step fn-auth-command
                                   fn-auth-sessionp fn-nntp-tokenize
                                   fn-nntp-command-inputp
                                   fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp))
           :expand ((fn-auth-command
                     as (car (fn-nntp-tokenize (car (cdr wire-event))))
                     (cdr (fn-nntp-tokenize (car (cdr wire-event)))))))))

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
                (fn-auth-config-requiredp (fn-auth-session-config as))
                (not (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
           (and (null (fn-post-result-submission
                       (fn-auth-step as archive config observation
                                     (list :command line))))
                (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-step as archive config observation
                                     (list :command line)))))
                (equal (fn-post-result-session
                        (fn-auth-step as archive config observation
                                      (list :command line)))
                       as)
                (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation
                                      (list :command line)))
                       (fn-auth-single as "480 authentication required"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-post-offeredp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-restricted-keywordp fn-auth-sessionp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-nntp-begin-article-effect)))))

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
; KEYSTONE.  382 is emitted at most once per connection, and only from the
; one branch that also records the TLS layer.

(defthm fn-auth-starttls-effect-only-with-382
  (implies (member-equal (fn-auth-starttls-effect)
                         (fn-post-result-effects (fn-auth-starttls as args)))
           (and (null args)
                (not (fn-auth-session-tlsp as))
                (fn-auth-config-tls-availablep (fn-auth-session-config as))
                (fn-auth-session-tlsp
                 (fn-post-result-session (fn-auth-starttls as args)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls fn-auth-single
                                   fn-auth-starttls-effect)
                                  (fn-nntp-single))))
  :rule-classes nil)

(defthm fn-auth-second-starttls-is-refused
  (implies (fn-auth-session-tlsp as)
           (and (equal (fn-post-result-effects (fn-auth-starttls as nil))
                       (fn-auth-single as "502 a TLS layer is already active"))
                (not (member-equal (fn-auth-starttls-effect)
                                   (fn-post-result-effects
                                    (fn-auth-starttls as nil))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-starttls fn-auth-single
                                   fn-auth-starttls-effect)
                                  (fn-nntp-single)))))

; -----------------------------------------------------------------------------
; KEYSTONE.  AUTHINFO PASS accepts only a supplied secret that equals the
; configured one, and only after a cached AUTHINFO USER.

(defthm fn-auth-pass-accepts-only-a-matching-secret
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
                (equal (fn-auth-cred-secret
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as))))
                       secret)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-checkp)
                           (fn-auth-single fn-auth-find-cred
                            fn-auth-token-argp fn-auth-sessionp
                            fn-nntp-keywordp fn-nntp-single))))
  :rule-classes nil)

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
    (:d fn-auth-starttls-effect) (:d fn-auth-capability-lines)
    (:d fn-auth-checkp) (:d fn-auth-postingp)
    (:d fn-auth-restricted-keywordp) (:d fn-auth-gatedp)
    (:d fn-auth-token-argp) (:d fn-auth-authinfo) (:d fn-auth-starttls)
    (:d fn-auth-command) (:d fn-auth-delegate) (:d fn-auth-step)))

(in-theory (disable fn-auth-vocabulary))
