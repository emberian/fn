; fn: the SASL exchanges AUTHINFO SASL runs (RFC 4643 section 2.4, RFC 4422):
; PLAIN (RFC 4616), SCRAM-SHA-256 (RFC 5802, RFC 7677) and
; SCRAM-SHA-256-PLUS with the tls-exporter binding (RFC 9266).
;
; This book is the exchange, mechanism by mechanism, as a function of the
; exchange's state, the client's decoded response, and what the connection
; knows: whether TLS is active, the per-connection nonce seed, and the TLS
; exporter value.  It decides everything but the wire: books/nntp-auth.lisp
; frames each outcome as an NNTP reply (383, 281, 283, 481, 482, 504),
; decodes the client's base64, and looks the named login up in the
; connection's credential snapshot.  The lookup is the caller's because the
; credential table is nntp-auth's; the exchange therefore runs in two
; phases on every response: `fn-sasl-response-login' says which login the
; response names (a parse, no credential), the caller finds that login's
; stored verifier (books/auth-secret.lisp), and `fn-sasl-step' decides.
;
; WHAT THE SERVER KEEPS BETWEEN RESPONSES (the connection's pending slot,
; in memory, for one exchange):
;
;   (:sasl-plain)                383 = was sent; the PLAIN message is awaited
;   (:sasl-scram-first PLUSP)    383 = was sent; client-first is awaited
;   (:sasl-scram-final PLUSP FLAG GS2 LOGIN NONCE BARE SERVER-FIRST)
;                                server-first was sent; client-final is awaited
;
; No password, SaltedPassword or key is ever in a state.
;
; THE SERVER NONCE.  s-nonce = base64 of the first 18 octets of
; BLAKE3-keyed(SEED, "fn/scram-server-nonce/v1" || c-nonce), SEED being 32
; octets the host drew from its CSPRNG for this connection alone and
; installed by the (:sasl-seed OCTETS) wire event (books/nntp-auth.lisp).
; fn chooses the derivation, so it is BLAKE3 (books/node-secret.lisp's rule).
; Two connections never share a seed, so an exchange recorded on one cannot
; complete on another (`fn-scram-finish-refuses-another-nonce'); on one
; connection the nonce is a function of the client's nonce, and a replayed
; exchange there replays a proof the server already judged.  That the seed
; is unpredictable is the host's CSPRNG (A-CRYPTO), not proved.
;
; AN UNKNOWN LOGIN.  SCRAM answers a login the snapshot does not hold with
; a server-first like any other -- the salt the first 16 octets of
; BLAKE3-derive_key("fn/scram-unknown-login-salt/v1", login), the count
; 4096 -- and fails at the proof, after the same work, so the reply
; sequence does not say whether the login exists.  The salt is not keyed by
; a secret, so a client that knows the derivation can tell an unknown login
; from a known one; fn does not claim logins are secret (XREDEEM's
; login-taken refusal names them), and this is stated rather than hidden.

(in-package "ACL2")
(include-book "scram")
(include-book "auth-secret")

; -----------------------------------------------------------------------------
; Constants

(defconst *fn-sasl-plain* (fn-scram-text "PLAIN"))
(defconst *fn-sasl-seed-octets* 32)
(defconst *fn-sasl-binding-octets* 32)
(defconst *fn-sasl-nonce-octets* 18)
(defconst *fn-sasl-nonce-tag* (fn-scram-text "fn/scram-server-nonce/v1"))
(defconst *fn-sasl-unknown-salt-context*
  (fn-scram-text "fn/scram-unknown-login-salt/v1"))

(defun fn-sasl-32p (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x) (equal (len x) 32)))

(defun fn-sasl-seedp (x)
  (declare (xargs :guard t))
  (fn-sasl-32p x))

(defun fn-sasl-bindingp (x)
  ; RFC 9266 section 2: the tls-exporter value is 32 octets.
  (declare (xargs :guard t))
  (fn-sasl-32p x))

(defun fn-sasl-firstn (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp (nfix n)) (atom xs))
      nil
    (cons (car xs) (fn-sasl-firstn (- (nfix n) 1) (cdr xs)))))

; -----------------------------------------------------------------------------
; Mechanisms
;
; What a connection offers (RFC 4643 section 2.1's SASL capability list),
; strongest first:
;   SCRAM-SHA-256-PLUS  TLS is active, the host installed the exporter value
;                       and the nonce seed
;   SCRAM-SHA-256       the host installed the nonce seed
;   PLAIN               TLS is active (RFC 4616 section 4: PLAIN SHOULD NOT
;                       be used without a confidentiality layer; fn refuses
;                       it with 483 instead)
; A mechanism not offered answers 503 when named (RFC 4643 section 2.4.2),
; PLAIN before TLS 483.

(defun fn-sasl-mech (word)
  ; The mechanism a command's word names, case-insensitively; nil for any
  ; other word.
  (declare (xargs :guard t))
  (cond ((fn-ot-ci-equal word *fn-scram-plus-mechanism*) :scram-plus)
        ((fn-ot-ci-equal word *fn-scram-mechanism*) :scram)
        ((fn-ot-ci-equal word *fn-sasl-plain*) :plain)
        (t nil)))

(defun fn-sasl-offeredp (mech tlsp seed binding)
  (declare (xargs :guard t))
  (cond ((equal mech :scram-plus)
         (and tlsp (fn-sasl-seedp seed) (fn-sasl-bindingp binding) t))
        ((equal mech :scram) (fn-sasl-seedp seed))
        ((equal mech :plain) (and tlsp t))
        (t nil)))

(defun fn-sasl-offers (tlsp seed binding)
  ; The capability's mechanism names, as octets, in the order above.
  (declare (xargs :guard t))
  (append (if (fn-sasl-offeredp :scram-plus tlsp seed binding)
              (list *fn-scram-plus-mechanism*)
            nil)
          (if (fn-sasl-offeredp :scram tlsp seed binding)
              (list *fn-scram-mechanism*)
            nil)
          (if (fn-sasl-offeredp :plain tlsp seed binding)
              (list *fn-sasl-plain*)
            nil)))

(defthm fn-sasl-offers-names-exactly-the-offered-mechanisms
  (iff (member-equal word (fn-sasl-offers tlsp seed binding))
       (or (and (equal word *fn-scram-plus-mechanism*)
                (fn-sasl-offeredp :scram-plus tlsp seed binding))
           (and (equal word *fn-scram-mechanism*)
                (fn-sasl-offeredp :scram tlsp seed binding))
           (and (equal word *fn-sasl-plain*)
                (fn-sasl-offeredp :plain tlsp seed binding))))
  :hints (("Goal" :in-theory (disable fn-sasl-offeredp))))

; -----------------------------------------------------------------------------
; The exchange states

(defun fn-sasl-statep (p)
  (declare (xargs :guard t))
  (and (consp p) (true-listp p)
       (or (and (equal (car p) :sasl-plain) (null (cdr p)))
           (and (equal (car p) :sasl-scram-first)
                (equal (len p) 2) (booleanp (cadr p)))
           (and (equal (car p) :sasl-scram-final)
                (equal (len p) 8) (booleanp (cadr p))))))

(defun fn-sasl-final-state (plusp flag gs2 login nonce bare server-first)
  (declare (xargs :guard t))
  (list :sasl-scram-final (and plusp t) flag gs2 login nonce bare server-first))

(defun fn-sasl-st (n st)
  (declare (xargs :guard t))
  (fn-scram-nth n st))

(defthm fn-sasl-statep-of-final-state
  (fn-sasl-statep (fn-sasl-final-state plusp flag gs2 login nonce bare
                                       server-first)))

; -----------------------------------------------------------------------------
; Outcomes
;
;   (:continue CHALLENGE STATE)  383 with CHALLENGE (empty: "383 =")
;   (:success FINAL)             281 when FINAL is nil, else 283 FINAL
;   (:fail REASON)               481: RFC 4643 2.4.2 "unable to authenticate"
;
; REASON is for the record (the log line), never for the wire: 481 carries
; no argument, so no reply says whether the login, the proof or the binding
; failed.

(defun fn-sasl-outcome-kind (o)
  (declare (xargs :guard t))
  (if (consp o) (car o) nil))

(defun fn-sasl-successp (o)
  (declare (xargs :guard t))
  (equal (fn-sasl-outcome-kind o) :success))

; -----------------------------------------------------------------------------
; The server nonce and the unknown login's salt

(defun fn-sasl-server-nonce (seed cnonce)
  (declare (xargs :guard t))
  (fn-ot-b64-encode
   (fn-sasl-firstn *fn-sasl-nonce-octets*
                   (fn-blake3-keyed seed (append *fn-sasl-nonce-tag*
                                                 (fn-scram-octets cnonce))))))

(defun fn-sasl-unknown-salt (login)
  (declare (xargs :guard t))
  (fn-sasl-firstn *fn-authsec-salt-octets*
                  (fn-blake3-derive-key *fn-sasl-unknown-salt-context*
                                        (fn-scram-octets login))))

; -----------------------------------------------------------------------------
; PLAIN (RFC 4616 section 2)
;
;   message = [authzid] UTF8NUL authcid UTF8NUL passwd
;
; The result is (AUTHZID AUTHCID PASSWD), AUTHZID nil when empty, or :bad.
; authcid and passwd are 1..255 octets of UTF-8 without NUL; fn reads them
; as octets (every fn login and password is ASCII; see books/scram.lisp on
; SASLprep).  An authzid is accepted only when it equals the authcid: fn has
; no proxy authorization (RFC 4616 section 2: the server MUST fail when the
; authcid may not act as the authzid).

(defun fn-sasl-split-nul (xs field)
  (declare (xargs :guard (true-listp field)))
  (if (consp xs)
      (if (equal (car xs) 0)
          (cons (revappend field nil) (fn-sasl-split-nul (cdr xs) nil))
        (fn-sasl-split-nul (cdr xs) (cons (car xs) field)))
    (list (revappend field nil))))

(defun fn-sasl-plain-parse (msg)
  (declare (xargs :guard t))
  (let ((parts (fn-sasl-split-nul (fn-scram-octets msg) nil)))
    (if (and (consp parts) (consp (cdr parts)) (consp (cddr parts))
             (null (cdddr parts))
             (consp (cadr parts)) (<= (len (cadr parts)) 255)
             (consp (caddr parts)) (<= (len (caddr parts)) 255)
             (<= (len (car parts)) 255))
        (list (if (consp (car parts)) (car parts) nil)
              (cadr parts) (caddr parts))
      :bad)))

(defun fn-sasl-plain-message (authzid authcid passwd)
  ; The client's message, for the round trip and the tests.
  (declare (xargs :guard t))
  (append (fn-scram-octets authzid) (list 0) (fn-scram-octets authcid)
          (list 0) (fn-scram-octets passwd)))

(defun fn-sasl-plain-step (response verifier)
  (declare (xargs :guard t))
  (let ((p (fn-sasl-plain-parse response)))
    (cond ((equal p :bad) (list :fail :plain-syntax))
          ((and (car p) (not (equal (car p) (cadr p))))
           (list :fail :authzid))
          ((fn-authsec-checkp verifier (caddr p)) (list :success nil))
          (t (list :fail :invalid-password)))))

; -----------------------------------------------------------------------------
; SCRAM-SHA-256[-PLUS]

(defun fn-sasl-scram-first-step (plusp response verifier seed binding)
  ; client-first-message in, server-first-message out.
  (declare (xargs :guard t))
  (let ((r (fn-scram-parse-client-first response)))
    (if (fn-scram-failp r)
        (list :fail (fn-scram-fail-reason r))
      (let ((flag (fn-scram-cf-flag r))
            (authzid (fn-scram-cf-authzid r))
            (login (fn-scram-cf-username r))
            (cnonce (fn-scram-cf-cnonce r)))
        (cond
         ; RFC 5802 section 6: a -PLUS exchange uses "p"; a plain one
         ; never does.
         ((and plusp (not (equal flag :p))) (list :fail :binding-required))
         ((and (not plusp) (equal flag :p))
          (list :fail :binding-not-negotiated))
         ; RFC 5802 section 6: "y" says the client could bind and believes
         ; the server cannot; if the server can, this is a downgrade and
         ; the server MUST fail.
         ((and (equal flag :y) (fn-sasl-bindingp binding))
          (list :fail :downgrade))
         ((and plusp (not (fn-sasl-bindingp binding)))
          (list :fail :no-binding))
         ((not (fn-sasl-seedp seed)) (list :fail :no-seed))
         ((and authzid (not (equal authzid login))) (list :fail :authzid))
         (t
          (let* ((snonce (fn-sasl-server-nonce seed cnonce))
                 (salt (if (fn-authsec-verifierp verifier)
                           (fn-authsec-ver-salt verifier)
                         (fn-sasl-unknown-salt login)))
                 (sf (fn-scram-server-first cnonce snonce salt
                                            *fn-scram-iterations*)))
            (list :continue sf
                  (fn-sasl-final-state plusp flag (fn-scram-cf-gs2 r) login
                                       (append (fn-scram-octets cnonce) snonce)
                                       (fn-scram-cf-bare r) sf)))))))))

(defun fn-sasl-scram-final-step (st response verifier binding)
  ; client-final-message in, server-final-message out.  A login the
  ; snapshot does not hold has no StoredKey and fails as a wrong proof does.
  (declare (xargs :guard t))
  (let* ((knownp (fn-authsec-verifierp verifier))
         (r (fn-scram-finish response
                             (fn-sasl-st 2 st) (fn-sasl-st 3 st) binding
                             (fn-sasl-st 5 st) (fn-sasl-st 6 st)
                             (fn-sasl-st 7 st)
                             (and knownp (fn-authsec-ver-stored-key verifier))
                             (fn-authsec-ver-server-key verifier))))
    (if (equal (car r) :accept)
        (list :success (fn-scram-nth 1 r))
      (list :fail (fn-scram-fail-reason r)))))

; -----------------------------------------------------------------------------
; The two phases

(defun fn-sasl-start (mech)
  ; AUTHINFO SASL MECH with no initial response: "383 =" (RFC 4643 2.4.2,
  ; RFC 4422 5.1: the mechanism is client-first, so the server's first
  ; challenge is empty).
  (declare (xargs :guard t))
  (list :continue nil
        (cond ((equal mech :plain) (list :sasl-plain))
              ((equal mech :scram-plus) (list :sasl-scram-first t))
              (t (list :sasl-scram-first nil)))))

(defun fn-sasl-initial-state (mech)
  ; The state an initial response is read in: the one `fn-sasl-start'
  ; would have entered.
  (declare (xargs :guard t))
  (car (cddr (fn-sasl-start mech))))

(defun fn-sasl-response-login (st response)
  ; Phase one: the login this response names, or nil.  A parse only.
  (declare (xargs :guard t))
  (cond ((not (consp st)) nil)
        ((equal (car st) :sasl-plain)
         (let ((p (fn-sasl-plain-parse response)))
           (if (equal p :bad) nil (cadr p))))
        ((equal (car st) :sasl-scram-first)
         (let ((r (fn-scram-parse-client-first response)))
           (if (fn-scram-failp r) nil (fn-scram-cf-username r))))
        ((equal (car st) :sasl-scram-final) (fn-sasl-st 4 st))
        (t nil)))

(defun fn-sasl-step (st response verifier seed binding)
  ; Phase two: VERIFIER is the stored verifier of the login phase one named
  ; (nil when the snapshot holds none).
  (declare (xargs :guard t))
  (cond ((not (consp st)) (list :fail :no-exchange))
        ((equal (car st) :sasl-plain) (fn-sasl-plain-step response verifier))
        ((equal (car st) :sasl-scram-first)
         (fn-sasl-scram-first-step (fn-sasl-st 1 st) response verifier seed
                                   binding))
        ((equal (car st) :sasl-scram-final)
         (fn-sasl-scram-final-step st response verifier binding))
        (t (list :fail :no-exchange))))

(defthm fn-sasl-step-continues-only-into-a-state
  (implies (equal (fn-sasl-outcome-kind (fn-sasl-step st response verifier
                                                      seed binding))
                  :continue)
           (fn-sasl-statep (car (cddr (fn-sasl-step st response verifier
                                                    seed binding)))))
  :hints (("Goal" :in-theory (disable fn-scram-parse-client-first
                                      fn-scram-finish fn-sasl-server-nonce
                                      fn-scram-server-first
                                      fn-sasl-plain-parse))))

; -----------------------------------------------------------------------------
; Keystones

; S1 (PLAIN is the stored check).  A PLAIN message with no authzid, or with
; the authcid as authzid, succeeds exactly when books/auth-secret.lisp's
; fn-authsec-checkp accepts its password against the verifier -- the check
; AUTHINFO USER/PASS runs; PLAIN adds no second password comparison.
(defthm fn-sasl-plain-succeeds-exactly-on-the-stored-check
  (implies (not (equal (fn-sasl-plain-parse response) :bad))
           (equal (fn-sasl-successp (fn-sasl-step (list :sasl-plain) response
                                                  verifier seed binding))
                  (and (or (not (car (fn-sasl-plain-parse response)))
                           (equal (car (fn-sasl-plain-parse response))
                                  (cadr (fn-sasl-plain-parse response))))
                       (fn-authsec-checkp verifier
                                          (caddr (fn-sasl-plain-parse
                                                  response))))))
  :hints (("Goal" :in-theory (disable fn-sasl-plain-parse fn-authsec-checkp))))

; S2 (no SCRAM success without a stored key).  A final response for a login
; whose verifier the snapshot does not hold never succeeds.
(defthm fn-sasl-scram-unknown-login-never-succeeds
  (implies (not (fn-authsec-verifierp verifier))
           (not (fn-sasl-successp
                 (fn-sasl-scram-final-step st response verifier binding))))
  :hints (("Goal" :in-theory (e/d (fn-scram-finish)
                                  (fn-scram-parse-client-final
                                   fn-scram-server-final
                                   fn-authsec-verifierp)))))

; S3 (the downgrade).  A client-first with the "y" flag on a connection
; whose exporter value is installed -- one that offers -PLUS -- is refused.
(defthm fn-sasl-scram-y-flag-with-a-binding-is-refused
  (implies (and (fn-sasl-bindingp binding)
                (not (fn-scram-failp (fn-scram-parse-client-first response)))
                (equal (fn-scram-cf-flag (fn-scram-parse-client-first response))
                       :y))
           (equal (fn-sasl-scram-first-step plusp response verifier seed
                                            binding)
                  (if plusp
                      (list :fail :binding-required)
                    (list :fail :downgrade))))
  :hints (("Goal" :in-theory (disable fn-scram-parse-client-first
                                      fn-sasl-bindingp))))

; S4 (the nonce and the binding hold across the exchange).  The final step
; succeeds only on a client-final whose nonce is the one this exchange's
; server-first carried and whose channel binding is this exchange's gs2
; header followed, under tls-exporter, by this connection's exporter value.
(defthm fn-sasl-scram-final-success-is-bound-to-the-exchange
  (implies (fn-sasl-successp (fn-sasl-scram-final-step st response verifier
                                                       binding))
           (and (equal (fn-scram-cfin-nonce
                        (fn-scram-parse-client-final response))
                       (fn-scram-octets (fn-sasl-st 5 st)))
                (equal (fn-scram-cfin-cbind
                        (fn-scram-parse-client-final response))
                       (fn-scram-expected-cbind (fn-sasl-st 2 st)
                                                (fn-sasl-st 3 st) binding))
                (fn-authsec-verifierp verifier)))
  :hints (("Goal"
           :use ((:instance fn-scram-finish-refuses-another-nonce
                            (msg response) (flag (fn-sasl-st 2 st))
                            (gs2 (fn-sasl-st 3 st))
                            (nonce (fn-sasl-st 5 st))
                            (bare (fn-sasl-st 6 st))
                            (server-first (fn-sasl-st 7 st))
                            (stored-key (and (fn-authsec-verifierp verifier)
                                             (fn-authsec-ver-stored-key
                                              verifier)))
                            (server-key (fn-authsec-ver-server-key verifier)))
                 (:instance fn-scram-finish-refuses-another-binding
                            (msg response) (flag (fn-sasl-st 2 st))
                            (gs2 (fn-sasl-st 3 st))
                            (nonce (fn-sasl-st 5 st))
                            (bare (fn-sasl-st 6 st))
                            (server-first (fn-sasl-st 7 st))
                            (stored-key (and (fn-authsec-verifierp verifier)
                                             (fn-authsec-ver-stored-key
                                              verifier)))
                            (server-key (fn-authsec-ver-server-key verifier)))
                 (:instance fn-sasl-scram-unknown-login-never-succeeds))
           :in-theory (disable fn-scram-finish fn-scram-parse-client-final
                               fn-authsec-verifierp
                               fn-sasl-scram-unknown-login-never-succeeds
                               fn-scram-finish-refuses-another-nonce
                               fn-scram-finish-refuses-another-binding))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2)

(deftheory fn-sasl-internals
  '((:d fn-sasl-32p) (:d fn-sasl-seedp) (:d fn-sasl-bindingp)
    (:d fn-sasl-firstn) (:d fn-sasl-mech) (:d fn-sasl-offeredp)
    (:d fn-sasl-offers) (:d fn-sasl-statep) (:d fn-sasl-final-state)
    (:d fn-sasl-st) (:d fn-sasl-outcome-kind) (:d fn-sasl-successp)
    (:d fn-sasl-server-nonce) (:d fn-sasl-unknown-salt)
    (:d fn-sasl-split-nul) (:d fn-sasl-plain-parse)
    (:d fn-sasl-plain-message) (:d fn-sasl-plain-step)
    (:d fn-sasl-scram-first-step) (:d fn-sasl-scram-final-step)
    (:d fn-sasl-start) (:d fn-sasl-initial-state)
    (:d fn-sasl-response-login) (:d fn-sasl-step)))

(in-theory (disable fn-sasl-internals))
