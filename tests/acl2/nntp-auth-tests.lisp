; Evidence for AUTHINFO (RFC 4643) and STARTTLS (RFC 4642): books/nntp-auth.lisp.
;
; Order follows docs/proof-style.md section 6: the guard-world audit, then
; the scenario transcripts written out of the RFCs, then the teeth.
;
; Every expected reply is written here from the RFC's own response table and
; assembled by `au-single'/`au-block', never by calling the function under
; test.

(in-package "ACL2")
(include-book "../../books/nntp-auth")

(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary fn-nntp-vocabulary
                          fn-nntp-post-vocabulary fn-peer-vocabulary
                          fn-auth-vocabulary)))

; -----------------------------------------------------------------------------
; Guard-world audit: the served entry is total in the executable sense.

(assert-event (equal (symbol-class 'fn-auth-step (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-auth-step nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-auth-command (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-auth-command nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-auth-capability-lines (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-auth-checkp (w state))
                     :common-lisp-compliant))

; -----------------------------------------------------------------------------
; The scenario

(defconst *au-groups* '("fn.letters"))
(defconst *au-id* "<auth@example.invalid>")
(defconst *au-payload*
  (append (fn-nntp-string-octets "Message-ID: <auth@example.invalid>")
          '(13 10) (fn-nntp-string-octets "Subject: hello") '(13 10 13 10)
          (fn-nntp-string-octets "Hello") '(13 10)))
(defconst *au-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *au-groups*) 1 *au-id* *au-payload*
                      *au-groups*)
   0 1 :durable))
(defconst *au-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *au-agent* (fn-nntp-string-octets "fn.example.invalid"))
(defconst *au-config*
  (fn-inj-make-config t *au-agent*
                      (list (fn-nntp-string-octets "fn.letters")) 32768))

; The configured source role that authorizes transit.  It is deliberately
; independent of the AUTHINFO credentials below: a peer has no reader login
; on this transcript, yet its transit commands reach fn-peer-step.
(defconst *au-peer-record*
  (fn-cfg-peer-make "transit" "transit.example.invalid"
                    '(:nntp "127.0.0.1" 119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(assert-event (fn-cfg-peerp *au-peer-record*))
(defconst *au-peer-change*
  (append *fn-cfg-default-change*
          (list (fn-cfg-set-peer-delta *au-peer-record*))))
(defconst *au-peer-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make 0 0 1 *au-peer-change*
                             *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *au-peer-cfg*))
(assert-event (equal (fn-cfg-peer-find "transit"
                                        (fn-cfg-peers (fn-cfg-value *au-peer-cfg*)))
                     *au-peer-record*))
(defconst *au-peer-node* (fn-node-initial-state '("fn.letters") 1048576))
(assert-event (fn-node-statep *au-peer-node*))

; A principal id is 32 octets (books/principal.lisp fn-prin-idp, which is the
; crypto seam's digest shape).  This one stands for a configured login; the
; test does not derive it, because deriving it needs the seam's fn-digest,
; which is constrained and cannot be evaluated -- the same fact that keeps
; the secret out of a digest.  See the header of books/nntp-auth.lisp.
(defconst *au-principal* (make-list 32 :initial-element 7))
(assert-event (fn-prin-idp *au-principal*))

(defconst *au-name* (fn-nntp-string-octets "reader"))
(defconst *au-secret* (fn-nntp-string-octets "correct-horse"))
; What the configuration holds is the VERIFIER, derived here by
; books/auth-secret.lisp from a salt and the secret.  The secret itself
; appears in no field of it, and fn-authsec-verifier-is-not-octets says a
; printable token could not sit in this slot at all.
; The digest is written out rather than computed into the constant: ACL2
; refuses to call an ATTACHMENT while computing a `defconst'
; (:DOC ignored-attachment), and that restriction is the point -- a
; constant over `fn-digest' would bake an attachment-dependent value into
; the logical world.  The assert-event below re-derives it under the real
; attachment, where top-level evaluation applies, so the literal cannot
; drift from what enrolment produces.
(defconst *au-salt* (make-list 16 :initial-element 3))
(assert-event (fn-authsec-saltp *au-salt*))
(defconst *au-digest*
  '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
    73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194))
(defconst *au-verifier* (fn-authsec-verifier *au-salt* *au-digest*))
(assert-event (equal *au-verifier* (fn-authsec-enrol *au-salt* *au-secret*)))
(assert-event (fn-authsec-verifierp *au-verifier*))
(assert-event (not (fn-cbor-octet-listp *au-verifier*)))
(defconst *au-cred*
  (fn-auth-make-cred *au-name* *au-principal* *au-verifier* t))
(assert-event (fn-auth-credp *au-cred*))
; The enrolled secret checks (fn-authsec-enrolled-secret-checks) and a
; wrong one does not.  The second is a WITNESS on these octets under the
; real SHA-256 attachment, not a theorem: second-preimage resistance is
; A-CRYPTO (specs/failures.md).
(assert-event (fn-auth-checkp *au-cred* *au-secret*))
(assert-event (not (fn-auth-checkp *au-cred*
                                   (fn-nntp-string-octets "wrong-horse"))))

; A second principal, whose credential does not allow posting: the posting
; allowance is tied to the authenticated principal and not to the connection.
(defconst *au-principal-ro* (make-list 32 :initial-element 9))
(defconst *au-salt-ro* (make-list 16 :initial-element 5))
(defconst *au-digest-ro*
  '(16 253 71 139 166 161 40 4 128 152 222 245 150 31 146 146
    162 213 89 91 217 56 233 234 208 64 14 230 20 40 189 59))
(defconst *au-verifier-ro* (fn-authsec-verifier *au-salt-ro* *au-digest-ro*))
(assert-event (equal *au-verifier-ro*
                     (fn-authsec-enrol *au-salt-ro*
                                       (fn-nntp-string-octets "guest-pass"))))
(defconst *au-cred-ro*
  (fn-auth-make-cred (fn-nntp-string-octets "guest") *au-principal-ro*
                     *au-verifier-ro* nil))
(assert-event (fn-auth-credp *au-cred-ro*))
(assert-event (not (equal *au-principal* *au-principal-ro*)))

(defconst *au-principal-peer-record*
  (fn-cfg-peer-make
   "principal-peer" "principal.example.invalid" '(:nntp "127.0.0.1" 119)
   '("fn.*" 32768 16) nil
   (list :principal (coerce (fn-id-hex-octets *au-principal*) 'string))))
(defconst *au-principal-peer-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make
          0 0 1 (append *fn-cfg-default-change*
                        (list (fn-cfg-set-peer-delta *au-principal-peer-record*)))
          *fn-cfg-default-stamp*))))
(assert-event (fn-cfg-peerp *au-principal-peer-record*))

; Three configurations: open (nothing required, no certificate), required
; (authentication required, a certificate configured), and protected-only.
(defconst *au-open* (fn-auth-open-config))
(defconst *au-required*
  (fn-auth-make-config t nil t (list *au-cred* *au-cred-ro*)))
(defconst *au-protected*
  (fn-auth-make-config t t t (list *au-cred*)))
(assert-event (fn-auth-configp *au-open*))
(assert-event (fn-auth-configp *au-required*))
(assert-event (fn-auth-configp *au-protected*))

(defun au-session (acfg tlsp)
  (fn-auth-open-session *au-archive* nil nil nil acfg tlsp))
(defconst *au-s-open* (au-session *au-open* nil))
(defconst *au-s-req* (au-session *au-required* nil))
(defconst *au-s-req-tls* (au-session *au-required* t))
(defconst *au-s-prot* (au-session *au-protected* nil))
(defconst *au-s-peer-req*
  (fn-auth-open-session (fn-node-acceptance *au-peer-node*) "transit"
                        *au-peer-node* *au-peer-cfg* *au-required* nil))
(defconst *au-s-principal-reader*
  (fn-auth-open-session (fn-node-acceptance *au-peer-node*) nil
                        *au-peer-node* *au-principal-peer-cfg*
                        *au-required* nil))
(assert-event (fn-auth-sessionp *au-s-open*))
(assert-event (fn-auth-sessionp *au-s-req*))
(assert-event (fn-auth-session-consistentp *au-s-req* *au-archive*))
(assert-event (null (fn-auth-session-subject *au-s-req*)))
(assert-event (equal (fn-auth-session-tlsp *au-s-req-tls*) t))
(assert-event (fn-auth-session-consistentp *au-s-peer-req*
                                           (fn-node-acceptance *au-peer-node*)))
(assert-event (null (fn-peer-session-peer
                     (fn-auth-session-base *au-s-principal-reader*))))

(defun au-step (as text)
  (fn-auth-step as *au-archive* *au-config* *au-obs* *au-obs*
                (list :command (fn-nntp-string-octets text))))
(defun au-reply (as text)
  (fn-post-result-effects (au-step as text)))
(defun au-after (as text)
  (fn-post-result-session (au-step as text)))

(defun au-peer-step (as text)
  (fn-auth-step as (fn-node-acceptance *au-peer-node*) *au-config*
                *au-obs* *au-obs*
                (list :command (fn-nntp-string-octets text))))
(defun au-peer-reply (as text)
  (fn-post-result-effects (au-peer-step as text)))

; The expected-reply assembler: its own CRLFs, no stuffing, independent of
; fn-nntp-single.
(defun au-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defun au-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10)
              (au-lines (cdr texts)))
    nil))
(defun au-block (initial texts)
  (list (list :reply (append (fn-nntp-string-octets initial) '(13 10)
                             (au-lines texts) '(46 13 10)))))

; -----------------------------------------------------------------------------
; RFC 4643 section 2.3: the AUTHINFO USER/PASS exchange

; Section 2.3.2: AUTHINFO USER is answered 381 unconditionally, so whether
; the name is configured is not disclosed.  Both a known and an unknown name.
(assert-event (equal (au-reply *au-s-req* "AUTHINFO USER reader")
                     (au-single "381 password required")))
(assert-event (equal (au-reply *au-s-req* "AUTHINFO USER nobody")
                     (au-single "381 password required")))
(assert-event (equal (au-reply *au-s-req* "AUTHINFO USER reader")
                     (au-reply *au-s-req* "AUTHINFO USER nobody")))

; Section 2.3.2: AUTHINFO PASS with no cached username is 482.
(assert-event (equal (au-reply *au-s-req* "AUTHINFO PASS correct-horse")
                     (au-single "482 authentication commands issued out of sequence")))

; The accepted exchange: 381 then 281, and the session now names the
; principal -- not the login string.
(defconst *au-after-user* (au-after *au-s-req* "AUTHINFO USER reader"))
(assert-event (equal (fn-auth-session-pending *au-after-user*) *au-name*))
(assert-event (null (fn-auth-session-subject *au-after-user*)))
(assert-event (equal (au-reply *au-after-user* "AUTHINFO PASS correct-horse")
                     (au-single "281 authentication accepted")))
; Macros, not constants: the accepting branch runs fn-authsec-checkp, whose
; digest is an ATTACHMENT, and ACL2 refuses to call one while computing a
; `defconst' (:DOC ignored-attachment).  Inside an assert-event top-level
; evaluation applies and the real SHA-256 runs, which is what these are for.
(defmacro au-authed ()
  '(au-after *au-after-user* "AUTHINFO PASS correct-horse"))
(assert-event (equal (fn-auth-session-subject (au-authed)) *au-principal*))
(assert-event (fn-auth-sessionp (au-authed)))
(assert-event (fn-auth-session-consistentp (au-authed) *au-archive*))

(defmacro au-principal-after-user ()
  '(fn-post-result-session
    (fn-auth-authinfo *au-s-principal-reader*
                      (list (fn-nntp-string-octets "USER") *au-name*))))
(defmacro au-principal-authed ()
  '(fn-post-result-session
    (fn-auth-authinfo (au-principal-after-user)
                      (list (fn-nntp-string-octets "PASS") *au-secret*))))
(assert-event
 (equal (fn-peer-session-peer (fn-auth-session-base (au-principal-authed)))
        "principal-peer"))
; RFC 4643 rejects every later AUTHINFO command as already authenticated.
; The principal and its derived peer therefore remain paired: neither a new
; USER nor a failing PASS can install another credential under stale peer A.
(assert-event
 (equal (fn-post-result-effects
         (fn-auth-authinfo
          (au-principal-authed)
          (list (fn-nntp-string-octets "USER")
                (fn-nntp-string-octets "guest"))))
        (au-single "502 already authenticated")))
(assert-event
 (equal (fn-peer-session-peer
         (fn-auth-session-base
          (fn-post-result-session
           (fn-auth-authinfo
            (au-principal-authed)
            (list (fn-nntp-string-octets "USER")
                  (fn-nntp-string-octets "guest"))))))
        "principal-peer"))
(assert-event
 (equal (fn-peer-session-peer
         (fn-auth-session-base
          (fn-post-result-session
           (fn-auth-authinfo
            (au-principal-authed)
            (list (fn-nntp-string-octets "PASS")
                  (fn-nntp-string-octets "wrong"))))))
        "principal-peer"))
(assert-event
 (equal (fn-auth-session-subject
         (fn-post-result-session
          (fn-auth-authinfo
           (au-principal-authed)
           (list (fn-nntp-string-octets "PASS")
                 (fn-nntp-string-octets "wrong")))))
        *au-principal*))
; Reconnect begins with no role even after an earlier connection authenticated.
(assert-event
 (null
  (fn-peer-session-peer
   (fn-auth-session-base
    (fn-auth-open-session (fn-node-acceptance *au-peer-node*) nil
                          *au-peer-node* *au-principal-peer-cfg*
                          *au-required* nil)))))
; A different authenticated account remains a reader.
(defmacro au-other-after-user ()
  '(fn-post-result-session
    (fn-auth-authinfo *au-s-principal-reader*
                      (list (fn-nntp-string-octets "USER")
                            (fn-nntp-string-octets "guest")))))
(defmacro au-other-authed ()
  '(fn-post-result-session
    (fn-auth-authinfo (au-other-after-user)
                      (list (fn-nntp-string-octets "PASS")
                            (fn-nntp-string-octets "guest-pass")))))
(assert-event
 (null (fn-peer-session-peer (fn-auth-session-base (au-other-authed)))))
; Ambiguous principal ownership fails closed as a reader.
(defconst *au-principal-peer-record-2*
  (fn-cfg-peer-make
   "principal-peer-2" "principal2.example.invalid" '(:nntp "127.0.0.1" 120)
   '("fn.*" 32768 16) nil
   (list :principal (coerce (fn-id-hex-octets *au-principal*) 'string))))
(defconst *au-principal-duplicate-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make
          0 0 1 (append *fn-cfg-default-change*
                        (list (fn-cfg-set-peer-delta *au-principal-peer-record*)
                              (fn-cfg-set-peer-delta *au-principal-peer-record-2*)))
          *fn-cfg-default-stamp*))))
(defmacro au-duplicate-session ()
  '(fn-auth-open-session (fn-node-acceptance *au-peer-node*) nil
                         *au-peer-node* *au-principal-duplicate-cfg*
                         *au-required* nil))
(defmacro au-duplicate-user ()
  '(fn-post-result-session
    (fn-auth-authinfo (au-duplicate-session)
                      (list (fn-nntp-string-octets "USER") *au-name*))))
(assert-event
 (null
  (fn-peer-session-peer
   (fn-auth-session-base
    (fn-post-result-session
     (fn-auth-authinfo (au-duplicate-user)
                       (list (fn-nntp-string-octets "PASS") *au-secret*)))))))
; STARTTLS resets authentication and the role derived from it.
(assert-event
 (null
  (fn-peer-session-peer
   (fn-auth-session-base
    (fn-post-result-session (fn-auth-starttls (au-principal-authed) nil))))))
; protected-only refuses before any role can be derived.
(assert-event
 (null
  (fn-peer-session-peer
   (fn-auth-session-base
    (fn-post-result-session
     (fn-auth-authinfo
      (fn-auth-open-session (fn-node-acceptance *au-peer-node*) nil
                            *au-peer-node* *au-principal-peer-cfg*
                            *au-protected* nil)
      (list (fn-nntp-string-octets "USER") *au-name*)))))))

; A wrong secret is 481, the session stays unauthenticated, and the cached
; name is cleared so the password cannot be retried without a fresh USER.
(assert-event (equal (au-reply *au-after-user* "AUTHINFO PASS wrong")
                     (au-single "481 authentication failed")))
(defmacro au-failed () '(au-after *au-after-user* "AUTHINFO PASS wrong"))
(assert-event (null (fn-auth-session-subject (au-failed))))
(assert-event (null (fn-auth-session-pending (au-failed))))
(assert-event (equal (au-reply (au-failed) "AUTHINFO PASS correct-horse")
                     (au-single "482 authentication commands issued out of sequence")))

; An unknown username reaches 481 and never 281: the 381 above disclosed
; nothing and the PASS is where it fails.
(assert-event (equal (au-reply (au-after *au-s-req* "AUTHINFO USER nobody")
                               "AUTHINFO PASS anything")
                     (au-single "481 authentication failed")))

; Section 2.3.1 note [2]: once authenticated the command is unavailable.
; Never 480 -- section 2.3.2 forbids it here.
(assert-event (equal (au-reply (au-authed) "AUTHINFO USER reader")
                     (au-single "502 already authenticated")))

; Section 2.4: SASL is deferred, not refused.  502, and the capability block
; never carries a SASL argument.
(assert-event (equal (au-reply *au-s-req* "AUTHINFO SASL PLAIN")
                     (au-single "502 no SASL mechanism is offered")))
(assert-event (equal (au-reply *au-s-req* "AUTHINFO")
                     (au-single "501 syntax error")))
(assert-event (equal (au-reply *au-s-req* "AUTHINFO USER")
                     (au-single "501 syntax error")))
(assert-event (equal (au-reply *au-s-req* "AUTHINFO USER a b")
                     (au-single "501 syntax error")))

; Section 2.3.2's 483: a cleartext mechanism on an unprotected connection.
(assert-event (equal (au-reply *au-s-prot* "AUTHINFO USER reader")
                     (au-single "483 a protected channel is required; use STARTTLS")))
(assert-event (equal (au-reply (au-session *au-protected* t) "AUTHINFO USER reader")
                     (au-single "381 password required")))

; -----------------------------------------------------------------------------
; RFC 4643 section 2.2: 480 before authentication, and the command is not
; performed.  The keystone, witnessed on a real command.

(assert-event (equal (au-reply *au-s-req* "GROUP fn.letters")
                     (au-single "480 authentication required")))
(assert-event (equal (au-reply *au-s-req* "POST")
                     (au-single "480 authentication required")))
(assert-event (equal (au-reply *au-s-req* "ARTICLE 1")
                     (au-single "480 authentication required")))
; Not performed: the session is untouched, so no group was selected.
(assert-event (equal (au-after *au-s-req* "GROUP fn.letters") *au-s-req*))
; ... and the wire was never offered article mode.
(assert-event (not (fn-post-offeredp (au-reply *au-s-req* "POST"))))
(assert-event (null (fn-post-result-submission (au-step *au-s-req* "POST"))))

; The control: the same commands DO run once authenticated, so the
; assertions above are not vacuous.
(assert-event (not (equal (au-reply (au-authed) "GROUP fn.letters")
                          (au-single "480 authentication required"))))
(assert-event (fn-post-offeredp (au-reply (au-authed) "POST")))
; ... and they run with no configuration requiring authentication at all.
(assert-event (not (equal (au-reply *au-s-open* "GROUP fn.letters")
                          (au-single "480 authentication required"))))

; The four commands an unauthenticated client keeps: it can still discover
; the server and still authenticate (RFC 4643 section 2.2's own reasoning).
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "CAPABILITIES"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "HELP"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "QUIT"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "AUTHINFO"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "STARTTLS"))))
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "POST")))
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "ARTICLE")))
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "XPAT")))
; Transit is authorized by the configured peer role, not AUTHINFO.  These
; three commands therefore bypass the reader gate and let the peer machine
; make its reachable offer/stream decisions.
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "IHAVE"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "CHECK"))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "TAKETHIS"))))
(assert-event (equal (au-peer-reply *au-s-peer-req*
                                    "IHAVE <auth-peer@example.invalid>")
                     (append (au-single "335 send it; end with <CR-LF>.<CR-LF>")
                             (list (fn-nntp-begin-article-effect)))))
(assert-event (equal (au-peer-reply *au-s-peer-req*
                                    "CHECK <auth-peer@example.invalid>")
                     (list (fn-nntp-reply-effect
                            (fn-nntp-crlf
                             (append (fn-nntp-string-octets "238 ")
                                     (fn-nntp-string-octets
                                      "<auth-peer@example.invalid>")))))))
(assert-event (equal (au-peer-reply *au-s-peer-req*
                                    "TAKETHIS <auth-peer@example.invalid>")
                     (list (fn-nntp-begin-article-effect))))
; The reader control is the separating witness: it has the same required
; AUTHINFO policy, no configured source role, and fn-peer-step refuses it.
(assert-event (equal (au-reply *au-s-req* "IHAVE <auth-peer@example.invalid>")
                     (au-single "502 transit is not permitted on this connection")))

; -----------------------------------------------------------------------------
; The posting allowance is the authenticated principal's

(assert-event (fn-auth-postingp (au-authed)))
(defmacro au-authed-ro ()
  '(au-after (au-after *au-s-req* "AUTHINFO USER guest")
             "AUTHINFO PASS guest-pass"))
(assert-event (equal (fn-auth-session-subject (au-authed-ro)) *au-principal-ro*))
(assert-event (not (fn-auth-postingp (au-authed-ro))))

; Teeth for fn-auth-post-without-permission-is-not-offered.
;
; The witness is reachable and non-degenerate: this principal PASSED the
; 480 gate -- it is authenticated -- and is still refused, with RFC 3977
; section 6.3.1.1's 440 and no 340 offer, so no body can follow and no
; submission can leave.
(assert-event (equal (au-reply (au-authed-ro) "POST")
                     (au-single "440 posting not permitted for this principal")))
(assert-event (not (fn-post-offeredp (au-reply (au-authed-ro) "POST"))))
(assert-event (null (fn-post-result-submission
                     (au-step (au-authed-ro) "POST"))))
(assert-event (equal (fn-post-result-session (au-step (au-authed-ro) "POST"))
                     (au-authed-ro)))
; Hypothesis (not (fn-auth-postingp as)): drop it -- the same command on the
; principal that MAY post -- and the conclusion fails, so the theorem is not
; vacuous.
(assert-event (fn-auth-postingp (au-authed)))
(assert-event (fn-post-offeredp (au-reply (au-authed) "POST")))
; Hypothesis (fn-nntp-keywordp keyword "POST"): drop it -- any other
; keyword on the same session -- and the first conjunct fails, because the
; book does not answer that command at all and delegates it.
(assert-event (null (fn-auth-command (au-authed-ro) *au-config*
                                     (fn-nntp-string-octets "HELP") nil)))
(assert-event (not (fn-auth-postingp *au-s-req*)))
; With authentication not required the connection's own configuration
; decides, exactly as before this book existed.
(assert-event (fn-auth-postingp *au-s-open*))

; -----------------------------------------------------------------------------
; RFC 4642 section 2.2: STARTTLS

; 382 and the one effect the host acts on.
(defconst *au-starttls* (au-step *au-s-req* "STARTTLS"))
(assert-event (equal (fn-post-result-effects *au-starttls*)
                     (append (au-single "382 continue with TLS negotiation")
                             (list (list :starttls)))))
(assert-event (member-equal (fn-auth-starttls-effect)
                            (fn-post-result-effects *au-starttls*)))
; RFC 4642 section 2.2 forbids pipelining STARTTLS, so 382 leaves the
; session HANDSHAKING and NOT in TLS: the host owes a handshake and
; (:tls-established) is the only transition that records the layer.
(assert-event (fn-auth-session-handshakingp
               (fn-post-result-session *au-starttls*)))
(assert-event (not (fn-auth-session-tlsp
                    (fn-post-result-session *au-starttls*))))
(assert-event
 (fn-auth-session-tlsp
  (fn-post-result-session
   (fn-auth-step (fn-post-result-session *au-starttls*) *au-archive*
                 *au-config* *au-obs* *au-obs* (list :tls-established)))))
(assert-event
 (not (fn-auth-session-handshakingp
       (fn-post-result-session
        (fn-auth-step (fn-post-result-session *au-starttls*) *au-archive*
                      *au-config* *au-obs* *au-obs* (list :tls-established))))))
; And a handshaking connection answers nothing at all.
(assert-event
 (null (fn-post-result-effects
        (fn-auth-step (fn-post-result-session *au-starttls*) *au-archive*
                      *au-config* *au-obs* *au-obs*
                      (list :command (fn-nntp-string-octets "CAPABILITIES"))))))
; Section 2.2.2: the protocol state is reset across the handshake.  Nothing
; cached before it survives.
(assert-event (null (fn-auth-session-pending
                     (fn-post-result-session
                      (au-step *au-after-user* "STARTTLS")))))
(assert-event (null (fn-auth-session-subject
                     (fn-post-result-session
                      (au-step (au-authed) "STARTTLS")))))

; Section 2.2.2: once a TLS layer is active STARTTLS is not a valid command.
; 502, never 480 or 483, and no second handshake effect.
(assert-event (equal (au-reply *au-s-req-tls* "STARTTLS")
                     (au-single "502 a TLS layer is already active")))
(assert-event (not (member-equal (fn-auth-starttls-effect)
                                 (au-reply *au-s-req-tls* "STARTTLS"))))
(assert-event (not (member-equal (fn-auth-starttls-effect)
                                 (au-reply
                                  (fn-post-result-session *au-starttls*)
                                  "STARTTLS"))))

; Section 2.2.2: unable to initiate, for a configuration reason, is 580.
(assert-event (equal (au-reply *au-s-open* "STARTTLS")
                     (au-single "580 can not initiate TLS negotiation")))
(assert-event (not (member-equal (fn-auth-starttls-effect)
                                 (au-reply *au-s-open* "STARTTLS"))))
(assert-event (equal (au-reply *au-s-req* "STARTTLS x")
                     (au-single "501 syntax error")))

; -----------------------------------------------------------------------------
; RFC 3977 section 5.2 with RFC 4642 section 2.1 and RFC 4643 section 2.1:
; the capability block in every state

(defconst *au-reader-lines*
  '("VERSION 2" "READER" "OVER MSGID" "HDR"
    "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT"
    "IMPLEMENTATION fn-nntp-lab"))
(defconst *au-reader-lines-posting*
  '("VERSION 2" "READER" "POST" "OVER MSGID" "HDR"
    "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT"
    "IMPLEMENTATION fn-nntp-lab"))

(defconst *au-peer-lines*
  '("VERSION 2" "READER" "OVER MSGID" "HDR"
    "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT"
    "IMPLEMENTATION fn-nntp-lab" "IHAVE" "STREAMING"))

; Unauthenticated, no TLS, a certificate configured: both labels.
(assert-event
 (equal (au-reply *au-s-req* "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-reader-lines*
                          '("STARTTLS" "AUTHINFO USER")))))
; Under TLS, still unauthenticated: STARTTLS gone, AUTHINFO USER kept.
(assert-event
 (equal (au-reply *au-s-req-tls* "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-reader-lines* '("AUTHINFO USER")))))
; Authenticated: AUTHINFO USER gone, POST present because this principal may
; post, STARTTLS still offered because this connection is not yet protected.
(assert-event
 (equal (au-reply (au-authed) "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-reader-lines-posting* '("STARTTLS")))))
; Authenticated as the read-only principal: no POST label.
(assert-event
 (equal (au-reply (au-authed-ro) "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-reader-lines* '("STARTTLS")))))
; No certificate and nothing required: the reader's own block, unchanged
; from before this book existed.
(assert-event
 (equal (au-reply *au-s-open* "CAPABILITIES")
        (au-block "101 capability list follows" *au-reader-lines-posting*)))
; Protected-only and unprotected: AUTHINFO USER is NOT advertised, because
; the server will not accept it now (RFC 4643 section 2.1).
(assert-event
 (equal (au-reply *au-s-prot* "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-reader-lines* '("STARTTLS")))))
; The real composed path takes its base list from the peer record pinned at
; open, then appends the access labels the reader AUTHINFO policy permits.
; The peer is unauthenticated as a reader, but its configured source role
; makes IHAVE and STREAMING honest promises.
(assert-event
 (equal (au-peer-reply *au-s-peer-req* "CAPABILITIES")
        (au-block "101 capability list follows"
                  (append *au-peer-lines* '("STARTTLS" "AUTHINFO USER")))))
; The optional keyword argument of section 5.2.1 is accepted and changes
; nothing.
(assert-event (equal (au-reply *au-s-req* "CAPABILITIES READER")
                     (au-reply *au-s-req* "CAPABILITIES")))

; -----------------------------------------------------------------------------
; Delegation: every command this book does not claim is the peer/reader
; profile, value for value.

(assert-event
 (equal (fn-post-result-effects (au-step *au-s-open* "HELP"))
        (fn-post-result-effects
         (fn-peer-step (fn-auth-session-base *au-s-open*) *au-archive*
                       *au-config* *au-obs* *au-obs*
                       (list :command (fn-nntp-string-octets "HELP"))))))
(assert-event
 (equal (fn-post-result-effects (au-step *au-s-open* "GROUP fn.letters"))
        (fn-post-result-effects
         (fn-peer-step (fn-auth-session-base *au-s-open*) *au-archive*
                       *au-config* *au-obs* *au-obs*
                       (list :command
                             (fn-nntp-string-octets "GROUP fn.letters"))))))
(assert-event
 (equal (fn-post-result-effects (au-step *au-s-open* "NOSUCHCOMMAND"))
        (fn-post-result-effects
         (fn-peer-step (fn-auth-session-base *au-s-open*) *au-archive*
                       *au-config* *au-obs* *au-obs*
                       (list :command
                             (fn-nntp-string-octets "NOSUCHCOMMAND"))))))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis
;
; fn-auth-gated-command-is-refused-and-not-performed has four hypotheses that
; can be separated by a value.

; (1) fn-auth-config-requiredp.  With it false the same command is performed:
; the group IS selected.
(assert-event (not (fn-auth-config-requiredp *au-open*)))
(assert-event (not (equal (au-after *au-s-open* "GROUP fn.letters")
                          *au-s-open*)))

; (2) (not (fn-auth-session-subject as)).  Authenticated, the same command is
; performed against the same required configuration.
(assert-event (fn-auth-session-subject (au-authed)))
(assert-event (not (equal (au-after (au-authed) "GROUP fn.letters")
                          (au-authed))))

; (3) fn-auth-restricted-keywordp.  HELP is not restricted and answers its
; own 100 block rather than 480, under the required configuration.
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "HELP"))))
(assert-event (not (equal (au-reply *au-s-req* "HELP")
                          (au-single "480 authentication required"))))

; (4) fn-nntp-command-inputp.  A line carrying NUL is not command input, so
; the step delegates and the reader's own 501 answers it, not 480.
(defconst *au-nul-line* (list 71 0 82))
(assert-event (not (fn-nntp-command-inputp *au-nul-line*)))
(assert-event (not (equal (fn-post-result-effects
                           (fn-auth-step *au-s-req* *au-archive* *au-config*
                                         *au-obs* *au-obs*
                                         (list :command *au-nul-line*)))
                          (au-single "480 authentication required"))))

; fn-auth-starttls-is-not-advertised-under-tls.  Hypothesis tlsp: with it
; false and a certificate configured, the label IS in the list, so the
; theorem is not vacuous.
(assert-event (member-equal (fn-nntp-string-octets "STARTTLS")
                            (fn-auth-capability-lines *au-required* nil nil t)))
(assert-event (not (member-equal (fn-nntp-string-octets "STARTTLS")
                                 (fn-auth-capability-lines *au-required* nil t t))))

; fn-auth-authinfo-is-not-advertised-once-authenticated.  Hypothesis subject:
; with it nil the label IS in the list.
(assert-event (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                            (fn-auth-capability-lines *au-required* nil nil t)))
(assert-event (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                 (fn-auth-capability-lines *au-required*
                                                           *au-principal* nil t))))

; fn-auth-pass-accepts-only-a-checking-secret (books/nntp-auth.lisp:1372;
; the name here was the pre-rename one and matched nothing).  Note what
; the theorem does NOT say: that a wrong secret fails is A-CRYPTO, not a
; consequence of it, so the 481 below is a witness and not a corollary.
; The separating pair: the same
; cached name with the configured secret is 281 and with any other octet
; string is 481.  A secret that differs in one octet:
(assert-event (not (equal (fn-nntp-string-octets "correct-horsf") *au-secret*)))
(assert-event (equal (au-reply *au-after-user* "AUTHINFO PASS correct-horsf")
                     (au-single "481 authentication failed")))
; ... and fn-auth-checkp itself, on a credential that is not found at all.
(assert-event (null (fn-auth-find-cred (fn-nntp-string-octets "nobody")
                                       (fn-auth-config-creds *au-required*))))
(assert-event (not (fn-auth-checkp nil *au-secret*)))
(assert-event (fn-auth-checkp *au-cred* *au-secret*))

; fn-auth-second-starttls-is-refused.  Hypothesis fn-auth-session-tlsp: with
; it false and a certificate configured the reply IS 382 with the effect.
(assert-event (not (fn-auth-session-tlsp *au-s-req*)))
(assert-event (member-equal (fn-auth-starttls-effect)
                            (fn-post-result-effects
                             (fn-auth-starttls *au-s-req* nil))))
