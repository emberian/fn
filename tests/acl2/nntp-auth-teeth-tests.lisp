; Teeth for the login gate and the protected channel (plan T7, P1).
;
; Three claims share one book because they are one property of a served
; connection, and a client meets them in this order: the greeting says what
; this connection may do, AUTHINFO is refused 483 until the channel is
; protected, and until a login succeeds every archive command is 480 and is
; not performed.
;
;   fn-auth-gated-command-is-refused-and-not-performed   (books/nntp-auth)
;   fn-auth-step-protected-only-refuses-authinfo-before-tls
;   fn-served-open-greets-200-exactly-when-the-connection-may-post
;     and fn-served-open-greeting-agrees-with-the-post-label  (books/served)
;   fn-served-open-peer-pins-the-configuration
;     and fn-served-peer-and-reader-open-under-the-same-policy
;   fn-auth-step-preserves-the-config
;   fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place
;     (K1, books/nntp-auth-invariants)
;   the three capability-label keystones over the list the CAPABILITIES arm
;     actually builds (fn-auth-capability-lines-for-peer)
;
; The subject of the first two is `fn-auth-step', which books/served.lisp
; `fn-served-dispatch' calls and which host/owner-host.lisp `fn-owner-chunk'
; reaches through `fn-own-read' and `fn-served-step'; the native host's
; socket read is host/native/owner.lisp, through the same owner entry.  The
; subject of the greeting pair is `fn-served-open', which
; host/owner-host.lisp `fn-owner-open' calls through `fn-own-open'.
;
; WHAT A TOOTH IS HERE (AGENTS.md, "Teeth ship with the theorem").  For each
; keystone: one reachable, non-degenerate witness on a real archive with a
; real credential; one `must-fail' per hypothesis, the hypothesis dropped and
; every other one kept and the original hints kept, so the failure is the
; statement's and not a theory's; and beside each `must-fail' the concrete
; value that refutes the dropped-hypothesis statement, evaluated.  Two of the
; keystones here have NO hypothesis -- they are equalities -- and for those a
; `must-fail' names the weaker statement that was true of the definition
; before the 2026-09-21 measurement repaired it (PRF-039), with the value
; that separates the two.
;
; Every expected reply is assembled here from the RFC's own response table by
; `aut-single', never by calling the function under test.

(in-package "ACL2")
(include-book "../../books/nntp-auth-invariants")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")


; -----------------------------------------------------------------------------
; The scenario: one group, one accepted article, one credential that may
; post, under three AUTHINFO policies.

(defconst *aut-groups* '("fn.letters"))
(defconst *aut-id* "<teeth@example.invalid>")
(defconst *aut-payload*
  (append (fn-nntp-string-octets "Message-ID: <teeth@example.invalid>")
          '(13 10) (fn-nntp-string-octets "Subject: teeth") '(13 10 13 10)
          (fn-nntp-string-octets "Hello") '(13 10)))
(defconst *aut-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *aut-groups*) 1 *aut-id* *aut-payload*
                      *aut-groups*)
   0 1 :durable))
(defconst *aut-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *aut-agent* (fn-nntp-string-octets "fn.example.invalid"))

; The pinned injection configuration, and the same one with posting off: the
; greeting keystone separates on exactly this bit and on fn-auth-postingp.
(defconst *aut-config*
  (fn-inj-make-config t *aut-agent*
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *aut-config-no-post*
  (fn-inj-make-config nil *aut-agent*
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(assert-event (fn-inj-config-allow *aut-config*))
(assert-event (not (fn-inj-config-allow *aut-config-no-post*)))

; The credential.  The verifier is books/auth-secret.lisp's, over a salt and
; the secret; the digest is written out because ACL2 refuses to call an
; attachment while computing a `defconst' (:DOC ignored-attachment), and the
; assert-event below re-derives it under the real SHA-256 so the literal
; cannot drift from what enrolment produces.
(defconst *aut-principal* (make-list 32 :initial-element 7))
(assert-event (fn-prin-idp *aut-principal*))
(defconst *aut-name* (fn-nntp-string-octets "reader"))
(defconst *aut-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *aut-salt* (make-list 16 :initial-element 3))
(defconst *aut-digest*
  '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
    73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194))
(defconst *aut-verifier* (fn-authsec-verifier *aut-salt* *aut-digest*))
(assert-event (equal *aut-verifier* (fn-authsec-enrol *aut-salt* *aut-secret*)))
(defconst *aut-cred*
  (fn-auth-make-cred *aut-name* *aut-principal* *aut-verifier* t))
(assert-event (fn-auth-credp *aut-cred*))
(assert-event (fn-auth-checkp *aut-cred* *aut-secret*))

(defconst *aut-open* (fn-auth-open-config))
(defconst *aut-required* (fn-auth-make-config t nil t (list *aut-cred*)))
(defconst *aut-protected* (fn-auth-make-config t t t (list *aut-cred*)))
(assert-event (fn-auth-configp *aut-open*))
(assert-event (fn-auth-configp *aut-required*))
(assert-event (fn-auth-configp *aut-protected*))
(assert-event (not (fn-auth-config-requiredp *aut-open*)))
(assert-event (fn-auth-config-requiredp *aut-required*))
(assert-event (not (fn-auth-config-protected-onlyp *aut-required*)))
(assert-event (fn-auth-config-protected-onlyp *aut-protected*))

(defun aut-session (acfg tlsp)
  (fn-auth-open-session *aut-archive* nil nil nil acfg tlsp))
(defconst *aut-s-open* (aut-session *aut-open* nil))
(defconst *aut-s-req* (aut-session *aut-required* nil))
(defconst *aut-s-prot* (aut-session *aut-protected* nil))
(defconst *aut-s-prot-tls* (aut-session *aut-protected* t))
(assert-event (fn-auth-sessionp *aut-s-req*))
(assert-event (fn-auth-sessionp *aut-s-prot*))
(assert-event (null (fn-auth-session-subject *aut-s-req*)))
(assert-event (not (fn-auth-session-handshakingp *aut-s-req*)))
(assert-event (not (fn-auth-session-tlsp *aut-s-prot*)))
(assert-event (equal (fn-auth-session-tlsp *aut-s-prot-tls*) t))

(defun aut-step (as text)
  (fn-auth-step as *aut-archive* *aut-config* *aut-obs* *aut-obs*
                (list :command (fn-nntp-string-octets text))))
(defun aut-reply (as text)
  (fn-post-result-effects (aut-step as text)))
(defun aut-after (as text)
  (fn-post-result-session (aut-step as text)))

; The expected replies, assembled from the RFC's table with their own CRLFs.
(defun aut-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))

(defconst *aut-480* "480 authentication required")
(defconst *aut-483* "483 a protected channel is required; use STARTTLS")

; An authenticated session, as a macro: the accepting branch runs
; fn-authsec-checkp, whose digest is an ATTACHMENT, and ACL2 will not call
; one while computing a `defconst'.  Inside an assert-event top-level
; evaluation applies and the real SHA-256 runs.
(defconst *aut-after-user* (aut-after *aut-s-req* "AUTHINFO USER reader"))
(defmacro aut-authed ()
  '(aut-after *aut-after-user* "AUTHINFO PASS correct-horse"))
(assert-event (equal (fn-auth-session-subject (aut-authed)) *aut-principal*))
(assert-event (fn-auth-sessionp (aut-authed)))

; -----------------------------------------------------------------------------
; KEYSTONE 1: fn-auth-gated-command-is-refused-and-not-performed
;
;   (implies (and (fn-auth-sessionp as)                                    ; H1
;                 (not (fn-auth-session-handshakingp as))                  ; H2
;                 (fn-auth-config-requiredp (fn-auth-session-config as))   ; H3
;                 (not (fn-auth-session-subject as))                       ; H4
;                 (fn-nntp-command-inputp line)                            ; H5
;                 (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)) ; H6
;                 (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line)))) ; H7
;            (and (null       ... submission)
;                 (not (fn-post-offeredp ... effects))
;                 (equal      ... session) as)
;                 (equal      ... effects) (fn-auth-single as "480 ...")))

; The witness is reachable and non-degenerate: the archive HOLDS fn.letters
; with one article in it, so the refused GROUP is a command that would have
; done something, and the same command on the same connection once
; authenticated does do it.
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "GROUP")))
(assert-event (equal (aut-reply *aut-s-req* "GROUP fn.letters")
                     (aut-single *aut-480*)))
(assert-event (equal (aut-after *aut-s-req* "GROUP fn.letters") *aut-s-req*))
(assert-event (not (fn-post-offeredp (aut-reply *aut-s-req* "POST"))))
(assert-event (null (fn-post-result-submission (aut-step *aut-s-req* "POST"))))
(assert-event (equal (aut-reply *aut-s-req* "ARTICLE 1")
                     (aut-single *aut-480*)))
; Non-degenerate: authenticated, the very same command selects the group.
(assert-event (not (equal (aut-reply (aut-authed) "GROUP fn.letters")
                          (aut-single *aut-480*))))
(assert-event (not (equal (aut-after (aut-authed) "GROUP fn.letters")
                          (aut-authed))))

; H1 dropped.  A value of the session's shape whose base is not a peer
; session: `fn-auth-sessionp' refuses it, so `fn-auth-step' answers with the
; empty result and the effect list is NOT the 480 line.  Every other
; hypothesis holds of it -- the configuration requires authentication, no
; subject is installed and it is not handshaking.
(defconst *aut-forged*
  (fn-auth-make-session :not-a-peer-session *aut-required* nil nil nil nil))
(assert-event (not (fn-auth-sessionp *aut-forged*)))
(assert-event (fn-auth-config-requiredp (fn-auth-session-config *aut-forged*)))
(assert-event (null (fn-auth-session-subject *aut-forged*)))
(assert-event (not (fn-auth-session-handshakingp *aut-forged*)))
(assert-event (equal (aut-reply *aut-forged* "GROUP fn.letters") nil))
(assert-event (not (equal (aut-reply *aut-forged* "GROUP fn.letters")
                          (aut-single *aut-480*))))

(local
 (must-fail
  (defthm aut-gate-without-sessionp
    (implies (and (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H2 dropped.  After a 382 the connection is HANDSHAKING: RFC 4642 section
; 2.2 says the octets behind the command line are handshake bytes, so the
; step answers nothing at all rather than 480.
(defconst *aut-s-handshaking* (aut-after *aut-s-req* "STARTTLS"))
(assert-event (fn-auth-session-handshakingp *aut-s-handshaking*))
(assert-event (fn-auth-sessionp *aut-s-handshaking*))
(assert-event (fn-auth-config-requiredp
               (fn-auth-session-config *aut-s-handshaking*)))
(assert-event (null (fn-auth-session-subject *aut-s-handshaking*)))
(assert-event (equal (aut-reply *aut-s-handshaking* "GROUP fn.letters") nil))

(local
 (must-fail
  (defthm aut-gate-without-not-handshaking
    (implies (and (fn-auth-sessionp as)
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H3 dropped.  With no policy requiring a login the same command runs and the
; group IS selected, which is what the gate is for.
(assert-event (not (equal (aut-reply *aut-s-open* "GROUP fn.letters")
                          (aut-single *aut-480*))))
(assert-event (not (equal (aut-after *aut-s-open* "GROUP fn.letters")
                          *aut-s-open*)))

(local
 (must-fail
  (defthm aut-gate-without-required
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H4 dropped.  Authenticated under the SAME required configuration, the
; command runs: the gate is the missing subject and not the policy alone.
(assert-event (fn-auth-session-subject (aut-authed)))
(assert-event (not (equal (aut-reply (aut-authed) "ARTICLE 1")
                          (aut-single *aut-480*))))

(local
 (must-fail
  (defthm aut-gate-without-no-subject
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H5 dropped, and this is the one that needs a value built on purpose.  A
; line over RFC 3977 section 3.1's 512-octet limit
; (*fn-nntp-max-command-octets*, 510 without the CRLF) is not command input,
; so the step delegates and the reader's own preflight answers, not the gate
; -- while the line still tokenizes to GROUP with two arguments, each of
; them inside the 497-octet argument limit, so H6 and H7 both hold of it.
(defconst *aut-over-long-line*
  (append (fn-nntp-string-octets "GROUP ")
          (make-list 490 :initial-element 97)
          '(32)
          (make-list 30 :initial-element 98)))
(assert-event (equal (len *aut-over-long-line*) 527))
(assert-event (not (fn-nntp-command-inputp *aut-over-long-line*)))
(assert-event (fn-nntp-command-arguments-at-mostp
               (fn-nntp-tokenize *aut-over-long-line*)))
(assert-event (fn-auth-restricted-keywordp
               (car (fn-nntp-tokenize *aut-over-long-line*))))
(assert-event (not (equal (fn-post-result-effects
                           (fn-auth-step *aut-s-req* *aut-archive* *aut-config*
                                         *aut-obs* *aut-obs*
                                         (list :command *aut-over-long-line*)))
                          (aut-single *aut-480*))))

(local
 (must-fail
  (defthm aut-gate-without-command-inputp
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H6 dropped.  A line INSIDE the 510-octet command limit whose single
; argument is over the 497-octet argument limit: command input, a restricted
; keyword, and still not the gate's -- the argument preflight refuses it
; first.
(defconst *aut-over-long-argument-line*
  (append (fn-nntp-string-octets "GROUP ")
          (make-list 498 :initial-element 97)))
(assert-event (equal (len *aut-over-long-argument-line*) 504))
(assert-event (fn-nntp-command-inputp *aut-over-long-argument-line*))
(assert-event (not (fn-nntp-command-arguments-at-mostp
                    (fn-nntp-tokenize *aut-over-long-argument-line*))))
(assert-event (fn-auth-restricted-keywordp
               (car (fn-nntp-tokenize *aut-over-long-argument-line*))))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-auth-step *aut-s-req* *aut-archive* *aut-config*
                            *aut-obs* *aut-obs*
                            (list :command *aut-over-long-argument-line*)))
             (aut-single *aut-480*))))

(local
 (must-fail
  (defthm aut-gate-without-arguments-at-most
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-inputp line)
                  (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; H7 dropped.  HELP is not restricted -- RFC 4643 section 2.2's own
; reasoning is that a client must still be able to discover the server and
; still authenticate -- so under the same required policy it answers its own
; block and not 480.
(assert-event (not (fn-auth-restricted-keywordp
                    (fn-nntp-string-octets "HELP"))))
(assert-event (not (equal (aut-reply *aut-s-req* "HELP")
                          (aut-single *aut-480*))))

(local
 (must-fail
  (defthm aut-gate-without-restricted-keyword
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-requiredp (fn-auth-session-config as))
                  (not (fn-auth-session-subject as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single as "480 authentication required")))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                              fn-auth-tls-eventp fn-post-offeredp)
                             (fn-peer-step fn-auth-delegate fn-auth-single
                              fn-auth-restricted-keywordp fn-auth-sessionp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp
                              fn-nntp-command-arguments-at-mostp
                              fn-nntp-begin-article-effect)))))))

; The two hypotheses that are NOT here, and why.  The keystone used to carry
; `(consp (fn-nntp-tokenize line))' and
; `(fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))'.  No value
; violates either while H7 holds, so neither has a `must-fail' case; rather
; than leave two hypotheses with no tooth, books/nntp-auth.lisp proves
; `fn-auth-restricted-keyword-is-a-keyword-token' and drops them.  The fact
; itself, and the reason a restricted keyword's token is never empty:
(assert-event (fn-nntp-keyword-tokenp (fn-nntp-string-octets "GROUP")))
(assert-event (not (fn-auth-restricted-keywordp nil)))

; -----------------------------------------------------------------------------
; KEYSTONE 2: fn-auth-step-protected-only-refuses-authinfo-before-tls
;
;   (implies (and (fn-auth-sessionp as)                                     ; G1
;                 (not (fn-auth-session-handshakingp as))                   ; G2
;                 (not (fn-auth-session-subject as))                        ; G3
;                 (fn-auth-config-protected-onlyp (fn-auth-session-config as)) ; G4
;                 (not (fn-auth-session-tlsp as))                           ; G5
;                 (fn-nntp-command-inputp line)                             ; G6
;                 (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)) ; G7
;                 (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO")) ; G8
;            (and (equal ... effects) (fn-auth-single as "483 ..."))
;                 (equal ... session)  as)
;                 (null  ... submission)))
;
; The witness is non-degenerate: the name below IS the configured one and the
; secret below IS the enrolled one, so the 483 is a refusal of a login that
; would otherwise succeed, and the same exchange over TLS does succeed.

(assert-event (equal (aut-reply *aut-s-prot* "AUTHINFO USER reader")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-reply *aut-s-prot* "AUTHINFO PASS correct-horse")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-after *aut-s-prot* "AUTHINFO USER reader")
                     *aut-s-prot*))
(assert-event (null (fn-post-result-submission
                     (aut-step *aut-s-prot* "AUTHINFO USER reader"))))
; Nothing was cached, so a PASS behind the refused USER is still 483 and not
; 481: the secret is never compared on this channel.
(assert-event (null (fn-auth-session-pending
                     (aut-after *aut-s-prot* "AUTHINFO USER reader"))))
; Over TLS, the same policy and the same credential: 381 then 281.
(assert-event (equal (aut-reply *aut-s-prot-tls* "AUTHINFO USER reader")
                     (aut-single "381 password required")))
(defconst *aut-prot-after-user*
  (aut-after *aut-s-prot-tls* "AUTHINFO USER reader"))
(assert-event (equal (aut-reply *aut-prot-after-user* "AUTHINFO PASS correct-horse")
                     (aut-single "281 authentication accepted")))

; G1 dropped: the forged session again, now under the protected-only policy.
(defconst *aut-forged-prot*
  (fn-auth-make-session :not-a-peer-session *aut-protected* nil nil nil nil))
(assert-event (not (fn-auth-sessionp *aut-forged-prot*)))
(assert-event (fn-auth-config-protected-onlyp
               (fn-auth-session-config *aut-forged-prot*)))
(assert-event (equal (aut-reply *aut-forged-prot* "AUTHINFO USER reader") nil))

(local
 (must-fail
  (defthm aut-483-without-sessionp
    (implies (and (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G2 dropped: a handshaking connection answers nothing, not 483.
(defconst *aut-s-prot-handshaking* (aut-after *aut-s-prot* "STARTTLS"))
(assert-event (fn-auth-session-handshakingp *aut-s-prot-handshaking*))
(assert-event (equal (aut-reply *aut-s-prot-handshaking* "AUTHINFO USER reader")
                     nil))

(local
 (must-fail
  (defthm aut-483-without-not-handshaking
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G3 dropped: an authenticated connection is 502 (section 2.3.1 note [2]),
; never 483 and never 480.
(defmacro aut-prot-authed ()
  '(aut-after *aut-prot-after-user* "AUTHINFO PASS correct-horse"))
(assert-event (fn-auth-session-subject (aut-prot-authed)))
(assert-event (equal (aut-reply (aut-prot-authed) "AUTHINFO USER reader")
                     (aut-single "502 already authenticated")))

(local
 (must-fail
  (defthm aut-483-without-no-subject
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G4 dropped: the required-but-not-protected policy answers 381 on the same
; cleartext connection, which is the whole point of the protected-only bit.
(assert-event (equal (aut-reply *aut-s-req* "AUTHINFO USER reader")
                     (aut-single "381 password required")))

(local
 (must-fail
  (defthm aut-483-without-protected-only
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G5 dropped: with a TLS layer the same protected-only policy answers 381.
(assert-event (not (equal (aut-reply *aut-s-prot-tls* "AUTHINFO USER reader")
                          (aut-single *aut-483*))))

(local
 (must-fail
  (defthm aut-483-without-not-tls
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G6 dropped: an over-long AUTHINFO line is refused by the command preflight
; before the policy is read.
(defconst *aut-authinfo-over-long-line*
  (append (fn-nntp-string-octets "AUTHINFO USER ")
          (make-list 480 :initial-element 97)
          '(32)
          (make-list 30 :initial-element 98)))
(assert-event (not (fn-nntp-command-inputp *aut-authinfo-over-long-line*)))
(assert-event (fn-nntp-command-arguments-at-mostp
               (fn-nntp-tokenize *aut-authinfo-over-long-line*)))
(assert-event (fn-nntp-keywordp
               (car (fn-nntp-tokenize *aut-authinfo-over-long-line*))
               "AUTHINFO"))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-auth-step *aut-s-prot* *aut-archive* *aut-config*
                            *aut-obs* *aut-obs*
                            (list :command *aut-authinfo-over-long-line*)))
             (aut-single *aut-483*))))

(local
 (must-fail
  (defthm aut-483-without-command-inputp
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G7 dropped: an AUTHINFO line inside the command limit whose argument is
; over the argument limit.  The variant keyword is left off, because
; "AUTHINFO USER " plus an argument over 497 octets is already over the
; 510-octet command limit and would drop G6 as well.
(defconst *aut-authinfo-over-long-argument-line*
  (append (fn-nntp-string-octets "AUTHINFO ")
          (make-list 498 :initial-element 97)))
(assert-event (equal (len *aut-authinfo-over-long-argument-line*) 507))
(assert-event (fn-nntp-command-inputp *aut-authinfo-over-long-argument-line*))
(assert-event (fn-nntp-keywordp
               (car (fn-nntp-tokenize *aut-authinfo-over-long-argument-line*))
               "AUTHINFO"))
(assert-event (not (fn-nntp-command-arguments-at-mostp
                    (fn-nntp-tokenize *aut-authinfo-over-long-argument-line*))))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-auth-step *aut-s-prot* *aut-archive* *aut-config*
                            *aut-obs* *aut-obs*
                            (list :command *aut-authinfo-over-long-argument-line*)))
             (aut-single *aut-483*))))

(local
 (must-fail
  (defthm aut-483-without-arguments-at-most
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; G8 dropped: STARTTLS is the command a client is SUPPOSED to send on this
; channel, and it is answered 382 and not 483.  So is CAPABILITIES, which is
; how the client learns that AUTHINFO is not on offer yet.
(assert-event (not (equal (aut-reply *aut-s-prot* "STARTTLS")
                          (aut-single *aut-483*))))
(assert-event (not (equal (aut-reply *aut-s-prot* "CAPABILITIES")
                          (aut-single *aut-483*))))

(local
 (must-fail
  (defthm aut-483-without-the-authinfo-keyword
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
             (equal (fn-post-result-effects
                     (fn-auth-step as archive config observation injection
                                   (list :command line)))
                    (fn-auth-single
                     as "483 a protected channel is required; use STARTTLS")))
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
                              fn-nntp-command-arguments-at-mostp)))))))

; -----------------------------------------------------------------------------
; KEYSTONE 3: the capability labels, on the list the CAPABILITIES arm builds
;
; fn-auth-starttls-is-not-advertised-under-tls-on-any-connection and
; fn-auth-authinfo-is-not-advertised-once-authenticated-on-any-connection are
; over fn-auth-capability-lines-for-peer, which is what fn-auth-command puts
; in the 101 block; fn-auth-capability-lines is its `record' = nil instance.
; A peer record is built here because that is the argument the reader-facing
; entry cannot reach, and it is the one PRF-039 found every client arriving
; under on a box with a loopback peer.

(defconst *aut-peer-record*
  (fn-cfg-peer-make "transit" "transit.example.invalid"
                    '(:nntp "127.0.0.1" 119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(assert-event (fn-cfg-peerp *aut-peer-record*))
(assert-event (fn-cfg-peer-inbound *aut-peer-record*))

; Hypothesis tlsp dropped: with no TLS layer and a certificate configured the
; STARTTLS label IS in the list -- on a reader's and on a peer's alike -- so
; neither statement is vacuous.
(assert-event (member-equal (fn-nntp-string-octets "STARTTLS")
                            (fn-auth-capability-lines-for-peer
                             *aut-required* nil nil t nil)))
(assert-event (member-equal (fn-nntp-string-octets "STARTTLS")
                            (fn-auth-capability-lines-for-peer
                             *aut-required* nil nil t *aut-peer-record*)))
(assert-event (not (member-equal (fn-nntp-string-octets "STARTTLS")
                                 (fn-auth-capability-lines-for-peer
                                  *aut-required* nil t t *aut-peer-record*))))

(local
 (must-fail
  (defthm aut-starttls-never-advertised
    (not (member-equal (fn-nntp-string-octets "STARTTLS")
                       (fn-auth-capability-lines-for-peer
                        acfg subject tlsp postingp record)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-capability-lines-for-peer
                              fn-auth-access-capability-lines
                              fn-peer-capability-lines
                              fn-nntp-capability-lines)
                             (fn-auth-config-tls-availablep
                              fn-auth-config-protected-onlyp
                              fn-auth-config-creds
                              fn-cfg-peer-inbound)))))))

; Hypothesis subject dropped: unauthenticated, with a credential configured
; and the channel the policy permits, AUTHINFO USER IS advertised.
(assert-event (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                            (fn-auth-capability-lines-for-peer
                             *aut-required* nil nil t *aut-peer-record*)))
(assert-event (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                 (fn-auth-capability-lines-for-peer
                                  *aut-required* *aut-principal* nil t
                                  *aut-peer-record*))))

(local
 (must-fail
  (defthm aut-authinfo-never-advertised
    (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                       (fn-auth-capability-lines-for-peer
                        acfg subject tlsp postingp record)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-capability-lines-for-peer
                              fn-auth-access-capability-lines
                              fn-peer-capability-lines
                              fn-nntp-capability-lines)
                             (fn-auth-config-tls-availablep
                              fn-auth-config-protected-onlyp
                              fn-auth-config-creds
                              fn-cfg-peer-inbound)))))))

; fn-auth-authinfo-is-not-advertised-before-tls-under-protected-only, one
; per hypothesis.  Protected-only dropped: the required policy advertises it
; on the same cleartext channel.  `(not tlsp)' dropped: the same protected
; policy advertises it once TLS is up.
(assert-event (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                            (fn-auth-capability-lines-for-peer
                             *aut-required* nil nil t *aut-peer-record*)))
(assert-event (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                            (fn-auth-capability-lines-for-peer
                             *aut-protected* nil t t *aut-peer-record*)))
(assert-event (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                 (fn-auth-capability-lines-for-peer
                                  *aut-protected* nil nil t
                                  *aut-peer-record*))))

(local
 (must-fail
  (defthm aut-authinfo-not-advertised-under-protected-only-alone
    (implies (fn-auth-config-protected-onlyp acfg)
             (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                (fn-auth-capability-lines-for-peer
                                 acfg subject tlsp postingp record))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-capability-lines-for-peer
                              fn-auth-access-capability-lines
                              fn-peer-capability-lines
                              fn-nntp-capability-lines)
                             (fn-auth-config-tls-availablep
                              fn-auth-config-protected-onlyp
                              fn-auth-config-creds
                              fn-cfg-peer-inbound)))))))

(local
 (must-fail
  (defthm aut-authinfo-not-advertised-before-tls-alone
    (implies (not tlsp)
             (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                (fn-auth-capability-lines-for-peer
                                 acfg subject tlsp postingp record))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-auth-capability-lines-for-peer
                              fn-auth-access-capability-lines
                              fn-peer-capability-lines
                              fn-nntp-capability-lines)
                             (fn-auth-config-tls-availablep
                              fn-auth-config-protected-onlyp
                              fn-auth-config-creds
                              fn-cfg-peer-inbound)))))))

; The unfold that makes the three claims above claims about what a client
; sees: on a CAPABILITIES command the step's whole effect list is the 101
; block over exactly that list.  Witnessed on the required policy, where the
; block is not the ground reader list.
(assert-event
 (equal (aut-reply *aut-s-req* "CAPABILITIES")
        (fn-nntp-result-effects
         (fn-nntp-multi (fn-auth-reader-session *aut-s-req*)
                        "101 capability list follows"
                        (fn-auth-capability-lines-for-peer
                         (fn-auth-session-config *aut-s-req*)
                         (fn-auth-session-subject *aut-s-req*)
                         (fn-auth-session-tlsp *aut-s-req*)
                         (and (fn-inj-config-allow *aut-config*)
                              (fn-auth-postingp *aut-s-req*))
                         (fn-auth-peer-record *aut-s-req*))))))

; -----------------------------------------------------------------------------
; KEYSTONE 4: the greeting (PRF-039)
;
;   fn-served-open-greets-200-exactly-when-the-connection-may-post
;     (equal (equal (effects of fn-served-open) (list (reply 200-line)))
;            (and (fn-inj-config-allow config)
;                 (fn-auth-postingp (fn-auth-open-session ... acfg nil))
;                 t))
;
; It has no hypothesis: it is an equality between two booleans, so a tooth
; is a value that separates them, and the `must-fail' is the WEAKER equality
; that was true of the definition before 2026-09-21 -- the greeting read the
; injection configuration alone, so a node under a policy requiring a login
; greeted 200 and then answered POST 480, against section 5.1.2's MUST.

(defun aut-open-effects (config acfg)
  (fn-served-result-effects
   (fn-served-open *aut-archive* 510 8192 config *aut-obs* *aut-obs* acfg)))
(defconst *aut-greet-200*
  (list (fn-nntp-reply-effect *fn-served-greeting-posting*)))
(defconst *aut-greet-201*
  (list (fn-nntp-reply-effect *fn-served-greeting*)))
(assert-event (not (equal *aut-greet-200* *aut-greet-201*)))

; Both sides true: posting allowed and nothing required, so 200.
(assert-event (fn-auth-postingp (aut-session *aut-open* nil)))
(assert-event (equal (aut-open-effects *aut-config* *aut-open*)
                     *aut-greet-200*))
; The separating value, and the defect: the injection configuration allows
; posting, but the policy requires a login the connection has not made, so
; fn-auth-postingp is false and the greeting MUST be 201.
(assert-event (fn-inj-config-allow *aut-config*))
(assert-event (not (fn-auth-postingp (aut-session *aut-required* nil))))
(assert-event (equal (aut-open-effects *aut-config* *aut-required*)
                     *aut-greet-201*))
; And the other side of the conjunction: posting off in the injection
; configuration is 201 whatever the policy says.
(assert-event (equal (aut-open-effects *aut-config-no-post* *aut-open*)
                     *aut-greet-201*))

(local
 (must-fail
  (defthm aut-greeting-from-the-injection-configuration-alone
    (equal (equal (fn-served-result-effects
                   (fn-served-open archive line-limit body-limit config
                                   observation injection acfg))
                  (list (fn-nntp-reply-effect *fn-served-greeting-posting*)))
           (and (fn-inj-config-allow config) t))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-served-open fn-served-greeting
                              fn-served-make-result fn-served-result-effects)
                             (fn-auth-postingp fn-auth-open-session
                              fn-inj-config-allow
                              fn-auth-open-session-is-consistent)))))))

; fn-served-open-greeting-agrees-with-the-post-label, the corollary over the
; label rather than over the bit.  Its teeth are the same three
; configurations read on the other side: the POST label is in the block
; exactly where the greeting is 200.
(defun aut-open-label (config acfg)
  (member-equal
   (fn-nntp-string-octets "POST")
   (fn-auth-capability-lines
    (fn-auth-session-config (fn-auth-open-session *aut-archive* nil nil nil
                                                  acfg nil))
    (fn-auth-session-subject (fn-auth-open-session *aut-archive* nil nil nil
                                                   acfg nil))
    (fn-auth-session-tlsp (fn-auth-open-session *aut-archive* nil nil nil
                                                acfg nil))
    (and (fn-inj-config-allow config)
         (fn-auth-postingp (fn-auth-open-session *aut-archive* nil nil nil
                                                 acfg nil))))))
(assert-event (and (aut-open-label *aut-config* *aut-open*) t))
(assert-event (not (aut-open-label *aut-config* *aut-required*)))
(assert-event (not (aut-open-label *aut-config-no-post* *aut-open*)))

; -----------------------------------------------------------------------------
; KEYSTONE 5: one policy for a peer connection and the reader beside it
;
;   fn-served-open-peer-pins-the-configuration
;     (equal (pinned config) (if (fn-auth-configp acfg) acfg (fn-auth-open-config)))
;   fn-served-peer-and-reader-open-under-the-same-policy
;     (equal (pinned config of the peer open) (pinned config of the reader open))
;
; No hypothesis again.  The `must-fail' is the pre-repair definition's own
; equality -- the peer open pinned the literal `(fn-auth-open-config)' -- and
; the separating value is the operator's required policy, under which the
; whole gate above answers one way for a reader and, before the repair,
; another way for a client the owner had resolved to a peer record.

(defconst *aut-peer-node* (fn-node-initial-state '("fn.letters") 1048576))
(defconst *aut-peer-cfg*
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make
          0 0 1 (append *fn-cfg-default-change*
                        (list (fn-cfg-set-peer-delta *aut-peer-record*)))
          *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *aut-peer-cfg*))

(defun aut-peer-open-config (acfg)
  (fn-auth-session-config
   (fn-served-conn-session
    (fn-served-result-conn
     (fn-served-open-peer *aut-archive* 510 8192 *aut-config* *aut-obs*
                          *aut-obs* "transit" *aut-peer-node* *aut-peer-cfg*
                          acfg)))))
(defun aut-reader-open-config (acfg)
  (fn-auth-session-config
   (fn-served-conn-session
    (fn-served-result-conn
     (fn-served-open *aut-archive* 510 8192 *aut-config* *aut-obs* *aut-obs*
                     acfg)))))

; Both arms of the `if', and the one that matters: a real configuration is
; pinned as it stands, and the two opens agree.
(assert-event (equal (aut-peer-open-config *aut-required*) *aut-required*))
(assert-event (equal (aut-peer-open-config *aut-protected*) *aut-protected*))
(assert-event (equal (aut-peer-open-config 17) (fn-auth-open-config)))
(assert-event (equal (aut-peer-open-config *aut-required*)
                     (aut-reader-open-config *aut-required*)))
(assert-event (equal (aut-peer-open-config 17)
                     (aut-reader-open-config 17)))
; Non-degenerate: the operator's policy is NOT the open one, so the equality
; above is not two ways of writing the same constant.
(assert-event (not (equal *aut-required* (fn-auth-open-config))))
; And what the difference is worth on the wire: under the pinned policy a
; peer-opened connection meets the same 480 gate a reader does.
(assert-event
 (equal (fn-post-result-effects
         (fn-auth-step
          (fn-served-conn-session
           (fn-served-result-conn
            (fn-served-open-peer *aut-archive* 510 8192 *aut-config* *aut-obs*
                                 *aut-obs* "transit" *aut-peer-node*
                                 *aut-peer-cfg* *aut-required*)))
          *aut-archive* *aut-config* *aut-obs* *aut-obs*
          (list :command (fn-nntp-string-octets "ARTICLE 1"))))
        (aut-single *aut-480*)))

(local
 (must-fail
  (defthm aut-peer-open-pins-the-open-config
    (equal (fn-auth-session-config
            (fn-served-conn-session
             (fn-served-result-conn
              (fn-served-open-peer archive line-limit body-limit config
                                   observation injection peer node cfg acfg))))
           (fn-auth-open-config))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-served-open-peer fn-auth-open-session)
                             (fn-auth-configp fn-auth-open-config
                              fn-peer-open-session)))))))

; -----------------------------------------------------------------------------
; KEYSTONE 6: the policy the connection was opened under does not move
;
;   fn-auth-step-preserves-the-config
;     (equal (fn-auth-session-config (session of the step)) 
;            (fn-auth-session-config as))
;
; No hypothesis, so the tooth is a witness that the equality is not two ways
; of writing the same constant and that it survives the transitions that DO
; write the session: a cached username, a login, the handshake, and a
; command this book delegates.

(assert-event (equal (fn-auth-session-config *aut-s-req*) *aut-required*))
(assert-event (not (equal *aut-required* (fn-auth-open-config))))
(assert-event (equal (fn-auth-session-config *aut-after-user*) *aut-required*))
(assert-event (equal (fn-auth-session-config (aut-authed)) *aut-required*))
(assert-event (equal (fn-auth-session-config *aut-s-handshaking*)
                     *aut-required*))
(assert-event (equal (fn-auth-session-config
                      (aut-after (aut-authed) "GROUP fn.letters"))
                     *aut-required*))
(assert-event (equal (fn-auth-session-config
                      (fn-post-result-session
                       (fn-auth-step *aut-s-handshaking* *aut-archive*
                                     *aut-config* *aut-obs* *aut-obs*
                                     (list :tls-established))))
                     *aut-required*))
; Non-degenerate the other way: the sessions above really are different
; values, so the equality is about a field and not about a fixed point.
(assert-event (not (equal (aut-authed) *aut-s-req*)))
(assert-event (not (equal *aut-s-handshaking* *aut-s-req*)))

; -----------------------------------------------------------------------------
; KEYSTONE 7: K1, a refused POST does not touch the framing
;   (books/nntp-auth-invariants.lisp)
;
;   (implies (and (fn-served-connp conn)                                    ; K1a
;                 (not (fn-auth-session-handshakingp
;                       (fn-served-conn-session conn)))                     ; K1b
;                 (not (fn-auth-postingp (fn-served-conn-session conn)))    ; K1c
;                 (fn-served-post-command-eventp event))                    ; K1d
;            (and (equal (wire after) (wire before))
;                 (equal (session after) (session before))
;                 (null (submission of the effects))))
;
; This is the theorem that carries the gate to the dispatcher: a POST the
; auth layer refused leaves the wire in command mode, so no body can follow
; and a submission has nowhere to come from.

(defconst *aut-post-event*
  (list :command (fn-nntp-string-octets "POST")))
(assert-event (fn-served-post-command-eventp *aut-post-event*))

(defconst *aut-conn-req*
  (fn-served-result-conn
   (fn-served-open *aut-archive* 510 8192 *aut-config* *aut-obs* *aut-obs*
                   *aut-required*)))
(defconst *aut-conn-open*
  (fn-served-result-conn
   (fn-served-open *aut-archive* 510 8192 *aut-config* *aut-obs* *aut-obs*
                   *aut-open*)))
(assert-event (fn-served-connp *aut-conn-req*))
(assert-event (fn-served-connp *aut-conn-open*))
(assert-event (not (fn-auth-postingp (fn-served-conn-session *aut-conn-req*))))
(assert-event (fn-auth-postingp (fn-served-conn-session *aut-conn-open*)))

; The witness: refused, the wire and the session are the ones the command
; arrived on and no submission leaves.
(assert-event (equal (fn-served-conn-wire
                      (fn-served-result-conn
                       (fn-served-dispatch *aut-conn-req* *aut-post-event*)))
                     (fn-served-conn-wire *aut-conn-req*)))
(assert-event (equal (fn-served-conn-session
                      (fn-served-result-conn
                       (fn-served-dispatch *aut-conn-req* *aut-post-event*)))
                     (fn-served-conn-session *aut-conn-req*)))
(assert-event (null (fn-served-submission
                     (fn-served-result-effects
                      (fn-served-dispatch *aut-conn-req* *aut-post-event*)))))
; Non-degenerate, and it is K1c that separates: the same event on a
; connection whose policy permits posting DOES switch the wire into article
; mode, so the theorem is about the refusal and not about fn-served-dispatch
; never touching a wire.
(assert-event (not (equal (fn-served-conn-wire
                           (fn-served-result-conn
                            (fn-served-dispatch *aut-conn-open*
                                                *aut-post-event*)))
                          (fn-served-conn-wire *aut-conn-open*))))

(local
 (must-fail
  (defthm aut-k1-without-not-posting
    (implies (and (fn-served-connp conn)
                  (not (fn-auth-session-handshakingp
                        (fn-served-conn-session conn)))
                  (fn-served-post-command-eventp event))
             (equal (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-dispatch conn event)))
                    (fn-served-conn-wire conn)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-served-dispatch fn-served-post-command-eventp)
                             (fn-auth-step fn-auth-sessionp fn-auth-postingp
                              fn-wire-begin-article fn-post-offeredp
                              fn-served-submission fn-served-connp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp fn-nntp-keywordp
                              fn-nntp-command-arguments-at-mostp)))))))

; K1d dropped.  An IHAVE line is a command event this predicate does not
; admit, and on a connection the owner resolved to a peer record it reaches
; fn-peer-step, which offers 335 and switches the wire -- the same wire the
; theorem says a refused POST leaves alone.
(defconst *aut-peer-conn*
  (fn-served-result-conn
   (fn-served-open-peer *aut-archive* 510 8192 *aut-config* *aut-obs*
                        *aut-obs* "transit" *aut-peer-node* *aut-peer-cfg*
                        *aut-required*)))
(defconst *aut-ihave-event*
  (list :command
        (fn-nntp-string-octets "IHAVE <fresh-teeth@example.invalid>")))
(assert-event (fn-served-connp *aut-peer-conn*))
(assert-event (not (fn-served-post-command-eventp *aut-ihave-event*)))
(assert-event (not (fn-auth-postingp (fn-served-conn-session *aut-peer-conn*))))
(assert-event (not (equal (fn-served-conn-wire
                           (fn-served-result-conn
                            (fn-served-dispatch *aut-peer-conn*
                                                *aut-ihave-event*)))
                          (fn-served-conn-wire *aut-peer-conn*))))

(local
 (must-fail
  (defthm aut-k1-without-the-post-command-event
    (implies (and (fn-served-connp conn)
                  (not (fn-auth-session-handshakingp
                        (fn-served-conn-session conn)))
                  (not (fn-auth-postingp (fn-served-conn-session conn))))
             (equal (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-dispatch conn event)))
                    (fn-served-conn-wire conn)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fn-served-dispatch fn-served-post-command-eventp)
                             (fn-auth-step fn-auth-sessionp fn-auth-postingp
                              fn-wire-begin-article fn-post-offeredp
                              fn-served-submission fn-served-connp
                              fn-nntp-tokenize fn-nntp-command-inputp
                              fn-nntp-keyword-tokenp fn-nntp-keywordp
                              fn-nntp-command-arguments-at-mostp)))))))

; K1a (fn-served-connp) and K1b (not handshaking) have NO `must-fail' here,
; and the reason is written down rather than papered over.  Both are
; proof-support hypotheses: K1b because the lift K1 uses,
; fn-auth-step-post-without-permission-is-not-offered, carries it, and K1a
; because fn-auth-step-effects-well-formed -- the fact that rules a
; (:submit ...) out of the effect list at all -- takes
; fn-auth-session-consistentp, which is the conjunct fn-served-connp
; supplies.  A violating value would have to be a connection on which a
; REFUSED POST still switched the wire or still carried a submission, and
; the two instances below show the conclusion surviving instead, which is
; evidence and not a theorem.  What would settle it is K1 restated without
; them; the attempt on 2026-09-22 reached one open case, a session that is
; fn-auth-sessionp but not consistent with its connection's archive, and the
; lane did not weaken K1 to get there.  Recorded on PRF-031 as the teeth
; obligation K1 still owes.

(defconst *aut-conn-handshaking*
  (fn-served-make-conn (fn-served-conn-wire *aut-conn-req*)
                       *aut-s-handshaking* *aut-archive* *aut-config*
                       *aut-obs* *aut-obs*))
(assert-event (fn-auth-session-handshakingp
               (fn-served-conn-session *aut-conn-handshaking*)))
(assert-event (equal (fn-served-conn-wire
                      (fn-served-result-conn
                       (fn-served-dispatch *aut-conn-handshaking*
                                           *aut-post-event*)))
                     (fn-served-conn-wire *aut-conn-handshaking*)))

(defconst *aut-conn-forged*
  (fn-served-make-conn (fn-served-conn-wire *aut-conn-req*)
                       *aut-forged* *aut-archive* *aut-config*
                       *aut-obs* *aut-obs*))
(assert-event (not (fn-served-connp *aut-conn-forged*)))
(assert-event (equal (fn-served-conn-wire
                      (fn-served-result-conn
                       (fn-served-dispatch *aut-conn-forged* *aut-post-event*)))
                     (fn-served-conn-wire *aut-conn-forged*)))
(assert-event (null (fn-served-submission
                     (fn-served-result-effects
                      (fn-served-dispatch *aut-conn-forged*
                                          *aut-post-event*)))))
