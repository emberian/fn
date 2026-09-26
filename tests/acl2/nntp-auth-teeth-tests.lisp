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
;   the peer role a login binds (PRF-049, keystones 8 to 10 at the end):
;     fn-auth-step-binds-a-peer-role-only-by-a-principal-login,
;     fn-auth-step-principal-login-binds-exactly-the-unique-match,
;     fn-auth-step-starttls-clears-a-principal-role
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
                      *aut-groups* 841000000)
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
(defun aut-step-pinned (as text index)
  (fn-auth-step-pinned as *aut-archive* index nil *aut-config* *aut-obs*
                       *aut-obs* (list :command (fn-nntp-string-octets text))))

; The pinned and legacy public steps make the same AUTHINFO decision even
; with no index.  A delegated STAT on an accepted article separates them
; when that pin is stale, so the handled-command premise does real work.
(assert-event
 (and (fn-auth-command
       *aut-s-req* *aut-config*
       (car (fn-nntp-tokenize (fn-nntp-string-octets "AUTHINFO USER reader")))
       (cdr (fn-nntp-tokenize (fn-nntp-string-octets "AUTHINFO USER reader"))))
      (equal (aut-step-pinned *aut-s-req* "AUTHINFO USER reader" nil)
             (aut-step *aut-s-req* "AUTHINFO USER reader"))))
(defconst *aut-stat-id-line* "STAT <teeth@example.invalid>")
(assert-event
 (not (equal (aut-step-pinned *aut-s-open* *aut-stat-id-line* nil)
             (aut-step *aut-s-open* *aut-stat-id-line*))))
(must-fail
 (defthm fn-auth-false-all-commands-agree-with-stale-pin
   (equal (aut-step-pinned *aut-s-open* *aut-stat-id-line* nil)
          (aut-step *aut-s-open* *aut-stat-id-line*))))
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

; -----------------------------------------------------------------------------
; KEYSTONES 8 to 11: the peer role a login binds (PRF-049)
;
; The subject of 8 to 10 is `fn-auth-step', as above; the subject of 11 is
; `fn-ocfg-open', which host/owner-host.lisp `fn-owner-open' calls, and its
; teeth are in tests/acl2/owner-config-tests.lisp because they need an owner.
;
;   8  fn-auth-step-binds-a-peer-role-only-by-a-principal-login   (2 hyps)
;   9  fn-auth-step-principal-login-binds-exactly-the-unique-match (11 hyps)
;  10  fn-auth-step-starttls-clears-a-principal-role               (2 hyps)
;  11  fn-ocfg-open-begins-unbound                                 (1 hyp)
;
; The scenario is a connection the owner opened as a reader over a real node
; and a real peer table (fn-auth-open-session with no peer, a node and a
; replayed configuration: what books/owner.lisp fn-own-reader-context pins),
; the credential above, and four tables: the principal bound to exactly one
; peer beside a source-address peer; the same principal bound to two peers;
; no principal row at all; and a row group that carries an auth-principal row
; yet denotes a source-address record, which is the table the repair of
; 2026-09-22 in fn-auth-principal-match is for.
;
; The must-fails are generated by a macro per keystone that states the
; keystone's conclusion over a hypothesis list and proves it from the
; keystone itself with the step closed; the full list is admitted first, so
; the macro's statement is the keystone's and not a paraphrase of it, and
; each dropped-hypothesis instance is then shown refuted by a value
; evaluated beside it.  tools/teeth_check.py does not expand macros, so it
; does not count these must-fails; the values beside them are ground and it
; does see those.

(defconst *aut-node* (fn-node-initial-state '("fn.letters") 1048576))
(defconst *aut-node-archive* (fn-node-acceptance *aut-node*))
(defconst *aut-hex* (fn-digest-hex *aut-principal*))
(assert-event (fn-node-statep *aut-node*))
(assert-event (stringp *aut-hex*))

(defconst *aut-principal-record*
  (fn-cfg-peer-make "principal-peer" "principal.example.invalid"
                    '(:nntp "127.0.0.1" 119) '("fn.*" 32768 16) nil
                    (list :principal *aut-hex*)))
(defconst *aut-principal-record-2*
  (fn-cfg-peer-make "principal-peer-2" "principal2.example.invalid"
                    '(:nntp "127.0.0.1" 120) '("fn.*" 32768 16) nil
                    (list :principal *aut-hex*)))
(assert-event (fn-cfg-peerp *aut-principal-record*))
(assert-event (fn-cfg-peerp *aut-principal-record-2*))

(defun aut-table (deltas)
  (fn-config-replay
   0 510
   (list (fn-cfg-record-make 0 0 1 (append *fn-cfg-default-change* deltas)
                             *fn-cfg-default-stamp*))))
(defconst *aut-cfg-one*
  (aut-table (list (fn-cfg-set-peer-delta *aut-peer-record*)
                   (fn-cfg-set-peer-delta *aut-principal-record*))))
(defconst *aut-cfg-two*
  (aut-table (list (fn-cfg-set-peer-delta *aut-principal-record*)
                   (fn-cfg-set-peer-delta *aut-principal-record-2*))))
(defconst *aut-cfg-none*
  (aut-table (list (fn-cfg-set-peer-delta *aut-peer-record*))))
(assert-event (fn-cfgp *aut-cfg-one*))
(assert-event (fn-cfgp *aut-cfg-two*))
(assert-event (fn-cfgp *aut-cfg-none*))
(defun aut-rows (cfg) (fn-cfg-peers (fn-cfg-value cfg)))
(assert-event (equal (fn-cfg-peer-find "principal-peer" (aut-rows *aut-cfg-one*))
                     *aut-principal-record*))
(assert-event (equal (fn-cfg-peer-find "transit" (aut-rows *aut-cfg-one*))
                     *aut-peer-record*))
(assert-event (equal (fn-cfg-peer-find "principal-peer-2" (aut-rows *aut-cfg-two*))
                     *aut-principal-record-2*))

; What the match is on each table, evaluated: one peer, then no peer for a
; duplicate (two rows name the digest) and for a mismatch (none does).
(assert-event (equal (fn-auth-principal-peer-count *aut-hex* (aut-rows *aut-cfg-one*)) 1))
(assert-event (equal (fn-auth-principal-peer-count *aut-hex* (aut-rows *aut-cfg-two*)) 2))
(assert-event (equal (fn-auth-principal-peer-count *aut-hex* (aut-rows *aut-cfg-none*)) 0))
(assert-event (equal (fn-auth-principal-match *aut-principal* *aut-cfg-one*)
                     "principal-peer"))
(assert-event (null (fn-auth-principal-match *aut-principal* *aut-cfg-two*)))
(assert-event (null (fn-auth-principal-match *aut-principal* *aut-cfg-none*)))

; The second credential: a real enrolment for a different principal, which
; no row of any table names.  Its verifier literal is the one
; tests/acl2/nntp-auth-tests.lisp re-derives under the real SHA-256.
(defconst *aut-principal-guest* (make-list 32 :initial-element 9))
(defconst *aut-salt-guest* (make-list 16 :initial-element 5))
(defconst *aut-digest-guest*
  '(16 253 71 139 166 161 40 4 128 152 222 245 150 31 146 146
    162 213 89 91 217 56 233 234 208 64 14 230 20 40 189 59))
(defconst *aut-cred-guest*
  (fn-auth-make-cred (fn-nntp-string-octets "guest") *aut-principal-guest*
                     (fn-authsec-verifier *aut-salt-guest* *aut-digest-guest*)
                     nil))
(assert-event (equal (fn-auth-cred-secret *aut-cred-guest*)
                     (fn-authsec-enrol *aut-salt-guest*
                                       (fn-nntp-string-octets "guest-pass"))))
(assert-event (fn-auth-credp *aut-cred-guest*))
(assert-event (null (fn-auth-principal-match *aut-principal-guest* *aut-cfg-one*)))
(defconst *aut-role-policy*
  (fn-auth-make-config t nil t (list *aut-cred* *aut-cred-guest*)))
(defconst *aut-role-protected*
  (fn-auth-make-config t t t (list *aut-cred* *aut-cred-guest*)))
(assert-event (fn-auth-configp *aut-role-policy*))
(assert-event (fn-auth-configp *aut-role-protected*))

; The reader connection the owner opens (books/owner.lisp
; fn-own-reader-context pins exactly this: no peer, the live node, the live
; configuration) and a source-address peer connection (fn-own-open-peer).
(defun aut-reader (cfg acfg tlsp)
  (fn-auth-open-session *aut-node-archive* nil *aut-node* cfg acfg tlsp))
(defun aut-source-peer (cfg acfg)
  (fn-auth-open-session *aut-node-archive* "transit" *aut-node* cfg acfg nil))
(defun aut-role-step (as text)
  (fn-auth-step as *aut-node-archive* *aut-config* *aut-obs* *aut-obs*
                (list :command (fn-nntp-string-octets text))))
(defun aut-role-after (as text)
  (fn-post-result-session (aut-role-step as text)))
(defun aut-role-reply (as text)
  (fn-post-result-effects (aut-role-step as text)))

(defconst *aut-r-one* (aut-reader *aut-cfg-one* *aut-role-policy* nil))
(defconst *aut-r-two* (aut-reader *aut-cfg-two* *aut-role-policy* nil))
(defconst *aut-r-none* (aut-reader *aut-cfg-none* *aut-role-policy* nil))
(assert-event (fn-auth-sessionp *aut-r-one*))
(assert-event (fn-auth-session-consistentp *aut-r-one* *aut-node-archive*))
(assert-event (null (fn-auth-session-peer *aut-r-one*)))
(defconst *aut-r-one-user* (aut-role-after *aut-r-one* "AUTHINFO USER reader"))
(defconst *aut-r-two-user* (aut-role-after *aut-r-two* "AUTHINFO USER reader"))
(defconst *aut-r-none-user* (aut-role-after *aut-r-none* "AUTHINFO USER reader"))
(defconst *aut-r-guest-user* (aut-role-after *aut-r-one* "AUTHINFO USER guest"))
(assert-event (null (fn-auth-session-peer *aut-r-one-user*)))
(assert-event (equal (fn-auth-session-pending *aut-r-one-user*) *aut-name*))

; After PASS: macros, because the accepting branch runs the SHA-256
; attachment, which a `defconst' may not call.
(defmacro aut-bound ()
  '(aut-role-after *aut-r-one-user* "AUTHINFO PASS correct-horse"))
(defmacro aut-dup-authed ()
  '(aut-role-after *aut-r-two-user* "AUTHINFO PASS correct-horse"))
(defmacro aut-none-authed ()
  '(aut-role-after *aut-r-none-user* "AUTHINFO PASS correct-horse"))
(defmacro aut-guest-authed ()
  '(aut-role-after *aut-r-guest-user* "AUTHINFO PASS guest-pass"))

; The table the repair is for.  `fn-cfgp' asks only that the peers slot be a
; row list, and a (:set-peer name rows) delta is admitted when its rows are
; keyed by name (books/config.lisp), so one peer's row group can carry an
; auth-source-address row AND an auth-principal row naming the digest.  The
; record it denotes is the source-address one (fn-cfg-peer-of-rows reads
; that slot first), so a role bound from the principal row would not be
; principal-derived and STARTTLS would not clear it.  The row count alone,
; which is what the binding read before 2026-09-22, says one.
(defconst *aut-shadow-record*
  (fn-cfg-peer-make "shadow" "shadow.example.invalid"
                    '(:nntp "127.0.0.2" 119) '("fn.*" 32768 16) nil
                    '(:source-address "127.0.0.2")))
(defconst *aut-cfg-shadow*
  (aut-table (list (fn-cfg-set-peer
                    "shadow"
                    (append (fn-cfg-peer-rows *aut-shadow-record*)
                            (list (fn-cfg-row-make "shadow" "auth-principal"
                                                   *aut-hex* 0)))))))
(assert-event (fn-cfgp *aut-cfg-shadow*))
(assert-event (equal (fn-auth-principal-peer-count *aut-hex* (aut-rows *aut-cfg-shadow*)) 1))
(assert-event (equal (fn-auth-principal-peer-name *aut-hex* (aut-rows *aut-cfg-shadow*))
                     "shadow"))
(assert-event (equal (fn-cfg-peer-auth (fn-cfg-peer-find "shadow" (aut-rows *aut-cfg-shadow*)))
                     '(:source-address "127.0.0.2")))
(assert-event (null (fn-auth-principal-match *aut-principal* *aut-cfg-shadow*)))

; What the binding read before the repair: the row count and the first row's
; name, with no look at the record.  On the shadow table it names "shadow",
; whose record is a source-address one -- a role STARTTLS would have kept.
(defun aut-pre-repair-peer (principal cfg)
  (let ((hex (fn-digest-hex principal))
        (rows (fn-cfg-peers (fn-cfg-value cfg))))
    (and (equal (fn-auth-principal-peer-count hex rows) 1)
         (fn-auth-principal-peer-name hex rows))))
(assert-event (equal (aut-pre-repair-peer *aut-principal* *aut-cfg-shadow*)
                     "shadow"))
(assert-event
 (not (fn-auth-principal-rolep
       (fn-auth-with-base
        *aut-r-one*
        (fn-peer-make-session (fn-peer-session-base (fn-auth-session-base *aut-r-one*))
                              "shadow" nil 0 *aut-node* *aut-cfg-shadow*)))))
(defconst *aut-r-shadow-user*
  (aut-role-after (aut-reader *aut-cfg-shadow* *aut-role-policy* nil)
                  "AUTHINFO USER reader"))
(defmacro aut-shadow-authed ()
  '(aut-role-after *aut-r-shadow-user* "AUTHINFO PASS correct-horse"))

; -----------------------------------------------------------------------------
; KEYSTONE 8: fn-auth-step-binds-a-peer-role-only-by-a-principal-login
;
;   (implies (and (not (fn-auth-session-peer as))                       ; B1
;                 (fn-auth-session-peer (session of the step)))          ; B2
;            (and <the connection was well-formed, not handshaking,
;                  unauthenticated, and the policy accepted its channel>
;                 <the event was AUTHINFO PASS <one token>, after a USER,
;                  and the token checks against the cached name's verifier>
;                 <the subject is that credential's principal>
;                 <the role is fn-auth-principal-match of it under the
;                  pinned configuration, and it is principal-derived>))

(defconst *aut-k8-conclusion*
  '(and (fn-auth-sessionp as)
        (not (fn-auth-session-handshakingp as))
        (not (fn-auth-session-subject as))
        (not (and (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                  (not (fn-auth-session-tlsp as))))
        (equal (car wire-event) :command)
        (fn-nntp-keywordp (car (fn-nntp-tokenize (cadr wire-event))) "AUTHINFO")
        (fn-nntp-keywordp (cadr (fn-nntp-tokenize (cadr wire-event))) "PASS")
        (fn-auth-token-argp (cddr (fn-nntp-tokenize (cadr wire-event))))
        (fn-auth-session-pending as)
        (fn-auth-checkp
         (fn-auth-find-cred (fn-auth-session-pending as)
                            (fn-auth-config-creds (fn-auth-session-config as)))
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
(defconst *aut-k8-hyps*
  '((b1 . (not (fn-auth-session-peer as)))
    (b2 . (fn-auth-session-peer
           (fn-post-result-session
            (fn-auth-step as archive config observation injection
                          wire-event))))))

; The hypothesis list a tooth states, picked by name from a keystone's list,
; so every instance below is the keystone's own text with some names left
; out.
(defun aut-hyps (keys alist)
  (declare (xargs :mode :program))
  (if (consp keys)
      (cons (cdr (assoc-eq (car keys) alist)) (aut-hyps (cdr keys) alist))
    nil))

(defmacro aut-tooth (name keys alist conclusion keystone)
  `(defthm ,name
     (implies (and ,@(aut-hyps keys alist)) ,conclusion)
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use ((:instance ,keystone))
              :in-theory (disable fn-auth-step fn-auth-sessionp
                                  fn-auth-session-peer fn-auth-checkp
                                  fn-auth-find-cred fn-nntp-tokenize
                                  fn-auth-principal-rolep
                                  fn-auth-principal-match
                                  fn-nntp-command-inputp fn-nntp-keywordp
                                  fn-auth-token-argp)))))
(defmacro aut-k8 (name keys)
  `(aut-tooth ,name ,keys ,*aut-k8-hyps* ,*aut-k8-conclusion*
              fn-auth-step-binds-a-peer-role-only-by-a-principal-login))

; The keystone's own statement, admitted through the macro first.
(aut-k8 aut-k8-full (b1 b2))

; The witness: a reader on the one-peer table logs in and becomes
; "principal-peer" -- the role the table gives this principal, derived from
; its (:principal ...) record, with the principal installed as the subject.
(assert-event (null (fn-auth-session-peer *aut-r-one-user*)))
(assert-event (equal (aut-role-reply *aut-r-one-user* "AUTHINFO PASS correct-horse")
                     (aut-single "281 authentication accepted")))
(assert-event (equal (fn-auth-session-peer (aut-bound)) "principal-peer"))
(assert-event (equal (fn-auth-session-subject (aut-bound)) *aut-principal*))
(assert-event (fn-auth-principal-rolep (aut-bound)))
(assert-event (fn-auth-sessionp (aut-bound)))
(assert-event (fn-auth-session-consistentp (aut-bound) *aut-node-archive*))
; What every other login on these tables does: the duplicate, the mismatch
; (a principal with no row), the other credential, and the shadow row all
; answer 281 and install the subject, and leave the connection a reader.
(assert-event (equal (fn-auth-session-subject (aut-dup-authed)) *aut-principal*))
(assert-event (null (fn-auth-session-peer (aut-dup-authed))))
(assert-event (equal (fn-auth-session-subject (aut-none-authed)) *aut-principal*))
(assert-event (null (fn-auth-session-peer (aut-none-authed))))
(assert-event (equal (fn-auth-session-subject (aut-guest-authed))
                     *aut-principal-guest*))
(assert-event (null (fn-auth-session-peer (aut-guest-authed))))
(assert-event (equal (fn-auth-session-subject (aut-shadow-authed)) *aut-principal*))
(assert-event (null (fn-auth-session-peer (aut-shadow-authed))))
; Protected-only before TLS: the exchange is refused and no role can follow
; (fn-auth-step-protected-only-refuses-authinfo-before-tls, PRF-031).
(defconst *aut-r-prot* (aut-reader *aut-cfg-one* *aut-role-protected* nil))
(assert-event (equal (aut-role-reply *aut-r-prot* "AUTHINFO USER reader")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-role-after *aut-r-prot* "AUTHINFO USER reader")
                     *aut-r-prot*))

; B1 dropped.  A connection the owner resolved to a source-address peer
; already has a role, and a CAPABILITIES keeps it: the step's session is a
; peer and the event was not AUTHINFO at all.
(defconst *aut-src* (aut-source-peer *aut-cfg-one* *aut-role-policy*))
(assert-event (fn-auth-sessionp *aut-src*))
(assert-event (equal (fn-auth-session-peer (aut-role-after *aut-src* "CAPABILITIES"))
                     "transit"))
(assert-event (not (fn-nntp-keywordp
                    (car (fn-nntp-tokenize (fn-nntp-string-octets "CAPABILITIES")))
                    "AUTHINFO")))
(local (must-fail (aut-k8 aut-k8-without-b1 (b2))))

; B2 dropped.  A reader that stays a reader: a GROUP on the unauthenticated
; connection is not an AUTHINFO line either.
(assert-event (null (fn-auth-session-peer (aut-role-after *aut-r-one* "GROUP fn.letters"))))
(assert-event (not (fn-nntp-keywordp
                    (car (fn-nntp-tokenize (fn-nntp-string-octets "GROUP fn.letters")))
                    "AUTHINFO")))
(local (must-fail (aut-k8 aut-k8-without-b2 (b1))))

; -----------------------------------------------------------------------------
; KEYSTONE 9: fn-auth-step-principal-login-binds-exactly-the-unique-match
;
;   (implies (and (fn-auth-sessionp as)                                   ; P1
;                 (not (fn-auth-session-handshakingp as))                 ; P2
;                 (not (fn-auth-session-peer as))                         ; P3
;                 (not (fn-auth-session-subject as))                      ; P4
;                 (not (and protected-only (not tlsp)))                   ; P5
;                 (fn-nntp-command-inputp line)                           ; P6
;                 (fn-nntp-keywordp (car tokens) "AUTHINFO")              ; P7
;                 (fn-nntp-keywordp (cadr tokens) "PASS")                 ; P8
;                 (fn-auth-token-argp (cddr tokens))                      ; P9
;                 (fn-auth-session-pending as)                            ; P10
;                 (fn-auth-checkp cred (caddr tokens)))                   ; P11
;            (and (equal effects (fn-auth-single as "281 ..."))
;                 (equal subject (fn-auth-cred-principal cred))
;                 (equal role (fn-auth-principal-match principal cfg))))
;
; `fn-nntp-command-arguments-at-mostp' is not a hypothesis: a PASS line
; inside the 510-octet command bound has a secret of at most 496 octets,
; which the book proves (fn-auth-pass-line-arguments-are-in-bounds) rather
; than assumes.

(defconst *aut-k9-hyps*
  '((p1 . (fn-auth-sessionp as))
    (p2 . (not (fn-auth-session-handshakingp as)))
    (p3 . (not (fn-auth-session-peer as)))
    (p4 . (not (fn-auth-session-subject as)))
    (p5 . (not (and (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                    (not (fn-auth-session-tlsp as)))))
    (p6 . (fn-nntp-command-inputp line))
    (p7 . (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
    (p8 . (fn-nntp-keywordp (cadr (fn-nntp-tokenize line)) "PASS"))
    (p9 . (fn-auth-token-argp (cddr (fn-nntp-tokenize line))))
    (p10 . (fn-auth-session-pending as))
    (p11 . (fn-auth-checkp
            (fn-auth-find-cred (fn-auth-session-pending as)
                               (fn-auth-config-creds (fn-auth-session-config as)))
            (caddr (fn-nntp-tokenize line))))))
(defconst *aut-k9-conclusion*
  '(and (equal (fn-post-result-effects
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
(defmacro aut-k9 (name keys)
  `(aut-tooth ,name ,keys ,*aut-k9-hyps* ,*aut-k9-conclusion*
              fn-auth-step-principal-login-binds-exactly-the-unique-match))

(aut-k9 aut-k9-full (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11))

; The witnesses are the four logins above: on the one-peer table the role is
; the match, "principal-peer"; on the duplicate, mismatch and shadow tables
; the match is nil and so is the role -- the 281 identical in all four.
(assert-event (equal (aut-role-reply *aut-r-two-user* "AUTHINFO PASS correct-horse")
                     (aut-single "281 authentication accepted")))
(assert-event (equal (aut-role-reply *aut-r-none-user* "AUTHINFO PASS correct-horse")
                     (aut-single "281 authentication accepted")))

; A session with chosen fields over a real base, for the values no command
; sequence reaches.
(defun aut-mk (base acfg pending subject tlsp handshaking)
  (fn-auth-make-session base acfg pending subject tlsp handshaking))
(defconst *aut-reader-base* (fn-auth-session-base *aut-r-one*))
(defconst *aut-src-base* (fn-auth-session-base *aut-src*))
(defconst *aut-pass* "AUTHINFO PASS correct-horse")
(defconst *aut-281* (aut-single "281 authentication accepted"))

; P1 dropped: a value of the session's shape whose base is not a peer
; session, with a cached name.  The step returns it unchanged and says
; nothing.
(defconst *aut-forged-role*
  (aut-mk :not-a-peer-session *aut-role-policy* *aut-name* nil nil nil))
(assert-event (not (fn-auth-sessionp *aut-forged-role*)))
(assert-event (null (fn-auth-session-peer *aut-forged-role*)))
(assert-event (equal (aut-role-reply *aut-forged-role* *aut-pass*) nil))
(local (must-fail (aut-k9 aut-k9-without-p1 (p2 p3 p4 p5 p6 p7 p8 p9 p10 p11))))

; P2 dropped: handshaking, with a cached name.  Nothing is answered.
(defconst *aut-hs-role* (aut-mk *aut-reader-base* *aut-role-policy* *aut-name* nil nil t))
(assert-event (fn-auth-sessionp *aut-hs-role*))
(assert-event (equal (aut-role-reply *aut-hs-role* *aut-pass*) nil))
(local (must-fail (aut-k9 aut-k9-without-p2 (p1 p3 p4 p5 p6 p7 p8 p9 p10 p11))))

; P3 dropped: a source-address peer with a cached name logs in; 281 and the
; subject, but the role is still "transit" and not the match.
(defconst *aut-src-user* (aut-mk *aut-src-base* *aut-role-policy* *aut-name* nil nil nil))
(assert-event (fn-auth-sessionp *aut-src-user*))
(assert-event (equal (aut-role-reply *aut-src-user* *aut-pass*) *aut-281*))
(assert-event (equal (fn-auth-session-peer (aut-role-after *aut-src-user* *aut-pass*))
                     "transit"))
(assert-event (equal (fn-auth-principal-match *aut-principal* *aut-cfg-one*)
                     "principal-peer"))
(local (must-fail (aut-k9 aut-k9-without-p3 (p1 p2 p4 p5 p6 p7 p8 p9 p10 p11))))

; P4 dropped: already authenticated is 502.
(defconst *aut-authed-user*
  (aut-mk *aut-reader-base* *aut-role-policy* *aut-name* *aut-principal* nil nil))
(assert-event (fn-auth-sessionp *aut-authed-user*))
(assert-event (equal (aut-role-reply *aut-authed-user* *aut-pass*)
                     (aut-single "502 already authenticated")))
(local (must-fail (aut-k9 aut-k9-without-p4 (p1 p2 p3 p5 p6 p7 p8 p9 p10 p11))))

; P5 dropped: protected-only without TLS is 483, even with a cached name.
(defconst *aut-prot-user* (aut-mk *aut-reader-base* *aut-role-protected* *aut-name* nil nil nil))
(assert-event (fn-auth-sessionp *aut-prot-user*))
(assert-event (equal (aut-role-reply *aut-prot-user* *aut-pass*) (aut-single *aut-483*)))
(local (must-fail (aut-k9 aut-k9-without-p5 (p1 p2 p3 p4 p6 p7 p8 p9 p10 p11))))

; P6 dropped: the same three tokens on a line past the 510-octet command
; bound.  The preflight refuses it and the reader answers; no 281.
(defconst *aut-long-pass*
  (append (fn-nntp-string-octets "AUTHINFO") (make-list 500 :initial-element 32)
          (fn-nntp-string-octets "PASS correct-horse")))
(assert-event (not (fn-nntp-command-inputp *aut-long-pass*)))
(assert-event (equal (fn-nntp-tokenize *aut-long-pass*)
                     (fn-nntp-tokenize (fn-nntp-string-octets *aut-pass*))))
(assert-event (not (equal (fn-post-result-effects
                           (fn-auth-step *aut-r-one-user* *aut-node-archive*
                                         *aut-config* *aut-obs* *aut-obs*
                                         (list :command *aut-long-pass*)))
                          *aut-281*)))
(local (must-fail (aut-k9 aut-k9-without-p6 (p1 p2 p3 p4 p5 p7 p8 p9 p10 p11))))

; P7 dropped: another keyword with the same arguments is not a login.
(assert-event (not (equal (aut-role-reply *aut-r-one-user* "XAUTHINFO PASS correct-horse")
                          *aut-281*)))
(local (must-fail (aut-k9 aut-k9-without-p7 (p1 p2 p3 p4 p5 p6 p8 p9 p10 p11))))

; P8 dropped: USER with the secret as its argument caches a name, 381.
(assert-event (equal (aut-role-reply *aut-r-one-user* "AUTHINFO USER correct-horse")
                     (aut-single "381 password required")))
(local (must-fail (aut-k9 aut-k9-without-p8 (p1 p2 p3 p4 p5 p6 p7 p9 p10 p11))))

; P9 dropped: PASS with the secret and one more token is 501.
(assert-event (equal (aut-role-reply *aut-r-one-user* "AUTHINFO PASS correct-horse extra")
                     (aut-single "501 syntax error")))
(local (must-fail (aut-k9 aut-k9-without-p9 (p1 p2 p3 p4 p5 p6 p7 p8 p10 p11))))

; P10 dropped: PASS before USER is 482.
(assert-event (equal (aut-role-reply *aut-r-one* *aut-pass*)
                     (aut-single "482 authentication commands issued out of sequence")))
(local (must-fail (aut-k9 aut-k9-without-p10 (p1 p2 p3 p4 p5 p6 p7 p8 p9 p11))))

; P11 dropped: a secret that does not check is 481, under the real SHA-256.
(assert-event (not (fn-auth-checkp *aut-cred* (fn-nntp-string-octets "wrong-horse"))))
(assert-event (equal (aut-role-reply *aut-r-one-user* "AUTHINFO PASS wrong-horse")
                     (aut-single "481 authentication failed")))
(local (must-fail (aut-k9 aut-k9-without-p11 (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10))))

; -----------------------------------------------------------------------------
; KEYSTONE 10: fn-auth-step-starttls-clears-a-principal-role
;
;   (implies (and (not (fn-auth-session-handshakingp as))                ; S1
;                 (fn-auth-session-handshakingp (session of the step)))   ; S2
;            (and (null subject) (null pending)
;                 (not (fn-auth-principal-rolep (session of the step)))
;                 (equal role (if (fn-auth-principal-rolep as) nil
;                                (fn-auth-session-peer as)))))

(defconst *aut-k10-hyps*
  '((s1 . (not (fn-auth-session-handshakingp as)))
    (s2 . (fn-auth-session-handshakingp
           (fn-post-result-session
            (fn-auth-step as archive config observation injection
                          wire-event))))
    ; PRF-164: the TLS handshake, not the XREDEEM redemption hold.
    (s3 . (not (fn-auth-redeem-waitp
                (fn-post-result-session
                 (fn-auth-step as archive config observation injection
                               wire-event)))))))
(defconst *aut-k10-conclusion*
  '(and (null (fn-auth-session-subject
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
(defmacro aut-k10 (name keys)
  `(aut-tooth ,name ,keys ,*aut-k10-hyps* ,*aut-k10-conclusion*
              fn-auth-step-starttls-clears-a-principal-role))

(aut-k10 aut-k10-full (s1 s2 s3))
; S3 dropped: the XREDEEM hold is handshaking with a pending redemption
; state, so `no cached name' fails for it (books/nntp-auth.lisp
; fn-auth-step-pinned-xredeem-pass-holds-for-the-owner; the evaluated
; witness is tests/acl2/accounts-wire-tests.lisp's *awt-wait*).
(local (must-fail (aut-k10 aut-k10-without-s3 (s1 s2))))

; The witness: the bound connection sends STARTTLS.  382, handshaking, and
; the role, the subject and the cached name are gone.
(assert-event (equal (aut-role-reply (aut-bound) "STARTTLS")
                     (append (aut-single "382 continue with TLS negotiation")
                             (list (fn-auth-starttls-effect)))))
(assert-event (fn-auth-session-handshakingp (aut-role-after (aut-bound) "STARTTLS")))
(assert-event (null (fn-auth-session-peer (aut-role-after (aut-bound) "STARTTLS"))))
(assert-event (null (fn-auth-session-subject (aut-role-after (aut-bound) "STARTTLS"))))
(assert-event (null (fn-auth-session-pending (aut-role-after (aut-bound) "STARTTLS"))))
; Separating: a source-address peer keeps its role across the same command,
; so the theorem distinguishes the two origins and does not merely clear.
(assert-event (fn-auth-session-handshakingp (aut-role-after *aut-src* "STARTTLS")))
(assert-event (equal (fn-auth-session-peer (aut-role-after *aut-src* "STARTTLS"))
                     "transit"))
(assert-event (not (fn-auth-principal-rolep *aut-src*)))
; And out the other side: the handshake re-entry leaves a TLS reader, which
; a fresh login over TLS binds again.
(defmacro aut-after-tls ()
  '(fn-post-result-session
    (fn-auth-step (aut-role-after (aut-bound) "STARTTLS") *aut-node-archive*
                  *aut-config* *aut-obs* *aut-obs* (list :tls-established))))
(assert-event (equal (fn-auth-session-tlsp (aut-after-tls)) t))
(assert-event (null (fn-auth-session-peer (aut-after-tls))))
(assert-event (equal (fn-auth-session-peer
                      (aut-role-after (aut-role-after (aut-after-tls)
                                                      "AUTHINFO USER reader")
                                      *aut-pass*))
                     "principal-peer"))

; S1 dropped: a session already handshaking over a bound base.  The step
; answers nothing and returns it, so it is still handshaking and the role
; is still principal-derived.
(defmacro aut-hs-bound ()
  '(aut-mk (fn-auth-session-base (aut-bound)) *aut-role-policy* nil nil nil t))
(assert-event (fn-auth-sessionp (aut-hs-bound)))
(assert-event (fn-auth-session-handshakingp (aut-role-after (aut-hs-bound) "CAPABILITIES")))
(assert-event (fn-auth-principal-rolep (aut-role-after (aut-hs-bound) "CAPABILITIES")))
(local (must-fail (aut-k10 aut-k10-without-s1 (s2))))

; S2 dropped: any step that does not enter the handshake, here CAPABILITIES
; on the bound connection, keeps the principal-derived role.
(assert-event (not (fn-auth-session-handshakingp (aut-role-after (aut-bound) "CAPABILITIES"))))
(assert-event (fn-auth-principal-rolep (aut-role-after (aut-bound) "CAPABILITIES")))
(local (must-fail (aut-k10 aut-k10-without-s2 (s1))))

; =============================================================================
; P1 at the host-called step (keystones 11 to 17, books/nntp-auth-invariants,
; section "P1 at the host-called step").
;
; The subject of keystones 11, 12 and 15 to 17 is `fn-auth-step-pinned', the
; one call books/served.lisp:617 `fn-served-dispatch' makes into this layer;
; the subject of 13 and 14 is `fn-served-dispatch' itself.  The host reaches
; both from host/owner-host.lisp:1240 (`fn-owner-chunk', through
; `fn-ocfg-read-tls-prefix').  Each keystone is admitted here once more from
; its own hypothesis list, with every hypothesis named, and then once per
; hypothesis with that one left out under `must-fail'; beside each
; `must-fail' is the evaluated value that refutes the weaker statement.

(defconst *aut-pin* (fn-served-conn-pinned-index *aut-conn-req*))

(defun aut-pinned-octets (as line)
  (fn-auth-step-pinned as *aut-archive* *aut-pin* nil *aut-config* *aut-obs*
                       *aut-obs* (list :command line)))
(defun aut-pinned (as text)
  (aut-pinned-octets as (fn-nntp-string-octets text)))
(defun aut-pinned-reply (as text)
  (fn-post-result-effects (aut-pinned as text)))
(defun aut-pinned-after (as text)
  (fn-post-result-session (aut-pinned as text)))
(defun aut-delegated (as text)
  (fn-auth-delegate-pinned as *aut-archive* *aut-pin* nil *aut-config*
                           *aut-obs* *aut-obs*
                           (list :command (fn-nntp-string-octets text))))
(defun aut-dispatch-octets (conn line)
  (fn-served-dispatch conn (list :command line)))
(defun aut-dispatch (conn text)
  (aut-dispatch-octets conn (fn-nntp-string-octets text)))

(defmacro aut-p1-tooth (name keys alist conclusion keystone)
  `(defthm ,name
     (implies (and ,@(aut-hyps keys alist)) ,conclusion)
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use ((:instance ,keystone))
              :in-theory (disable fn-auth-step-pinned fn-auth-delegate-pinned
                                  fn-served-dispatch fn-served-connp
                                  fn-auth-sessionp fn-auth-single
                                  fn-auth-postingp fn-auth-find-cred
                                  fn-auth-cred-postingp fn-auth-cred-principal
                                  fn-auth-restricted-keywordp
                                  fn-auth-config-requiredp
                                  fn-auth-config-protected-onlyp
                                  fn-nntp-tokenize fn-nntp-command-inputp
                                  fn-nntp-keywordp
                                  fn-nntp-command-arguments-at-mostp)))))

; -----------------------------------------------------------------------------
; KEYSTONE 11: fn-auth-step-pinned-gated-command-is-refused-and-not-performed
; (b) at the step.  Hypotheses H1 to H7 of keystone 1, over the pinned step.

(defconst *aut-k11-hyps*
  '((h1 . (fn-auth-sessionp as))
    (h2 . (not (fn-auth-session-handshakingp as)))
    (h3 . (fn-auth-config-requiredp (fn-auth-session-config as)))
    (h4 . (not (fn-auth-session-subject as)))
    (h5 . (fn-nntp-command-inputp line))
    (h6 . (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
    (h7 . (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))))
(defconst *aut-k11-conclusion*
  '(and (null (fn-post-result-submission
               (fn-auth-step-pinned as archive index verdicts config
                                    observation injection
                                    (list :command line))))
        (not (fn-post-offeredp
              (fn-post-result-effects
               (fn-auth-step-pinned as archive index verdicts config
                                    observation injection
                                    (list :command line)))))
        (equal (fn-post-result-session
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               as)
        (equal (fn-post-result-effects
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               (fn-auth-single as "480 authentication required"))))
(defmacro aut-k11 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k11-hyps* ,*aut-k11-conclusion*
                 fn-auth-step-pinned-gated-command-is-refused-and-not-performed))

(aut-k11 aut-k11-full (h1 h2 h3 h4 h5 h6 h7))

; The witness: GROUP and ARTICLE on an unauthenticated connection under the
; required policy, and POST, which the archive's one group would accept
; once authenticated.  480, the session unchanged, no submission, no offer.
(assert-event (equal (aut-pinned-reply *aut-s-req* "GROUP fn.letters")
                     (aut-single *aut-480*)))
(assert-event (equal (aut-pinned-after *aut-s-req* "GROUP fn.letters")
                     *aut-s-req*))
(assert-event (equal (aut-pinned-reply *aut-s-req* "ARTICLE 1")
                     (aut-single *aut-480*)))
(assert-event (equal (aut-pinned-reply *aut-s-req* "POST")
                     (aut-single *aut-480*)))
(assert-event (null (fn-post-result-submission (aut-pinned *aut-s-req* "POST"))))
; Non-degenerate: authenticated, the same GROUP selects the group.
(assert-event (not (equal (aut-pinned-reply (aut-authed) "GROUP fn.letters")
                          (aut-single *aut-480*))))
(assert-event (not (equal (aut-pinned-after (aut-authed) "GROUP fn.letters")
                          (aut-authed))))

; H1 dropped: the forged session is answered nothing.
(assert-event (equal (aut-pinned-reply *aut-forged* "GROUP fn.letters") nil))
(local (must-fail (aut-k11 aut-k11-without-h1 (h2 h3 h4 h5 h6 h7))))
; H2 dropped: a handshaking session is answered nothing.
(assert-event (equal (aut-pinned-reply *aut-s-handshaking* "GROUP fn.letters")
                     nil))
(local (must-fail (aut-k11 aut-k11-without-h2 (h1 h3 h4 h5 h6 h7))))
; H3 dropped: the open policy serves GROUP unauthenticated.
(assert-event (not (equal (aut-pinned-reply *aut-s-open* "GROUP fn.letters")
                          (aut-single *aut-480*))))
(local (must-fail (aut-k11 aut-k11-without-h3 (h1 h2 h4 h5 h6 h7))))
; H4 dropped: the authenticated session (witness above).
(local (must-fail (aut-k11 aut-k11-without-h4 (h1 h2 h3 h5 h6 h7))))
; H5 dropped: the over-long GROUP line is delegated to the reader preflight.
(assert-event
 (not (equal (fn-post-result-effects
              (aut-pinned-octets *aut-s-req* *aut-over-long-line*))
             (aut-single *aut-480*))))
(local (must-fail (aut-k11 aut-k11-without-h5 (h1 h2 h3 h4 h6 h7))))
; H6 dropped: the over-long GROUP argument is delegated too.
(assert-event
 (not (equal (fn-post-result-effects
              (aut-pinned-octets *aut-s-req* *aut-over-long-argument-line*))
             (aut-single *aut-480*))))
(local (must-fail (aut-k11 aut-k11-without-h6 (h1 h2 h3 h4 h5 h7))))
; H7 dropped: HELP is answered unauthenticated.
(assert-event (not (equal (aut-pinned-reply *aut-s-req* "HELP")
                          (aut-single *aut-480*))))
(local (must-fail (aut-k11 aut-k11-without-h7 (h1 h2 h3 h4 h5 h6))))

; -----------------------------------------------------------------------------
; KEYSTONE 12: fn-auth-step-pinned-protected-only-refuses-authinfo-before-tls
; (a) at the step.  Hypotheses G1 to G8 of keystone 2, over the pinned step.

(defconst *aut-k12-hyps*
  '((g1 . (fn-auth-sessionp as))
    (g2 . (not (fn-auth-session-handshakingp as)))
    (g3 . (not (fn-auth-session-subject as)))
    (g4 . (fn-auth-config-protected-onlyp (fn-auth-session-config as)))
    (g5 . (not (fn-auth-session-tlsp as)))
    (g6 . (fn-nntp-command-inputp line))
    (g7 . (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
    (g8 . (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))))
(defconst *aut-k12-conclusion*
  '(and (equal (fn-post-result-effects
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               (fn-auth-single
                as "483 a protected channel is required; use STARTTLS"))
        (equal (fn-post-result-session
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               as)
        (null (fn-post-result-submission
               (fn-auth-step-pinned as archive index verdicts config
                                    observation injection
                                    (list :command line))))))
(defmacro aut-k12 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k12-hyps* ,*aut-k12-conclusion*
                 fn-auth-step-pinned-protected-only-refuses-authinfo-before-tls))

(aut-k12 aut-k12-full (g1 g2 g3 g4 g5 g6 g7 g8))

; The witness: a clear connection under protected-only sends the correct
; secret.  483, and the session is the one it arrived on: no name is
; cached, no subject is installed, and the reply is the same for USER, for
; the right PASS and for a wrong one, so the secret is never compared.
(assert-event (equal (aut-pinned-reply *aut-s-prot* "AUTHINFO USER reader")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-pinned-reply *aut-s-prot* "AUTHINFO PASS correct-horse")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-pinned-reply *aut-s-prot* "AUTHINFO PASS wrong-horse")
                     (aut-single *aut-483*)))
(assert-event (equal (aut-pinned-after *aut-s-prot* "AUTHINFO USER reader")
                     *aut-s-prot*))
(assert-event (null (fn-auth-session-pending
                     (aut-pinned-after *aut-s-prot* "AUTHINFO USER reader"))))
; Non-degenerate: over TLS the same policy caches the name (381).
(assert-event (equal (aut-pinned-reply *aut-s-prot-tls* "AUTHINFO USER reader")
                     (aut-single "381 password required")))

; G1 dropped: the forged protected session is answered nothing.
(assert-event (equal (aut-pinned-reply *aut-forged-prot* "AUTHINFO USER reader")
                     nil))
(local (must-fail (aut-k12 aut-k12-without-g1 (g2 g3 g4 g5 g6 g7 g8))))
; G2 dropped: a handshaking session is answered nothing.
(assert-event (equal (aut-pinned-reply *aut-s-prot-handshaking*
                                       "AUTHINFO USER reader")
                     nil))
(local (must-fail (aut-k12 aut-k12-without-g2 (g1 g3 g4 g5 g6 g7 g8))))
; G3 dropped: an authenticated session is 502.
(assert-event (equal (aut-pinned-reply (aut-prot-authed) "AUTHINFO USER reader")
                     (aut-single "502 already authenticated")))
(local (must-fail (aut-k12 aut-k12-without-g3 (g1 g2 g4 g5 g6 g7 g8))))
; G4 dropped: required but not protected-only answers 381 in the clear.
(assert-event (equal (aut-pinned-reply *aut-s-req* "AUTHINFO USER reader")
                     (aut-single "381 password required")))
(local (must-fail (aut-k12 aut-k12-without-g4 (g1 g2 g3 g5 g6 g7 g8))))
; G5 dropped: over TLS, 381 (witness above).
(local (must-fail (aut-k12 aut-k12-without-g5 (g1 g2 g3 g4 g6 g7 g8))))
; G6 dropped: the over-long AUTHINFO line is delegated.
(assert-event
 (not (equal (fn-post-result-effects
              (aut-pinned-octets *aut-s-prot* *aut-authinfo-over-long-line*))
             (aut-single *aut-483*))))
(local (must-fail (aut-k12 aut-k12-without-g6 (g1 g2 g3 g4 g5 g7 g8))))
; G7 dropped: the over-long AUTHINFO argument is delegated.
(assert-event
 (not (equal (fn-post-result-effects
              (aut-pinned-octets *aut-s-prot*
                                 *aut-authinfo-over-long-argument-line*))
             (aut-single *aut-483*))))
(local (must-fail (aut-k12 aut-k12-without-g7 (g1 g2 g3 g4 g5 g6 g8))))
; G8 dropped: STARTTLS on the same connection is 382.
(assert-event (not (equal (aut-pinned-reply *aut-s-prot* "STARTTLS")
                          (aut-single *aut-483*))))
(local (must-fail (aut-k12 aut-k12-without-g8 (g1 g2 g3 g4 g5 g6 g7))))

; -----------------------------------------------------------------------------
; KEYSTONES 13 and 14: the same two answers from fn-served-dispatch, where
; the WHOLE connection is unchanged.

(defconst *aut-conn-prot*
  (fn-served-result-conn
   (fn-served-open *aut-archive* 510 8192 *aut-config* *aut-obs* *aut-obs*
                   *aut-protected*)))
(assert-event (fn-served-connp *aut-conn-prot*))
(defconst *aut-conn-req-hs*
  (fn-served-result-conn (aut-dispatch *aut-conn-req* "STARTTLS")))
(defconst *aut-conn-prot-hs*
  (fn-served-result-conn (aut-dispatch *aut-conn-prot* "STARTTLS")))
(defconst *aut-conn-prot-tls*
  (fn-served-result-conn
   (fn-served-dispatch *aut-conn-prot-hs* (list :tls-established))))
(assert-event (fn-served-connp *aut-conn-req-hs*))
(assert-event (fn-auth-session-handshakingp
               (fn-served-conn-session *aut-conn-req-hs*)))
(assert-event (fn-served-connp *aut-conn-prot-tls*))
(assert-event (equal (fn-auth-session-tlsp
                      (fn-served-conn-session *aut-conn-prot-tls*))
                     t))
; A connection whose session slot holds the forged session: not a served
; connection, and every session hypothesis but the recognizer holds.
(defconst *aut-conn-forged* (update-nth 1 *aut-forged* *aut-conn-req*))
(defconst *aut-conn-forged-prot* (update-nth 1 *aut-forged-prot* *aut-conn-prot*))
(assert-event (not (fn-served-connp *aut-conn-forged*)))
(assert-event (not (fn-served-connp *aut-conn-forged-prot*)))
; Authenticated connections, as macros (the PASS runs the SHA-256
; attachment).
(defmacro aut-conn-authed ()
  '(fn-served-result-conn
    (aut-dispatch (fn-served-result-conn
                   (aut-dispatch *aut-conn-req* "AUTHINFO USER reader"))
                  "AUTHINFO PASS correct-horse")))
(defmacro aut-conn-prot-authed ()
  '(fn-served-result-conn
    (aut-dispatch (fn-served-result-conn
                   (aut-dispatch *aut-conn-prot-tls* "AUTHINFO USER reader"))
                  "AUTHINFO PASS correct-horse")))
(assert-event (fn-served-connp (aut-conn-authed)))
(assert-event (fn-auth-session-subject (fn-served-conn-session (aut-conn-authed))))
(assert-event (fn-served-connp (aut-conn-prot-authed)))
(assert-event (fn-auth-session-subject
               (fn-served-conn-session (aut-conn-prot-authed))))

(defconst *aut-k13-hyps*
  '((c1 . (fn-served-connp conn))
    (c2 . (not (fn-auth-session-handshakingp (fn-served-conn-session conn))))
    (c3 . (fn-auth-config-requiredp
           (fn-auth-session-config (fn-served-conn-session conn))))
    (c4 . (not (fn-auth-session-subject (fn-served-conn-session conn))))
    (c5 . (fn-nntp-command-inputp line))
    (c6 . (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
    (c7 . (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))))
(defconst *aut-k13-conclusion*
  '(and (equal (fn-served-result-conn
                (fn-served-dispatch conn (list :command line)))
               conn)
        (equal (fn-served-result-effects
                (fn-served-dispatch conn (list :command line)))
               (fn-auth-single (fn-served-conn-session conn)
                               "480 authentication required"))))
(defmacro aut-k13 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k13-hyps* ,*aut-k13-conclusion*
                 fn-served-dispatch-of-a-gated-command-is-480-and-changes-nothing))

(aut-k13 aut-k13-full (c1 c2 c3 c4 c5 c6 c7))

; The witness: POST, GROUP and ARTICLE on the served connection that
; requires authentication.  The connection after is the connection before,
; field for field, and the one effect is the 480 line.
(assert-event (equal (fn-served-result-conn (aut-dispatch *aut-conn-req* "POST"))
                     *aut-conn-req*))
(assert-event (equal (fn-served-result-effects (aut-dispatch *aut-conn-req* "POST"))
                     (aut-single *aut-480*)))
(assert-event (equal (fn-served-result-conn
                      (aut-dispatch *aut-conn-req* "GROUP fn.letters"))
                     *aut-conn-req*))
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-req* "ARTICLE 1"))
                     (aut-single *aut-480*)))
; Non-degenerate: on the open policy the same POST switches the wire.
(assert-event (not (equal (fn-served-result-conn
                           (aut-dispatch *aut-conn-open* "POST"))
                          *aut-conn-open*)))

; C1 dropped: the forged connection answers nothing.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-forged* "GROUP fn.letters"))
                     nil))
(local (must-fail (aut-k13 aut-k13-without-c1 (c2 c3 c4 c5 c6 c7))))
; C2 dropped: a handshaking connection answers nothing.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-req-hs* "GROUP fn.letters"))
                     nil))
(local (must-fail (aut-k13 aut-k13-without-c2 (c1 c3 c4 c5 c6 c7))))
; C3 dropped: the open policy selects the group.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch *aut-conn-open* "GROUP fn.letters"))
                          (aut-single *aut-480*))))
(local (must-fail (aut-k13 aut-k13-without-c3 (c1 c2 c4 c5 c6 c7))))
; C4 dropped: authenticated, the group is selected.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch (aut-conn-authed) "GROUP fn.letters"))
                          (aut-single *aut-480*))))
(local (must-fail (aut-k13 aut-k13-without-c4 (c1 c2 c3 c5 c6 c7))))
; C5 dropped: the over-long GROUP line.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch-octets *aut-conn-req*
                                                *aut-over-long-line*))
                          (aut-single *aut-480*))))
(local (must-fail (aut-k13 aut-k13-without-c5 (c1 c2 c3 c4 c6 c7))))
; C6 dropped: the over-long GROUP argument.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch-octets *aut-conn-req*
                                                *aut-over-long-argument-line*))
                          (aut-single *aut-480*))))
(local (must-fail (aut-k13 aut-k13-without-c6 (c1 c2 c3 c4 c5 c7))))
; C7 dropped: HELP.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch *aut-conn-req* "HELP"))
                          (aut-single *aut-480*))))
(local (must-fail (aut-k13 aut-k13-without-c7 (c1 c2 c3 c4 c5 c6))))

(defconst *aut-k14-hyps*
  '((e1 . (fn-served-connp conn))
    (e2 . (not (fn-auth-session-handshakingp (fn-served-conn-session conn))))
    (e3 . (not (fn-auth-session-subject (fn-served-conn-session conn))))
    (e4 . (fn-auth-config-protected-onlyp
           (fn-auth-session-config (fn-served-conn-session conn))))
    (e5 . (not (fn-auth-session-tlsp (fn-served-conn-session conn))))
    (e6 . (fn-nntp-command-inputp line))
    (e7 . (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
    (e8 . (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))))
(defconst *aut-k14-conclusion*
  '(and (equal (fn-served-result-conn
                (fn-served-dispatch conn (list :command line)))
               conn)
        (equal (fn-served-result-effects
                (fn-served-dispatch conn (list :command line)))
               (fn-auth-single
                (fn-served-conn-session conn)
                "483 a protected channel is required; use STARTTLS"))))
(defmacro aut-k14 (name keys)
  `(aut-p1-tooth
    ,name ,keys ,*aut-k14-hyps* ,*aut-k14-conclusion*
    fn-served-dispatch-of-authinfo-on-a-clear-connection-is-483-and-changes-nothing))

(aut-k14 aut-k14-full (e1 e2 e3 e4 e5 e6 e7 e8))

; The witness: the clear protected-only connection sends USER, then PASS
; with the right secret.  Each is 483 and leaves the connection as it was.
(assert-event (equal (fn-served-result-conn
                      (aut-dispatch *aut-conn-prot* "AUTHINFO USER reader"))
                     *aut-conn-prot*))
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-prot* "AUTHINFO USER reader"))
                     (aut-single *aut-483*)))
(assert-event (equal (fn-served-result-conn
                      (aut-dispatch *aut-conn-prot* "AUTHINFO PASS correct-horse"))
                     *aut-conn-prot*))

; E1 dropped: the forged protected connection answers nothing.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-forged-prot* "AUTHINFO USER reader"))
                     nil))
(local (must-fail (aut-k14 aut-k14-without-e1 (e2 e3 e4 e5 e6 e7 e8))))
; E2 dropped: handshaking answers nothing.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-prot-hs* "AUTHINFO USER reader"))
                     nil))
(local (must-fail (aut-k14 aut-k14-without-e2 (e1 e3 e4 e5 e6 e7 e8))))
; E3 dropped: authenticated (over TLS) is 502.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch (aut-conn-prot-authed) "AUTHINFO USER reader"))
                     (aut-single "502 already authenticated")))
(local (must-fail (aut-k14 aut-k14-without-e3 (e1 e2 e4 e5 e6 e7 e8))))
; E4 dropped: the required policy in the clear caches the name.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-req* "AUTHINFO USER reader"))
                     (aut-single "381 password required")))
(local (must-fail (aut-k14 aut-k14-without-e4 (e1 e2 e3 e5 e6 e7 e8))))
; E5 dropped: over TLS, 381.
(assert-event (equal (fn-served-result-effects
                      (aut-dispatch *aut-conn-prot-tls* "AUTHINFO USER reader"))
                     (aut-single "381 password required")))
(local (must-fail (aut-k14 aut-k14-without-e5 (e1 e2 e3 e4 e6 e7 e8))))
; E6 dropped: the over-long AUTHINFO line.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch-octets *aut-conn-prot*
                                                *aut-authinfo-over-long-line*))
                          (aut-single *aut-483*))))
(local (must-fail (aut-k14 aut-k14-without-e6 (e1 e2 e3 e4 e5 e7 e8))))
; E7 dropped: the over-long AUTHINFO argument.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch-octets
                            *aut-conn-prot* *aut-authinfo-over-long-argument-line*))
                          (aut-single *aut-483*))))
(local (must-fail (aut-k14 aut-k14-without-e7 (e1 e2 e3 e4 e5 e6 e8))))
; E8 dropped: STARTTLS is 382 and moves the connection into the handshake.
(assert-event (not (equal (fn-served-result-effects
                           (aut-dispatch *aut-conn-prot* "STARTTLS"))
                          (aut-single *aut-483*))))
(local (must-fail (aut-k14 aut-k14-without-e8 (e1 e2 e3 e4 e5 e6 e7))))

; -----------------------------------------------------------------------------
; KEYSTONES 15 to 17: the posting allowance follows the credential.
;
; Two enrolled principals under one required policy: "reader" with the
; posting flag and "guest" without it.

(defconst *aut-p-policy* *aut-role-policy*)
(defconst *aut-p-s* (aut-session *aut-p-policy* nil))
(defconst *aut-p-reader-user* (aut-pinned-after *aut-p-s* "AUTHINFO USER reader"))
(defconst *aut-p-guest-user* (aut-pinned-after *aut-p-s* "AUTHINFO USER guest"))
(defmacro aut-p-reader ()
  '(aut-pinned-after *aut-p-reader-user* "AUTHINFO PASS correct-horse"))
(defmacro aut-p-guest ()
  '(aut-pinned-after *aut-p-guest-user* "AUTHINFO PASS guest-pass"))
(assert-event (fn-auth-sessionp *aut-p-s*))
(assert-event (equal (fn-auth-session-subject (aut-p-reader)) *aut-principal*))
(assert-event (equal (fn-auth-session-subject (aut-p-guest)) *aut-principal-guest*))
; A session whose subject is not the principal of the credential under its
; cached name.  No command sequence reaches it; it is here only to refute
; the statements that leave out the premise excluding it.
(defconst *aut-p-mismatch*
  (fn-auth-make-session (fn-auth-session-base *aut-p-s*) *aut-p-policy*
                        *aut-name* *aut-principal-guest* nil nil))
(assert-event (fn-auth-sessionp *aut-p-mismatch*))

(defconst *aut-k15-hyps*
  '((l1 . (not (fn-auth-session-subject as)))
    (l2 . (fn-auth-session-subject
           (fn-post-result-session
            (fn-auth-step-pinned as archive index verdicts config
                                 observation injection wire-event))))))
(defconst *aut-k15-conclusion*
  '(iff (fn-auth-postingp
         (fn-post-result-session
          (fn-auth-step-pinned as archive index verdicts config
                               observation injection wire-event)))
        (fn-auth-cred-postingp
         (fn-auth-find-cred (fn-auth-session-pending as)
                            (fn-auth-config-creds
                             (fn-auth-session-config as))))))
(defmacro aut-k15 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k15-hyps* ,*aut-k15-conclusion*
                 fn-auth-step-pinned-login-installs-the-credential-posting-flag))

(aut-k15 aut-k15-full (l1 l2))

; The witness, both ways: the reader's login installs a posting allowance,
; the guest's installs none, under the same policy and the same injection
; configuration (which allows posting).
(assert-event (fn-auth-postingp (aut-p-reader)))
(assert-event (not (fn-auth-postingp (aut-p-guest))))
(assert-event (fn-inj-config-allow *aut-config*))

; L1 dropped: the mismatched session keeps its subject over HELP; its
; allowance is false while the credential under its cached name posts.
(assert-event (equal (fn-auth-session-subject (aut-pinned-after *aut-p-mismatch* "HELP"))
                     *aut-principal-guest*))
(assert-event (not (fn-auth-postingp (aut-pinned-after *aut-p-mismatch* "HELP"))))
(assert-event (fn-auth-cred-postingp
               (fn-auth-find-cred *aut-name* (list *aut-cred* *aut-cred-guest*))))
(local (must-fail (aut-k15 aut-k15-without-l1 (l2))))
; L2 dropped: USER reader cached, no login yet; HELP leaves it unauthenticated
; under the required policy, so the allowance is false while the credential
; under the cached name posts.
(assert-event (null (fn-auth-session-subject
                     (aut-pinned-after *aut-p-reader-user* "HELP"))))
(assert-event (not (fn-auth-postingp (aut-pinned-after *aut-p-reader-user* "HELP"))))
(local (must-fail (aut-k15 aut-k15-without-l2 (l1))))

(defconst *aut-k16-hyps*
  '((p1 . (fn-auth-sessionp as))
    (p2 . (not (fn-auth-session-handshakingp as)))
    (p3 . (fn-auth-session-subject as))
    (p4 . (not (fn-auth-cred-postingp
                (fn-auth-find-cred (fn-auth-session-pending as)
                                   (fn-auth-config-creds
                                    (fn-auth-session-config as))))))
    (p5 . (fn-nntp-command-inputp line))
    (p6 . (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
    (p7 . (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))))
(defconst *aut-k16-conclusion*
  '(and (equal (fn-post-result-effects
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               (fn-auth-single
                as "440 posting not permitted for this principal"))
        (equal (fn-post-result-session
                (fn-auth-step-pinned as archive index verdicts config
                                     observation injection
                                     (list :command line)))
               as)
        (null (fn-post-result-submission
               (fn-auth-step-pinned as archive index verdicts config
                                    observation injection
                                    (list :command line))))))
(defmacro aut-k16 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k16-hyps* ,*aut-k16-conclusion*
                 fn-auth-step-pinned-post-by-a-principal-without-the-flag-is-440))

(aut-k16 aut-k16-full (p1 p2 p3 p4 p5 p6 p7))

(defconst *aut-440* "440 posting not permitted for this principal")
; The witness: the guest logs in and sends POST.  440, session unchanged.
(assert-event (equal (aut-pinned-reply (aut-p-guest) "POST") (aut-single *aut-440*)))
(assert-event (equal (aut-pinned-after (aut-p-guest) "POST") (aut-p-guest)))
(assert-event (null (fn-post-result-submission (aut-pinned (aut-p-guest) "POST"))))
; Non-degenerate: the reader, same policy, is offered 340.
(assert-event (fn-post-offeredp (aut-pinned-reply (aut-p-reader) "POST")))

; P1 dropped: a value with the guest's fields over a non-session base.
(defconst *aut-p-forged-guest*
  (fn-auth-make-session :not-a-peer-session *aut-p-policy*
                        (fn-nntp-string-octets "guest") *aut-principal-guest*
                        nil nil))
(assert-event (not (fn-auth-sessionp *aut-p-forged-guest*)))
(assert-event (equal (aut-pinned-reply *aut-p-forged-guest* "POST") nil))
(local (must-fail (aut-k16 aut-k16-without-p1 (p2 p3 p4 p5 p6 p7))))
; P2 dropped: the guest's fields, handshaking: answered nothing.
(defconst *aut-p-hs-guest*
  (fn-auth-make-session (fn-auth-session-base *aut-p-s*) *aut-p-policy*
                        (fn-nntp-string-octets "guest") *aut-principal-guest*
                        nil t))
(assert-event (fn-auth-sessionp *aut-p-hs-guest*))
(assert-event (equal (aut-pinned-reply *aut-p-hs-guest* "POST") nil))
(local (must-fail (aut-k16 aut-k16-without-p2 (p1 p3 p4 p5 p6 p7))))
; P3 dropped: no subject and no cached name: the gate answers 480.
(assert-event (equal (aut-pinned-reply *aut-p-s* "POST") (aut-single *aut-480*)))
(local (must-fail (aut-k16 aut-k16-without-p3 (p1 p2 p4 p5 p6 p7))))
; P4 dropped: the reader is offered 340 (witness above).
(local (must-fail (aut-k16 aut-k16-without-p4 (p1 p2 p3 p5 p6 p7))))
; P5 dropped: an over-long POST line goes to the reader preflight.
(defconst *aut-post-over-long-line*
  (append (fn-nntp-string-octets "POST ")
          (make-list 490 :initial-element 97)
          '(32)
          (make-list 30 :initial-element 98)))
(assert-event (not (fn-nntp-command-inputp *aut-post-over-long-line*)))
(assert-event (fn-nntp-command-arguments-at-mostp
               (fn-nntp-tokenize *aut-post-over-long-line*)))
(assert-event (fn-nntp-keywordp (car (fn-nntp-tokenize *aut-post-over-long-line*))
                                "POST"))
(assert-event (not (equal (fn-post-result-effects
                           (aut-pinned-octets (aut-p-guest)
                                              *aut-post-over-long-line*))
                          (aut-single *aut-440*))))
(local (must-fail (aut-k16 aut-k16-without-p5 (p1 p2 p3 p4 p6 p7))))
; P6 dropped: an over-long POST argument.
(defconst *aut-post-over-long-argument-line*
  (append (fn-nntp-string-octets "POST ")
          (make-list 498 :initial-element 97)))
(assert-event (fn-nntp-command-inputp *aut-post-over-long-argument-line*))
(assert-event (not (fn-nntp-command-arguments-at-mostp
                    (fn-nntp-tokenize *aut-post-over-long-argument-line*))))
(assert-event (not (equal (fn-post-result-effects
                           (aut-pinned-octets (aut-p-guest)
                                              *aut-post-over-long-argument-line*))
                          (aut-single *aut-440*))))
(local (must-fail (aut-k16 aut-k16-without-p6 (p1 p2 p3 p4 p5 p7))))
; P7 dropped: the guest may read.
(assert-event (not (equal (aut-pinned-reply (aut-p-guest) "GROUP fn.letters")
                          (aut-single *aut-440*))))
(local (must-fail (aut-k16 aut-k16-without-p7 (p1 p2 p3 p4 p5 p6))))

(defconst *aut-k17-hyps*
  '((d1 . (fn-auth-sessionp as))
    (d2 . (not (fn-auth-session-handshakingp as)))
    (d3 . (fn-auth-cred-postingp
           (fn-auth-find-cred (fn-auth-session-pending as)
                              (fn-auth-config-creds
                               (fn-auth-session-config as)))))
    (d4 . (equal (fn-auth-cred-principal
                  (fn-auth-find-cred (fn-auth-session-pending as)
                                     (fn-auth-config-creds
                                      (fn-auth-session-config as))))
                 (fn-auth-session-subject as)))
    (d5 . (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))))
(defconst *aut-k17-conclusion*
  '(equal (fn-auth-step-pinned as archive index verdicts config
                               observation injection (list :command line))
          (fn-auth-delegate-pinned as archive index verdicts config
                                   observation injection
                                   (list :command line))))
(defmacro aut-k17 (name keys)
  `(aut-p1-tooth ,name ,keys ,*aut-k17-hyps* ,*aut-k17-conclusion*
                 fn-auth-step-pinned-post-by-a-principal-with-the-flag-is-delegated))

(aut-k17 aut-k17-full (d1 d2 d3 d4 d5))

; The witness: the reader's POST is the delegated POST, and that is the 340
; offer (the pinned injection configuration allows posting).
(assert-event (equal (aut-pinned (aut-p-reader) "POST")
                     (aut-delegated (aut-p-reader) "POST")))
(assert-event (fn-post-offeredp
               (fn-post-result-effects (aut-delegated (aut-p-reader) "POST"))))

; D1 dropped: the reader's fields with a TLS flag that is not a boolean: not
; a session, answered nothing, while the delegation offers 340.
(defmacro aut-p-bad-tls-reader ()
  '(fn-auth-make-session (fn-auth-session-base (aut-p-reader)) *aut-p-policy*
                         *aut-name* *aut-principal* :maybe nil))
(assert-event (not (fn-auth-sessionp (aut-p-bad-tls-reader))))
(assert-event (not (equal (aut-pinned (aut-p-bad-tls-reader) "POST")
                          (aut-delegated (aut-p-bad-tls-reader) "POST"))))
(local (must-fail (aut-k17 aut-k17-without-d1 (d2 d3 d4 d5))))
; D2 dropped: the reader's fields, handshaking.
(defmacro aut-p-hs-reader ()
  '(fn-auth-make-session (fn-auth-session-base (aut-p-reader)) *aut-p-policy*
                         *aut-name* *aut-principal* nil t))
(assert-event (fn-auth-sessionp (aut-p-hs-reader)))
(assert-event (not (equal (aut-pinned (aut-p-hs-reader) "POST")
                          (aut-delegated (aut-p-hs-reader) "POST"))))
(local (must-fail (aut-k17 aut-k17-without-d2 (d1 d3 d4 d5))))
; D3 dropped: the guest is answered 440, not delegated.
(assert-event (not (equal (aut-pinned (aut-p-guest) "POST")
                          (aut-delegated (aut-p-guest) "POST"))))
(local (must-fail (aut-k17 aut-k17-without-d3 (d1 d2 d4 d5))))
; D4 dropped: the reader's name is cached but nobody has logged in; the
; gate answers 480.
(assert-event (not (equal (aut-pinned *aut-p-reader-user* "POST")
                          (aut-delegated *aut-p-reader-user* "POST"))))
(local (must-fail (aut-k17 aut-k17-without-d4 (d1 d2 d3 d5))))
; D5 dropped: AUTHINFO from the logged-in reader is 502, not delegated.
(assert-event (not (equal (aut-pinned (aut-p-reader) "AUTHINFO USER reader")
                          (aut-delegated (aut-p-reader) "AUTHINFO USER reader"))))
(local (must-fail (aut-k17 aut-k17-without-d5 (d1 d2 d3 d4))))
