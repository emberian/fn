; Witnesses and teeth for the pull session (books/peer-pull-session.lisp,
; PRF-125): the feed's protected preamble in front of the NEWNEWS round.
;
; The witness is one whole TLS session as the host drives it: A's greeting,
; the 382, the host's TLS report, 381 and 281 to the credential, then the
; round of tests/acl2/peer-pull-tests.lisp (DATE, a NEWNEWS listing one
; Message-ID, the local node's greeting, 335, the article, 235).
(in-package "ACL2")
(include-book "../../books/peer-pull-session")
(include-book "must-fail-checked")

(defun ps-line (s) (append (fn-record-string-octets s) '(13 10)))
(defun ps-begin (plan c now cred)
  (mv-let (s e) (fn-pull-session-begin plan c now cred) (list s e)))
(defun ps-run (s es) (mv-let (a b) (fn-pull-session-run s es) (list a b)))

(defconst *ps-peer* (fn-record-string-octets "A"))
(defconst *ps-wildmat* (fn-record-string-octets "fn.*"))
(defconst *ps-now* 811000000000)
(defconst *ps-fresh* (fn-pull-fresh-cursor *ps-peer*))
(defconst *ps-user* (fn-record-string-octets "nodeB"))
(defconst *ps-pass* (fn-record-string-octets "s3cret"))
(defconst *ps-cred* (list *ps-user* *ps-pass*))
(defconst *ps-starttls* (list :tls :starttls "localhost" "/a/anchor.pem"))
(defconst *ps-auth* (list :authinfo "/b/A.fnauth" nil))
(defconst *ps-lab-auth* (list :authinfo "/b/A.fnauth" t))
(defun ps-plan (host security auth)
  (list *ps-peer* (fn-record-string-octets host) 11119 *ps-wildmat* 2000
        security auth *fn-pull-default-unavailable-rounds*))

(defconst *ps-tls-plan* (ps-plan "10.1.2.3" *ps-starttls* *ps-auth*))
(defconst *ps-lab-plan* (ps-plan "127.0.0.1" (list :clear) *ps-lab-auth*))

; -----------------------------------------------------------------------------
; The plan read from configuration rows carries the security and the
; credential policy.
(defconst *ps-rows*
  (list (fn-cfg-row-make "A" "path-identity" "a.example" 0)
        (fn-cfg-row-make "A" "transport-nntp" "10.1.2.3" 11119)
        (fn-cfg-row-make "A" "transport-security" "starttls" 1)
        (fn-cfg-row-make "A" "transport-server-name" "localhost" 0)
        (fn-cfg-row-make "A" "transport-trust-anchor" "/a/anchor.pem" 0)
        (fn-cfg-row-make "A" "inbound-groups" "fn.*" 1048576)
        (fn-cfg-row-make "A" "inbound-inflight" "" 4)
        (fn-cfg-row-make "A" "outbound-auth-profile" "/b/A.fnauth" 0)
        (fn-cfg-row-make "A" "pull-interval" "" 2)))
(assert-event (equal (fn-pull-plans *ps-rows*) (list *ps-tls-plan*)))
(assert-event (equal (fn-pull-plan-verdict *ps-tls-plan*) :tls))
(assert-event (equal (fn-pull-plan-profile-path *ps-tls-plan*) "/b/A.fnauth"))

; -----------------------------------------------------------------------------
; The TLS session, end to end.
(defconst *ps-b0* (ps-begin *ps-tls-plan* *ps-fresh* *ps-now* *ps-cred*))
(defconst *ps-s0* (car *ps-b0*))
(defconst *ps-first* (- *ps-now* *fn-pull-first-window-ms*))
; The begin journals the first instant, then dials; nothing else.
(assert-event (equal (cadr *ps-b0*)
                     (list (cons :journal (list *ps-peer* *ps-first* 0 nil))
                           (list :dial))))

(defconst *ps-preamble*
  (list (cons :remote (ps-line "200 A ready"))
        (cons :remote (ps-line "382 begin TLS"))
        (list :tls-up)
        (cons :remote (ps-line "381 password"))
        (cons :remote (ps-line "281 ok"))))
(defconst *ps-round-events*
  (list (cons :remote (ps-line "111 20260925120000"))
        (cons :remote (append (ps-line "230 list follows")
                              (ps-line "<a@fn.invalid>")
                              (ps-line ".")))
        (cons :local (ps-line "200 transit"))
        (cons :local (ps-line "335 send it"))
        (cons :remote (append (ps-line "220 0 <a@fn.invalid>")
                              (ps-line "Subject: s") (ps-line "")
                              (ps-line "body") (ps-line ".")))
        (cons :local (ps-line "235 accepted"))))
(defconst *ps-events* (append *ps-preamble* *ps-round-events*))
(defconst *ps-run* (ps-run *ps-s0* *ps-events*))
(defconst *ps-end* (car *ps-run*))
(defconst *ps-effects* (cadr *ps-run*))

; The wire, in order: STARTTLS, the handshake against the plan's server name
; and anchor, USER and PASS (the profile's bytes), DATE, the one NEWNEWS,
; the local IHAVE, ARTICLE, the forwarded article, QUIT, close.
(assert-event
 (equal (fn-pull-remote-effects *ps-effects*)
        (list (ps-line "STARTTLS")
              (ps-line "AUTHINFO USER nodeB")
              (ps-line "AUTHINFO PASS s3cret")
              (ps-line "DATE")
              (fn-pull-newnews-octets *ps-wildmat* *ps-first*)
              (append (fn-record-string-octets "ARTICLE ") (ps-line "<a@fn.invalid>"))
              (ps-line "QUIT"))))
(assert-event (member-equal (list :tls "localhost" "/a/anchor.pem") *ps-effects*))
(assert-event (equal (fn-pull-r-phase (fn-pull-s-round *ps-end*)) :done))
(assert-event (fn-pull-session-readyp *ps-end*))
(assert-event (equal (fn-pull-session-log-line *ps-end*)
                     (fn-record-string-octets
                      "pull peer=A round=done cursor=advanced transport=tls")))

; KEYSTONE fn-pull-session-credentials-wait-for-tls-and-login.
; Witness: the observations of that session obey the feed's gate, and the
; gate's stages were each reached (382, the TLS report, 281): the complete
; antecedent (verdict :tls) and conclusion on a run that sends the secret.
(defconst *ps-obs* (fn-pull-session-obs *ps-s0* *ps-events*))
(assert-event (equal (fn-pull-plan-verdict *ps-tls-plan*) :tls))
(assert-event (fn-fc-gate-okp (fn-fc-gate-start (fn-fc-security (fn-pull-s-fc *ps-s0*)))
                              (fn-fc-loginp (fn-pull-s-fc *ps-s0*))
                              *ps-obs*))
(assert-event (equal (strip-cars *ps-obs*)
                     '(:starttls :need-input :tls :auth-user :need-input
                       :auth-pass :need-input :ready)))
(assert-event (fn-fc-loginp (fn-pull-s-fc *ps-s0*)))
; Mutation: a peer that answers the greeting with 381 on a TLS plan never
; gets the credential; the round fails in the preamble, the cursor held.
(defconst *ps-inject*
  (ps-run *ps-s0* (list (cons :remote (append (ps-line "200 A ready")
                                              (ps-line "381 send it"))))))
(assert-event (equal (fn-pull-remote-effects (cadr *ps-inject*))
                     (list (ps-line "STARTTLS"))))
(assert-event (fn-pull-session-done-p (car *ps-inject*)))
(assert-event (equal (fn-pull-session-log-line (car *ps-inject*))
                     (fn-record-string-octets
                      "pull peer=A round=failed cursor=held at=preamble")))
; Tooth (verdict :tls): the loopback-lab plan (clear, credential, explicit
; permission, 127.0.0.1) is not :tls, and its session sends the credential
; before any 382 or TLS report: the gate fails on its observations.
(defconst *ps-lab-s0* (car (ps-begin *ps-lab-plan* *ps-fresh* *ps-now* *ps-cred*)))
(defconst *ps-lab-events*
  (list (cons :remote (ps-line "200 A ready"))
        (cons :remote (ps-line "381 password"))
        (cons :remote (ps-line "281 ok"))))
(assert-event (equal (fn-pull-plan-verdict *ps-lab-plan*) :clear-lab))
(assert-event (equal (fn-pull-remote-effects (cadr (ps-run *ps-lab-s0* *ps-lab-events*)))
                     (list (ps-line "AUTHINFO USER nodeB")
                           (ps-line "AUTHINFO PASS s3cret")
                           (ps-line "DATE"))))
(must-fail-checked
 (assert-event (fn-fc-gate-okp (fn-fc-gate-start (fn-fc-security (fn-pull-s-fc *ps-lab-s0*)))
                               (fn-fc-loginp (fn-pull-s-fc *ps-lab-s0*))
                               (fn-pull-session-obs *ps-lab-s0* *ps-lab-events*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-pull-session-refuses-a-clear-credential-without-the-lab-exception.
; Witness: a clear transport to 127.0.0.1 with a credential whose profile
; lacks the permission.  Every antecedent literal holds; every conclusion.
(defconst *ps-refused-plan* (ps-plan "127.0.0.1" (list :clear) *ps-auth*))
(defconst *ps-rb* (ps-begin *ps-refused-plan* *ps-fresh* *ps-now* nil))
(assert-event (equal (fn-pull-plan-security *ps-refused-plan*) '(:clear)))
(assert-event (fn-pull-plan-auth *ps-refused-plan*))
(assert-event (not (equal (fn-pull-auth-allow-clear *ps-auth*) t)))
(assert-event (equal (fn-pull-plan-verdict *ps-refused-plan*) :refused-clear-credential))
(assert-event (null (fn-pull-plan-profile-path *ps-refused-plan*)))
(assert-event (equal (cadr *ps-rb*)
                     (list (cons :journal (list *ps-peer* *ps-first* 0 nil)) (list :close))))
(assert-event (equal (ps-run (car *ps-rb*) *ps-events*) (list (car *ps-rb*) nil)))
(assert-event (equal (fn-pull-session-close (car *ps-rb*))
                     (list *ps-peer* *ps-first* 0 nil)))
(assert-event (equal (fn-pull-session-log-line (car *ps-rb*))
                     (fn-record-string-octets
                      "pull peer=A round=failed cursor=held refused=clear-credential")))
; The permission without a loopback literal is refused too.
(assert-event (equal (fn-pull-plan-verdict (ps-plan "10.1.2.3" (list :clear) *ps-lab-auth*))
                     :refused-clear-credential))
; Tooth (clear security): the same credential over STARTTLS dials.
(must-fail-checked
 (assert-event (not (member-equal (list :dial)
                                  (cadr (ps-begin (ps-plan "127.0.0.1" *ps-starttls* *ps-auth*)
                                                  *ps-fresh* *ps-now* *ps-cred*))))))
; Tooth (a credential): a clear anonymous pull dials (PRF-100's pull).
(must-fail-checked
 (assert-event (not (member-equal (list :dial)
                                  (cadr (ps-begin (ps-plan "127.0.0.1" (list :clear) nil)
                                                  *ps-fresh* *ps-now* nil))))))
; Tooth (no lab exception): permission and a loopback literal dial.
(must-fail-checked
 (assert-event (not (member-equal (list :dial)
                                  (cadr (ps-begin *ps-lab-plan* *ps-fresh* *ps-now*
                                                  *ps-cred*))))))
; A TLS plan whose profile could not be read is refused, never dialled
; without its credential.
(assert-event (equal (fn-pull-s-refusal (car (ps-begin *ps-tls-plan* *ps-fresh* *ps-now* nil)))
                     :refused-profile))

; -----------------------------------------------------------------------------
; After :ready the round is PRF-100's.
; fn-pull-begin-ready-is-the-round-after-the-greeting: witness on a 200.
(assert-event
 (equal (mv-let (r e c) (fn-pull-on-line (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*)
                                         (fn-record-string-octets "200 A ready"))
          (list r e c))
        (list (fn-pull-begin-ready *ps-fresh* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*)
              (list (cons :remote (ps-line "DATE"))) t)))
; Tooth (a greeting code): a 400 does not enter the ready round.
(must-fail-checked
 (assert-event
  (equal (mv-let (r e c) (fn-pull-on-line (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*)
                                          (fn-record-string-octets "400 go away"))
           (declare (ignore e c))
           r)
         (fn-pull-begin-ready *ps-fresh* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*))))

; KEYSTONE fn-pull-session-journal-is-the-cursor-at-every-cut.
; Witness: from the fresh cursor through the TLS session to its close.
(defconst *ps-j0* (fn-pull-journal-effects (cadr *ps-b0*)))
(assert-event (equal (fn-pull-replay *ps-fresh* *ps-j0*)
                     (fn-pull-round-cursor (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*))))
(assert-event (equal (fn-pull-replay *ps-fresh*
                                     (append *ps-j0* (fn-pull-journal-effects *ps-effects*)))
                     (fn-pull-round-cursor (fn-pull-s-round *ps-end*))))
(assert-event (equal (fn-pull-replay *ps-fresh*
                                     (append *ps-j0* (fn-pull-journal-effects
                                                      (fn-pull-session-close-effects *ps-end*))))
                     (fn-pull-session-close *ps-end*)))
(assert-event (equal (fn-pull-session-close *ps-end*)
                     (list *ps-peer* (- (fn-pull-date-ms (fn-record-string-octets
                                                          "111 20260925120000"))
                                        *fn-pull-overlap-ms*)
                           1 nil)))
; Every cut inside the preamble recovers the begin's cursor: a kill after
; STARTTLS, after the TLS report or after the credential journals nothing.
(assert-event
 (null (fn-pull-journal-effects (cadr (ps-run *ps-s0* (take 3 *ps-preamble*))))))
; Tooth (the journal replays to C): an older journaled instant with a
; journaled (not fresh) C: the begin journals nothing and the replay is not
; the round's cursor.
(defconst *ps-held-c* (list *ps-peer* 900 2 nil))
(must-fail-checked
 (assert-event (equal (fn-pull-replay *ps-fresh*
                                      (append (list (list *ps-peer* 5 0 nil))
                                              (fn-pull-journal-effects
                                               (cadr (ps-begin *ps-tls-plan* *ps-held-c*
                                                               *ps-now* *ps-cred*)))))
                      (fn-pull-round-cursor (fn-pull-begin *ps-held-c* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*)))))
; Tooth (startable C): a cursor whose advance count is not a natural.
(defconst *ps-bad* (list *ps-peer* 5 -1 nil))
(must-fail-checked
 (assert-event (equal (fn-pull-replay *ps-bad*
                                      (fn-pull-journal-effects
                                       (cadr (ps-begin *ps-tls-plan* *ps-bad* *ps-now*
                                                       *ps-cred*))))
                      (fn-pull-round-cursor (fn-pull-begin *ps-bad* *ps-wildmat* *ps-now* *fn-pull-default-unavailable-rounds*)))))

; -----------------------------------------------------------------------------
; PRF-165 over the host's step and close: a clear anonymous session whose
; peer lists <a> and <b>, answers ARTICLE <a> with 430, and whose local
; node has <b>.  Bound 2 from the plan.
(defconst *ps-u-plan* (list *ps-peer* (fn-record-string-octets "127.0.0.1") 119
                            *ps-wildmat* 2000 (list :clear) nil 2))
(defconst *ps-a* (fn-record-string-octets "<a@fn.invalid>"))
(defconst *ps-u-events*
  (list (cons :remote (ps-line "200 A ready"))
        (cons :remote (ps-line "111 20260925120000"))
        (cons :remote (append (ps-line "230 list follows") (ps-line "<a@fn.invalid>")
                              (ps-line "<b@fn.invalid>") (ps-line ".")))
        (cons :local (ps-line "200 transit"))
        (cons :local (ps-line "335 send it"))
        (cons :remote (ps-line "430 no such article"))
        (cons :local (ps-line "200 transit"))
        (cons :local (ps-line "435 have it"))))
(defconst *ps-u-s0* (car (ps-begin *ps-u-plan* *ps-fresh* *ps-now* nil)))
(defconst *ps-u1* (car (ps-run *ps-u-s0* *ps-u-events*)))
(defconst *ps-u1-close* (fn-pull-session-close *ps-u1*))
(defconst *ps-u2-s0* (car (ps-begin *ps-u-plan* *ps-u1-close* (+ *ps-now* 60000) nil)))
(defconst *ps-u2* (car (ps-run *ps-u2-s0* *ps-u-events*)))
(defconst *ps-u2-close* (fn-pull-session-close *ps-u2*))
(assert-event (equal (fn-pull-r-bound (fn-pull-s-round *ps-u1*)) 2))

; KEYSTONE fn-pull-session-unavailable-id-is-retried-below-the-bound.
(assert-event (member-equal *ps-a* (fn-pull-list (fn-pull-r-unavailable (fn-pull-s-round *ps-u1*)))))
(assert-event (fn-pull-completep (fn-pull-s-round *ps-u1*)))
(assert-event (equal (fn-pull-cursor-since *ps-u1-close*) (fn-pull-r-since (fn-pull-s-round *ps-u1*))))
(assert-event (equal (fn-pull-count-of *ps-a* (fn-pull-cursor-pending *ps-u1-close*)) 1))
; Tooth (below the bound): the second session's close moves the instant.
(must-fail-checked (assert-event (equal (fn-pull-cursor-since *ps-u2-close*)
                                (fn-pull-r-since (fn-pull-s-round *ps-u2*)))))

; KEYSTONE fn-pull-session-complete-round-past-the-bound-advances and
; fn-pull-session-close-advances-only-past-a-fully-answered-round.
(assert-event (equal (fn-pull-cursor-advances *ps-u2-close*) 1))
(assert-event (null (fn-pull-cursor-pending *ps-u2-close*)))
(assert-event (fn-pull-all-answered-or-droppedp
               (fn-pull-r-listed (fn-pull-s-round *ps-u2*)) (fn-pull-r-answers (fn-pull-s-round *ps-u2*))
               (fn-pull-r-unavailable (fn-pull-s-round *ps-u2*)) (fn-pull-r-pending (fn-pull-s-round *ps-u2*))
               (fn-pull-r-bound (fn-pull-s-round *ps-u2*))))
(assert-event (equal (fn-pull-session-log-line *ps-u2*)
                     (append (fn-record-string-octets
                              "pull peer=A round=done cursor=advanced unavailable=1 dropped=")
                             *ps-a* (fn-record-string-octets " transport=clear"))))
; Tooth (the antecedent / not holding): the first session holds.
(must-fail-checked (assert-event (equal (fn-pull-cursor-advances *ps-u1-close*) 1)))

; KEYSTONE fn-pull-session-step-marks-unavailable-only-on-the-peers-reply.
(defconst *ps-u-article* (car (ps-run *ps-u-s0* (take 5 *ps-u-events*))))
(assert-event (fn-pull-session-readyp *ps-u-article*))
(assert-event (equal (fn-pull-r-phase (fn-pull-s-round *ps-u-article*)) :article))
(assert-event (equal (fn-pull-r-unavailable
                      (fn-pull-s-round (car (ps-run *ps-u-article* (list (nth 5 *ps-u-events*))))))
                     (list *ps-a*)))
; Tooth (after the preamble): a 430 before :ready (as the peer's greeting)
; marks nothing.
(assert-event (null (fn-pull-r-unavailable
                     (fn-pull-s-round (car (ps-run *ps-u-s0* (list (cons :remote (ps-line "430 no")))))))))
(must-fail-checked (assert-event (fn-pull-session-readyp *ps-u-s0*)))

; -----------------------------------------------------------------------------
; friend-path-2: every failed step names why
; (fn-pull-session-failure-names-every-failed-step).  The host carries the
; first failure of a round (fn-pull-session-step-triple) into its log line.
(defun ps-why-run (s es why)
  (if (consp es)
      (let ((tr (fn-pull-session-step-triple s (car es))))
        (ps-why-run (car tr) (cdr es) (or why (caddr tr))))
    (list s why)))

; Positive: the peer refuses the login after the password (481): the round
; fails in the preamble, and the reason is the refusal, its code and phase.
(defconst *ps-481*
  (ps-why-run *ps-s0* (list (cons :remote (ps-line "200 A ready"))
                            (cons :remote (ps-line "382 begin TLS"))
                            (list :tls-up)
                            (cons :remote (ps-line "381 password"))
                            (cons :remote (ps-line "481 authentication failed")))
              nil))
(assert-event (fn-pull-session-done-p (car *ps-481*)))
(assert-event (equal (cadr *ps-481*) '("login-refused" 481 "auth-pass")))
(assert-event (equal (fn-pull-session-log-line-why (car *ps-481*) (cadr *ps-481*))
                     (fn-record-string-octets
                      "pull peer=A round=failed cursor=held at=preamble reason=login-refused code=481 phase=auth-pass")))
; The old mutation, now with its reason: 381 where 382 was due.
(defconst *ps-381*
  (ps-why-run *ps-s0* (list (cons :remote (append (ps-line "200 A ready")
                                                  (ps-line "381 send it"))))
              nil))
(assert-event (equal (cadr *ps-381*) '("starttls-refused" 381 "starttls")))
; A lost connection names its cause, before and after :ready.
(assert-event (equal (cadr (ps-why-run *ps-s0* (list (list :lost :dial)) nil))
                     '("lost-dial" nil "preamble")))
(defconst *ps-lost-after*
  (ps-why-run *ps-s0* (append *ps-preamble* (list (list :lost :timeout))) nil))
(assert-event (fn-pull-session-done-p (car *ps-lost-after*)))
(assert-event (equal (car (cadr *ps-lost-after*)) "lost-timeout"))
(assert-event (equal (fn-pull-session-log-line-why (car *ps-lost-after*) (cadr *ps-lost-after*))
                     (append (fn-pull-session-log-line (car *ps-lost-after*))
                             (fn-record-string-octets " reason=lost-timeout")
                             (fn-record-string-octets " phase=")
                             (fn-record-string-octets (caddr (cadr *ps-lost-after*))))))
; A bare (:lost) still fails and is named `lost'.
(assert-event (equal (cadr (ps-why-run *ps-s0* (list (list :lost)) nil))
                     '("lost" nil "preamble")))
; Teeth: a round that completes names no failure at any step, and its line
; is the line it always was.
(defconst *ps-ok* (ps-why-run *ps-s0* *ps-events* nil))
(assert-event (null (cadr *ps-ok*)))
(assert-event (equal (fn-pull-session-log-line-why (car *ps-ok*) (cadr *ps-ok*))
                     (fn-pull-session-log-line (car *ps-ok*))))
; A step on a round that already ended names nothing (the done hypothesis).
(assert-event (null (caddr (fn-pull-session-step-triple (car *ps-481*) (list :lost :eof)))))
; The iff without its done conjunct fails: the ended round's own phase is :failed.
(must-fail-checked
 (defthm ps-failure-without-done
   (let* ((s2 (car (fn-pull-session-step s event))))
     (iff (fn-pull-session-failure s event s2)
          (equal (fn-pull-r-phase (fn-pull-s-round s2)) :failed)))
   :hints (("Goal" :in-theory (e/d (fn-pull-session-failure)
                                   (fn-pull-session-step fn-pull-done-p
                                    fn-pull-session-readyp fn-pull-preamble-why
                                    fn-pull-session-fc-events))))
   :rule-classes nil))

; The feed's line for a refused login (fn-peer-feed-failure-line): the same
; words, from the machine before the chunk and its step on it.
(defconst *ps-auth-pass-fc*
  (fn-pull-s-fc (car (ps-why-run *ps-s0* (list (cons :remote (ps-line "200 A ready"))
                                               (cons :remote (ps-line "382 begin TLS"))
                                               (list :tls-up)
                                               (cons :remote (ps-line "381 password")))
                                 nil))))
(assert-event (equal (fn-fc-phase *ps-auth-pass-fc*) :auth-pass))
(assert-event
 (equal (fn-peer-feed-failure-line "A" *ps-auth-pass-fc*
                                   (fn-fc-step *ps-auth-pass-fc* (ps-line "481 no"))
                                   (ps-line "481 no"))
        (fn-record-string-octets
         "refused feed peer=A connection=failed reason=login-refused code=481 phase=auth-pass")))
(assert-event (equal (fn-peer-feed-lost-line "A" :eof)
                     (fn-record-string-octets
                      "refused feed peer=A connection=failed reason=lost-eof")))
