; Witnesses and teeth for the pull session (books/peer-pull-session.lisp,
; PRF-125): the feed's protected preamble in front of the NEWNEWS round.
;
; The witness is one whole TLS session as the host drives it: A's greeting,
; the 382, the host's TLS report, 381 and 281 to the credential, then the
; round of tests/acl2/peer-pull-tests.lisp (DATE, a NEWNEWS listing one
; Message-ID, the local node's greeting, 335, the article, 235).
(in-package "ACL2")
(include-book "../../books/peer-pull-session")
(include-book "std/testing/must-fail" :dir :system)

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
        security auth))

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
                     (list (cons :journal (list *ps-peer* *ps-first* 0))
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
(must-fail
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
                     (list (cons :journal (list *ps-peer* *ps-first* 0)) (list :close))))
(assert-event (equal (ps-run (car *ps-rb*) *ps-events*) (list (car *ps-rb*) nil)))
(assert-event (equal (fn-pull-session-close (car *ps-rb*))
                     (list *ps-peer* *ps-first* 0)))
(assert-event (equal (fn-pull-session-log-line (car *ps-rb*))
                     (fn-record-string-octets
                      "pull peer=A round=failed cursor=held refused=clear-credential")))
; The permission without a loopback literal is refused too.
(assert-event (equal (fn-pull-plan-verdict (ps-plan "10.1.2.3" (list :clear) *ps-lab-auth*))
                     :refused-clear-credential))
; Tooth (clear security): the same credential over STARTTLS dials.
(must-fail
 (assert-event (not (member-equal (list :dial)
                                  (cadr (ps-begin (ps-plan "127.0.0.1" *ps-starttls* *ps-auth*)
                                                  *ps-fresh* *ps-now* *ps-cred*))))))
; Tooth (a credential): a clear anonymous pull dials (PRF-100's pull).
(must-fail
 (assert-event (not (member-equal (list :dial)
                                  (cadr (ps-begin (ps-plan "127.0.0.1" (list :clear) nil)
                                                  *ps-fresh* *ps-now* nil))))))
; Tooth (no lab exception): permission and a loopback literal dial.
(must-fail
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
 (equal (mv-let (r e c) (fn-pull-on-line (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now*)
                                         (fn-record-string-octets "200 A ready"))
          (list r e c))
        (list (fn-pull-begin-ready *ps-fresh* *ps-wildmat* *ps-now*)
              (list (cons :remote (ps-line "DATE"))) t)))
; Tooth (a greeting code): a 400 does not enter the ready round.
(must-fail
 (assert-event
  (equal (mv-let (r e c) (fn-pull-on-line (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now*)
                                          (fn-record-string-octets "400 go away"))
           (declare (ignore e c))
           r)
         (fn-pull-begin-ready *ps-fresh* *ps-wildmat* *ps-now*))))

; KEYSTONE fn-pull-session-journal-is-the-cursor-at-every-cut.
; Witness: from the fresh cursor through the TLS session to its close.
(defconst *ps-j0* (fn-pull-journal-effects (cadr *ps-b0*)))
(assert-event (equal (fn-pull-replay *ps-fresh* *ps-j0*)
                     (fn-pull-round-cursor (fn-pull-begin *ps-fresh* *ps-wildmat* *ps-now*))))
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
                           1)))
; Every cut inside the preamble recovers the begin's cursor: a kill after
; STARTTLS, after the TLS report or after the credential journals nothing.
(assert-event
 (null (fn-pull-journal-effects (cadr (ps-run *ps-s0* (take 3 *ps-preamble*))))))
; Tooth (the journal replays to C): an older journaled instant with a
; journaled (not fresh) C: the begin journals nothing and the replay is not
; the round's cursor.
(defconst *ps-held-c* (list *ps-peer* 900 2))
(must-fail
 (assert-event (equal (fn-pull-replay *ps-fresh*
                                      (append (list (list *ps-peer* 5 0))
                                              (fn-pull-journal-effects
                                               (cadr (ps-begin *ps-tls-plan* *ps-held-c*
                                                               *ps-now* *ps-cred*)))))
                      (fn-pull-round-cursor (fn-pull-begin *ps-held-c* *ps-wildmat* *ps-now*)))))
; Tooth (startable C): a cursor whose advance count is not a natural.
(defconst *ps-bad* (list *ps-peer* 5 -1))
(must-fail
 (assert-event (equal (fn-pull-replay *ps-bad*
                                      (fn-pull-journal-effects
                                       (cadr (ps-begin *ps-tls-plan* *ps-bad* *ps-now*
                                                       *ps-cred*))))
                      (fn-pull-round-cursor (fn-pull-begin *ps-bad* *ps-wildmat* *ps-now*)))))
