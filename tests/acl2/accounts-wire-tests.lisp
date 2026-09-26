; Teeth for the XREDEEM wire keystones (PRF-164, PKT-439; books/nntp-auth.lisp).
; The subject is fn-auth-step-pinned, the dispatcher books/served.lisp
; fn-served-dispatch calls for every framed event, reached by
; host/owner-host.lisp fn-owner-chunk through fn-own-read, and by the owner's
; re-entry fn-owner-account-outcome (host/native-admin-host.lisp) through
; fn-ocfg-read-step.  Per keystone: a reachable witness asserting the
; antecedent and the conclusion, and per hypothesis a removal witness whose
; other hypotheses hold, whose omitted hypothesis fails, and whose
; conclusion fails (AGENTS.md, "Teeth ship with each keystone").
(in-package "ACL2")
(include-book "../../books/nntp-auth")
(include-book "std/testing/must-fail" :dir :system)

(defconst *awt-archive* (fn-initial-state '("fn.letters")))
(defconst *awt-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *awt-config*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *awt-protected* (fn-auth-make-config t t t nil))
(defconst *awt-open* (fn-auth-make-config nil nil t nil))
(defun awt-session (acfg tlsp)
  (fn-auth-open-session *awt-archive* nil nil nil acfg tlsp))
(defconst *awt-prot* (awt-session *awt-protected* nil))
(defconst *awt-prot-tls* (awt-session *awt-protected* t))
(defconst *awt-open-s* (awt-session *awt-open* nil))
(assert-event (fn-auth-sessionp *awt-prot*))
(assert-event (fn-auth-sessionp *awt-prot-tls*))

(defun awt-step (as event)
  (fn-auth-step-pinned as *awt-archive* nil nil *awt-config* *awt-obs* *awt-obs*
                       event))
(defun awt-line (text) (fn-nntp-string-octets text))
(defun awt-cmd (text) (list :command (awt-line text)))
(defun awt-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defconst *awt-483* "483 a protected channel is required; use STARTTLS")
(defconst *awt-redeem* "XREDEEM 000102030405060708090a0b0c0d0efa robin")

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-xredeem-before-tls-is-483
;   H1 sessionp  H2 not handshaking  H3 no subject  H4 protected-only
;   H5 not tlsp  H6 command input  H7 arguments at most  H8 XREDEEM keyword
(defmacro awt-483-hyps (as text)
  `(and (fn-auth-sessionp ,as)
        (not (fn-auth-session-handshakingp ,as))
        (not (fn-auth-session-subject ,as))
        (fn-auth-config-protected-onlyp (fn-auth-session-config ,as))
        (not (fn-auth-session-tlsp ,as))
        (fn-nntp-command-inputp (awt-line ,text))
        (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line ,text)))
        (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line ,text))) "XREDEEM")))
(defmacro awt-483-concl (as text)
  `(and (equal (fn-post-result-effects (awt-step ,as (awt-cmd ,text)))
               (awt-single *awt-483*))
        (equal (fn-post-result-session (awt-step ,as (awt-cmd ,text))) ,as)
        (null (fn-post-result-submission (awt-step ,as (awt-cmd ,text))))))
(assert-event (and (awt-483-hyps *awt-prot* *awt-redeem*)
                   (awt-483-concl *awt-prot* *awt-redeem*)))
; H5 removed: over TLS the same line answers 381.
(assert-event (and (fn-auth-session-tlsp *awt-prot-tls*)
                   (not (awt-483-concl *awt-prot-tls* *awt-redeem*))
                   (equal (fn-post-result-effects
                           (awt-step *awt-prot-tls* (awt-cmd *awt-redeem*)))
                          (awt-single "381 send the password with XREDEEM PASS"))))
; H4 removed: a listener that does not require TLS answers 381 in cleartext.
(assert-event (and (not (fn-auth-config-protected-onlyp
                         (fn-auth-session-config *awt-open-s*)))
                   (not (awt-483-concl *awt-open-s* *awt-redeem*))))
; H8 removed: another verb is not refused 483 (DATE answers 111).
(assert-event (and (not (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line "DATE")))
                                          "XREDEEM"))
                   (not (awt-483-concl *awt-prot* "DATE"))))
; H2 removed: a holding session answers nothing.
(defconst *awt-held*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        nil nil nil t))
(assert-event (and (fn-auth-sessionp *awt-held*)
                   (fn-auth-session-handshakingp *awt-held*)
                   (not (awt-483-concl *awt-held* *awt-redeem*))))
; H3 removed: an authenticated session is answered 502.
(defconst *awt-authed*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        nil (make-list 32 :initial-element 7) nil nil))
(assert-event (and (fn-auth-sessionp *awt-authed*)
                   (fn-auth-session-subject *awt-authed*)
                   (equal (fn-post-result-effects
                           (awt-step *awt-authed* (awt-cmd *awt-redeem*)))
                          (awt-single "502 already authenticated"))
                   (not (awt-483-concl *awt-authed* *awt-redeem*))))
; H1 removed: a value that is not a session is answered nothing.
(assert-event (and (not (fn-auth-sessionp nil))
                   (not (awt-483-concl nil *awt-redeem*))))
; H6 removed: a line carrying a NUL is not command input and is not
; answered 483 by this arm.
(assert-event (and (not (fn-nntp-command-inputp
                         (append (awt-line "XREDEEM a") '(0) (awt-line " b"))))
                   (not (equal (fn-post-result-effects
                                (awt-step *awt-prot*
                                          (list :command
                                                (append (awt-line "XREDEEM a")
                                                        '(0) (awt-line " b")))))
                               (awt-single *awt-483*)))))
; H7's removal: a line with more arguments than RFC 3977 allows is framed
; out before the arm; the bound is the tokenizer's (checked, not refuted
; here: every XREDEEM line the arm sees satisfies it).
(assert-event (fn-nntp-command-arguments-at-mostp
               (fn-nntp-tokenize (awt-line *awt-redeem*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-xredeem-pass-holds-for-the-owner
(defconst *awt-381* (fn-post-result-session
                     (awt-step *awt-prot-tls* (awt-cmd *awt-redeem*))))
(assert-event (equal (fn-auth-session-pending *awt-381*)
                     (list :xredeem (awt-line "000102030405060708090a0b0c0d0efa")
                           (awt-line "robin"))))
(defconst *awt-pass* "XREDEEM PASS correct-horse")
(defconst *awt-wait* (fn-post-result-session (awt-step *awt-381* (awt-cmd *awt-pass*))))
(assert-event (null (fn-post-result-effects (awt-step *awt-381* (awt-cmd *awt-pass*)))))
(assert-event (fn-auth-redeem-waitp *awt-wait*))
(assert-event (fn-auth-session-handshakingp *awt-wait*))
(assert-event (fn-auth-sessionp *awt-wait*))
(assert-event (equal (fn-auth-redeem-request *awt-wait*)
                     (list (awt-line "000102030405060708090a0b0c0d0efa")
                           (awt-line "robin") (awt-line "correct-horse"))))
; The pending-form hypothesis removed: PASS with nothing cached is 482 and
; does not hold.
(assert-event (and (null (fn-auth-session-pending *awt-prot-tls*))
                   (equal (fn-post-result-effects
                           (awt-step *awt-prot-tls* (awt-cmd *awt-pass*)))
                          (awt-single "482 redemption commands issued out of sequence"))
                   (not (fn-auth-redeem-waitp
                         (fn-post-result-session
                          (awt-step *awt-prot-tls* (awt-cmd *awt-pass*)))))))
; The TLS-or-open hypothesis removed: before TLS on the protected listener,
; the cached exchange is refused 483 and nothing is held.
(defconst *awt-381-clear*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        (fn-auth-session-pending *awt-381*) nil nil nil))
(assert-event (and (fn-auth-sessionp *awt-381-clear*)
                   (not (fn-auth-redeem-waitp
                         (fn-post-result-session
                          (awt-step *awt-381-clear* (awt-cmd *awt-pass*)))))))
; The one-token-password hypothesis removed: two words are 501.
(assert-event (equal (fn-post-result-effects
                      (awt-step *awt-381* (awt-cmd "XREDEEM PASS a b")))
                     (awt-single "501 syntax error")))
; The session holds: the served fold stops, so a command after the PASS line
; in the same read is not answered by the step.
(assert-event (null (fn-post-result-effects (awt-step *awt-wait* (awt-cmd "DATE")))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-redeem-outcome-answers-the-word
(assert-event (equal (fn-post-result-effects
                      (awt-step *awt-wait* '(:account-outcome :bound)))
                     (awt-single "281 account bound; authenticate with AUTHINFO on a new connection")))
(assert-event (equal (fn-post-result-effects
                      (awt-step *awt-wait* '(:account-outcome :refused)))
                     (awt-single "482 invitation code refused")))
(assert-event (let ((s (fn-post-result-session
                        (awt-step *awt-wait* '(:account-outcome :bound)))))
                (and (null (fn-auth-session-pending s))
                     (not (fn-auth-session-handshakingp s))
                     (null (fn-auth-session-subject s))
                     (fn-auth-sessionp s))))
; The waiting hypothesis removed: a session that is not holding answers the
; event with nothing (the owner cannot make a 281 out of thin air).
(assert-event (and (fn-auth-sessionp *awt-381*)
                   (not (fn-auth-redeem-waitp *awt-381*))
                   (null (fn-post-result-effects
                          (awt-step *awt-381* '(:account-outcome :bound))))))
; A STARTTLS handshake is not a redemption hold: the outcome event does not
; answer it (fn-auth-handshaking-session-serves-nothing).
(assert-event (and (fn-auth-session-handshakingp *awt-held*)
                   (not (fn-auth-redeem-waitp *awt-held*))
                   (null (fn-post-result-effects
                          (awt-step *awt-held* '(:account-outcome :bound))))))
