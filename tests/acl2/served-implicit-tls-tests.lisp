; Witnesses and teeth for books/served-implicit-tls.lisp (PRF-162).
(in-package "ACL2")
(include-book "../../books/served-implicit-tls")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

(defconst *sit-groups* (list (fn-nntp-string-octets "fn.test")))
(defconst *sit-config*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      *sit-groups* 1048576))
(defconst *sit-observation* (fn-clock-observation 1000000 843004800000 500 t))

; A policy that requires a login, allows AUTHINFO only on a protected
; channel, and has TLS available: the configuration the hbox walk runs.
(defconst *sit-acfg* (fn-auth-make-config t t t nil))

(defun sit-open (acfg)
  (fn-sit-opened nil (fn-midx-build nil) nil nil *fn-nntp-max-initial-line-octets*
                 1048576 *sit-config* *sit-observation* *sit-observation* acfg))

(defun sit-implicit (acfg)
  (fn-served-result-conn (fn-served-dispatch (sit-open acfg) *fn-sit-established-event*)))

(defun sit-starttls (acfg)
  (fn-served-result-conn
   (fn-served-dispatch
    (fn-served-result-conn (fn-served-dispatch (sit-open acfg) *fn-sit-starttls-event*))
    *fn-sit-established-event*)))

(defun sit-command (conn text)
  (fn-served-result-effects
   (fn-served-dispatch conn (list :command (fn-nntp-string-octets text)))))

(defun sit-reply (conn text)
  (fn-nntp-single (fn-auth-reader-session (fn-served-conn-session conn)) text))

; ---------------------------------------------------------------------------
; fn-served-implicit-tls-is-the-starttls-session: the reachable witness.
; Both hypotheses hold, and the two connections are equal.
(assert-event (fn-auth-configp *sit-acfg*))
(assert-event (fn-auth-config-tls-availablep *sit-acfg*))
(assert-event (equal (sit-implicit *sit-acfg*) (sit-starttls *sit-acfg*)))
; The STARTTLS path really went through 382 and the handshake effect.
(assert-event
 (member-equal (fn-auth-starttls-effect)
               (sit-command (sit-open *sit-acfg*) "STARTTLS")))
; And the common state behaves as a protected connection: STARTTLS again
; is 502, and AUTHINFO USER is not refused 483 under protected_only.
(assert-event
 (equal (sit-command (sit-implicit *sit-acfg*) "STARTTLS")
        (fn-nntp-result-effects
         (sit-reply (sit-implicit *sit-acfg*) "502 a TLS layer is already active"))))
(assert-event
 (not (equal (sit-command (sit-implicit *sit-acfg*) "AUTHINFO USER guest")
             (fn-nntp-result-effects
              (sit-reply (sit-implicit *sit-acfg*)
                         "483 a protected channel is required; use STARTTLS")))))
; Before either event the same command IS refused 483: the protection is
; the event's.
(assert-event
 (equal (sit-command (sit-open *sit-acfg*) "AUTHINFO USER guest")
        (fn-nntp-result-effects
         (sit-reply (sit-open *sit-acfg*)
                    "483 a protected channel is required; use STARTTLS"))))

; Hypothesis removed: TLS not available.  The retained hypothesis holds,
; the removed one fails, and the conclusion fails: STARTTLS answers 580 and
; owes no handshake, so the host never delivers the event that would make
; the plaintext connection the implicit one.
(defconst *sit-no-tls* (fn-auth-make-config t t nil nil))
(assert-event (fn-auth-configp *sit-no-tls*))
(assert-event (not (fn-auth-config-tls-availablep *sit-no-tls*)))
(assert-event (not (member-equal (fn-auth-starttls-effect)
                                 (sit-command (sit-open *sit-no-tls*) "STARTTLS"))))
(assert-event
 (equal (sit-command (sit-open *sit-no-tls*) "STARTTLS")
        (fn-nntp-result-effects
         (sit-reply (sit-open *sit-no-tls*) "580 can not initiate TLS negotiation"))))

; Hypothesis removed: not a policy.  TLS-availablep still reads t off the
; malformed list, but the open pins the policy that offers nothing: 580,
; no handshake, and the conclusion fails.
(defconst *sit-malformed* (list :fn-auth-config t t t :not-creds))
(assert-event (fn-auth-config-tls-availablep *sit-malformed*))
(assert-event (not (fn-auth-configp *sit-malformed*)))
(assert-event (not (member-equal (fn-auth-starttls-effect)
                                 (sit-command (sit-open *sit-malformed*) "STARTTLS"))))

(defmacro sit-keystone-without (hyps)
  `(defthm sit-keystone-weakened
     (implies (and ,@hyps)
              (let ((c0 (fn-sit-opened archive index buckets verdicts line-limit
                                       body-limit config observation injection
                                       acfg)))
                (and (member-equal
                      (fn-auth-starttls-effect)
                      (fn-served-result-effects
                       (fn-served-dispatch c0 *fn-sit-starttls-event*)))
                     (equal (fn-served-result-conn
                             (fn-served-dispatch c0 *fn-sit-established-event*))
                            (fn-served-result-conn
                             (fn-served-dispatch
                              (fn-served-result-conn
                               (fn-served-dispatch c0 *fn-sit-starttls-event*))
                              *fn-sit-established-event*))))))
     :hints (("Goal" :in-theory (enable fn-sit-opened fn-served-dispatch
                                        fn-served-open-group-indexed
                                        fn-served-open-indexed
                                        fn-served-pin-group-index
                                        fn-auth-step-pinned fn-auth-command
                                        fn-auth-starttls fn-auth-tls-established
                                        fn-auth-open-session
                                        fn-auth-clear-principal-peer
                                        fn-auth-gatedp fn-auth-principal-rolep
                                        fn-peer-open-session fn-post-offeredp
                                        fn-auth-single fn-nntp-single fn-auth-starttls-effect)))))
(must-fail (sit-keystone-without ((fn-auth-configp acfg))))
(must-fail (sit-keystone-without ((fn-auth-config-tls-availablep acfg))))

; ---------------------------------------------------------------------------
; fn-served-implicit-tls-session-is-protected: the witness.
(assert-event
 (null (fn-served-result-effects
        (fn-served-dispatch (sit-open *sit-acfg*) *fn-sit-established-event*))))
(assert-event (fn-auth-session-tlsp (fn-served-conn-session (sit-implicit *sit-acfg*))))
(assert-event
 (not (fn-auth-session-handshakingp (fn-served-conn-session (sit-implicit *sit-acfg*)))))
; The conclusion is not the opened state's: before the event there is no
; TLS layer.
(assert-event (not (fn-auth-session-tlsp (fn-served-conn-session (sit-open *sit-acfg*)))))
