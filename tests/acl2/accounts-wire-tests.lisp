; Teeth for the XREDEEM wire keystones (PRF-164, PKT-439; books/nntp-auth.lisp).
; The subject is fn-auth-step-pinned, the dispatcher books/served.lisp
; fn-served-dispatch calls for every framed event, reached by
; host/owner-host.lisp fn-owner-chunk-span-at through fn-own-read, and by the owner's
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

(defun awt-step (as event fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-auth-step-pinned as *awt-archive* nil nil *awt-config* *awt-obs* *awt-obs*
                       event fn-arena))
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
;   H9 no active COMPRESS layer (RFC 8054)
(defmacro awt-483-hyps (as text)
  `(and (fn-auth-sessionp ,as)
        (not (fn-auth-session-handshakingp ,as))
        (not (fn-auth-sasl-waitingp ,as))
        (not (fn-zc-activep (fn-auth-session-compress ,as)))
        (not (fn-auth-session-subject ,as))
        (fn-auth-config-protected-onlyp (fn-auth-session-config ,as))
        (not (fn-auth-session-tlsp ,as))
        (fn-nntp-command-inputp (awt-line ,text))
        (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line ,text)))
        (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line ,text))) "XREDEEM")))
(defmacro awt-483-concl (as text)
  `(and (equal (fn-post-result-effects (in-arena-awt-step *sr-arena* ,as (awt-cmd ,text)))
               (awt-single *awt-483*))
        (equal (fn-post-result-session (in-arena-awt-step *sr-arena* ,as (awt-cmd ,text))) ,as)
        (null (fn-post-result-submission (in-arena-awt-step *sr-arena* ,as (awt-cmd ,text))))))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift awt-step 2)
; Literal positive also exposes recognizer anchors to the static teeth checker.
(assert-event
  (and
    (fn-auth-sessionp *awt-prot*)
    (not (fn-auth-session-handshakingp *awt-prot*))
    (not (fn-auth-sasl-waitingp *awt-prot*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-prot*)))
    (not (fn-auth-session-subject *awt-prot*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot*))
    (not (fn-auth-session-tlsp *awt-prot*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (awt-483-concl *awt-prot* *awt-redeem*)))
; H5 removed: over TLS the same line answers 381.
(assert-event (and (fn-auth-session-tlsp *awt-prot-tls*)
                   (not (awt-483-concl *awt-prot-tls* *awt-redeem*))
                   (equal (fn-post-result-effects
                           (in-arena-awt-step *sr-arena* *awt-prot-tls* (awt-cmd *awt-redeem*)))
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
                        nil nil nil t nil nil))
(assert-event (and (fn-auth-sessionp *awt-held*)
                   (fn-auth-session-handshakingp *awt-held*)
                   (not (awt-483-concl *awt-held* *awt-redeem*))))
; H3 removed: an authenticated session is answered 502.
(defconst *awt-authed*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        nil (make-list 32 :initial-element 7) nil nil nil nil))
(assert-event (and (fn-auth-sessionp *awt-authed*)
                   (fn-auth-session-subject *awt-authed*)
                   (equal (fn-post-result-effects
                           (in-arena-awt-step *sr-arena* *awt-authed* (awt-cmd *awt-redeem*)))
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
                                (in-arena-awt-step *sr-arena* *awt-prot* (list :command
                                                (append (awt-line "XREDEEM a")
                                                        '(0) (awt-line " b")))))
                               (awt-single *awt-483*)))))
; H9 removed: under an active COMPRESS layer XREDEEM is 502 (RFC 8054
; section 2.2.2), not 483.  Reachable by a source-address peer connection.
(defconst *awt-compressed*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        nil nil nil nil '(:active :deflate) nil))
(assert-event (and (fn-auth-sessionp *awt-compressed*)
                   (fn-zc-activep (fn-auth-session-compress *awt-compressed*))
                   (equal (fn-post-result-effects
                           (in-arena-awt-step *sr-arena* *awt-compressed* (awt-cmd *awt-redeem*)))
                          (awt-single "502 not permitted once a compression layer is active"))
                   (not (awt-483-concl *awt-compressed* *awt-redeem*))))
; Complete literal teeth for fn-auth-step-pinned-xredeem-before-tls-is-483.
; The old H7 bound check is replaced by an actual counterexample below.
(defthm
  awt-complete-before-tls-positive
  (and
    (and
      (fn-auth-sessionp *awt-prot*)
      (not (fn-auth-session-handshakingp *awt-prot*))
      (not (fn-auth-sasl-waitingp *awt-prot*))
      (not (fn-zc-activep (fn-auth-session-compress *awt-prot*)))
      (not (fn-auth-session-subject *awt-prot*))
      (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot*))
      (not (fn-auth-session-tlsp *awt-prot*))
      (fn-nntp-command-inputp (awt-line *awt-redeem*))
      (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
      (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM"))
    (and
      (equal
        (fn-post-result-effects
          (fn-auth-step-pinned
            *awt-prot*
            *awt-archive*
            nil
            nil
            *awt-config*
            *awt-obs*
            *awt-obs*
            (list :command (awt-line *awt-redeem*))
            nil))
        (fn-auth-single *awt-prot* "483 a protected channel is required; use STARTTLS"))
      (equal
        (fn-post-result-session
          (fn-auth-step-pinned
            *awt-prot*
            *awt-archive*
            nil
            nil
            *awt-config*
            *awt-obs*
            *awt-obs*
            (list :command (awt-line *awt-redeem*))
            nil))
        *awt-prot*)
      (null
        (fn-post-result-submission
          (fn-auth-step-pinned
            *awt-prot*
            *awt-archive*
            nil
            nil
            *awt-config*
            *awt-obs*
            *awt-obs*
            (list :command (awt-line *awt-redeem*))
            nil)))))
  :rule-classes
  nil)

; Corrupted-state removal: session-shape. Every other hypothesis holds.
(defthm
  awt-complete-without-session-shape
  (and
    (not (fn-auth-session-handshakingp (append *awt-prot* (quote (nil)))))
    (not (fn-auth-sasl-waitingp (append *awt-prot* (quote (nil)))))
    (not (fn-zc-activep (fn-auth-session-compress (append *awt-prot* (quote (nil))))))
    (not (fn-auth-session-subject (append *awt-prot* (quote (nil)))))
    (fn-auth-config-protected-onlyp (fn-auth-session-config (append *awt-prot* (quote (nil)))))
    (not (fn-auth-session-tlsp (append *awt-prot* (quote (nil)))))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (fn-auth-sessionp (append *awt-prot* (quote (nil)))))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              (append *awt-prot* (quote (nil)))
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single
            (append *awt-prot* (quote (nil)))
            "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              (append *awt-prot* (quote (nil)))
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (append *awt-prot* (quote (nil))))
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              (append *awt-prot* (quote (nil)))
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: handshake. Every other hypothesis holds.
(defthm
  awt-complete-without-handshake
  (and
    (fn-auth-sessionp *awt-held*)
    (not (fn-auth-sasl-waitingp *awt-held*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-held*)))
    (not (fn-auth-session-subject *awt-held*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-held*))
    (not (fn-auth-session-tlsp *awt-held*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (not (fn-auth-session-handshakingp *awt-held*)))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-held*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single *awt-held* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-held*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          *awt-held*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-held*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: sasl. Every other hypothesis holds.
(defthm
  awt-complete-without-sasl
  (and
    (fn-auth-sessionp (update-nth 2 (quote (:sasl-plain)) *awt-prot*))
    (not (fn-auth-session-handshakingp (update-nth 2 (quote (:sasl-plain)) *awt-prot*)))
    (not
      (fn-zc-activep (fn-auth-session-compress (update-nth 2 (quote (:sasl-plain)) *awt-prot*))))
    (not (fn-auth-session-subject (update-nth 2 (quote (:sasl-plain)) *awt-prot*)))
    (fn-auth-config-protected-onlyp
      (fn-auth-session-config (update-nth 2 (quote (:sasl-plain)) *awt-prot*)))
    (not (fn-auth-session-tlsp (update-nth 2 (quote (:sasl-plain)) *awt-prot*)))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (not (fn-auth-sasl-waitingp (update-nth 2 (quote (:sasl-plain)) *awt-prot*))))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              (update-nth 2 (quote (:sasl-plain)) *awt-prot*)
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single
            (update-nth 2 (quote (:sasl-plain)) *awt-prot*)
            "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              (update-nth 2 (quote (:sasl-plain)) *awt-prot*)
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (update-nth 2 (quote (:sasl-plain)) *awt-prot*))
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              (update-nth 2 (quote (:sasl-plain)) *awt-prot*)
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: compression. Every other hypothesis holds.
(defthm
  awt-complete-without-compression
  (and
    (fn-auth-sessionp *awt-compressed*)
    (not (fn-auth-session-handshakingp *awt-compressed*))
    (not (fn-auth-sasl-waitingp *awt-compressed*))
    (not (fn-auth-session-subject *awt-compressed*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-compressed*))
    (not (fn-auth-session-tlsp *awt-compressed*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (not (fn-zc-activep (fn-auth-session-compress *awt-compressed*))))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-compressed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single *awt-compressed* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-compressed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          *awt-compressed*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-compressed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: subject. Every other hypothesis holds.
(defthm
  awt-complete-without-subject
  (and
    (fn-auth-sessionp *awt-authed*)
    (not (fn-auth-session-handshakingp *awt-authed*))
    (not (fn-auth-sasl-waitingp *awt-authed*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-authed*)))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-authed*))
    (not (fn-auth-session-tlsp *awt-authed*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (not (fn-auth-session-subject *awt-authed*)))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-authed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single *awt-authed* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-authed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          *awt-authed*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-authed*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: protected-only. Every other hypothesis holds.
(defthm
  awt-complete-without-protected-only
  (and
    (fn-auth-sessionp *awt-open-s*)
    (not (fn-auth-session-handshakingp *awt-open-s*))
    (not (fn-auth-sasl-waitingp *awt-open-s*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-open-s*)))
    (not (fn-auth-session-subject *awt-open-s*))
    (not (fn-auth-session-tlsp *awt-open-s*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-open-s*)))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-open-s*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single *awt-open-s* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-open-s*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          *awt-open-s*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-open-s*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: tls. Every other hypothesis holds.
(defthm
  awt-complete-without-tls
  (and
    (fn-auth-sessionp *awt-prot-tls*)
    (not (fn-auth-session-handshakingp *awt-prot-tls*))
    (not (fn-auth-sasl-waitingp *awt-prot-tls*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-prot-tls*)))
    (not (fn-auth-session-subject *awt-prot-tls*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot-tls*))
    (fn-nntp-command-inputp (awt-line *awt-redeem*))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line *awt-redeem*)))
    (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line *awt-redeem*))) "XREDEEM")
    (not (not (fn-auth-session-tlsp *awt-prot-tls*)))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-prot-tls*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          (fn-auth-single *awt-prot-tls* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-prot-tls*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))
          *awt-prot-tls*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-prot-tls*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line *awt-redeem*))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: command-input. Every other hypothesis holds.
(defthm
  awt-complete-without-command-input
  (and
    (fn-auth-sessionp *awt-prot*)
    (not (fn-auth-session-handshakingp *awt-prot*))
    (not (fn-auth-sasl-waitingp *awt-prot*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-prot*)))
    (not (fn-auth-session-subject *awt-prot*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot*))
    (not (fn-auth-session-tlsp *awt-prot*))
    (fn-nntp-command-arguments-at-mostp
      (fn-nntp-tokenize (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b"))))
    (fn-nntp-keywordp
      (car (fn-nntp-tokenize (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b"))))
      "XREDEEM")
    (not (fn-nntp-command-inputp (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b"))))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b")))
              nil))
          (fn-auth-single *awt-prot* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b")))
              nil))
          *awt-prot*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 520 :initial-element 32) (awt-line "a b")))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: argument-bound. Every other hypothesis holds.
(defthm
  awt-complete-without-argument-bound
  (and
    (fn-auth-sessionp *awt-prot*)
    (not (fn-auth-session-handshakingp *awt-prot*))
    (not (fn-auth-sasl-waitingp *awt-prot*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-prot*)))
    (not (fn-auth-session-subject *awt-prot*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot*))
    (not (fn-auth-session-tlsp *awt-prot*))
    (fn-nntp-command-inputp (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97)))
    (fn-nntp-keywordp
      (car (fn-nntp-tokenize (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97))))
      "XREDEEM")
    (not
      (fn-nntp-command-arguments-at-mostp
        (fn-nntp-tokenize (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97)))))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97)))
              nil))
          (fn-auth-single *awt-prot* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97)))
              nil))
          *awt-prot*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (append (awt-line "XREDEEM ") (make-list 498 :initial-element 97)))
              nil))))))
  :rule-classes
  nil)

; Session/input removal: keyword. Every other hypothesis holds.
(defthm
  awt-complete-without-keyword
  (and
    (fn-auth-sessionp *awt-prot*)
    (not (fn-auth-session-handshakingp *awt-prot*))
    (not (fn-auth-sasl-waitingp *awt-prot*))
    (not (fn-zc-activep (fn-auth-session-compress *awt-prot*)))
    (not (fn-auth-session-subject *awt-prot*))
    (fn-auth-config-protected-onlyp (fn-auth-session-config *awt-prot*))
    (not (fn-auth-session-tlsp *awt-prot*))
    (fn-nntp-command-inputp (awt-line "DATE"))
    (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (awt-line "DATE")))
    (not (fn-nntp-keywordp (car (fn-nntp-tokenize (awt-line "DATE"))) "XREDEEM"))
    (not
      (and
        (equal
          (fn-post-result-effects
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line "DATE"))
              nil))
          (fn-auth-single *awt-prot* "483 a protected channel is required; use STARTTLS"))
        (equal
          (fn-post-result-session
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line "DATE"))
              nil))
          *awt-prot*)
        (null
          (fn-post-result-submission
            (fn-auth-step-pinned
              *awt-prot*
              *awt-archive*
              nil
              nil
              *awt-config*
              *awt-obs*
              *awt-obs*
              (list :command (awt-line "DATE"))
              nil))))))
  :rule-classes
  nil)

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-xredeem-pass-holds-for-the-owner
(defconst *awt-381* (fn-post-result-session
                     (in-arena-awt-step *sr-arena* *awt-prot-tls* (awt-cmd *awt-redeem*))))
(assert-event (equal (fn-auth-session-pending *awt-381*)
                     (list :xredeem (awt-line "000102030405060708090a0b0c0d0efa")
                           (awt-line "robin"))))
(defconst *awt-pass* "XREDEEM PASS correct-horse")
(defconst *awt-wait* (fn-post-result-session (in-arena-awt-step *sr-arena* *awt-381* (awt-cmd *awt-pass*))))
(assert-event (null (fn-post-result-effects (in-arena-awt-step *sr-arena* *awt-381* (awt-cmd *awt-pass*)))))
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
                           (in-arena-awt-step *sr-arena* *awt-prot-tls* (awt-cmd *awt-pass*)))
                          (awt-single "482 redemption commands issued out of sequence"))
                   (not (fn-auth-redeem-waitp
                         (fn-post-result-session
                          (in-arena-awt-step *sr-arena* *awt-prot-tls* (awt-cmd *awt-pass*)))))))
; The TLS-or-open hypothesis removed: before TLS on the protected listener,
; the cached exchange is refused 483 and nothing is held.
(defconst *awt-381-clear*
  (fn-auth-make-session (fn-auth-session-base *awt-prot*) *awt-protected*
                        (fn-auth-session-pending *awt-381*) nil nil nil nil nil))
(assert-event (and (fn-auth-sessionp *awt-381-clear*)
                   (not (fn-auth-redeem-waitp
                         (fn-post-result-session
                          (in-arena-awt-step *sr-arena* *awt-381-clear* (awt-cmd *awt-pass*)))))))
; The one-token-password hypothesis removed: two words are 501.
(assert-event (equal (fn-post-result-effects
                      (in-arena-awt-step *sr-arena* *awt-381* (awt-cmd "XREDEEM PASS a b")))
                     (awt-single "501 syntax error")))
; The session holds: the served fold stops, so a command after the PASS line
; in the same read is not answered by the step.
(assert-event (null (fn-post-result-effects (in-arena-awt-step *sr-arena* *awt-wait* (awt-cmd "DATE")))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-redeem-outcome-answers-the-word
(assert-event (equal (fn-post-result-effects
                      (in-arena-awt-step *sr-arena* *awt-wait* '(:account-outcome :bound)))
                     (awt-single "281 account bound; authenticate with AUTHINFO on a new connection")))
(assert-event (equal (fn-post-result-effects
                      (in-arena-awt-step *sr-arena* *awt-wait* '(:account-outcome :refused)))
                     (awt-single "482 invitation code refused")))
(assert-event (let ((s (fn-post-result-session
                        (in-arena-awt-step *sr-arena* *awt-wait* '(:account-outcome :bound)))))
                (and (null (fn-auth-session-pending s))
                     (not (fn-auth-session-handshakingp s))
                     (null (fn-auth-session-subject s))
                     (fn-auth-sessionp s))))
; The waiting hypothesis removed: a session that is not holding gets no 281
; for a :bound word (the owner cannot make a 281 out of thin air), and no
; reply at all: the outcome is not client input, so the step answers it with
; nothing and leaves the session as it was (a 501 here would be a syntax
; error the client never caused).
(assert-event
 (let ((r (in-arena-awt-step *sr-arena* *awt-381* '(:account-outcome :bound))))
   (and (fn-auth-sessionp *awt-381*)
        (not (fn-auth-redeem-waitp *awt-381*))
        (null (fn-post-result-effects r))
        (null (fn-post-result-submission r))
        (equal (fn-post-result-session r) *awt-381*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-host-event-answers-nothing
;   H1 not a client event  H2 not holding for the owner's word
; Reachable positive witnesses: the owner's outcome after the hold (above),
; and a probe event, on the same non-holding session: no reply, no
; submission, the session unchanged (fn-auth-step-pinned-stray-event-changes-nothing).
(assert-event
 (let ((r (in-arena-awt-step *sr-arena* *awt-381* '(:foo))))
   (and (not (fn-auth-client-eventp '(:foo)))
        (not (fn-auth-redeem-waitp *awt-381*))
        (null (fn-post-result-effects r))
        (null (fn-post-result-submission r))
        (equal (fn-post-result-session r) *awt-381*))))
; H1 removed: a client's (:reject REASON) on the same session is answered
; (the reader's 501), so the conclusion fails.
(assert-event
 (let ((r (in-arena-awt-step *sr-arena* *awt-381* '(:reject :line-too-long))))
   (and (fn-auth-client-eventp '(:reject :line-too-long))
        (not (fn-auth-redeem-waitp *awt-381*))
        (equal (fn-post-result-effects r) (awt-single "501 syntax error")))))
; H2 removed: the holding session answers the same host event 281, so the
; conclusion fails (the keystone above names the reply).
(assert-event
 (let ((r (in-arena-awt-step *sr-arena* *awt-wait* '(:account-outcome :bound))))
   (and (not (fn-auth-client-eventp '(:account-outcome :bound)))
        (fn-auth-redeem-waitp *awt-wait*)
        (fn-post-result-effects r))))
; A STARTTLS handshake is not a redemption hold: the outcome event does not
; answer it (fn-auth-handshaking-session-serves-nothing).
(assert-event (and (fn-auth-session-handshakingp *awt-held*)
                   (not (fn-auth-redeem-waitp *awt-held*))
                   (null (fn-post-result-effects
                          (in-arena-awt-step *sr-arena* *awt-held* '(:account-outcome :bound))))))

; KEYSTONE fn-auth-step-pinned-xredeem-pass-holds-for-the-owner, the
; hypothesis the COMPRESS layer added (no active layer): the 381 session
; with a layer set answers the PASS 502 and holds nothing (RFC 8054 section
; 2.2.2: no authentication after COMPRESS).
(defconst *awt-381-compressed*
  (fn-auth-make-session (fn-auth-session-base *awt-381*) (fn-auth-session-config *awt-381*)
                        (fn-auth-session-pending *awt-381*) nil
                        (fn-auth-session-tlsp *awt-381*) nil '(:active :deflate) nil))
(assert-event (and (fn-auth-sessionp *awt-381-compressed*)
                   (equal (fn-post-result-effects
                           (in-arena-awt-step *sr-arena* *awt-381-compressed* (awt-cmd *awt-pass*)))
                          (awt-single "502 not permitted once a compression layer is active"))
                   (not (fn-auth-redeem-waitp
                         (fn-post-result-session
                          (in-arena-awt-step *sr-arena* *awt-381-compressed* (awt-cmd *awt-pass*)))))))

; Positive SASL-phase anchor for the retained phase premise above.
(assert-event (and (fn-auth-sessionp (update-nth 2 '(:sasl-plain) *awt-prot*))
                   (fn-auth-sasl-waitingp (update-nth 2 '(:sasl-plain) *awt-prot*))))
