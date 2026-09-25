; Teeth for books/nntp-xpat.lisp: XPAT on the served reader step, the comma
; alternative, case, the RFC 2980 section 2.9 join, and the XPAT label.
;
; Expected replies are assembled by `xp-block'/`xp-single' from text written
; out of the RFCs, never by calling the response builder under test.
(in-package "ACL2")
(include-book "../../books/nntp-xpat")
(include-book "std/testing/must-fail" :dir :system)

(defconst *xp-groups* '("fn.letters" "fn.empty"))
(defconst *xp-id* "<Probe@Id.invalid>")
(defconst *xp-payload*
  (append (fn-nntp-string-octets "Message-ID: <Probe@Id.invalid>") '(13 10)
          (fn-nntp-string-octets "Subject: probe root") '(13 10)
          '(13 10)
          (fn-nntp-string-octets "Hi") '(13 10)))
(defconst *xp-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *xp-groups*) 1 *xp-id* *xp-payload*
                      '("fn.letters") 841000000)
   0 1 :durable))
(assert-event (fn-nntp-projectionp *xp-archive*))
(defconst *xp-env*
  (fn-nntp-env (fn-clock-observation 1000 843136496000 1000 t) nil nil))

; The session the served step holds after GROUP fn.letters.
(defconst *xp-session* (fn-nntp-make-session t "fn.letters" nil t))
(assert-event (fn-nntp-sessionp *xp-session*))
(assert-event
 (equal (fn-nntp-result-session
         (fn-nntp-step-pinned (fn-nntp-open-session *xp-archive*) *xp-archive*
                              nil nil *xp-env*
                              (list :command
                                    (fn-nntp-string-octets "GROUP fn.letters"))))
        (fn-nntp-make-session t "fn.letters" 1 t)))

(defun xp-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10) (xp-lines (cdr texts)))
    nil))
(defun xp-block (initial lines)
  (list (list :reply (append (fn-nntp-string-octets initial) '(13 10)
                             (xp-lines lines) '(46 13 10)))))
(defun xp-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defmacro xp-reply (text)
  `(fn-nntp-result-effects
    (fn-nntp-step-pinned *xp-session* *xp-archive* nil nil *xp-env*
                         (list :command (fn-nntp-string-octets ,text)))))

; -----------------------------------------------------------------------------
; Reachable witnesses on the served reader step.

; A match: RFC 2980 section 2.9.1's 221 and the header line.
(assert-event (equal (xp-reply "XPAT Subject 1-1 *root*")
                     (xp-block "221 header follows" (list "1 probe root"))))
; Case (RFC 3977 section 4.2, "matches the same character"): *Root* does not
; match "probe root".
(assert-event (equal (xp-reply "XPAT Subject 1-1 *Root*")
                     (xp-block "221 header follows" nil)))
; The comma alternative ORs: *zzz* matches nothing, *zzz*,*root* matches.
(assert-event (equal (xp-reply "XPAT Subject 1-1 *zzz*")
                     (xp-block "221 header follows" nil)))
(assert-event (equal (xp-reply "XPAT Subject 1-1 *zzz*,*root*")
                     (xp-block "221 header follows" (list "1 probe root"))))
; A second argument is joined, not ORed (RFC 2980 section 2.9): the one
; pattern "*zzz* *root*" does not match; "probe root" as two arguments is the
; one pattern "probe root", which does.
(assert-event (equal (xp-reply "XPAT Subject 1-1 *zzz* *root*")
                     (xp-block "221 header follows" nil)))
(assert-event (equal (xp-reply "XPAT Subject 1-1 probe root")
                     (xp-block "221 header follows" (list "1 probe root"))))
; The message-id form.
(assert-event (equal (xp-reply "XPAT Subject <Probe@Id.invalid> *zzz*,*root*")
                     (xp-block "221 header follows"
                               (list "<Probe@Id.invalid> probe root"))))

; -----------------------------------------------------------------------------
; fn-nntp-step-pinned-xpat-is-the-xpat-response: the witness and one
; counterexample per hypothesis, every other hypothesis holding.

(defun xp-subject-conclusion (session line)
  (declare (xargs :verify-guards nil))
  (equal (fn-nntp-step-pinned session *xp-archive* nil nil *xp-env*
                              (list :command line))
         (fn-nntp-xpat-response session *xp-archive* (cdr (fn-nntp-tokenize line)))))

(defconst *xp-line* (fn-nntp-string-octets "XPAT Subject 1-1 *root*"))
(assert-event (xp-subject-conclusion *xp-session* *xp-line*))
(assert-event (equal (fn-nntp-result-effects
                      (fn-nntp-xpat-response *xp-session* *xp-archive*
                                             (cdr (fn-nntp-tokenize *xp-line*))))
                     (xp-block "221 header follows" (list "1 probe root"))))
; Without fn-nntp-sessionp: a five-element record whose open and projected
; slots read t.  The step answers nothing; XPAT alone would answer.
(assert-event (not (xp-subject-conclusion (list t "fn.letters" nil t :extra)
                                          *xp-line*)))
; Without an open session.
(assert-event (not (xp-subject-conclusion
                    (fn-nntp-make-session nil "fn.letters" nil t) *xp-line*)))
; Without the projection: the step's 503.
(assert-event (not (xp-subject-conclusion
                    (fn-nntp-make-session t "fn.letters" nil nil) *xp-line*)))
(assert-event (equal (fn-nntp-result-effects
                      (fn-nntp-step-pinned (fn-nntp-make-session t "fn.letters" nil nil)
                                           *xp-archive* nil nil *xp-env*
                                           (list :command *xp-line*)))
                     (xp-single "503 archive projection unavailable")))
; Without fn-nntp-command-inputp: the same four tokens on a line past the
; 510-octet preflight (the separator run is long).  The step's 501.
(defun xp-spaces (n) (if (zp n) nil (cons 32 (xp-spaces (1- n)))))
(defconst *xp-long-line*
  (append (fn-nntp-string-octets "XPAT Subject 1-1") (xp-spaces 600)
          (fn-nntp-string-octets "*root*")))
(assert-event (equal (fn-nntp-tokenize *xp-long-line*) (fn-nntp-tokenize *xp-line*)))
(assert-event (not (fn-nntp-command-inputp *xp-long-line*)))
(assert-event (not (xp-subject-conclusion *xp-session* *xp-long-line*)))
; Without the XPAT keyword: HDR's 225 is not XPAT's 221.
(assert-event (not (xp-subject-conclusion
                    *xp-session* (fn-nntp-string-octets "HDR Subject 1-1 *root*"))))

; -----------------------------------------------------------------------------
; fn-nntp-xpat-alternation-is-or: witness and its one hypothesis.

(defun xp-parsed (text)
  (declare (xargs :verify-guards nil))
  (fn-wildmat-result-value (fn-wildmat-parse-text (fn-nntp-string-octets text))))
(defconst *xp-content* (fn-nntp-string-octets "probe root"))
(assert-event (equal (xp-parsed "*zzz*,*root*")
                     (append (xp-parsed "*zzz*") (xp-parsed "*root*"))))
(assert-event (fn-nxp-all-positivep (xp-parsed "*root*")))
(assert-event (fn-nntp-xpat-matchesp (append (xp-parsed "*zzz*") (xp-parsed "*root*"))
                                     *xp-content*))
(assert-event (not (fn-nntp-xpat-matchesp (xp-parsed "*zzz*") *xp-content*)))
; Without positive alternatives on the right: "*,!*root*" -- the rightmost
; alternative that matches is the negated one, so the whole does not match,
; although "*" alone does.
(defconst *xp-negated* (cdr (xp-parsed "*,!*root*")))
(assert-event (not (fn-nxp-all-positivep *xp-negated*)))
(assert-event (fn-nntp-xpat-matchesp (xp-parsed "*") *xp-content*))
(assert-event (not (fn-nntp-xpat-matchesp (append (xp-parsed "*") *xp-negated*)
                                          *xp-content*)))
(must-fail
 (defthm xp-alternation-without-positive-alternatives
   (iff (fn-nntp-xpat-matchesp (append p q) content)
        (or (fn-nntp-xpat-matchesp p content)
            (fn-nntp-xpat-matchesp q content)))))

; -----------------------------------------------------------------------------
; fn-auth-capability-lines-advertise-xpat (no hypothesis): the label in the
; reader step's block, posting and not.
(assert-event (member-equal (fn-nntp-string-octets "XPAT")
                            (fn-nntp-capability-lines t)))
(assert-event (member-equal (fn-nntp-string-octets "XPAT")
                            (fn-nntp-capability-lines nil)))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step-pinned *xp-session* *xp-archive* nil nil *xp-env*
                              (list :command (fn-nntp-string-octets "CAPABILITIES"))))
        (xp-block "101 capability list follows"
                  '("VERSION 2" "READER" "OVER MSGID" "HDR" "XPAT" "NEWNEWS"
                    "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT"
                    "IMPLEMENTATION fn-nntp-lab"))))
