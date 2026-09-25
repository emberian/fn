; Teeth for books/owner-bound-commit.lisp (PKT-069): the bound submission's
; commit route commits only under the filing plan's groups.
(in-package "ACL2")
(include-book "../../books/owner-bound-commit")
(include-book "std/testing/must-fail" :dir :system)

(defun obct-line (text)
  (append (fn-record-string-octets text) '(13 10)))

(defun obct-article (lines)
  (if (consp lines)
      (append (obct-line (car lines)) (obct-article (cdr lines)))
    (append '(13 10) (obct-line "body"))))

(defconst *obct-common*
  (list "From: poster@example.invalid"
        "Date: Wed, 23 Sep 2026 12:00:00 +0000"
        "Newsgroups: fn.test"
        "Message-ID: <obc-1@example.invalid>"))
(defconst *obct-cancel*
  (obct-article (append *obct-common*
                        (list "Subject: cmsg cancel <target@example.invalid>"
                              "Control: cancel <target@example.invalid>"))))
(defconst *obct-ordinary*
  (obct-article (append *obct-common* (list "Subject: hello"))))
(defconst *obct-fn-test* (list (fn-record-string-octets "fn.test")))
(defconst *obct-filed* (list (fn-record-string-octets "control.cancel")))
(defconst *obct-domain* '("fn.test" "control.cancel"))

; Witnesses (reachable, non-degenerate): an ordinary article commits under
; its own groups; a cancel commits under control.cancel, the groups the
; signed author passes after filing (host/native/hybrid-control.lisp).
(assert-event (equal (fn-obc-commit-gate *obct-ordinary* *obct-fn-test* *obct-domain*)
                     :commit))
(assert-event (equal (fn-obc-commit-gate *obct-cancel* *obct-filed* *obct-domain*)
                     :commit))
(assert-event (equal (fn-pa-filing-plan *obct-cancel* *obct-filed* *obct-domain*)
                     (list :file *obct-filed*)))
; The route the finding named: a cancel under the groups its Newsgroups
; names is refused, and without control.cancel it is refused by the plan.
(assert-event (equal (fn-obc-commit-gate *obct-cancel* *obct-fn-test* *obct-domain*)
                     (list :refused :not-filed)))
(assert-event (equal (fn-obc-commit-gate *obct-cancel* *obct-filed* '("fn.test"))
                     (list :refused :control-not-filed)))

; Teeth for fn-obc-commit-only-after-filing (one hypothesis, the gate's
; :commit): without it the plan does not file in the committed groups.
(must-fail
 (assert-event
  (equal (fn-pa-filing-plan *obct-cancel* *obct-fn-test* *obct-domain*)
         (list :file *obct-fn-test*))))

; Teeth for fn-obc-control-commits-only-in-its-filing-group: without the
; :control hypothesis an ordinary article commits in fn.test, which is not a
; control group; without the gate the cancel's own groups are fn.test.
(must-fail
 (assert-event
  (fn-ctl-control-group-namep "fn.test")))
(must-fail
 (assert-event
  (equal *obct-fn-test*
         (list (fn-record-string-octets
                (fn-ctl-filing-group (cadr (fn-ctl-classify-octets *obct-cancel*))))))))
