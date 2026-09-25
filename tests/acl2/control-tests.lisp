; Teeth for packet C1 (books/control-classify.lisp and the filing plan
; fn-pa-filing-plan in books/peer-authored-accept.lisp): reachable witnesses
; for each keystone and, per hypothesis, a witness where the conclusion fails
; without it.
(in-package "ACL2")
(include-book "../../books/peer-authored-accept")
(include-book "std/testing/must-fail" :dir :system)

(defun ct-line (text)
  (declare (xargs :guard t))
  (append (fn-record-string-octets text) '(13 10)))

(defun ct-article (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (ct-line (car lines)) (ct-article (cdr lines)))
    (append '(13 10) (ct-line "body"))))

(defconst *ct-common*
  (list "From: poster@example.invalid"
        "Date: Wed, 23 Sep 2026 12:00:00 +0000"
        "Newsgroups: fn.test"
        "Message-ID: <ctl-1@example.invalid>"))

(defconst *ct-cancel*
  (ct-article (append *ct-common*
                      (list "Subject: cmsg cancel <target@example.invalid>"
                            "Control: cancel <target@example.invalid>"))))
(defconst *ct-cmsg*
  (ct-article (append *ct-common*
                      (list "Subject: cmsg cancel <target@example.invalid>"))))
(defconst *ct-also-control*
  (ct-article (list "From: poster@example.invalid"
                    "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                    "Newsgroups: fn.test,fn.test.ctl"
                    "Message-ID: <ctl-2@example.invalid>"
                    "Subject: cmsg newgroup fn.x"
                    "Also-Control: newgroup fn.x")))
(defconst *ct-unknown*
  (ct-article (append *ct-common* (list "Subject: x" "Control: Frobnicate a b"))))
(defconst *ct-obsolete*
  (ct-article (append *ct-common* (list "Subject: x" "Control: sendsys"))))
(defconst *ct-upper*
  (ct-article (append *ct-common* (list "Subject: x" "Control: CANCEL <t@x>"))))
(defconst *ct-two*
  (ct-article (append *ct-common* (list "Subject: x" "Control: cancel <t@x>"
                                        "Control: cancel <u@x>"))))
(defconst *ct-supersedes*
  (ct-article (append *ct-common* (list "Subject: x" "Control: cancel <t@x>"
                                        "Supersedes: <t@x>"))))
(defconst *ct-bad-verb*
  (ct-article (append *ct-common* (list "Subject: x" "Control: can/cel <t@x>"))))
; No SP after the colon: outside RFC 5536's "Control:" SP grammar.
(defconst *ct-empty*
  (ct-article (append *ct-common*
                      (list "Subject: x"
                            (concatenate 'string "Control:"
                                         (coerce (list (code-char 9)) 'string)
                                         "cancel <t@x>")))))
(defconst *ct-signed*
  (ct-article (append *ct-common* (list "Subject: x" "Control: cancel <t@x>"
                                        "FN-Authorship: x"))))

(defconst *ct-fn-test* (list (fn-record-string-octets "fn.test")))
(defconst *ct-with-cancel* '("fn.test" "control.cancel"))
(defconst *ct-without* '("fn.test"))

; Every fixture parses.
(assert-event (fn-article-result-okp (fn-article-parse *ct-cancel*)))
(assert-event (fn-article-result-okp (fn-article-parse *ct-cmsg*)))
(assert-event (fn-article-result-okp (fn-article-parse *ct-also-control*)))

; ---------------------------------------------------------------------------
; The classifier.
(assert-event (equal (fn-ctl-classify-octets *ct-cancel*)
                     (list :control (fn-record-string-octets "cancel")
                           (list (fn-record-string-octets
                                  "<target@example.invalid>")))))
(assert-event (equal (fn-ctl-classify-octets *ct-cmsg*) :ordinary))
(assert-event (equal (fn-ctl-classify-octets *ct-also-control*) :ordinary))
(assert-event (equal (fn-ctl-filing-group
                      (cadr (fn-ctl-classify-octets *ct-unknown*)))
                     "control"))
(assert-event (equal (fn-ctl-filing-group
                      (cadr (fn-ctl-classify-octets *ct-obsolete*)))
                     "control"))
(assert-event (equal (fn-ctl-filing-group
                      (cadr (fn-ctl-classify-octets *ct-upper*)))
                     "control.cancel"))
(assert-event (equal (fn-ctl-classify-octets *ct-two*)
                     (list :malformed :duplicate-control)))
(assert-event (equal (fn-ctl-classify-octets *ct-supersedes*)
                     (list :malformed :control-and-supersedes)))
(assert-event (equal (fn-ctl-classify-octets *ct-bad-verb*)
                     (list :malformed :control-syntax)))
(assert-event (equal (fn-ctl-classify-octets *ct-empty*)
                     (list :malformed :control-syntax)))
(assert-event (equal (fn-ctl-classify-octets '(1 2 3)) :unparsed))

; ---------------------------------------------------------------------------
; fn-ctl-classify-reads-only-the-control-field.  Witness: the cancel's
; fields with its Subject removed classify the same.  Teeth: F a Control
; field (hypothesis 1), or F a Supersedes field (hypothesis 2), changes it.
(defconst *ct-cancel-fields*
  (fn-article-fields (fn-article-result-article
                      (fn-article-parse *ct-cancel*))))
(defconst *ct-subject-field* (nth 4 *ct-cancel-fields*))
(defconst *ct-control-field* (nth 5 *ct-cancel-fields*))
(defconst *ct-supersedes-field*
  (car (last (fn-article-fields (fn-article-result-article
                                 (fn-article-parse *ct-supersedes*))))))
(assert-event (equal (fn-ctl-field-name *ct-subject-field*)
                     (fn-record-string-octets "subject")))
(assert-event (equal (fn-ctl-field-name *ct-supersedes-field*)
                     *fn-ctl-supersedes-name*))
(assert-event
 (equal (fn-ctl-classify-fields (append (take 4 *ct-cancel-fields*)
                                        (cons *ct-subject-field*
                                              (nthcdr 5 *ct-cancel-fields*))))
        (fn-ctl-classify-fields (append (take 4 *ct-cancel-fields*)
                                        (nthcdr 5 *ct-cancel-fields*)))))
(must-fail
 (assert-event
  (equal (fn-ctl-classify-fields (append (take 5 *ct-cancel-fields*)
                                         (cons *ct-control-field* nil)))
         (fn-ctl-classify-fields (take 5 *ct-cancel-fields*)))))
(must-fail
 (assert-event
  (equal (fn-ctl-classify-fields (append *ct-cancel-fields*
                                         (cons *ct-supersedes-field* nil)))
         (fn-ctl-classify-fields *ct-cancel-fields*))))

; ---------------------------------------------------------------------------
; fn-ctl-control-article-is-filed-only-in-control, over fn-pa-filing-plan.
; Witness: a cancel naming fn.test with control.cancel configured is filed
; in control.cancel and not fn.test; without the group it is refused.
(assert-event (equal (fn-pa-filing-plan *ct-cancel* *ct-fn-test* *ct-with-cancel*)
                     (list :file (list (fn-record-string-octets
                                        "control.cancel")))))
(assert-event (equal (fn-pa-filing-plan *ct-cancel* *ct-fn-test* *ct-without*)
                     (list :refused :control-not-filed)))
(assert-event (equal (fn-pa-filing-plan *ct-unknown* *ct-fn-test*
                                        '("fn.test" "control"))
                     (list :file (list (fn-record-string-octets "control")))))
(assert-event (equal (fn-pa-filing-plan *ct-two* *ct-fn-test* *ct-with-cancel*)
                     (list :refused :control-malformed)))
(assert-event (equal (fn-pa-filing-plan *ct-signed* *ct-fn-test*
                                        *ct-with-cancel*)
                     (list :refused :control-signed)))
; Teeth (the one hypothesis: classified :control).  An ordinary article is
; filed in its Newsgroups' group, which is not a control group.
(must-fail
 (assert-event
  (let ((plan (fn-pa-filing-plan *ct-cmsg* *ct-fn-test* *ct-with-cancel*)))
    (or (not (equal (car plan) :file))
        (equal (cadr plan)
               (list (fn-record-string-octets
                      (fn-ctl-filing-group
                       (cadr (fn-ctl-classify-octets *ct-cmsg*))))))))))
; The filing step is what does it: the ingress's own groups name fn.test.
(must-fail
 (assert-event
  (equal (fn-pa-filing-plan *ct-cancel* *ct-fn-test* *ct-with-cancel*)
         (list :file *ct-fn-test*))))

; fn-ctl-unsigned-control-filing-by-definition: its carrier hypothesis.
(must-fail
 (assert-event
  (equal (fn-pa-filing-plan *ct-signed* *ct-fn-test* *ct-with-cancel*)
         (list :file (list (fn-record-string-octets "control.cancel"))))))

; ---------------------------------------------------------------------------
; fn-ctl-cmsg-subject-is-ordinary.  Witness: the cmsg Subject article, and
; the .ctl / Also-Control one, keep their groups.  Teeth (no Control field):
; the same article with a Control field does not.
(assert-event (equal (fn-pa-filing-plan *ct-cmsg* *ct-fn-test* *ct-with-cancel*)
                     (list :file *ct-fn-test*)))
(assert-event (equal (fn-pa-filing-plan *ct-also-control* *ct-fn-test*
                                        *ct-with-cancel*)
                     (list :file *ct-fn-test*)))
(must-fail
 (assert-event (equal (fn-pa-filing-plan *ct-cancel* *ct-fn-test* *ct-without*)
                      (list :file *ct-fn-test*))))

; The served POST's reply words (fn-pa-served-word) carry the three reasons.
(assert-event (equal (fn-pa-served-word :refused :control-not-filed)
                     :control-not-filed))
(assert-event (equal (fn-pa-served-word :refused :control-signed)
                     :control-signed))
; D27 (signed-path): a signed article whose composite was not formed or is
; past the profile's R carries its word to the poster.
(assert-event (equal (fn-pa-served-word :refused :signed-record) :signed-record))
(assert-event (equal (fn-pa-served-word :refused :event) :event))
