; Teeth for books/control-visible.lisp: reachable witnesses for
; fn-ctl-visible-add-is-visible and fn-ctl-visible-extend-is-visible, and
; per hypothesis (the carried list is the definition's) a witness where the
; conclusion fails without it.
(in-package "ACL2")
(include-book "../../books/control-visible")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cvt-p* (make-list 32 :initial-element 17))
(defconst *cvt-p-hex* (fn-record-octets-string (fn-stx-hex-octets *cvt-p*)))
(defconst *cvt-p-verified* (fn-stx-make-verdict :verified *cvt-p* 1))
(defun cvt-art (msgid groups)
  (fn-make-article msgid nil groups nil t nil))
(defconst *cvt-t* (cvt-art "<t@example.invalid>" (list "fn.mod.a")))
(defconst *cvt-c* (cvt-art "<c@example.invalid>" (list "control.cancel")))
(defconst *cvt-o* (cvt-art "<o@example.invalid>" (list "fn.mod.a")))
(defconst *cvt-a* (cvt-art "<a@example.invalid>" (list "fn.misc")))
(defconst *cvt-verdicts*
  (list (cons "<a@example.invalid>" *cvt-p-verified*)
        (cons "<c@example.invalid>" *cvt-p-verified*)))
; The authority record (P holds cancel over fn.mod.*) withdrawing T, and
; the author record withdrawing P's own signed A, both caused by C.
(defconst *cvt-w-t*
  (fn-ctl-withdrawal-make "<t@example.invalid>" "<c@example.invalid>"
                          *cvt-p-hex* (list "fn.mod.*") 1))
(defconst *cvt-w-a*
  (fn-ctl-withdrawal-make "<a@example.invalid>" "<c@example.invalid>"
                          *cvt-p-hex* nil 1))
(defconst *cvt-ws* (list *cvt-w-t* *cvt-w-a*))

; fn-ctl-visible-add-is-visible.  Witnesses (the carried list is the
; definition's in each):
;   the cancel arrives after its targets: C over (O A T) drops T and A;
(assert-event
 (let ((old (list *cvt-o* *cvt-a* *cvt-t*)))
   (and (equal (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*) old)
        (equal (fn-ctl-visible-add *cvt-c* old old *cvt-ws* *cvt-verdicts*)
               (list *cvt-c* *cvt-o*))
        (equal (fn-ctl-visible-add *cvt-c* old old *cvt-ws* *cvt-verdicts*)
               (fn-ctl-visible-articles (cons *cvt-c* old) *cvt-ws*
                                        *cvt-verdicts*)))))
;   the target arrives after its cancel (D29's early cancel): T over (C O)
;   is never added;
(assert-event
 (let* ((old (list *cvt-c* *cvt-o*))
        (vis (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*)))
   (and (equal vis old)
        (equal (fn-ctl-visible-add *cvt-t* vis old *cvt-ws* *cvt-verdicts*)
               old)
        (equal (fn-ctl-visible-articles (cons *cvt-t* old) *cvt-ws*
                                        *cvt-verdicts*)
               old))))
;   an ordinary article is consed and nothing is walked.
(assert-event
 (let* ((old (list *cvt-c* *cvt-t*))
        (vis (fn-ctl-visible-articles old *cvt-ws* *cvt-verdicts*)))
   (and (equal vis (list *cvt-c*))
        (not (fn-ctl-causes-p *cvt-ws* "<o@example.invalid>"))
        (equal (fn-ctl-visible-add *cvt-o* vis old *cvt-ws* *cvt-verdicts*)
               (list *cvt-o* *cvt-c*)))))
; Teeth, the one hypothesis: a carried list that is not the definition's
; (here the raw archive, which still holds the withdrawn T) is not repaired
; by an ordinary article, so the conclusion fails.
(must-fail
 (assert-event
  (let ((old (list *cvt-c* *cvt-t*)))
    (equal (fn-ctl-visible-add *cvt-o* old old *cvt-ws* *cvt-verdicts*)
           (fn-ctl-visible-articles (cons *cvt-o* old) *cvt-ws*
                                    *cvt-verdicts*)))))

; fn-ctl-visible-extend-is-visible.  Witness: from the empty archive, the
; batch (O C T A) newest first gives the definition's list (O C).
(assert-event
 (let ((delta (list *cvt-o* *cvt-c* *cvt-t* *cvt-a*)))
   (and (equal (fn-ctl-visible-extend delta nil nil *cvt-ws* *cvt-verdicts*)
               (fn-ctl-visible-articles delta *cvt-ws* *cvt-verdicts*))
        (equal (fn-ctl-visible-extend delta nil nil *cvt-ws* *cvt-verdicts*)
               (list *cvt-o* *cvt-c*)))))
; Teeth, the one hypothesis: a carried list holding an article the archive
; does not (O over the empty archive) is not repaired by the batch (C): the
; stray O stays and the conclusion fails.
(must-fail
 (assert-event
  (equal (fn-ctl-visible-extend (list *cvt-c*) (list *cvt-o*) nil *cvt-ws*
                                *cvt-verdicts*)
         (fn-ctl-visible-articles (list *cvt-c*) *cvt-ws* *cvt-verdicts*))))

; -----------------------------------------------------------------------------
; The refresh kernel (control-c3b): fn-ctl-refresh-visible-is-visible.

(defun cvt-line (text)
  (append (fn-record-string-octets text) '(13 10)))
(defun cvt-octets (lines)
  (if (consp lines)
      (append (cvt-line (car lines)) (cvt-octets (cdr lines)))
    (append '(13 10) (cvt-line "body"))))
; A real signed-cancel article C2 (payload classified `cancel <t@...>'),
; its target T, an ordinary O, all verified as P's.
(defconst *cvt-c2*
  (fn-make-article "<c2@example.invalid>"
                   (cvt-octets (list "From: p@example.invalid"
                                     "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                                     "Newsgroups: control.cancel"
                                     "Message-ID: <c2@example.invalid>"
                                     "Subject: cmsg cancel <t@example.invalid>"
                                     "Control: cancel <t@example.invalid>"))
                   (list "control.cancel") nil t nil))
(defconst *cvt-cfg* (fn-cfg-initial))
(defconst *cvt-v0* (list (cons "<t@example.invalid>" *cvt-p-verified*)))
(defconst *cvt-v1* (cons (cons "<c2@example.invalid>" *cvt-p-verified*) *cvt-v0*))

; Witness: the old view (T O) under no records; the refresh sees C2 consed
; with its verdict; the record it decides withdraws T by the author basis,
; the incremental list is (C2 O), and so is the definition's.
(assert-event
 (let* ((old (list *cvt-t* *cvt-o*))
        (new (cons *cvt-c2* old))
        (vis (fn-ctl-visible-articles old nil *cvt-v0*))
        (ws2 (fn-ctl-refresh-withdrawals new old nil *cvt-v1* nil nil)))
   (and (equal vis old)
        (equal (len ws2) 1)
        (equal (fn-ctl-w-target (car ws2)) "<t@example.invalid>")
        (equal (fn-ctl-refresh-visible new old vis ws2 *cvt-v0* *cvt-v1*)
               (list *cvt-c2* *cvt-o*))
        (equal (fn-ctl-refresh-visible new old vis ws2 *cvt-v0* *cvt-v1*)
               (fn-ctl-visible-articles new ws2 *cvt-v1*)))))
; Teeth, hypothesis 1 (the carried list is the definition's): a carried
; (O) that lost T is not repaired by an ordinary article.
(must-fail
 (assert-event
  (let* ((old (list *cvt-t* *cvt-o*))
         (new (cons *cvt-a* old))
         (ws2 (fn-ctl-refresh-withdrawals new old nil *cvt-v0* nil nil)))
    (equal (fn-ctl-refresh-visible new old (list *cvt-o*) ws2 *cvt-v0* *cvt-v0*)
           (fn-ctl-visible-articles new ws2 *cvt-v0*)))))
; Teeth, hypothesis 2 (distinct Message-IDs): X reuses O's Message-ID and
; its verdict names Q, whom record W0 (caused by K) names; the definition
; then withdraws O by lookup, the incremental path keeps it.
(defconst *cvt-q* (make-list 32 :initial-element 34))
(defconst *cvt-q-verified* (fn-stx-make-verdict :verified *cvt-q* 1))
(defconst *cvt-q-hex* (fn-record-octets-string (fn-stx-hex-octets *cvt-q*)))
(defconst *cvt-k* (cvt-art "<k@example.invalid>" (list "fn.misc")))
(defconst *cvt-x* (cvt-art "<o@example.invalid>" (list "fn.misc")))
(defconst *cvt-w0*
  (fn-ctl-withdrawal-make "<o@example.invalid>" "<k@example.invalid>"
                          *cvt-q-hex* nil 1))
(assert-event
 (let* ((old (list *cvt-k* *cvt-o*))
        (new (cons *cvt-x* old)))
   (and (not (no-duplicatesp-equal (fn-article-msgids new)))
        (equal (fn-ctl-visible-articles old (list *cvt-w0*) nil) old))))
(must-fail
 (assert-event
  (let* ((old (list *cvt-k* *cvt-o*))
         (new (cons *cvt-x* old))
         (v1 (list (cons "<o@example.invalid>" *cvt-q-verified*)))
         (ws2 (fn-ctl-refresh-withdrawals new old (list *cvt-w0*) v1 nil nil)))
    (equal (fn-ctl-refresh-visible new old old ws2 nil v1)
           (fn-ctl-visible-articles new ws2 v1)))))

; fn-ctl-visible-state-statep.  Witness: an acceptance state holding the
; signed cancel C2 and its target T (each with a membership), the record
; the refresh decides for C2, and the visible state: still a state, T out,
; the watermarks unchanged.  Teeth, the one hypothesis: a record that is
; not a state (duplicate group names) has a visible state that is not one.
(assert-event
 (let* ((c3 (fn-make-article "<c2@example.invalid>" (fn-article-payload *cvt-c2*)
                             (list "control.cancel") (list (cons "control.cancel" 1)) t :legacy))
        (t3 (fn-make-article "<t@example.invalid>" nil (list "fn.mod.a")
                             (list (cons "fn.mod.a" 1)) t :legacy))
        (st (fn-make-state (list "control.cancel" "fn.mod.a")
                           (list (cons "control.cancel" 2) (cons "fn.mod.a" 2))
                           (list c3 t3) 2 nil nil))
        (ws (fn-ctl-articles-withdrawals (list c3 t3) *cvt-v1* nil nil))
        (vis (fn-ctl-visible-state st ws *cvt-v1*)))
   (and (fn-statep st)
        (equal (len ws) 1)
        (fn-statep vis)
        (equal (fn-state-articles vis) (list c3))
        (equal (fn-state-nexts vis) (fn-state-nexts st)))))
(must-fail
 (assert-event
  (let ((bad (fn-make-state (list "fn.a" "fn.a") nil nil 0 nil nil)))
    (fn-statep (fn-ctl-visible-state bad nil nil)))))

; ---------------------------------------------------------------------------
; control-c3d.  Supersedes (RFC 5537 section 5.4): an ordinary article S of
; P's with `Supersedes: <t@...>' withdraws P's T by the author basis, under
; the same decision as a cancel; S itself stays visible.
(defconst *cvt-s*
  (fn-make-article "<s@example.invalid>"
                   (cvt-octets (list "From: p@example.invalid"
                                     "Date: Wed, 23 Sep 2026 12:00:00 +0000"
                                     "Newsgroups: fn.mod.a"
                                     "Message-ID: <s@example.invalid>"
                                     "Subject: corrected"
                                     "Supersedes: <t@example.invalid>"))
                   (list "fn.mod.a") nil t nil))
(defconst *cvt-vs* (cons (cons "<s@example.invalid>" *cvt-p-verified*) *cvt-v0*))
(assert-event
 (let* ((arts (list *cvt-s* *cvt-t*))
        (ws (fn-ctl-articles-withdrawals arts *cvt-vs* nil nil)))
   (and (equal (fn-ctl-target-octets (fn-article-payload *cvt-s*))
               "<t@example.invalid>")
        (equal (fn-ctl-classify-octets (fn-article-payload *cvt-s*)) :ordinary)
        (equal (len ws) 1)
        (equal (fn-ctl-w-cause (car ws)) "<s@example.invalid>")
        (equal (fn-ctl-visible-articles arts ws *cvt-vs*) (list *cvt-s*)))))
; Two Supersedes fields, or Supersedes beside Control, name no target.
(assert-event
 (and (null (fn-ctl-target-octets
             (cvt-octets (list "From: p@example.invalid"
                               "Newsgroups: fn.mod.a"
                               "Message-ID: <s2@example.invalid>"
                               "Subject: x"
                               "Supersedes: <t@example.invalid>"
                               "Supersedes: <o@example.invalid>"))))
      (null (fn-ctl-target-octets
             (cvt-octets (list "From: p@example.invalid"
                               "Newsgroups: control.cancel"
                               "Message-ID: <s3@example.invalid>"
                               "Subject: x"
                               "Control: cancel <o@example.invalid>"
                               "Supersedes: <t@example.invalid>"))))))
; An unverified superseder withdraws nothing (the plan declines).
(assert-event
 (null (fn-ctl-articles-withdrawals (list *cvt-s* *cvt-t*) *cvt-v0* nil nil)))

; ---------------------------------------------------------------------------
; control-c3d.  fn-ctl-refresh-withdrawals-is-the-journal: live equals
; recovery.  Journal: T accepted at txid 4, P's cancel C2 at txid 5, O at 6;
; a grant (P, cancel, fn.mod.*) at txid 1; a revoke appended at txid 9.
(defun cvt-rec (seq txid msgid groups)
  (fn-record-make seq txid 1 msgid '(65) groups "a" "s" "e" 2 :legacy))
(defconst *cvt-rt* (cvt-rec 0 4 "<t@example.invalid>" '("fn.mod.a")))
(defconst *cvt-rc2* (cvt-rec 1 5 "<c2@example.invalid>" '("control.cancel")))
(defconst *cvt-ro* (cvt-rec 2 6 "<o@example.invalid>" '("fn.mod.a")))
(defconst *cvt-grant*
  (fn-cfg-record-make 0 1 1 (list (fn-cfg-grant-control "fn.mod.*" *cvt-p-hex* "cancel"))
                      nil))
(defconst *cvt-revoke-9*
  (fn-cfg-record-make 1 9 2 (list (fn-cfg-revoke-control "fn.mod.*" *cvt-p-hex*)) nil))
(defconst *cvt-revoke-3*
  (fn-cfg-record-make 1 3 2 (list (fn-cfg-revoke-control "fn.mod.*" *cvt-p-hex*)) nil))
(defconst *cvt-jold* (list *cvt-c2* *cvt-t*))
(defconst *cvt-jv0* *cvt-v1*)
(defconst *cvt-jv* (cons (cons "<o@example.invalid>" *cvt-p-verified*) *cvt-v1*))
(defun cvt-journal-conclusion (ws verdicts r0 more-r c0 more-c)
  (equal (fn-ctl-refresh-withdrawals (cons *cvt-o* *cvt-jold*) *cvt-jold* ws verdicts
                                     (append r0 more-r) (append c0 more-c))
         (fn-ctl-journal-withdrawals
          (fn-ctl-archive-entries (cons *cvt-o* *cvt-jold*) verdicts
                                  (append r0 more-r))
          (append c0 more-c))))
(defun cvt-journal-ws (v0 r0 c0)
  (fn-ctl-journal-withdrawals (fn-ctl-archive-entries *cvt-jold* v0 r0) c0))
; Witness: every hypothesis holds; the one record is the authority's grant
; scope at generation 1, and it survives the revoke appended at txid 9.
(assert-event
 (let ((ws (cvt-journal-ws *cvt-jv0* (list *cvt-rt* *cvt-rc2*) (list *cvt-grant*))))
   (and (equal ws (list (fn-ctl-withdrawal-make "<t@example.invalid>"
                                                "<c2@example.invalid>" *cvt-p-hex*
                                                (list "fn.mod.*") 1)))
        (fn-ctl-all-recorded-p *cvt-jold* (list *cvt-rt* *cvt-rc2*))
        (fn-ctl-entries-below-p (fn-ctl-archive-entries *cvt-jold* *cvt-jv0*
                                                        (list *cvt-rt* *cvt-rc2*))
                                9)
        (cvt-journal-conclusion ws *cvt-jv* (list *cvt-rt* *cvt-rc2*) (list *cvt-ro*)
                                (list *cvt-grant*) (list *cvt-revoke-9*)))))
; Hypothesis 1 removed (the carried records are the journal): carried nil.
(must-fail
 (assert-event
  (cvt-journal-conclusion nil *cvt-jv* (list *cvt-rt* *cvt-rc2*) (list *cvt-ro*)
                          (list *cvt-grant*) (list *cvt-revoke-9*))))
; Hypothesis 2 removed (every withdrawing article recorded): C2's record
; arrives only in the appended records, so the carried record was decided
; under the configuration at no txid, and recovery's under txid 5.
(assert-event
 (not (fn-ctl-all-recorded-p *cvt-jold* (list *cvt-rt*))))
(must-fail
 (assert-event
  (cvt-journal-conclusion (cvt-journal-ws *cvt-jv0* (list *cvt-rt*) (list *cvt-grant*))
                          *cvt-jv* (list *cvt-rt*) (list *cvt-rc2* *cvt-ro*)
                          (list *cvt-grant*) (list *cvt-revoke-9*))))
; Hypothesis 3 removed (the verdicts grew only by a fresh Message-ID): the
; new pair names C2 again, verified as Q's.
(must-fail
 (assert-event
  (cvt-journal-conclusion (cvt-journal-ws *cvt-jv0* (list *cvt-rt* *cvt-rc2*)
                                          (list *cvt-grant*))
                          (cons (cons "<c2@example.invalid>" *cvt-q-verified*) *cvt-jv0*)
                          (list *cvt-rt* *cvt-rc2*) (list *cvt-ro*)
                          (list *cvt-grant*) (list *cvt-revoke-9*))))
; Hypothesis 4 removed (appended configuration records come later): a
; revoke at txid 3, before the cancel, changes recovery's decision.
(assert-event
 (not (fn-ctl-entries-below-p (fn-ctl-archive-entries *cvt-jold* *cvt-jv0*
                                                      (list *cvt-rt* *cvt-rc2*))
                              3)))
(must-fail
 (assert-event
  (cvt-journal-conclusion (cvt-journal-ws *cvt-jv0* (list *cvt-rt* *cvt-rc2*)
                                          (list *cvt-grant*))
                          *cvt-jv* (list *cvt-rt* *cvt-rc2*) (list *cvt-ro*)
                          (list *cvt-grant*) (list *cvt-revoke-3*))))
