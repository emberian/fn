; Teeth for packets C2 and C3 (books/control-authority.lisp, the
; authorities slot of books/config.lisp, and the `control grant|revoke'
; plan of books/native-admin.lisp).  Per keystone: a reachable witness that
; asserts the complete antecedent and the conclusion, and per hypothesis a
; removal witness that checks every retained hypothesis, the omitted one's
; failure and the conclusion's failure (AGENTS.md, "Teeth ship with each
; keystone").
(in-package "ACL2")
(include-book "../../books/control-authority")
(include-book "../../books/native-admin")
(include-book "std/testing/must-fail" :dir :system)

; Principals: P (octets 17) and Q (octets 34), as details and as hex.
(defconst *cat-p* (make-list 32 :initial-element 17))
(defconst *cat-q* (make-list 32 :initial-element 34))
(defconst *cat-p-hex* (fn-record-octets-string (fn-stx-hex-octets *cat-p*)))
(defconst *cat-q-hex* (fn-record-octets-string (fn-stx-hex-octets *cat-q*)))
(defconst *cat-p-verified* (fn-stx-make-verdict :verified *cat-p* 1))
(defconst *cat-q-verified* (fn-stx-make-verdict :verified *cat-q* 1))
(defconst *cat-p-carried* (fn-stx-make-verdict :carried *cat-p* nil))

(assert-event (fn-cfg-principal-hexp *cat-p-hex*))
(assert-event (equal (fn-ctl-verified-principal *cat-p-verified*) *cat-p-hex*))
(assert-event (null (fn-ctl-verified-principal *cat-p-carried*)))
(assert-event (equal (fn-ctl-named-principal *cat-p-carried*) *cat-p-hex*))

; P holds cancel over fn.mod.*.
(defconst *cat-rows* (list (fn-cfg-row-make "fn.mod.*" *cat-p-hex* "cancel" 0)))
(defconst *cat-in* (list "fn.mod.a"))
(defconst *cat-cross* (list "fn.mod.a" "fn.other"))

(assert-event (fn-ctl-pattern-covers-p "fn.mod.*" "fn.mod.a"))
(assert-event (not (fn-ctl-pattern-covers-p "fn.mod.*" "fn.mod")))
(assert-event (not (fn-ctl-pattern-covers-p "fn.mod.*" "fn.modx.a")))
(assert-event (fn-ctl-pattern-covers-p "fn.mod" "fn.mod"))

; ---------------------------------------------------------------------------
; fn-ctl-authorize-requires-verified-verdict.  Hypothesis: :execute.
(assert-event
 (let ((d (fn-ctl-authorize *cat-p-verified* "cancel" *cat-in* *cat-rows*)))
   (and (equal d (list :execute "cancel" *cat-p-hex* (list "fn.mod.*")))
        (equal (fn-stx-verdict-token *cat-p-verified*) :verified)
        (fn-ctl-principal-detailp (fn-stx-verdict-detail *cat-p-verified*)))))
; Removal of :execute: a carried verdict of the same principal.
(assert-event
 (let ((d (fn-ctl-authorize *cat-p-carried* "cancel" *cat-in* *cat-rows*)))
   (and (equal d (list :decline :carried))
        (not (equal (fn-stx-verdict-token *cat-p-carried*) :verified)))))
(assert-event (equal (fn-ctl-authorize nil "cancel" *cat-in* *cat-rows*)
                     (list :decline :unsigned)))

; ---------------------------------------------------------------------------
; fn-ctl-authorize-requires-a-covering-grant.  Hypotheses: :execute; GROUP
; is among GROUPS.
(assert-event
 (let* ((row (fn-ctl-covering-row *cat-p-hex* "cancel" *cat-rows* "fn.mod.a")))
   (and (equal (car (fn-ctl-authorize *cat-p-verified* "cancel" *cat-in*
                                      *cat-rows*))
               :execute)
        (member-equal "fn.mod.a" *cat-in*)
        (member-equal row *cat-rows*)
        (equal (fn-cfg-row-b row) *cat-p-hex*)
        (equal (fn-cfg-row-c row) "cancel")
        (fn-ctl-pattern-covers-p (fn-cfg-row-a row) "fn.mod.a"))))
; Removal of :execute: the cross-post outside the grant, refused by name.
(assert-event
 (and (member-equal "fn.other" *cat-cross*)
      (equal (fn-ctl-authorize *cat-p-verified* "cancel" *cat-cross* *cat-rows*)
             (list :decline :outside-namespace))
      (not (member-equal (fn-ctl-covering-row *cat-p-hex* "cancel" *cat-rows*
                                              "fn.other")
                         *cat-rows*))))
; Removal of membership: an executed decision says nothing of fn.other.
(assert-event
 (and (equal (car (fn-ctl-authorize *cat-p-verified* "cancel" *cat-in*
                                    *cat-rows*))
             :execute)
      (not (member-equal "fn.other" *cat-in*))
      (not (member-equal (fn-ctl-covering-row *cat-p-hex* "cancel" *cat-rows*
                                              "fn.other")
                         *cat-rows*))))
; The wrong principal: Q holds nothing.
(assert-event (equal (fn-ctl-authorize *cat-q-verified* "cancel" *cat-in* *cat-rows*)
                     (list :decline :no-grant)))

; ---------------------------------------------------------------------------
; fn-cfg-grant-control-admissible-iff (no hypotheses).
(assert-event
 (and (null (fn-cfg-delta-reason (fn-cfg-empty-value) 1 nil 0 512
                                 (fn-cfg-grant-control "fn.mod.*" *cat-p-hex* "cancel")))
      (fn-cfg-namespace-patternp "fn.mod.*")))
(assert-event
 (equal (fn-cfg-delta-reason (fn-cfg-empty-value) 1 nil 0 512
                             (fn-cfg-grant-control "fn.mod.*" *cat-p-hex* "newgroup"))
        :verb-not-grantable))
(assert-event
 (equal (fn-cfg-delta-reason (fn-cfg-empty-value) 1 nil 0 512
                             (fn-cfg-grant-control "fn..*" *cat-p-hex* "cancel"))
        :namespace-pattern))
(assert-event
 (equal (fn-cfg-delta-reason (fn-cfg-empty-value) 1 nil 0 512
                             (fn-cfg-revoke-control "fn.mod.*" *cat-p-hex*))
        :no-such-grant))

; The operator surface: `control grant' plans the delta; a reserved
; namespace is refused by name.
(defun cat-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (cat-argv (cdr words)))
    nil))
(assert-event
 (equal (fn-native-admin-plan-deltas
         (fn-native-admin-plan (cat-argv (list "control" "grant" *cat-p-hex*
                                               "cancel" "fn.mod.*"))))
        (list (fn-cfg-grant-control "fn.mod.*" *cat-p-hex* "cancel"))))
(assert-event
 (equal (fn-native-admin-plan-deltas
         (fn-native-admin-plan (cat-argv (list "control" "revoke" *cat-p-hex*
                                               "cancel" "fn.mod.*"))))
        (list (fn-cfg-revoke-control "fn.mod.*" *cat-p-hex*))))
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (cat-argv (list "control" "grant" *cat-p-hex*
                                               "cancel" "example.*"))))
        :reserved-group-name))

; ---------------------------------------------------------------------------
; Journals: a grant at txid 1, a revoke at txid 9, one cancel at txid 5.
(defconst *cat-grant-rec*
  (fn-cfg-record-make 0 1 1 (list (fn-cfg-grant-control "fn.mod.*" *cat-p-hex* "cancel"))
                      nil))
(defconst *cat-revoke-at-9*
  (fn-cfg-record-make 1 9 2 (list (fn-cfg-revoke-control "fn.mod.*" *cat-p-hex*))
                      nil))
(defconst *cat-revoke-at-3*
  (fn-cfg-record-make 1 3 2 (list (fn-cfg-revoke-control "fn.mod.*" *cat-p-hex*))
                      nil))
(defconst *cat-classified*
  (list :control '(99 97 110 99 101 108)
        (list (fn-record-string-octets "<t@example.invalid>"))))
(defconst *cat-entries*
  (list (list 5 "<c@example.invalid>" *cat-p-verified* "<t@example.invalid>")))

; fn-ctl-revoke-changes-decisions-not-records.  Hypothesis: every entry is
; below the first appended record's txid.
(assert-event
 (let ((before (fn-ctl-journal-withdrawals *cat-entries* (list *cat-grant-rec*)))
       (after (fn-ctl-journal-withdrawals
               *cat-entries* (append (list *cat-grant-rec*) (list *cat-revoke-at-9*)))))
   (and (fn-ctl-entries-below-p *cat-entries* 9)
        (equal before after)
        (equal before
               (list (fn-ctl-withdrawal-make "<t@example.invalid>"
                                             "<c@example.invalid>" *cat-p-hex*
                                             (list "fn.mod.*") 1))))))
; Removal: a revoke at txid 3, before the cancel, does change the record.
(assert-event
 (and (not (fn-ctl-entries-below-p *cat-entries* 3))
      (not (equal (fn-ctl-journal-withdrawals
                   *cat-entries* (append (list *cat-grant-rec*)
                                         (list *cat-revoke-at-3*)))
                  (fn-ctl-journal-withdrawals *cat-entries*
                                              (list *cat-grant-rec*))))))
; Revocation changes the FUTURE decision: after the revoke P holds nothing.
(assert-event
 (let ((v (fn-cfg-apply (fn-cfg-empty-value) 2 nil
                        (list (fn-cfg-grant-control "fn.mod.*" *cat-p-hex* "cancel")
                              (fn-cfg-revoke-control "fn.mod.*" *cat-p-hex*)))))
   (equal (fn-ctl-authorize *cat-p-verified* "cancel" *cat-in*
                            (fn-cfg-authorities v))
          (list :decline :no-grant))))

; ---------------------------------------------------------------------------
; C3.  Articles: target T (unsigned, fn.mod.a), cross-posted target X
; (fn.mod.a, fn.other), P's own signed article A (fn.misc), the cancel C.
(defun cat-art (msgid groups)
  (fn-make-article msgid nil groups nil t nil))
(defconst *cat-t* (cat-art "<t@example.invalid>" (list "fn.mod.a")))
(defconst *cat-x* (cat-art "<x@example.invalid>" *cat-cross*))
(defconst *cat-a* (cat-art "<a@example.invalid>" (list "fn.misc")))
(defconst *cat-c* (cat-art "<c@example.invalid>" (list "control.cancel")))
(defconst *cat-other* (cat-art "<o@example.invalid>" (list "fn.mod.a")))
(defconst *cat-verdicts*
  (list (cons "<a@example.invalid>" *cat-p-verified*)
        (cons "<c@example.invalid>" *cat-p-verified*)))
(defun cat-w (target cause principal scope)
  (fn-ctl-withdrawal-make target cause principal scope 1))
(defconst *cat-w-t* (cat-w "<t@example.invalid>" "<c@example.invalid>" *cat-p-hex*
                           (list "fn.mod.*")))
(defconst *cat-w-x* (cat-w "<x@example.invalid>" "<c@example.invalid>" *cat-p-hex*
                           (list "fn.mod.*")))
(defconst *cat-w-a* (cat-w "<a@example.invalid>" "<c@example.invalid>" *cat-p-hex* nil))
(defconst *cat-w-q* (cat-w "<a@example.invalid>" "<c@example.invalid>" *cat-q-hex* nil))

; fn-ctl-cancel-plan-record-is-bound: the plan for C under the granted
; configuration.
(assert-event
 (let* ((cfg (fn-cfg-make 1 (fn-cfg-apply (fn-cfg-empty-value) 1 nil
                                          (list (fn-cfg-grant-control
                                                 "fn.mod.*" *cat-p-hex* "cancel")))))
        (w (fn-ctl-cancel-plan "<c@example.invalid>" *cat-p-verified*
                               *cat-classified* cfg)))
   (and (fn-ctl-withdrawalp w) (equal w *cat-w-t*))))
(assert-event
 (equal (fn-ctl-cancel-plan "<c@example.invalid>" *cat-p-carried* *cat-classified*
                            (fn-cfg-initial))
        (list :decline :carried)))

; fn-ctl-cancel-executes-only-for-author-or-authority.  Hypothesis: the
; effect withdraws.  Witnesses: the author case and the authority case.
(assert-event
 (and (equal (fn-ctl-withdrawal-effect *cat-w-a* (list "fn.misc") *cat-p-verified*)
             :author)
      (equal (fn-ctl-named-principal *cat-p-verified*) (fn-ctl-w-principal *cat-w-a*))))
(assert-event
 (and (equal (fn-ctl-withdrawal-effect *cat-w-t* (list "fn.mod.a") nil) :authority)
      (fn-ctl-covers-every-p (fn-ctl-w-scope *cat-w-t*) (list "fn.mod.a"))))
; Removal: the wrong principal (Q, no grant) on P's article, and the
; cross-post outside the grant: neither withdraws, and neither disjunct holds.
(assert-event
 (and (equal (fn-ctl-withdrawal-effect *cat-w-q* (list "fn.misc") *cat-p-verified*)
             (list :decline :no-grant))
      (not (equal (fn-ctl-named-principal *cat-p-verified*)
                  (fn-ctl-w-principal *cat-w-q*)))
      (not (consp (fn-ctl-w-scope *cat-w-q*)))))
(assert-event
 (and (equal (fn-ctl-withdrawal-effect *cat-w-x* *cat-cross* nil)
             (list :decline :outside-namespace))
      (null (fn-ctl-named-principal nil))
      (not (fn-ctl-covers-every-p (fn-ctl-w-scope *cat-w-x*) *cat-cross*))))

; fn-ctl-target-is-never-visible-beside-its-cancel.  The early cancel: C
; committed first, T after; the first view holding T holds C.
(defconst *cat-early* (list *cat-t* *cat-c* *cat-other*))
(assert-event
 (and (member-equal *cat-w-t* (list *cat-w-t*))
      (fn-ctl-withdrawalp *cat-w-t*)
      (equal (fn-ctl-w-target *cat-w-t*) (fn-article-msgid *cat-t*))
      (fn-ctl-has-msgid-p (fn-ctl-w-cause *cat-w-t*) *cat-early*)
      (fn-ctl-effect-withdrawsp (fn-ctl-withdrawal-effect *cat-w-t* (list "fn.mod.a") nil))
      (equal (fn-ctl-visible-articles *cat-early* (list *cat-w-t*) *cat-verdicts*)
             (list *cat-c* *cat-other*))))
; Removal of "the cause is in the view": a view pinned before C.
(assert-event
 (and (not (fn-ctl-has-msgid-p "<c@example.invalid>" (list *cat-t* *cat-other*)))
      (member-equal *cat-t* (fn-ctl-visible-articles (list *cat-t* *cat-other*)
                                                     (list *cat-w-t*) *cat-verdicts*))))
; Removal of "the effect withdraws": the cross-post, cause present, stays.
(assert-event
 (let ((view (list *cat-x* *cat-c*)))
   (and (fn-ctl-has-msgid-p "<c@example.invalid>" view)
        (equal (fn-ctl-w-target *cat-w-x*) (fn-article-msgid *cat-x*))
        (not (fn-ctl-effect-withdrawsp
              (fn-ctl-withdrawal-effect *cat-w-x* *cat-cross* nil)))
        (member-equal *cat-x* (fn-ctl-visible-articles view (list *cat-w-x*)
                                                       *cat-verdicts*)))))
; Removal of "the target matches": another article in the same group stays.
(assert-event
 (and (not (equal (fn-ctl-w-target *cat-w-t*) (fn-article-msgid *cat-other*)))
      (member-equal *cat-other* (fn-ctl-visible-articles *cat-early* (list *cat-w-t*)
                                                         *cat-verdicts*))))
; Removal of membership of the record: no records, T is served.
(assert-event
 (member-equal *cat-t* (fn-ctl-visible-articles *cat-early* nil *cat-verdicts*)))

; fn-ctl-pinned-view-keeps-its-archive.  Hypothesis: the cause is absent.
(assert-event
 (let ((pinned (list *cat-t* *cat-other*)))
   (and (not (fn-ctl-has-msgid-p (fn-ctl-w-cause *cat-w-t*) pinned))
        (equal (fn-ctl-visible-articles pinned (list *cat-w-t*) *cat-verdicts*)
               (fn-ctl-visible-articles pinned nil *cat-verdicts*))
        (equal (fn-ctl-visible-articles pinned nil *cat-verdicts*) pinned))))
; Removal: once the view advances past C, the archive changes.
(assert-event
 (and (fn-ctl-has-msgid-p (fn-ctl-w-cause *cat-w-t*) *cat-early*)
      (not (equal (fn-ctl-visible-articles *cat-early* (list *cat-w-t*) *cat-verdicts*)
                  (fn-ctl-visible-articles *cat-early* nil *cat-verdicts*)))))

; fn-ctl-visible-is-arrival-order-independent (no hypotheses): T then C and
; C then T serve the same articles, and neither serves T.
(assert-event
 (let ((tc (fn-ctl-visible-articles (list* *cat-t* *cat-c* (list *cat-other*))
                                    (list *cat-w-t*) *cat-verdicts*))
       (ct (fn-ctl-visible-articles (list* *cat-c* *cat-t* (list *cat-other*))
                                    (list *cat-w-t*) *cat-verdicts*)))
   (and (not (member-equal *cat-t* tc)) (not (member-equal *cat-t* ct))
        (member-equal *cat-other* tc) (member-equal *cat-other* ct)
        (member-equal *cat-c* tc) (member-equal *cat-c* ct))))
