; Teeth for books/owner-control-post-reason.lisp (row S10, lane operability-2).
(in-package "ACL2")
(include-book "../../books/owner-control-post-reason")

; The reason: the Store's word for a refused completion, nothing otherwise.
(assert-event (equal (fn-ocpr-reason :refused :unaffordable) :unaffordable))
(assert-event (equal (fn-ocpr-reason :refused :store-full) :store-full))
(assert-event (null (fn-ocpr-reason :accepted :durable)))
(assert-event (null (fn-ocpr-reason :duplicate :duplicate)))
(assert-event (null (fn-ocpr-reason :uncertain :uncertain)))
; A word that is no symbol (a malformed completion) names nothing rather
; than a fabricated reason.
(assert-event (null (fn-ocpr-reason :refused "unaffordable")))
(assert-event (null (fn-ocpr-reason :refused nil)))

; The line: with no control submission in flight (an owner value that holds
; none) the class is :absent and the line is the plain one; the keystone's
; other arm.  The positive witness (a refused completion of an in-flight
; control submission) is the native case, tests/test_native_operator_refusals
; (SCN-209): the line carries ` reason=' and the reply the word.
(assert-event (equal (fn-own-control-outcome-result nil :unaffordable) :absent))
(assert-event (equal (fn-ocpr-log-line nil :unaffordable)
                     (fn-olog-control-post-line nil :unaffordable)))
(assert-event (equal (fn-olog-field "reason" (fn-olog-symbol-text :unaffordable))
                     (fn-olog-text "reason=unaffordable")))

; KEYSTONE fn-ocpr-line-names-the-reason-exactly-when-refused (PRF-972; an
; equality over an `if', no hypothesis), the refused arm by name.  The owner
; value is CONSTRUCTED, not a run: nothing but a control submission in
; flight (id :control, no ledger mark), which is all the class reads.  The
; completion of :unaffordable is then :refused, and the line is the plain
; line followed by ` reason=unaffordable'.
(defconst *ocpr-o*
  (fn-own-make nil nil nil 0 0 nil nil nil nil nil nil
               (list *fn-own-control-id*) nil nil nil))
(assert-event (fn-own-control-submissionp (fn-own-inflight *ocpr-o*)))
(assert-event
 (and (equal (fn-own-control-outcome-result *ocpr-o* :unaffordable) :refused)
      (equal (fn-ocpr-log-line *ocpr-o* :unaffordable)
             (append (fn-olog-control-post-line *ocpr-o* :unaffordable)
                     (fn-olog-text " ")
                     (fn-olog-field "reason" (fn-olog-symbol-text :unaffordable))))
      (not (equal (fn-ocpr-log-line *ocpr-o* :unaffordable)
                  (fn-olog-control-post-line *ocpr-o* :unaffordable)))))
; The same in-flight control submission with a word that refuses nothing
; takes the plain arm: the reason is named exactly when refused.
(assert-event
 (and (not (equal (fn-own-control-outcome-result *ocpr-o* :bogus) :refused))
      (equal (fn-ocpr-log-line *ocpr-o* :bogus)
             (fn-olog-control-post-line *ocpr-o* :bogus))))
