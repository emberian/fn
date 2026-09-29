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
