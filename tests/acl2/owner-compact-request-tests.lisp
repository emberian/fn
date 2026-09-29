; Teeth for books/owner-compact-request.lisp (PKT-868, lane operations).
(in-package "ACL2")
(include-book "../../books/owner-compact-request")
(include-book "must-fail-checked")

; KEYSTONE fn-ock-requested-next-is-due-with-a-suffix, positive witness: a
; request, nothing in flight, no deferral, a suffix of 10 below K/2 = 64
; (the automatic rule is not due): the decision is :due.
(assert-event (not (fn-ock-publication-duep 0 10 128 nil)))
(assert-event (fn-ock-request-duep 0 10 nil))
(assert-event (equal (fn-ock-requested-next 0 10 128 nil nil nil t) :due))
; ... and without the request the same observations are :idle.
(assert-event (equal (fn-ock-requested-next 0 10 128 nil nil nil nil) :idle))
; Hypothesis removal, (not (natp inflight)): with a publication in flight the
; request coalesces; never a second :due.
(assert-event (not (equal (fn-ock-requested-next 0 10 128 nil 8 nil t) :due)))
(assert-event (equal (fn-ock-request-word 0 10 nil 8 nil) :coalesced))
; Hypothesis removal, (not blockedp): a deferral stands against a request.
(assert-event (equal (fn-ock-requested-next 0 10 128 nil nil t t) :blocked))
(assert-event (equal (fn-ock-request-word 0 10 nil nil t) :blocked))
(assert-event (equal (fn-ock-request-status :blocked) :refused))
; No suffix: nothing to compact, and a request does not make it due.
(assert-event (equal (fn-ock-requested-next 12 12 128 nil nil nil t) :idle))
(assert-event (equal (fn-ock-request-word 12 12 nil nil nil) :nothing-to-compact))
; The count the last attempt took is not a suffix again.
(assert-event (equal (fn-ock-requested-next 0 10 128 10 nil nil t) :idle))
; The answer :requested is the next decision's :due.
(assert-event (equal (fn-ock-request-word 0 10 nil nil nil) :requested))
(assert-event (equal (fn-ock-request-status :requested) :accepted))

(must-fail-checked
 (defthm ocr-requested-due-without-not-inflight
   (implies (and requested (not blockedp))
            (iff (equal (fn-ock-requested-next durable count k attempted inflight blockedp
                                               requested)
                        :due)
                 (or (fn-ock-publication-duep durable count k attempted)
                     (fn-ock-request-duep durable count attempted))))
   :rule-classes nil))
(must-fail-checked
 (defthm ocr-requested-due-without-not-blocked
   (implies (and requested (not (natp inflight)))
            (iff (equal (fn-ock-requested-next durable count k attempted inflight blockedp
                                               requested)
                        :due)
                 (or (fn-ock-publication-duep durable count k attempted)
                     (fn-ock-request-duep durable count attempted))))
   :rule-classes nil))
