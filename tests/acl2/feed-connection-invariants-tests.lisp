; Executable witnesses and premise teeth for the carried connection table.
(in-package "ACL2")
(include-book "../../books/feed-connection-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fci-one* (fn-fc-initial-state t 7))
(defconst *fci-two* (fn-fc-initial-state nil 8))
(defconst *fci-table-one*
  (fn-fc-table-put "one" *fci-one* (fn-fc-table-initial-state)))
(defconst *fci-table-two*
  (fn-fc-table-put "two" *fci-two* *fci-table-one*))

(assert-event
 (equal (symbol-class 'fn-fc-table-initial-state (w state))
        :common-lisp-compliant))

; Reachable nonempty construction, selected-state and removal witnesses.
(assert-event (fn-fc-tablep *fci-table-two*))
(assert-event (equal (fn-fc-table-lookup "one" *fci-table-two*) *fci-one*))
(assert-event (fn-fc-statep (fn-fc-table-lookup "two" *fci-table-two*)))
(assert-event
 (fn-fc-statep
  (fn-fc-next-state
   (fn-fc-step (fn-fc-table-lookup "one" *fci-table-two*)
               '(50 48 48 32 111 107 13 10)))))
(assert-event
 (and (fn-fc-tablep (fn-fc-table-remove "two" *fci-table-two*))
      (equal (fn-fc-table-lookup
              "two" (fn-fc-table-remove "two" *fci-table-two*)) nil)
      (equal (fn-fc-table-lookup
              "one" (fn-fc-table-remove "two" *fci-table-two*)) *fci-one*)))

; Each fn-fc-table-put preservation premise has teeth.
(must-fail
 (assert-event
  (fn-fc-tablep
   (fn-fc-table-put :not-a-string *fci-one*
                    (fn-fc-table-initial-state)))))
(must-fail
 (assert-event
  (fn-fc-tablep
   (fn-fc-table-put "bad-state" :not-a-state
                    (fn-fc-table-initial-state)))))
(must-fail
 (assert-event
  (fn-fc-tablep
   (fn-fc-table-put "new" *fci-one* '(:malformed-table)))))

; Remove preservation and selected-state validity both need the carried table
; invariant; selected-state validity also needs a present lookup.
(must-fail
 (assert-event
  (fn-fc-tablep (fn-fc-table-remove "absent" '(:malformed-table)))))
(must-fail
 (assert-event
  (let ((bad-table (list (cons "bad" :not-a-state))))
    (fn-fc-statep (fn-fc-table-lookup "bad" bad-table)))))
(must-fail
 (assert-event
  (fn-fc-statep (fn-fc-table-lookup "absent" *fci-table-two*))))

; The sole selected-state premise of step preservation has teeth.  Chunk shape
; is deliberately not a premise: invalid input returns the still-valid state.
(must-fail
 (assert-event
  (fn-fc-statep
   (fn-fc-next-state (fn-fc-step :not-a-state nil)))))
