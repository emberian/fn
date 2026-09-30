(in-package "ACL2")
(include-book "../../books/admission-preallocation-census")

; Reachable one-cell seek with a real consumer entry and its exact annotation.
; Fixture-only ghost summary establishes provenance; no served census walks it.
(assert-event
 (let* ((row '(:entry (97) (98) (99) 0 0 1 0))
        (carry (fn-scs-summary row))
        (metadata (fn-caac-list-cons carry nil))
        (cursor (fn-cep-state '(100) (list row) metadata nil nil :seek nil nil nil nil)))
  (mv-let (one cells) (fn-apr-entry-tick-source-execution cursor)
   (and (fn-cp-entryp row 0 2) (fn-scs-carryp carry)
        (equal one (fn-cep-tick cursor)) (eq (car one) :yield)
        (equal (fn-cp-nth 4 (cadr one)) (list row))
        (equal (fn-cp-nth 6 (cadr one)) :seek)
        (equal cells 23) (natp cells) (<= cells 29)))))

; Corrupted annotation is NOT provenance or permission. The operational model
; still prices all three actual fallback normalizations (head twice, tail once).
(assert-event
 (let* ((row '(:entry (97) (98) (99) 0 0 1 0))
        (cursor (fn-cep-state '(100) (list row) nil nil nil :seek nil nil nil nil)))
  (mv-let (one cells) (fn-apr-entry-tick-source-execution cursor)
   (and (not (fn-scs-carryp nil)) (equal one (fn-cep-tick cursor))
        (eq (car one) :yield) (equal cells 29)))))

(assert-event
 (let* ((row '(:entry (97) (98) (99) 0 0 1 0))
        (metadata (fn-caac-list-cons (fn-scs-summary row) nil))
        (cursor (fn-cep-state '(100) nil nil (list row) metadata :reverse nil nil nil nil)))
  (mv-let (one cells) (fn-apr-entry-tick-source-execution cursor)
   (and (equal one (fn-cep-tick cursor)) (eq (car one) :yield)
        (equal (fn-cp-nth 7 (cadr one)) (list row)) (equal cells 23)))))
(assert-event
 (let* ((row '(:entry (97) (98) (99) 0 0 1 0))
        (cursor (fn-cep-state '(97) (list row) nil nil nil :seek nil nil nil nil)))
  (mv-let (one cells) (fn-apr-entry-tick-source-execution cursor)
   (and (equal one (fn-cep-tick cursor)) (eq (car one) :yield)
        (equal (fn-cp-nth 9 (cadr one)) row) (equal cells 13)))))
(assert-event
 (let ((cursor (fn-cep-state '(100) nil nil nil nil :ready nil nil nil nil)))
  (mv-let (one cells) (fn-apr-entry-tick-source-execution cursor)
   (and (equal one (fn-cep-tick cursor)) (equal one (list :ready cursor))
        (equal cells 2)))))
(assert-event
 (mv-let (one cells) (fn-apr-entry-tick-source-execution nil)
  (and (equal one (fn-cep-tick nil))
       (equal one '(:refused :consumer-preparation-phase)) (equal cells 0))))
