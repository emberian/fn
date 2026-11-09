; THE STORED OWNERS. Three tables keep, per row, the owner kind their writes
; go out as: the cursor's conn-kind (its connection's reply), a read scan's
; qk (copied from that conn-kind) and an overlay's okind (its arena). The
; invariant FN2-DH-OWNERS-OK K: no row of those columns holds K. With K the
; commit kind, a write naming such a stored owner is never the commit
; kind's, so the cursor's run keeps the rows the commit kind holds
; (machines.lisp fn2-dispatch-held-claims). It holds after init (every
; column starts at 0) and every function the dispatch's chains reach keeps
; it (dispatch-held.lisp: one lemma per function, the writers of the
; columns asked that the value stored is not K).
(in-package "ACL2")
(include-book "dispatch-held")
(include-book "assembly-callbacks")

;; (stobj owner-column core-accessor)
(defconst *fn2-dispatch-held-owner-tables*
  '((fn2-cursor conn-kind fn2-cursor-table) (fn2-overlays okind fn2-core-overlays) (fn2-reads qk fn2-core-reads)))
(make-event
 (value (cons 'progn (fn2-dh-owner-events-all *fn2-dispatch-held-owner-tables* (w state)))))
(make-event (value (fn2-dh-owners-ok-form (w state))))
(make-event (value (cons 'progn (fn2-dh-owners-rules-forms (w state)))))
(in-theory (disable fn2-dh-owners-ok))
