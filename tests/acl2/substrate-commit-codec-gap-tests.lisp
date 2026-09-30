; Open representability counterexample, separate from certified transcript
; retention/authority teeth. No round-trip or supported-profile claim.
(in-package "ACL2")
(include-book "../../books/stx-commit-codec")
(include-book "../../books/statement-attach")
(defconst *stcg-oversize-commit*
  (fn-me-commit (make-list 513 :initial-element 1) 0
                (make-list 32 :initial-element 2) :remove
                (make-list 32 :initial-element 3)))
(make-event
 (list 'defconst '*stcg-oversize-wire*
       (list 'quote (fn-stx-commit-encode *stcg-oversize-commit*))))
; Positive encoder-side premises and exact output, affirmative decoder refusal.
(assert-event
 (and (fn-me-commitp *stcg-oversize-commit*)
      (fn-stx-commit-encodablep *stcg-oversize-commit*)
      (equal (fn-me-commit-id *stcg-oversize-commit*) (make-list 513 :initial-element 1))
      (equal *stcg-oversize-wire*
             (append '(89 2 1) (make-list 513 :initial-element 1)
                     '(0 88 32) (make-list 32 :initial-element 2)
                     '(1 88 32) (make-list 32 :initial-element 3)))
      (equal (len *stcg-oversize-wire*) 586)
      (equal *fn-stx-max-commit-octets* 512)
      (not (fn-cbor-at-mostp *stcg-oversize-wire* *fn-stx-max-commit-octets*))
      (equal (fn-stx-commit-decode-exact *stcg-oversize-wire*) (fn-stmt-error :limit))
      (not (fn-stmt-okp (fn-stx-commit-decode-exact *stcg-oversize-wire*)))))
