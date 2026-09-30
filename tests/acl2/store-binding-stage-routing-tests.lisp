; Actual composed Store regression. Execute on the matching modern owner
; source world; authoring these assertions is not their execution verdict.
(in-package "ACL2")
(include-book "../../books/store-events-carried")
(local (include-book "consumer-transaction-dispatch-tests"))

;@mutation-witness actual-store-local-v1-and-binding-v3-roundtrip
(assert-event
 (and (equal (fn-store-event-decode-exact (fn-store-event-encode *cnet-local*))
             (list :ok *cnet-local*))
      (equal (fn-store-event-decode-exact (fn-store-event-encode *cnet-binding*))
             (list :ok *cnet-binding*))))
;@mutation-witness actual-binding-retained-wire-carried-fields
(assert-event
 (and (fn-store-event-p *cnet-binding*) (fn-wire-event-p *cnet-binding*)
      (equal (fn-store-event-kind *cnet-binding*) :consumer-authority)
      (equal (fn-wire-event-kind *cnet-binding*) :consumer-authority)
      (equal (fn-store-event-sequence *cnet-binding*) 2)
      (equal (fn-store-event-txid *cnet-binding*) 3)
      (equal (fn-store-event-generation *cnet-binding*) 0)
      (fn-evc-authorityp *cnet-binding*)
      (equal (fn-evc-sequence *cnet-binding*) 2)
      (equal (fn-evc-txid *cnet-binding*) 3)
      (equal (fn-evc-generation *cnet-binding*) 0)))
