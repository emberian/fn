; Teeth for books/payload-kinds (lane entry-guards).
;
; Positive witnesses: a natural is a payload handle and never octets; a byte
; list (and NIL, the empty payload) is octets and never a handle.  The kind
; recognizers the host entry guard evaluates each refuse the other kind's
; value.  Mutation witnesses: a list holding a non-byte is not octets; a list
; of octet lists holding a handle is refused.
(in-package "ACL2")
(include-book "../../books/payload-kinds")
(assert-event (and (fn-payload-handle-p 7) (fn-payload-handle-p 0)))
(assert-event (not (fn-cbor-octet-listp 7)))
(assert-event (and (fn-cbor-octet-listp '(71 69 84)) (fn-cbor-octet-listp nil)))
(assert-event (and (not (fn-payload-handle-p '(71 69 84))) (not (fn-payload-handle-p nil))))
(assert-event (not (fn-cbor-octet-listp '(300))))
(assert-event (fn-octet-list-listp '((1 2) nil (3))))
(assert-event (not (fn-octet-list-listp '((1 2) 7))))
; Every kind the host evaluates is a defined function of one argument.
(assert-event (let ((names (strip-cars *fn-entry-guard-kinds*)))
                (and (symbol-listp names) (no-duplicatesp names)
                     (member 'fn-payload-handle-p names)
                     (member 'fn-cbor-octet-listp names))))
