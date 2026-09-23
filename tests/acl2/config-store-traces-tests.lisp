; The historical trace relation distinguishes a valid decrease from static
; final-capacity replay, including the opened and ready phases.
(in-package "ACL2")
(include-book "../../books/config-store-traces")
(include-book "config-observed-tests")

(assert-event
 (fn-cst-relation (fn-sn-open-state *cpo-t-open*)))
(assert-event (fn-cst-relation *cpo-t-ready*))
(assert-event (fn-cst-relation *cpo-t-live*))
(assert-event (fn-cst-relation *cpo-t-live-domain*))
(assert-event (not (fn-snt-relation *cpo-t-ready*)))
