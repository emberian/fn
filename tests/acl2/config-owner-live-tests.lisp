; Administrative completion changes the actual owner Store together with the
; live configuration; a prior physical capacity decrease remains recoverable.
(in-package "ACL2")
(include-book "../../books/config-owner-live")
(include-book "config-observed-tests")

(defconst *ocl-t-cfg*
  (fn-cnode-config
   (fn-replay-result-node
    (fn-cpr-replay *cpo-t-configs* *cpo-t-events*))))
(defconst *ocl-t-before*
  (fn-ocfg-make (fn-own-start *cpo-t-ready* 3)
                *ocl-t-cfg* nil *cpo-t-increase*))
(defconst *ocl-t-after* (fn-ocl-complete *ocl-t-before*))

(assert-event (fn-cst-relation *cpo-t-ready*))
(assert-event (null (fn-ocfg-staged *ocl-t-after*)))
(assert-event
 (equal (fn-sn-capacity (fn-own-store (fn-ocfg-owner *ocl-t-after*))) 20))
(assert-event
 (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner *ocl-t-after*)))
        (append *cpo-t-configs* (list *cpo-t-increase*))))
(assert-event
 (fn-cst-relation (fn-own-store (fn-ocfg-owner *ocl-t-after*))))
(assert-event
 (equal (fn-cfg-generation (fn-ocfg-config *ocl-t-after*)) 3))
(assert-event
 (equal (fn-ocfg-pins *ocl-t-after*) (fn-ocfg-pins *ocl-t-before*)))

; A record below the live reservation total remains staged after durable
; publication; the host must fence and reopen rather than report acceptance.
(defconst *ocl-t-refused-record*
  (fn-cfg-record-make 2 8 3 (list (fn-cfg-set-capacity 0))
                      *fn-cfg-default-stamp*))
(defconst *ocl-t-refused*
  (fn-ocfg-make (fn-ocfg-owner *ocl-t-before*)
                *ocl-t-cfg* nil *ocl-t-refused-record*))
(assert-event (equal (fn-ocl-complete *ocl-t-refused*) *ocl-t-refused*))
