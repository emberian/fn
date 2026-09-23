(in-package "ACL2")
(include-book "../../books/bp-fnbs-delivery-codec")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpah-delivered*
  (fn-bpah-delivery-record 3 8 2 '(1 2 3) :request-accepted '(114 105 100)))
(assert-event (fn-bpah-delivery-recordp *bpah-delivered*))
(assert-event (fn-cbor-octet-listp
               (fn-bpah-delivery-frame *bpah-delivered*)))
(assert-event (equal (fn-bpah-delivery-unframe
                      (fn-bpah-delivery-frame *bpah-delivered*))
                     *bpah-delivered*))
(assert-event (not (fn-bpah-delivery-recordp
                    (fn-bpah-delivery-record 3 8 2 '(1 2 3)
                                               :request-accepted '(0)))))
(assert-event (equal (fn-bpah-delivery-frame
                      (fn-bpah-delivery-record 3 8 2 nil
                                                 :request-accepted '(1)))
                     :bad))
(assert-event (null (fn-bpah-delivery-unframe
                     (append (fn-bpah-delivery-frame *bpah-delivered*) '(0)))))
(must-fail
 (assert-event (equal (fn-bpah-delivery-unframe
                       (append (fn-bpah-delivery-frame *bpah-delivered*) '(0)))
                      *bpah-delivered*)))
