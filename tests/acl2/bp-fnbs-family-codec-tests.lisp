(in-package "ACL2")
(include-book "../../books/bp-fnbs-family-codec")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnf-family-row*
  (fn-bpnf-family-record 2 5 0 3 '(159 0)))
(assert-event (fn-bpnf-family-recordp *bpnf-family-row*))
(assert-event (fn-cbor-octet-listp
               (fn-bpnf-family-frame *bpnf-family-row*)))
(assert-event
 (equal (fn-bpnf-family-unframe
         (fn-bpnf-family-frame *bpnf-family-row*))
        *bpnf-family-row*))
(assert-event
 (equal (fn-bpnf-family-frame
         (fn-bpnf-family-record 2 5 0 3 nil))
        :bad))
(assert-event
 (null (fn-bpnf-family-unframe
        (append (fn-bpnf-family-frame *bpnf-family-row*) '(0)))))
(must-fail
 (assert-event
  (equal (fn-bpnf-family-unframe
          (append (fn-bpnf-family-frame *bpnf-family-row*) '(0)))
         *bpnf-family-row*)))
