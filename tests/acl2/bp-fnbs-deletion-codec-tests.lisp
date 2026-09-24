(in-package "ACL2")
(include-book "../../books/bp-fnbs-deletion-codec")
(include-book "bp-report-deletion-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-cbor-octet-listp
               (fn-bpnf-delete-frame *bprd-request-record*)))
(assert-event (equal (fn-bpnf-delete-unframe
                      (fn-bpnf-delete-frame *bprd-request-record*))
                     *bprd-request-record*))
(assert-event
 (equal (fn-bpnf-delete-frame
         (fn-bpn-report-delete-record
          1 5 1 *bprd-identity* :block-unintelligible))
        :bad))
(assert-event (null (fn-bpnf-delete-unframe
                     (append (fn-bpnf-delete-frame
                              *bprd-request-record*) '(0)))))
(assert-event (null (fn-bpnf-delete-unframe
                     (cdr (fn-bpnf-delete-frame *bprd-request-record*)))))
(must-fail
 (assert-event
  (fn-bpnf-delete-unframe
   (append (fn-bpnf-delete-frame *bprd-request-record*) '(0)))))
