; Actual receive producer + explicit unfunded registered storage fixture.
(in-package "ACL2")
(include-book "../../books/bp-received-source-capture")
(include-book "bp-node-foundation-tests")
(include-book "bp-controller-registry-carry-tests")
(defun fn-bprx-source-test (current)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-bp-controller-registry
  (mv-let (result fn-bp-controller-registry)
   (let ((fn-bp-controller-registry (bpcc-install current fn-bp-controller-registry)))
    (mv-let (word capture left)
     (fn-bprx-registered-source-read '(:bp-controller 7 0) 4 fn-bp-controller-registry)
     (mv-let (stale absent stale-left)
      (fn-bprx-registered-source-read '(:bp-controller 8 0) 4 fn-bp-controller-registry)
      (mv (list word capture left stale absent stale-left) fn-bp-controller-registry))))
   result)))
; Real receive proposal has no durable custody yet. Exact held reference is
; selected from registered CURRENT, not a caller's copied :persist effect.
(assert-event
 (and (fn-bprx-pending-sourcep *bpnf-pending*)
      (fn-bprx-received-source-carryp *bpnf-pending*)
      (null (fn-bpnf-held-list *bpnf-pending*))
      (equal (fn-bprx-source-test *bpnf-pending*)
       (list :received-source
        (list :bp-received-source '(:bp-controller 7 0) 3 0 0
              (fn-bpn-nth 4 (fn-bpnf-issued *bpnf-pending*)))
        3 :stale-controller nil 3))))
(assert-event
 (equal (fn-bprx-source-test
   (fn-bpnf-with-issued *bpnf-pending*
    (fn-bpnf-operation 3 0 :store
      (fn-bpn-nth 4 (fn-bpnf-issued *bpnf-pending*)) :uncertain)))
  '(:received-source-uncertain nil 3 :stale-controller nil 3)))
(assert-event
 (equal (fn-bprx-source-test *bpnf-s0*)
  '(:received-source-unavailable nil 3 :stale-controller nil 3)))
