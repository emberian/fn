; Exact wire admission and TCPCL callback dispositions.
(in-package "ACL2")
(include-book "../../books/bp-node-receive-boundary")
(include-book "bp-node-foundation-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnrb-ready*
  (fn-bpnf-receive-wire-event
   *bpnf-config* *bpnf-wire* *bpnf-obs* *bpnf-ingress-p*))
(assert-event (fn-bpnf-receive-wire-readyp *bpnrb-ready*))
(assert-event
 (equal (fn-bpnf-tcpcl-ingress *bpnf-s0* 1 1 *bpnf-peer* '(112) 0)
        (list :cl (cons 3 1) 1 *bpnf-peer* '(112) 0)))
(assert-event
 (null (fn-bpnf-tcpcl-ingress *bpnf-s0* -1 1 *bpnf-peer* '(112) 0)))
(assert-event
 (equal (fn-bpnf-receive-wire-event-value *bpnrb-ready*)
        (list :receive-bundle *bpnf-bundle* *bpnf-wire* *bpnf-ingress-p*)))
(assert-event
 (fn-bpnf-host-eventp (fn-bpnf-receive-wire-event-value *bpnrb-ready*)))
(assert-event
 (equal (car (fn-bpnf-receive-wire-event
              *bpnf-config* '(1 2 3) *bpnf-obs* *bpnf-ingress-p*))
        :refused))
(assert-event
 (equal (fn-bpnf-receive-wire-event
         *bpnf-config* *bpnf-wire* *bpnf-obs* '(:cl :bad))
        '(:refused :receive-boundary)))
(assert-event
 (equal (fn-bpnf-receive-wire-event
         *bpnf-config* (append *bpnf-wire* (list 0))
         *bpnf-obs* *bpnf-ingress-p*)
        '(:refused :trailing-octets)))
(assert-event
 (equal (fn-bpnf-callback-result
         (list (list :receive-answer *bpnf-ingress-p* :stored))
         *bpnf-ingress-p* "final.fnb")
        '(:accepted "final.fnb")))
(assert-event
 (equal (fn-bpnf-callback-result
         (list (list :receive-answer *bpnf-ingress-p* :duplicate))
         *bpnf-ingress-p* "ignored.fnb")
        '(:accepted nil)))
(assert-event
 (equal (fn-bpnf-callback-result
         (list (list :receive-answer *bpnf-ingress-p* '(:refused :capacity)))
         *bpnf-ingress-p* nil)
        '(:refused :capacity)))
(assert-event
 (equal (fn-bpnf-callback-result
         (list (list :receive-answer *bpnf-ingress-p* '(:uncertain :persistence)))
         *bpnf-ingress-p* nil)
        '(:uncertain :persistence)))
(assert-event
 (equal (fn-bpnf-callback-result
         (list (list :receive-answer *bpnf-ingress-q* :stored))
         *bpnf-ingress-p* nil)
        '(:uncertain :machine-answer)))
(must-fail
 (assert-event
  (equal (fn-bpnf-callback-result
          (list (list :receive-answer *bpnf-ingress-p* '(:refused :capacity)))
          *bpnf-ingress-p* nil)
         '(:accepted nil))))
