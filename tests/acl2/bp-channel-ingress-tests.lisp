; Raw TCPCL session-init octets and observed channel are decided together.
(in-package "ACL2")
(include-book "../../books/bp-channel-ingress")
(include-book "bp-session-admission-tests")
(include-book "bp-node-foundation-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpcin-uri* (fn-record-string-octets "dtn://peer/"))
(defconst *bpcin-result*
  (fn-bpaj-tcpcl-ingress-result
   *bpat-cfg* *bpnf-s0* *bpat-channel* *bpcin-uri* 1 2))
(assert-event (equal (fn-bpaj-raw-announced-eid *bpcin-uri*) *bpat-eid*))
(assert-event
 (equal *bpcin-result*
        (list :admitted nil
              (list :cl (cons 3 1) 2 *bpat-eid*
                    (fn-record-string-octets "peer") 7))))
(must-fail (assert-event (equal (car *bpcin-result*) :refused)))

; The same valid announced bytes can have custody without Store authority.
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-no-trust* *bpnf-s0* *bpat-channel* *bpcin-uri* 1 2)
        (list :refused :no-trust-profile
              (list :cl (cons 3 1) 2 *bpat-eid* nil 0))))
(must-fail
 (assert-event
  (equal (car (fn-bpaj-tcpcl-ingress-result
               *bpat-no-trust* *bpnf-s0* *bpat-channel*
               *bpcin-uri* 1 2)) :admitted)))

; Announced-EID disagreement preserves the parsed EID and refuses authority.
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0* *bpat-channel*
         (fn-record-string-octets "dtn://other/") 1 2)
        (list :refused :eid-mismatch
              (list :cl (cons 3 1) 2 *bpat-other-eid* nil 0))))
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0*
         (list :tcp4 '(127 0 0 1) 4556 '(127 0 0 2))
         *bpcin-uri* 1 2)
        (list :refused :channel
              (list :cl (cons 3 1) 2 *bpat-eid* nil 0))))
; Malformed external bytes cannot form a typed ingress at all.
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0* *bpat-channel* '(100 116 110) 1 2)
        '(:refused :announced-eid nil)))
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0* *bpat-channel*
         (append *bpcin-uri* (make-list (+ 5 *fn-bpc-max-text*)
                                       :initial-element 65)) 1 2)
        '(:refused :announced-eid nil)))
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0* *bpat-channel* *bpcin-uri* -1 2)
        '(:refused :ingress-shape nil)))
