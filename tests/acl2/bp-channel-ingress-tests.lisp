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
(assert-event
 (equal (fn-bpnf-ingress-principal (caddr *bpcin-result*))
        (fn-record-string-octets "peer")))

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
(must-fail
 (assert-event
  (equal (fn-bpnf-ingress-principal
          (caddr (fn-bpaj-tcpcl-ingress-result
                  *bpat-no-trust* *bpnf-s0* *bpat-channel*
                  *bpcin-uri* 1 2)))
         (fn-record-string-octets "peer"))))

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
(must-fail
 (assert-event
  (equal (caddr (fn-bpaj-tcpcl-ingress-result
                 *bpat-cfg* *bpnf-s0* *bpat-channel*
                 (append *bpcin-uri* (make-list (+ 5 *fn-bpc-max-text*)
                                               :initial-element 65)) 1 2))
         (caddr *bpcin-result*))))
(assert-event
 (equal (fn-bpaj-tcpcl-ingress-result
         *bpat-cfg* *bpnf-s0* *bpat-channel* *bpcin-uri* -1 2)
        '(:refused :ingress-shape nil)))

;; ---------------------------------------------------------------------------
;; PRF-128 teeth: fn-bpaj-admitted-receive-event, the receive decision
;; host/native/bp-service.lisp fnn-bps-receive calls with the admission
;; answer of fnn-bps-tcpcl-admission.

; Two boundaries on one listener: the D23 policy cannot tell them apart.
(defconst *bpcin-ambiguous-cfg*
  (bpat-cfg
   (append *bpat-rows*
           (list (fn-cfg-row-make "x" "path-identity" "x.example.invalid" 0)
                 (fn-cfg-row-make "x" "auth-principal"
                                  "bp-only-no-nntp-principal" 0)
                 (fn-cfg-row-make "x" "transport-bp" "dtn://x/" 0)
                 (fn-cfg-row-make "x" "bp-trust" "network" 0)
                 (fn-cfg-row-make "x" "bp-boundary-listener" "127.0.0.1" 4556)
                 (fn-cfg-row-make "x" "bp-boundary-source" "127.0.0.1" 0)
                 (fn-cfg-row-make "x" "bp-boundary-translation" "none" 0)
                 (fn-cfg-row-make "x" "bp-boundary-originators"
                                  "all-co-resident" 0)))))
(defconst *bpcin-ambiguous*
  (fn-bpaj-tcpcl-ingress-result
   *bpcin-ambiguous-cfg* *bpnf-s0* *bpat-channel* *bpcin-uri* 1 2))
(assert-event (fn-cfgp *bpcin-ambiguous-cfg*))
(assert-event (equal (fn-bpaj-session-principal *bpcin-ambiguous-cfg*
                                                *bpat-channel* *bpat-eid*)
                     '(:refused :ambiguous-peer)))
(assert-event (equal (car *bpcin-ambiguous*) :refused))

; Reachable positive witness (keystone fn-bpaj-admitted-channel-receives-under-
; its-ingress, antecedent and conclusion): the allowlisted neighbour "peer" is
; admitted on its own listener; its bundle is :ready under the admitted
; ingress, and the foundation step takes kind-5 custody (a :persist).
(defconst *bpcin-admitted-answer*
  (fn-bpaj-admitted-receive-event *bpcin-result* *bpnf-config* *bpnf-wire*
                                  *bpnf-obs*))
(assert-event (equal (car *bpcin-result*) :admitted))
(assert-event
 (equal *bpcin-admitted-answer*
        (fn-bpnf-receive-wire-event *bpnf-config* *bpnf-wire* *bpnf-obs*
                                    (caddr *bpcin-result*))))
(assert-event (fn-bpnf-receive-wire-readyp *bpcin-admitted-answer*))
(assert-event
 (equal (fn-bpnf-ingress-principal
         (fn-bpn-nth 3 (fn-bpnf-receive-wire-event-value
                        *bpcin-admitted-answer*)))
        (fn-record-string-octets "peer")))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects
                   (fn-bpnf-step *bpnf-s0*
                                 (fn-bpnf-receive-wire-event-value
                                  *bpcin-admitted-answer*)))))
        :persist))

; Keystone fn-bpaj-refused-channel-takes-no-custody, reachable: the ambiguous
; channel's bundle is refused with the policy's reason and is not :ready.
(defconst *bpcin-ambiguous-answer*
  (fn-bpaj-admitted-receive-event *bpcin-ambiguous* *bpnf-config* *bpnf-wire*
                                  *bpnf-obs*))
(assert-event (equal *bpcin-ambiguous-answer* '(:refused :ambiguous-peer)))
(assert-event (not (fn-bpnf-receive-wire-readyp *bpcin-ambiguous-answer*)))
(assert-event
 (equal (fn-bpaj-admitted-receive-event
         (fn-bpaj-tcpcl-ingress-result *bpat-no-trust* *bpnf-s0* *bpat-channel*
                                       *bpcin-uri* 1 2)
         *bpnf-config* *bpnf-wire* *bpnf-obs*)
        '(:refused :no-trust-profile)))
; Hypothesis removal (not :admitted): an admitted channel's answer is :ready,
; so the conclusion fails without the hypothesis.
(must-fail
 (assert-event (not (fn-bpnf-receive-wire-readyp *bpcin-admitted-answer*))))
; Mutation witness, labelled: the removed rule.  The anonymous ingress the
; refused admission still stamps, handed straight to the receive boundary
; (the pre-PRF-128 host), is :ready and its step takes custody.
(assert-event
 (fn-bpnf-receive-wire-readyp
  (fn-bpnf-receive-wire-event *bpnf-config* *bpnf-wire* *bpnf-obs*
                              (caddr *bpcin-ambiguous*))))
; Hypothesis removal (admitted) for the admitted keystone: over the refused
; channel the answer is not the receive boundary's answer on its ingress.
(must-fail
 (assert-event
  (equal *bpcin-ambiguous-answer*
         (fn-bpnf-receive-wire-event *bpnf-config* *bpnf-wire* *bpnf-obs*
                                     (caddr *bpcin-ambiguous*)))))
