; Teeth of books/bp-listener-set.lisp: a relay's two boundaries on two
; ports (the four-node mission's X: its A-facing and its dtn7-facing
; boundary), and a port two boundaries share.
(in-package "ACL2")
(include-book "../../books/bp-listener-set")
(include-book "std/testing/must-fail" :dir :system)

(defun bpls-boundary (name eid port)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-cfg-row-make name "path-identity"
                         (string-append name ".example.invalid") 0)
        (fn-cfg-row-make name "auth-principal" "bp-only-no-nntp-principal" 0)
        (fn-cfg-row-make name "transport-bp" eid 0)
        (fn-cfg-row-make name "bp-trust" "network" 0)
        (fn-cfg-row-make name "bp-boundary-listener" "127.0.0.1" port)
        (fn-cfg-row-make name "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make name "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make name "bp-boundary-originators" "all-co-resident" 0)))

(defun bpls-cfg (rows)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cfg-make 9 (fn-cfg-value-make nil 0 nil nil nil rows nil nil nil nil)))

(defconst *bpls-a* (cons :dtn (fn-record-string-octets "//fn-a/")))
(defconst *bpls-r1* (cons :dtn (fn-record-string-octets "//dtn7-r1/")))
; X: a-boundary on 4101, r1-boundary on 4102.
(defconst *bpls-x*
  (bpls-cfg (append (bpls-boundary "a-boundary" "dtn://fn-a/" 4101)
                    (bpls-boundary "r1-boundary" "dtn://dtn7-r1/" 4102))))
; The same two boundaries on one port: neither is admissible there.
(defconst *bpls-shared*
  (bpls-cfg (append (bpls-boundary "a-boundary" "dtn://fn-a/" 4101)
                    (bpls-boundary "r1-boundary" "dtn://dtn7-r1/" 4101))))

(assert-event (fn-cfgp *bpls-x*))
(assert-event (fn-bpp-eidp *bpls-a*))
(assert-event (fn-bpp-eidp *bpls-r1*))
(assert-event (equal (fn-bpaj-listener-set *bpls-x*)
                     '((4101 . "a-boundary") (4102 . "r1-boundary"))))
(assert-event (equal (fn-bpaj-listener-ports *bpls-x*) '(4101 4102)))
(assert-event (equal (fn-bpaj-listener-ports *bpls-shared*) nil))

;; fn-bpaj-listener-session-is-admitted-under-its-row.
;; Witness (both arms, both ports): the complete antecedent and conclusion.
(assert-event (member-equal 4101 (fn-bpaj-listener-ports *bpls-x*)))
(assert-event (equal (fn-bpaj-listener-name *bpls-x* 4101) "a-boundary"))
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-x* (fn-bpaj-loopback-channel 4101) *bpls-a*)
                     (list :admitted (fn-record-string-octets "a-boundary") 9)))
(assert-event (fn-bpaj-unique-boundary-rowp
               (fn-cfg-peers (fn-cfg-value *bpls-x*)) "a-boundary"
               "transport-bp" (fn-bpaj-eid-text *bpls-a*) 0))
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-x* (fn-bpaj-loopback-channel 4102) *bpls-r1*)
                     (list :admitted (fn-record-string-octets "r1-boundary") 9)))
;; The refusal arm: A's EID announced on r1's listener is judged under r1's
;; row and refused :eid-mismatch, not :ambiguous-peer.
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-x* (fn-bpaj-loopback-channel 4102) *bpls-a*)
                     (list :refused :eid-mismatch)))
;; Hypothesis "the port is a bound listener": on the shared port (not in
;; the set) the session is :ambiguous-peer, neither conclusion arm; on a port
;; no row names, :no-trust-profile.
(must-fail (assert-event
            (member-equal 4101 (fn-bpaj-listener-ports *bpls-shared*))))
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-shared* (fn-bpaj-loopback-channel 4101) *bpls-a*)
                     (list :refused :ambiguous-peer)))
(must-fail (assert-event
            (member-equal (fn-bpaj-session-principal
                           *bpls-shared* (fn-bpaj-loopback-channel 4101) *bpls-a*)
                          (list (list :refused :eid-mismatch)
                                (list :admitted (fn-record-string-octets "a-boundary") 9)))))
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-x* (fn-bpaj-loopback-channel 4103) *bpls-a*)
                     (list :refused :no-trust-profile)))
;; Hypothesis "the announced value is an EID": a malformed one is refused
;; :channel, neither arm.
(must-fail (assert-event (fn-bpp-eidp '(:dtn 47))))
(assert-event (equal (fn-bpaj-session-principal
                      *bpls-x* (fn-bpaj-loopback-channel 4101) '(:dtn 47))
                     (list :refused :channel)))

;; fn-bpaj-admitted-session-arrives-on-a-bound-listener.
;; Witness: admitted on 4102, and 4102 is bound.
(assert-event (equal (car (fn-bpaj-session-principal
                           *bpls-x* (fn-bpaj-loopback-channel 4102) *bpls-r1*))
                     :admitted))
(assert-event (member-equal 4102 (fn-bpaj-listener-ports *bpls-x*)))
;; Hypothesis "admitted": a refused session on an unbound port.
(must-fail (assert-event (equal (car (fn-bpaj-session-principal
                                      *bpls-shared* (fn-bpaj-loopback-channel 4101)
                                      *bpls-a*))
                                :admitted)))
(must-fail (assert-event (member-equal 4101 (fn-bpaj-listener-ports *bpls-shared*))))
;; Hypothesis "a positive port": a listener row on port 0 admits a session
;; the kernel can never observe (it asks for an ephemeral port), and the set
;; does not bind it.
(defconst *bpls-zero* (bpls-cfg (bpls-boundary "a-boundary" "dtn://fn-a/" 0)))
(assert-event (equal (car (fn-bpaj-session-principal
                           *bpls-zero* (fn-bpaj-loopback-channel 0) *bpls-a*))
                     :admitted))
(must-fail (assert-event (posp 0)))
(must-fail (assert-event (member-equal 0 (fn-bpaj-listener-ports *bpls-zero*))))

;; fn-bpaj-listener-ports-are-distinct: a duplicated listener row binds once.
(defconst *bpls-dup*
  (bpls-cfg (append (bpls-boundary "a-boundary" "dtn://fn-a/" 4101)
                    (list (fn-cfg-row-make "a-boundary" "bp-boundary-listener"
                                           "127.0.0.1" 4101)))))
(assert-event (no-duplicatesp-equal (fn-bpaj-listener-ports *bpls-dup*)))
