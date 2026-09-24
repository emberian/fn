; The native BP command's exact mixed article/transport result policy.
(in-package "ACL2")
(include-book "../../host/bp-node-host")
(include-book "../../books/codec-attach")

; Reachable mixed evidence: one complete article was refused while the TCPCL
; session ended uncertain.  The process result is uncertain, not refused.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 1 0 :uncertain) :uncertain))

; Each domain can independently raise the run result, while NIL is the native
; command's no-adverse-operational-evidence value.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 0 1 :accepted) :uncertain))
(assert-event
 (equal (fn-bpn-host-run-outcome 0 1 0 :accepted) :refused))
(assert-event
 (equal (fn-bpn-host-run-outcome 1 0 0 nil) :accepted))

; Invalid host evidence fails closed.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 -1 0 :accepted) :uncertain))

; `bp send` RETRY: a durable authored wire is re-offered with its own
; identity, and only when ACL2 finds it is this node's bundle for this ADU to
; this peer under its sequence's authored-wire name.
(defun bpnh-test-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (atom chars) nil
    (cons (char-code (car chars)) (bpnh-test-octets (cdr chars)))))

(defconst *bpnh-test-config*
  (fn-bpn-host-config
   (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://fn-a/" 'list)))
   3600000 2 32 1048576))
(defconst *bpnh-test-peer*
  (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://dtn7d/incoming" 'list))))
(defconst *bpnh-test-adu* (bpnh-test-octets (coerce "fn-a article" 'list)))
(defconst *bpnh-test-wire*
  (fn-bpn-host-send *bpnh-test-config* *bpnh-test-peer* *bpnh-test-adu* 7
                    (fn-bpn-host-observation 5 812345678 0 t)))
(defconst *bpnh-test-wire-no-clock*
  (fn-bpn-host-send *bpnh-test-config* *bpnh-test-peer* *bpnh-test-adu* 3
                    (fn-bpn-host-observation 5 0 0 nil)))

; The reachable witness: the original creation time and sequence, from the
; wire, with a wall clock and without one (creation time 0).
(assert-event
 (equal (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                    *bpnh-test-adu* "authored-7.wire"
                                    *bpnh-test-wire*)
        '(812345678 7)))
(assert-event
 (equal (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                    *bpnh-test-adu* "authored-3.wire"
                                    *bpnh-test-wire-no-clock*)
        '(0 3)))

; Each condition refuses on its own: another ADU, another peer, another
; node, a name that is not this sequence's, and a truncated wire.
(assert-event
 (null (fn-bpn-host-authored-retry
        *bpnh-test-config* *bpnh-test-peer*
        (bpnh-test-octets (coerce "another article" 'list))
        "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry
        *bpnh-test-config*
        (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://other/incoming" 'list)))
        *bpnh-test-adu* "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry
        (fn-bpn-host-config
         (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://fn-b/" 'list)))
         3600000 2 32 1048576)
        *bpnh-test-peer* *bpnh-test-adu* "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                   *bpnh-test-adu* "authored-8.wire"
                                   *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                   *bpnh-test-adu* "authored-7.wire"
                                   (butlast *bpnh-test-wire* 1))))
