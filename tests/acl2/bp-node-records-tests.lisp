; Reachable FNBS sequence-frontier witnesses and teeth.
(in-package "ACL2")
(include-book "../../books/bp-node-records")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnr-zero* (fn-bpn-sequence-reserve 0))
(assert-event (fn-bpn-sequence-reservationp *bpnr-zero*))
(assert-event (equal (fn-bpn-sequence-reservation-sequence *bpnr-zero*) 0))
(assert-event (equal (fn-bpn-sequence-reservation-record *bpnr-zero*)
                     '(:bpn-sequence 1)))

; The durable frontier, rather than the caller, supplies the next send's
; sequence after a restart.
(defconst *bpnr-frame*
  (fn-bpn-sequence-record-frame (fn-bpn-sequence-reservation-record *bpnr-zero*)))
(assert-event (fn-cbor-octet-listp *bpnr-frame*))
(assert-event (equal (fn-bpn-sequence-record-unframe *bpnr-frame*)
                     '(:bpn-sequence 1)))
(assert-event (equal (fn-bpn-sequence-recover *bpnr-frame* t nil) '(:ready 1)))
(assert-event (equal (fn-bpn-sequence-reservation-sequence
                      (fn-bpn-sequence-reserve 1))
                     1))

; A fresh node is the sole case that starts at zero.  A damaged present record
; is a fault, never a silent reset that reuses sequence zero.
(assert-event (equal (fn-bpn-sequence-recover nil nil t) '(:ready 0)))
(assert-event (equal (fn-bpn-sequence-recover nil nil nil)
                     '(:fault :sequence-frontier-missing)))
(assert-event (equal (fn-bpn-sequence-recover '(1 2 3) t nil)
                     '(:fault :sequence-frontier)))

; Teeth for fn-bpn-sequence-reserve-advances-frontier's two hypotheses.
; The non-frontier value violates only the recognizer hypothesis.
(assert-event (not (fn-bpn-sequence-frontierp -1)))
(must-fail
 (assert-event
  (fn-bpn-sequence-reservationp (fn-bpn-sequence-reserve -1))))

; The frontier is well formed, but exhausted: there is no successor record.
(assert-event (fn-bpn-sequence-frontierp *fn-bpc-max-uint*))
(assert-event (equal (fn-bpn-sequence-reserve *fn-bpc-max-uint*)
                     '(:refused :sequence-exhausted)))
(must-fail
 (assert-event
  (fn-bpn-sequence-reservationp
   (fn-bpn-sequence-reserve *fn-bpc-max-uint*))))
