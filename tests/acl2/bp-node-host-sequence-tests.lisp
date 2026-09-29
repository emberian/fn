; Teeth for books/bp-node-host-sequence.lisp (PRF-983, PRF-984): a reachable
; positive witness per keystone asserting the complete antecedent and
; conclusion, hypothesis-removal witnesses for each hypothesis, and the
; corrupted-state witnesses, labelled.
(in-package "ACL2")
(include-book "../../books/bp-node-host-sequence")

; PRF-983, reachable positive witness: the frontier 5 recovered from the
; durable record, below the ceiling; the host reads a reservation whose
; sequence is 5 and whose frame is the successor record's octets.
(assert-event
 (let ((r (fn-bpn-host-sequence-reserve 5)))
   (and (fn-bpn-sequence-frontierp 5)
        (< 5 *fn-bpc-max-uint*)
        (equal (fn-bpn-host-sequence-reservationp r) t)
        (equal (fn-bpn-host-sequence-reservation-sequence r) 5)
        (equal (fn-bpn-host-sequence-reservation-frame r)
               (fn-bpn-sequence-record-frame (fn-bpn-sequence-record 6)))
        (fn-cbor-octet-listp (fn-bpn-host-sequence-reservation-frame r)))))

; PRF-983, hypothesis removal (the ceiling): a frontier that is not below
; the ceiling is the books' exhaustion refusal; every read of it is empty.
(assert-event
 (let ((r (fn-bpn-host-sequence-reserve *fn-bpc-max-uint*)))
   (and (fn-bpn-sequence-frontierp *fn-bpc-max-uint*)
        (not (< *fn-bpc-max-uint* *fn-bpc-max-uint*))
        (equal r '(:refused :sequence-exhausted))
        (equal (fn-bpn-host-sequence-reservationp r) nil)
        (equal (fn-bpn-host-sequence-reservation-sequence r) nil)
        (equal (fn-bpn-host-sequence-reservation-frame r) nil))))

; PRF-983, hypothesis removal (not a frontier): the host-arguments refusal,
; distinct from exhaustion, and the conclusion fails (no sequence is read).
(assert-event
 (and (not (fn-bpn-sequence-frontierp -1))
      (equal (fn-bpn-host-sequence-reserve -1) '(:refused :host-arguments))
      (not (fn-bpn-sequence-frontierp "5"))
      (equal (fn-bpn-host-sequence-reserve "5") '(:refused :host-arguments))
      (not (equal (fn-bpn-host-sequence-reservation-sequence
                   (fn-bpn-host-sequence-reserve "5"))
                  "5"))
      (equal (fn-bpn-host-sequence-reservationp '(:refused :host-arguments))
             nil)))

; PRF-984, reachable positive witness: the reservation of 5 previews the
; deployed spelling authored-5.wire, the books' name of its sequence.
(assert-event
 (let* ((r (fn-bpn-host-sequence-reserve 5))
        (name (fn-bpn-host-authored-wire-name r)))
   (and (equal (fn-bpn-host-sequence-reservationp r) t)
        (stringp name)
        (not (equal name ""))
        (equal name "authored-5.wire")
        (equal name (coerce (fn-bpn-authored-wire-name-chars
                             (fn-bpn-host-sequence-reservation-sequence r))
                            'string)))))

; PRF-984, hypothesis removal and corrupted state: a refusal, and a triple
; whose record does not carry the successor (a mutated reservation), are not
; reservations and name nothing: the host's non-empty check faults on them.
(assert-event
 (and (equal (fn-bpn-host-authored-wire-name '(:refused :sequence-exhausted))
             "")
      (not (fn-bpn-host-sequence-reservationp '(:reserved 5 (:bpn-sequence 7))))
      (equal (fn-bpn-host-authored-wire-name '(:reserved 5 (:bpn-sequence 7)))
             "")
      (equal (fn-bpn-host-authored-wire-name 5) "")))
