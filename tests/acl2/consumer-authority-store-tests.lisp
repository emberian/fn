; Actual private authority codec routes through Store/concrete carried readers.
; No foreign BP authorization or native activation follows from recognition.
(in-package "ACL2")
(include-book "../../books/store-events-carried")
(include-book "../../books/records-concrete")

(defconst *cast-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(assert-event
 (and (fn-cac-eventp *cast-event*) (fn-store-event-p *cast-event*)
      (fn-wire-event-p *cast-event*)
      (eq (fn-evc-class-by-shape *cast-event*) :authority)
      (not (eq (fn-evc-class-by-shape *cast-event*) :topic))
      (fn-evc-authorityp *cast-event*)
      (equal (fn-evc-sequence *cast-event*) 0)
      (equal (fn-evc-txid *cast-event*) 1)
      (equal (fn-evc-generation *cast-event*) 0)
      (fn-rcon-wire-event-p *cast-event*)
      (equal (fn-rcon-wire-event-sequence *cast-event*) 0)
      (equal (fn-rcon-wire-event-txid *cast-event*) 1)
      (equal (fn-rcon-wire-event-generation *cast-event*) 0)
      (equal (fn-rcon-store-event-encode *cast-event*) (fn-cac-encode *cast-event*))
      (equal (fn-store-event-decode-exact (fn-rcon-store-event-encode *cast-event*))
             (list :ok *cast-event*))
      (equal (fn-rcon-cpe-projection-step nil *cast-event* 0)
             '(:refused :authority-interpreter-required))))

; Carried shape needs recognition: a private tag with invalid coordinates
; still has that shape, but is neither a Store event nor wire authority.
(defconst *cast-bad* '(:consumer-authority :wrong 1 0 (:authority-begin (65) 0 1 7)))
(assert-event
 (and (not (fn-store-event-p *cast-bad*)) (not (fn-cac-eventp *cast-bad*))
      (eq (fn-evc-class-by-shape *cast-bad*) :authority)
      (equal (fn-evc-field-by-shape 0 *cast-bad*) :wrong)
      (null (fn-store-event-sequence *cast-bad*))))
