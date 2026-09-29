; The sequence-reservation boundary the native host calls: host/native/bp.lisp
; (fnn-bp-reserve-sequence, fnn-bp-authored-wire-publish), through
; host/bp-node-host.lisp, reserves the next authored sequence and reads the
; reservation by exactly these functions (lane decision-keystones-3, K4: the
; entries were :ideal in the host file with no theorem about them; here they
; are guard-verified with their keystones).  books/bp-node-records.lisp decides
; the reservation and books/bp-authored-wire.lisp its immutable name; this book
; refuses, by a name distinct from the books' own exhaustion refusal, what the
; books' functions are not defined over, and proves what the host reads.
(in-package "ACL2")
(include-book "bp-node-records")
(include-book "bp-authored-wire")

; -----------------------------------------------------------------------------
; Reserving.  The frontier is the one fn-bpn-host-sequence-frontier read out of
; the recovered durable record.  (:refused :host-arguments) is the host's
; refusal of a non-frontier; (:refused :sequence-exhausted) is the books'.

(defun fn-bpn-host-sequence-reserve (frontier)
  (declare (xargs :guard t))
  (if (fn-bpn-sequence-frontierp frontier)
      (fn-bpn-sequence-reserve frontier)
    (list :refused :host-arguments)))

(defun fn-bpn-host-sequence-reservationp (reservation)
  (declare (xargs :guard t))
  (and (fn-bpn-sequence-reservationp reservation) t))

(defun fn-bpn-host-sequence-reservation-sequence (reservation)
  (declare (xargs :guard t))
  (if (fn-bpn-sequence-reservationp reservation)
      (fn-bpn-sequence-reservation-sequence reservation)
    nil))

; The octets the host makes durable (staged, replaced, directory-barriered)
; before the reserved sequence goes on the wire: the successor record's frame.
(defun fn-bpn-host-sequence-reservation-frame (reservation)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (enable fn-bpn-sequence-reservationp
                                              fn-bpn-sequence-reservation-record)))))
  (if (fn-bpn-sequence-reservationp reservation)
      (fn-bpn-sequence-record-frame
       (fn-bpn-sequence-reservation-record reservation))
    nil))

; -----------------------------------------------------------------------------
; The immutable authored-wire name.  The preview is used only to observe the
; exact final path under the BP spool lock; the later operation carries that
; same ACL2 name (fn-bpn-authored-wire-authorize-carries-reservation).

; books/bp-authored-wire.lisp admits with guards unverified (eagerness 0).
(verify-guards fn-bpn-authored-wire-name-chars)
(verify-guards fn-bpn-authored-wire-name-for-reservation)

(defun fn-bpn-host-authored-wire-name (reservation)
  (declare (xargs :guard t))
  (let ((chars (fn-bpn-authored-wire-name-for-reservation reservation)))
    (if (character-listp chars) (coerce chars 'string) "")))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-983).  For a frontier the host recovered, the host reads a
; reservation exactly when the frontier is below the 64-bit ceiling; then the
; sequence it hands to fn-bpn-send is that frontier and the frame it makes
; durable first is the books' frame of the successor record, an octet list;
; at the ceiling the answer is the books' exhaustion refusal.  What is not a
; frontier is refused by the host-arguments name and is never a reservation.

(defthm fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling
  (let ((r (fn-bpn-host-sequence-reserve frontier)))
    (and (iff (fn-bpn-host-sequence-reservationp r)
              (and (fn-bpn-sequence-frontierp frontier)
                   (< frontier *fn-bpc-max-uint*)))
         (implies (and (fn-bpn-sequence-frontierp frontier)
                       (< frontier *fn-bpc-max-uint*))
                  (and (equal (fn-bpn-host-sequence-reservation-sequence r)
                              frontier)
                       (equal (fn-bpn-host-sequence-reservation-frame r)
                              (fn-bpn-sequence-record-frame
                               (fn-bpn-sequence-record (+ 1 frontier))))
                       (fn-cbor-octet-listp
                        (fn-bpn-host-sequence-reservation-frame r))))
         (implies (and (fn-bpn-sequence-frontierp frontier)
                       (not (< frontier *fn-bpc-max-uint*)))
                  (equal r '(:refused :sequence-exhausted)))
         (implies (not (fn-bpn-sequence-frontierp frontier))
                  (equal r '(:refused :host-arguments)))))
  :hints (("Goal"
           :in-theory (enable fn-bpn-sequence-reserve
                              fn-bpn-sequence-reservationp
                              fn-bpn-sequence-reservation-sequence
                              fn-bpn-sequence-reservation-record
                              fn-bpn-sequence-record
                              fn-bpn-sequence-recordp)
           :use (fn-bpn-sequence-frontierp-successor
                 (:instance fn-bpn-sequence-record-frame-octet-listp
                            (record (fn-bpn-sequence-record (+ 1 frontier))))))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-984).  The name the host previews is a string; for a
; reservation it is exactly the books' name of the reserved sequence and is
; not empty; it is empty exactly for what is not a reservation, so the host's
; non-empty check (fnn-bp-authored-wire-publish) faults exactly then.

(local
 (defthm fn-bpn-host-digits-rev-are-characters
   (character-listp (fn-bs-txn-natural-digits-rev n))
   :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits-rev)))))

(local
 (defthm fn-bpn-host-reverse-keeps-characters
   (implies (character-listp xs)
            (character-listp (fn-bs-txn-reverse xs)))
   :hints (("Goal" :in-theory (enable fn-bs-txn-reverse)))))

(local
 (defthm fn-bpn-host-digits-are-characters
   (character-listp (fn-bs-txn-natural-digits n))
   :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits)))))

(local
 (defthm fn-bpn-host-name-chars-are-non-empty-characters
   (and (character-listp (fn-bpn-authored-wire-name-chars sequence))
        (consp (fn-bpn-authored-wire-name-chars sequence)))
   :hints (("Goal" :in-theory (enable fn-bpn-authored-wire-name-chars)))))

(local
 (defthm fn-bpn-host-non-empty-characters-coerce-to-a-non-empty-string
   (implies (and (character-listp chars) (consp chars))
            (not (equal (coerce chars 'string) "")))
   :hints (("Goal" :use ((:instance coerce-inverse-1 (x chars)))))))

(defthm fn-bpn-host-authored-wire-name-names-the-reserved-sequence
  (and (stringp (fn-bpn-host-authored-wire-name reservation))
       (iff (equal (fn-bpn-host-authored-wire-name reservation) "")
            (not (fn-bpn-host-sequence-reservationp reservation)))
       (implies (fn-bpn-host-sequence-reservationp reservation)
                (equal (fn-bpn-host-authored-wire-name reservation)
                       (coerce (fn-bpn-authored-wire-name-chars
                                (fn-bpn-host-sequence-reservation-sequence
                                 reservation))
                               'string))))
  :hints (("Goal"
           :in-theory (enable fn-bpn-authored-wire-name-for-reservation)
           :use ((:instance
                  fn-bpn-host-non-empty-characters-coerce-to-a-non-empty-string
                  (chars (fn-bpn-authored-wire-name-chars
                          (fn-bpn-sequence-reservation-sequence reservation))))))))
