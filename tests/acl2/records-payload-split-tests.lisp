; Teeth for the record encoding's three pieces around the payload
; (books/records-seam.lisp fn-record-encode-splits-at-the-payload and the
; piece bounds; books/records-canonicality.lisp the implementation facts).
; Ground assertions evaluate through the attachment (records-attach).  The
; witness is built from the record's own field ceilings, so the head and
; tail constants are shown attained, not merely sufficient: a constant one
; octet smaller is refuted by this record.

(in-package "ACL2")
(include-book "../../books/records-canonicality")
(include-book "../../books/records-attach")

; The widest head and tail: every integer field u64, a Message-ID of
; *fn-record-max-msgid* octets, three metadata strings of
; *fn-record-max-metadata* octets, and a payload length with the u32 head.
(defconst *rpst-u64* *fn-cbor-max-uint64*)
(defconst *rpst-msgid*
  (concatenate 'string "<"
               (coerce (make-list (- *fn-record-max-msgid* 2) :initial-element #\a) 'string)
               ">"))
(defconst *rpst-meta*
  (coerce (make-list *fn-record-max-metadata* :initial-element #\m) 'string))
(defconst *rpst-long-group*
  (coerce (make-list *fn-record-max-group-name* :initial-element #\g) 'string))
(defconst *rpst-payload* (make-list 65536 :initial-element 65))
(defconst *rpst-record*
  (fn-record-make *rpst-u64* *rpst-u64* *rpst-u64* *rpst-msgid* *rpst-payload*
                  (list "fn.test" *rpst-long-group*)
                  *rpst-meta* *rpst-meta* *rpst-meta* *rpst-u64* *rpst-u64*))

(assert-event (fn-record-p *rpst-record*))

; The split, on the witness, through the attached encoder.
(assert-event
 (equal (fn-record-encode *rpst-record*)
        (append (fn-record-head-octets *rpst-record*)
                (fn-record-payload *rpst-record*)
                (fn-record-groups-octets *rpst-record*)
                (fn-record-tail-octets *rpst-record*))))

; Attained: the head and the tail at their constants exactly (a 65,536-octet
; payload takes the u32 byte-string head, 5 octets).
(assert-event (equal (len (fn-record-tail-octets *rpst-record*)) *fn-record-tail-max-octets*))
(assert-event (equal (len (fn-record-head-octets *rpst-record*)) *fn-record-head-max-octets*))
(assert-event (equal *fn-record-head-max-octets* 290))
(assert-event (equal *fn-record-tail-max-octets* 795))

; The groups section at its ceiling: the count's head is 1 octet for two
; groups (the ceiling allows 3), each name's head is 1 octet for "fn.test"
; and 3 for the 256-octet name (the ceiling allows 3 each).
(assert-event (equal (len (fn-record-groups-octets *rpst-record*))
                     (+ 1 (+ 1 7) (+ 3 256))))
(assert-event (<= (len (fn-record-groups-octets *rpst-record*))
                  (fn-record-groups-octets-ceiling (fn-record-groups *rpst-record*))))

; A small record: the split holds with the narrow heads.
(defconst *rpst-small*
  (fn-record-make 1 2 3 "<s@example.invalid>" (list 1 2 3) (list "fn.test")
                  "o" "c" "r" 4 5))
(assert-event (fn-record-p *rpst-small*))
(assert-event
 (equal (fn-record-encode *rpst-small*)
        (append (fn-record-head-octets *rpst-small*) (list 1 2 3)
                (fn-record-groups-octets *rpst-small*)
                (fn-record-tail-octets *rpst-small*))))

; A non-record has no pieces.
(assert-event (and (null (fn-record-head-octets '(1 2)))
                   (null (fn-record-groups-octets '(1 2)))
                   (null (fn-record-tail-octets '(1 2)))))
