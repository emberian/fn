; Teeth for the record codec at its D27 ceilings (design 2026-09-25-bounds
; §2.3, packet P2).
;
; The record's byte strings are encoded and read through the CBOR bounded API
; at the record width (books/records.lisp `fn-record-item-encode',
; `fn-record-item-decode'), so an article payload above the generic entry's
; 65 535-octet item cap round-trips; the generic entry still refuses it.
; Ground assertions evaluate through the attachment (records-attach); the
; `must-fail' cases are proof attempts.

(in-package "ACL2")
(include-book "../../books/records-canonicality")
(include-book "../../books/records-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable witness above the pre-D27 widths: a 70 000-octet payload (above
; the old 32 768 payload bound and the 65 535 CBOR item cap) and a 256-octet
; group name (above the old 128), with every other field distinct.

(defconst *rct-payload* (make-list 70000 :initial-element 65))
(defconst *rct-long-group*
  (coerce (make-list *fn-record-max-group-name* :initial-element #\a) 'string))
(defconst *rct-record*
  (fn-record-make 1 2 3 "<big@example.invalid>" *rct-payload*
                  (list "fn.test" *rct-long-group*)
                  "archive-a" "content-a" "release-a" 4 841000000))

(assert-event (fn-record-p *rct-record*))

; The encoding exceeds the pre-D27 record width (65 538) and decodes back.
(assert-event (< 65538 (len (fn-record-encode *rct-record*))))
(assert-event
 (equal (fn-record-decode-exact (fn-record-encode *rct-record*))
        (list :ok *rct-record*)))

; The payload item carries the canonical u32 head (0x5a) the generic entry
; never writes, and the generic one-item decoder refuses that item.
(defconst *rct-payload-item*
  (fn-record-item-encode (cons :bytes *rct-payload*)))
(assert-event (equal (car *rct-payload-item*) 90))
(assert-event (not (fn-cbor-result-okp (fn-cbor-decode *rct-payload-item*))))
(assert-event (equal (fn-cbor-encode (cons :bytes *rct-payload*)) nil))

; Records within the old widths keep their bytes: the golden schema-0 vector
; (books/records.lisp) is unchanged.
(assert-event
 (equal (fn-record-encode
         (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy))
        *fn-record-schema0-golden-octets*))

; -----------------------------------------------------------------------------
; `fn-record-encode-length-bound' (records-seam; no hypothesis).  The
; witness is within its bound, and the bound is not the payload alone: the
; per-group and fixed terms are needed.

(assert-event
 (<= (len (fn-record-encode *rct-record*))
     (fn-record-encoded-octets-ceiling 70000 2)))
(assert-event
 (< (+ 70000 256 7) (len (fn-record-encode *rct-record*))))
(must-fail
 (thm (<= (len (fn-record-encode record))
          (len (fn-record-payload record)))))

; The ceilings compose: the worst-case record at the payload and group
; ceilings fits the u32 record width, and one more payload octet at the
; group ceiling does not.
(assert-event
 (<= (fn-record-encoded-octets-ceiling *fn-record-max-payload*
                                       *fn-record-max-groups*)
     *fn-record-max-octets*))
(assert-event
 (< *fn-record-max-octets*
    (fn-record-encoded-octets-ceiling (+ *fn-record-max-payload* 33554432)
                                      *fn-record-max-groups*)))

; -----------------------------------------------------------------------------
; `fn-record-item-stream-bytes-round-trip' (records-invariants), one case per
; hypothesis.  A non-octet item or a non-octet remainder is refused by the
; item decoder's logical octet check.

(assert-event
 (equal (fn-record-item-decode
         (append (fn-record-item-encode (cons :bytes *rct-payload*)) '(1 2)))
        (fn-cbor-ok (cons :bytes *rct-payload*) '(1 2))))
; Outside the guard, so stated as a ground theorem over the logical
; definition rather than evaluated.
(local
 (defthm rct-item-decode-refuses-a-non-octet-remainder
   (not (fn-cbor-result-okp
         (fn-record-item-decode
          (append (fn-record-item-encode (cons :bytes '(1 2))) '(300)))))
   :hints (("Goal" :in-theory (enable fn-record-item-decode
                                      fn-record-item-encode)))
   :rule-classes nil))
(must-fail
 (thm (implies (and (<= (len xs) *fn-record-max-octets*)
                    (fn-cbor-octet-listp rest))
               (equal (fn-record-item-decode
                       (append (fn-record-item-encode (cons :bytes xs)) rest))
                      (fn-cbor-ok (cons :bytes xs) rest)))))
(must-fail
 (thm (implies (and (fn-cbor-octet-listp xs)
                    (<= (len xs) *fn-record-max-octets*))
               (equal (fn-record-item-decode
                       (append (fn-record-item-encode (cons :bytes xs)) rest))
                      (fn-cbor-ok (cons :bytes xs) rest)))))
(must-fail
 (thm (implies (and (fn-cbor-octet-listp xs)
                    (fn-cbor-octet-listp rest))
               (equal (fn-record-item-decode
                       (append (fn-record-item-encode (cons :bytes xs)) rest))
                      (fn-cbor-ok (cons :bytes xs) rest)))))
