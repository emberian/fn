; The attachment and streaming checks of the codec seams (plan 2026-09-22
; §4.1, step T1; review 2026-09-22-bp-node-machine-2 §4, family 3).
;
; The seam books constrain `fn-record-encode', `fn-record-decode-exact',
; `fn-stmt-encode-items', `fn-stmt-decode-items-bounded' and
; `fn-stmt-decode-prefix-items-bounded'; books/codec-attach.lisp attaches the
; implementations for evaluation.  Every `assert-event' below evaluates a
; seam function THROUGH THE ATTACHMENT and compares it with the concrete
; implementation on the same vector.  These are computations, not theorems:
; ACL2 never uses an attachment in a proof, and an exact-byte fact a proof
; needs comes from the concrete codec books (for the record,
; `fn-record-schema0-golden-octets-are-the-encoding' in books/records.lisp).
; What these checks establish is that the image's attachment configuration
; -- the one books/codec-attach.lisp installs and host/native/build.lisp
; includes -- evaluates each vector exactly as the concrete codec does.
;
; The streaming check is the item stream's split: an encoded item list is
; read as a counted prefix and its residual (what checkpoint-compaction's
; header-then-body read does), and at every split point the prefix is the
; list's first K items, the residual is the encoding of the rest, and the
; residual decodes to the rest.

(in-package "ACL2")
(include-book "../../books/records-canonicality")
(include-book "../../books/statement-codec")
(include-book "../../books/codec-attach")

; -----------------------------------------------------------------------------
; The record seam, attached, against the implementation.

(defconst *cst-record*
  (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy))

(defconst *cst-record-inputs*
  (list *fn-record-schema0-golden-octets*
        '(88 4 102 110 45 114 0)                                 ; :noncanonical
        '(68 102 110 45 115 0)                                   ; :magic
        '(68 102 110 45 114 2)                                   ; :unknown-version
        '(68 102 110 45 114 0 1 2 3 65 97 64 17)                 ; :groups-limit
        '(68 102 110 45 114 0 65 97)                             ; :field-type
        (append *fn-record-schema0-golden-octets* '(0))          ; :trailing
        (take 15 *fn-record-schema0-golden-octets*)              ; :truncated
        '(68 102 110 45 101 0)                                   ; a Store event's magic
        nil))

(defun cst-record-decoders-agree (inputs)
  (declare (xargs :mode :program))
  (or (atom inputs)
      (and (equal (fn-record-decode-exact (car inputs))
                  (fn-record-decode-exact-impl (car inputs)))
           (cst-record-decoders-agree (cdr inputs)))))

(assert-event (cst-record-decoders-agree *cst-record-inputs*))

; The attached encoder writes the concrete golden octets, octet for octet.
(assert-event (equal (fn-record-encode *cst-record*)
                     *fn-record-schema0-golden-octets*))
(assert-event (equal (fn-record-encode *cst-record*)
                     (fn-record-encode-impl *cst-record*)))
(assert-event (equal (fn-record-decode-exact *fn-record-schema0-golden-octets*)
                     (list :ok *cst-record*)))

; A value that is not a record encodes to nil on both sides.
(assert-event (equal (fn-record-encode '(:not-a-record)) nil))
(assert-event (equal (fn-record-encode-impl '(:not-a-record)) nil))

; -----------------------------------------------------------------------------
; The statement item seam, attached, against the implementation.

(defconst *cst-items*
  (list '(:uint . 1)
        (cons :bytes (fn-record-string-octets "fn-s"))
        '(:uint . 4294967295)
        (cons :bytes (make-list 300 :initial-element 7))
        '(:uint . 24)))

(assert-event (fn-stmt-item-listp *cst-items*))
(assert-event (equal (fn-stmt-encode-items *cst-items*)
                     (fn-stmt-encode-items-impl *cst-items*)))
(assert-event (equal (fn-stmt-decode-items 5 (fn-stmt-encode-items *cst-items*))
                     (fn-stmt-ok *cst-items*)))
(assert-event (equal (fn-stmt-decode-items 5 (fn-stmt-encode-items *cst-items*))
                     (fn-stmt-decode-items-impl
                      5 (fn-stmt-encode-items-impl *cst-items*))))
; Too little fuel is refused on both sides, with the same error.
(assert-event (equal (fn-stmt-decode-items 4 (fn-stmt-encode-items *cst-items*))
                     (fn-stmt-decode-items-impl
                      4 (fn-stmt-encode-items-impl *cst-items*))))
(assert-event (not (fn-stmt-okp
                    (fn-stmt-decode-items 4 (fn-stmt-encode-items *cst-items*)))))

; -----------------------------------------------------------------------------
; The streaming split: at every K from 0 to the list's length, and one past
; it, the counted prefix read through the attachment agrees with the
; implementation; where K is in range it is the first K items, its residual
; is the encoding of the rest, and the residual decodes to the rest.

(defun cst-split-agrees (k items)
  (declare (xargs :mode :program))
  (let* ((octets (fn-stmt-encode-items items))
         (head (fn-stmt-decode-prefix-items-bounded
                k octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
         (head-impl (fn-stmt-decode-prefix-items-bounded-impl
                     k octets *fn-cbor-max-input* *fn-cbor-max-bytes*)))
    (and (equal head head-impl)
         (if (<= k (len items))
             (and (fn-stmt-okp head)
                  (equal (fn-stmt-value head) (take k items))
                  (equal (fn-stmt-rest head)
                         (fn-stmt-encode-items (nthcdr k items)))
                  (equal (fn-stmt-decode-items (len items) (fn-stmt-rest head))
                         (fn-stmt-ok (nthcdr k items))))
           (not (fn-stmt-okp head))))))

(defun cst-every-split-agrees (k items)
  (declare (xargs :mode :program))
  (if (zp k)
      (cst-split-agrees 0 items)
    (and (cst-split-agrees k items)
         (cst-every-split-agrees (1- k) items))))

(assert-event (cst-every-split-agrees (1+ (len *cst-items*)) *cst-items*))

; An input cut inside an item is refused by the full decoder on both
; sides: the 300-octet byte string is the fourth item, starting at octet 11,
; and the cut keeps its three-octet head and ten octets of its body; and the
; whole stream less its final octet is refused likewise.
(assert-event
 (let ((cut (take 24 (fn-stmt-encode-items *cst-items*))))
   (and (not (fn-stmt-okp (fn-stmt-decode-items 5 cut)))
        (equal (fn-stmt-decode-items 5 cut)
               (fn-stmt-decode-items-impl 5 cut)))))
(assert-event
 (let ((cut (butlast (fn-stmt-encode-items *cst-items*) 1)))
   (and (not (fn-stmt-okp (fn-stmt-decode-items 5 cut)))
        (equal (fn-stmt-decode-items 5 cut)
               (fn-stmt-decode-items-impl 5 cut)))))
