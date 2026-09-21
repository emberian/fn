; fn: the canonical whole-state encoding of a logical checkpoint (C1-10).
;
; A checkpoint value (books/checkpoint.lisp) is the seven-tuple
;   (:fn-checkpoint 1 groups capacity frontier sequence node)
; whose NODE is the exact fn-node state after replaying SEQUENCE records.
; This book gives that value one byte encoding and proves it canonical in
; both directions.  Layout, a concatenation of the records book's CBOR
; primitives (deterministic uint32 and definite byte strings):
;
;   bstr "fn-c"                             ; schema magic
;   uint 0                                  ; schema version
;   uint sequence, uint frontier, uint capacity, uint group-count
;   bstr group[0] ... bstr group[group-count - 1]
;   TREE(node)
;
; TREE is a tagged encoding of the node's value universe: nil, naturals below
; 2^32, octet-domain strings, the symbols of *fn-cpc-symbols*, non-empty octet
; lists, and conses.  Each tag is a uint item; an octet list is a bytes item
; and never a cons chain, so every value has exactly one encoding.  The
; decoder is bounded by the frame that carries it (its own magic and kind
; table are defined at the end of this book; books/frame.lisp is unchanged)
; and by a depth fuel equal to the octets it has; it parses the header and
; compares configuration, frontier bound and record-count bound before it
; parses the node, so a hostile candidate is refused before the node
; allocates.
;
; The CBOR item reader here has no per-item whole-stream preflight: the
; frame bounded the payload once, and the records book's decoder would
; re-walk the remaining stream at every item.  Every other decision is the
; records book's primitive.

(in-package "ACL2")
(include-book "checkpoint")
(include-book "records-canonicality")
(include-book "frame-invariants")
(local (include-book "arithmetic/top" :dir :system))
; The codecs cluster withdrew its vocabulary at export (2026-09-19).  These
; proofs induct with the CBOR u16/u32 byte facts, so the book re-enables
; that one bundle.  It does NOT re-enable fn-record-record-vocabulary or
; fn-record-codec-vocabulary: those open the parse result to CAR/CADR/CADDR,
; and then every -domain lemma stated in FN-RECORD-PARSE-REST vocabulary --
; this book's own FN-CPC-READ-UINT-DOMAIN among them -- stops matching.
; A form that must open a record says so in its own hints, as
; books/records.lisp does.  FN-RECORD-CANONICALITY-VOCABULARY is in the
; bundle for the same reason as the includer bundle and not for the reason
; the two record vocabularies were rejected: it holds no (:D ...) rune, so
; it opens nothing -- it is the round-trip and success lemmas these proofs
; induct with.
(local (in-theory (enable fn-codecs-includer-vocabulary
                          fn-record-canonicality-vocabulary)))

(defconst *fn-cpc-magic* '(102 110 45 99))          ; "fn-c"
(defconst *fn-cpc-schema-version* 0)
(defconst *fn-cpc-header-uints* 5)
(defconst *fn-cpc-symbols* '(t :archive :forward))
(defconst *fn-cpc-max-groups* *fn-record-max-groups*)
(defconst *fn-cpc-max-payload* *fn-frame-max-payload*)

(defconst *fn-cpc-tag-nil* 0)
(defconst *fn-cpc-tag-nat* 1)
(defconst *fn-cpc-tag-string* 2)
(defconst *fn-cpc-tag-symbol* 3)
(defconst *fn-cpc-tag-cons* 4)
(defconst *fn-cpc-tag-octets* 5)

; -----------------------------------------------------------------------------
; One CBOR item without the whole-stream preflight

(defun fn-cpc-read-item (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (not (consp octets))
      (fn-cbor-error :truncated)
    (let ((head (car octets)))
      (if (< head 32)
          (fn-cbor-decode-unsigned head (cdr octets))
        (if (and (< 63 head) (< head 96))
            (fn-cbor-decode-bytes (- head 64) (cdr octets))
          (fn-cbor-error :unsupported))))))

(defthm fn-cpc-read-item-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cpc-read-item octets)))
           (equal (append (fn-cbor-encode
                           (fn-cbor-result-value (fn-cpc-read-item octets)))
                          (fn-cbor-result-rest (fn-cpc-read-item octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-cbor-unsigned-reencode-prefix
                            (additional (car octets)) (tail (cdr octets)))
                 (:instance fn-cbor-bytes-reencode-prefix
                            (additional (- (car octets) 64))
                            (tail (cdr octets))))
           :in-theory (disable fn-cbor-decode-unsigned fn-cbor-decode-bytes
                               fn-cbor-encode))))

(local
 (defthm fn-cpc-nthcdr-len-bound
   (<= (len (nthcdr n xs)) (len xs))
   :rule-classes :linear))

; The three length facts below are stated on the opened result shape
; (car = :ok, caddr = rest), which is what the goals show once the result
; accessors are enabled.
(local
 (defthm fn-cpc-decode-argument-rest-len
   (implies (equal (car (fn-cbor-decode-argument additional xs)) :ok)
            (<= (len (car (cdr (cdr (fn-cbor-decode-argument additional xs)))))
                (len xs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-decode-argument fn-cbor-ok
                                      fn-cbor-error)))))

(local
 (defthm fn-cpc-decode-unsigned-rest-len
   (implies (equal (car (fn-cbor-decode-unsigned additional tail)) :ok)
            (<= (len (car (cdr (cdr (fn-cbor-decode-unsigned additional tail)))))
                (len tail)))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cbor-decode-unsigned fn-cbor-ok
                             fn-cbor-error fn-cbor-result-okp
                             fn-cbor-result-value fn-cbor-result-rest)
                            (fn-cbor-decode-argument
                             fn-cbor-canonical-argumentp))))))

(local
 (defthm fn-cpc-decode-bytes-rest-len
   (implies (equal (car (fn-cbor-decode-bytes additional tail)) :ok)
            (<= (len (car (cdr (cdr (fn-cbor-decode-bytes additional tail)))))
                (len tail)))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cbor-decode-bytes fn-cbor-ok
                             fn-cbor-error fn-cbor-result-okp
                             fn-cbor-result-value fn-cbor-result-rest)
                            (fn-cbor-decode-argument
                             fn-cbor-canonical-argumentp
                             take nthcdr))))))

(defthm fn-cpc-read-item-shrinks
  (implies (fn-cbor-result-okp (fn-cpc-read-item octets))
           (< (len (fn-cbor-result-rest (fn-cpc-read-item octets)))
              (len octets)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-read-item fn-cbor-error
                            fn-cbor-result-okp fn-cbor-result-rest)
                           (fn-cbor-decode-unsigned
                            fn-cbor-decode-bytes)))))

(defthm fn-cpc-read-item-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-cpc-read-item octets)))
           (and (fn-cbor-valuep (fn-cbor-result-value (fn-cpc-read-item octets)))
                (fn-cbor-octet-listp
                 (fn-cbor-result-rest (fn-cpc-read-item octets)))
                (< (len (fn-cbor-result-rest (fn-cpc-read-item octets)))
                   (len octets))))
  :hints (("Goal"
           :use ((:instance fn-record-cbor-decode-unsigned-success-domain
                            (additional (car octets)) (tail (cdr octets)))
                 (:instance fn-record-cbor-decode-bytes-success-domain
                            (additional (- (car octets) 64))
                            (tail (cdr octets)))
                 fn-cpc-read-item-shrinks)
           :in-theory (e/d (fn-cpc-read-item fn-cbor-valuep fn-cbor-error
                            fn-cbor-result-okp)
                           (fn-cbor-decode-unsigned fn-cbor-decode-bytes
                            fn-cbor-result-value fn-cbor-result-rest
                            fn-cpc-read-item-shrinks)))))

(defun fn-cpc-read-uint (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((item (fn-cpc-read-item octets)))
    (if (not (fn-cbor-result-okp item))
        (fn-record-parse-error (fn-frame-item 1 item))
      (let ((value (fn-cbor-result-value item)))
        (if (and (consp value) (equal (car value) :uint))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest item))
          (fn-record-parse-error :field-type))))))

(defun fn-cpc-read-bytes (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((item (fn-cpc-read-item octets)))
    (if (not (fn-cbor-result-okp item))
        (fn-record-parse-error (fn-frame-item 1 item))
      (let ((value (fn-cbor-result-value item)))
        (if (and (consp value) (equal (car value) :bytes))
            (fn-record-parse-ok (cdr value) (fn-cbor-result-rest item))
          (fn-record-parse-error :field-type))))))

(local (in-theory (disable fn-cpc-read-item)))

(defthm fn-cpc-read-uint-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-uint octets)))
           (and (natp (fn-record-parse-value (fn-cpc-read-uint octets)))
                (<= (fn-record-parse-value (fn-cpc-read-uint octets))
                    *fn-cbor-max-uint*)
                (fn-cbor-octet-listp
                 (fn-record-parse-rest (fn-cpc-read-uint octets)))
                (< (len (fn-record-parse-rest (fn-cpc-read-uint octets)))
                   (len octets))))
  :hints (("Goal" :use fn-cpc-read-item-domain
           :in-theory (e/d (fn-cbor-valuep) (fn-cpc-read-item-domain)))))

(defthm fn-cpc-read-bytes-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-bytes octets)))
           (and (fn-cbor-octet-listp
                 (fn-record-parse-value (fn-cpc-read-bytes octets)))
                (<= (len (fn-record-parse-value (fn-cpc-read-bytes octets)))
                    *fn-cbor-max-bytes*)
                (fn-cbor-octet-listp
                 (fn-record-parse-rest (fn-cpc-read-bytes octets)))
                (< (len (fn-record-parse-rest (fn-cpc-read-bytes octets)))
                   (len octets))))
  :hints (("Goal" :use fn-cpc-read-item-domain
           :in-theory (e/d (fn-cbor-valuep) (fn-cpc-read-item-domain)))))

(local
 (defthm fn-cpc-uint-value-reassembles
   (implies (and (consp v) (equal (car v) :uint))
            (equal (cons :uint (cdr v)) v))))

(local
 (defthm fn-cpc-bytes-value-reassembles
   (implies (and (consp v) (equal (car v) :bytes))
            (equal (cons :bytes (cdr v)) v))))

(defthm fn-cpc-read-uint-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-uint octets)))
           (equal (append (fn-cbor-encode
                           (cons :uint
                                 (fn-record-parse-value
                                  (fn-cpc-read-uint octets))))
                          (fn-record-parse-rest (fn-cpc-read-uint octets)))
                  octets))
  :hints (("Goal" :use fn-cpc-read-item-reencode
           :in-theory (disable fn-cpc-read-item-reencode fn-cbor-encode))))

(defthm fn-cpc-read-bytes-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-bytes octets)))
           (equal (append (fn-cbor-encode
                           (cons :bytes
                                 (fn-record-parse-value
                                  (fn-cpc-read-bytes octets))))
                          (fn-record-parse-rest (fn-cpc-read-bytes octets)))
                  octets))
  :hints (("Goal" :use fn-cpc-read-item-reencode
           :in-theory (disable fn-cpc-read-item-reencode fn-cbor-encode))))

; -----------------------------------------------------------------------------
; The value direction of the primitives, stated on a prefix of a stream

(local
 (defthm fn-cpc-two-shape
   (implies (and (true-listp a) (equal (len a) 2))
            (and (consp a) (consp (cdr a)) (equal (cdr (cdr a)) nil)))
   :rule-classes nil
   :hints (("Goal" :expand ((len a) (len (cdr a)) (len (cdr (cdr a))))))))

(local
 (defthm fn-cpc-four-shape
   (implies (and (true-listp a) (equal (len a) 4))
            (and (consp a) (consp (cdr a)) (consp (cdr (cdr a)))
                 (consp (cdr (cdr (cdr a))))
                 (equal (cdr (cdr (cdr (cdr a)))) nil)))
   :rule-classes nil
   :hints (("Goal" :expand ((len a) (len (cdr a)) (len (cdr (cdr a)))
                            (len (cdr (cdr (cdr a))))
                            (len (cdr (cdr (cdr (cdr a))))))))))

(local
 (defthm fn-cpc-u16-from-append
   (implies (and (true-listp a) (equal (len a) 2))
            (and (consp (append a b))
                 (consp (cdr (append a b)))
                 (equal (fn-cbor-u16-from (append a b)) (fn-cbor-u16-from a))
                 (equal (cdr (cdr (append a b))) b)))
   :hints (("Goal" :use fn-cpc-two-shape
            :in-theory (enable fn-cbor-u16-from)))))

(local
 (defthm fn-cpc-u32-from-append
   (implies (and (true-listp a) (equal (len a) 4))
            (and (consp (append a b))
                 (consp (cdr (append a b)))
                 (consp (cdr (cdr (append a b))))
                 (consp (cdr (cdr (cdr (append a b)))))
                 (equal (fn-cbor-u32-from (append a b)) (fn-cbor-u32-from a))
                 (equal (cdr (cdr (cdr (cdr (append a b))))) b)))
   :hints (("Goal" :use fn-cpc-four-shape
            :in-theory (enable fn-cbor-u32-from)))))

(local
 (defthm fn-cpc-decode-argument-of-encoding
   (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                 (natp major) (< major 8)
                 (fn-cbor-octet-listp more))
            (equal (fn-cbor-decode-argument
                    (- (car (fn-cbor-encode-argument major n)) (* 32 major))
                    (append (cdr (fn-cbor-encode-argument major n)) more))
                   (fn-cbor-ok n more)))
   :hints (("Goal"
            :cases ((< n 24) (< n 256) (< n 65536))
            :in-theory (e/d (fn-cbor-encode-argument fn-cbor-decode-argument
                             fn-cbor-ok)
                            (fn-cbor-u16-bytes fn-cbor-u32-bytes
                             fn-cbor-u16-from fn-cbor-u32-from))))))

(local
 (defthm fn-cpc-encode-argument-head-bounds
   (implies (and (natp n) (<= n *fn-cbor-max-uint*) (natp major) (< major 8))
            (and (consp (fn-cbor-encode-argument major n))
                 (natp (car (fn-cbor-encode-argument major n)))
                 (<= (* 32 major) (car (fn-cbor-encode-argument major n)))
                 (< (car (fn-cbor-encode-argument major n)) (+ 27 (* 32 major)))
                 (fn-cbor-canonical-argumentp
                  (- (car (fn-cbor-encode-argument major n)) (* 32 major)) n)))
   :rule-classes
   (:rewrite
    (:linear :corollary
             (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                           (natp major) (< major 8))
                      (<= (* 32 major) (car (fn-cbor-encode-argument major n))))
             :trigger-terms ((car (fn-cbor-encode-argument major n))))
    (:linear :corollary
             (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                           (natp major) (< major 8))
                      (< (car (fn-cbor-encode-argument major n))
                         (+ 27 (* 32 major))))
             :trigger-terms ((car (fn-cbor-encode-argument major n)))))
   :hints (("Goal" :in-theory (e/d (fn-cbor-encode-argument
                                    fn-cbor-canonical-argumentp)
                                   (fn-cbor-u16-bytes fn-cbor-u32-bytes))))))

(defthm fn-cpc-read-uint-of-encoding
  (implies (and (natp n) (<= n *fn-cbor-max-uint*)
                (fn-cbor-octet-listp more))
           (equal (fn-cpc-read-uint (append (fn-cbor-encode (cons :uint n)) more))
                  (fn-record-parse-ok n more)))
  :hints (("Goal"
           :use ((:instance fn-cpc-decode-argument-of-encoding (major 0))
                 (:instance fn-cpc-encode-argument-head-bounds (major 0)))
           :in-theory (e/d (fn-cpc-read-item fn-cbor-encode fn-cbor-valuep
                            fn-cbor-decode-unsigned fn-cbor-ok
                            fn-cbor-result-okp fn-cbor-result-value
                            fn-cbor-result-rest)
                           (fn-cbor-encode-argument fn-cbor-decode-argument
                            fn-cbor-canonical-argumentp)))))

(local
 (defthm fn-cpc-take-of-append-exact
   (implies (true-listp xs)
            (equal (take (len xs) (append xs more)) xs))))

(local
 (defthm fn-cpc-nthcdr-of-append-exact
   (implies (true-listp xs)
            (equal (nthcdr (len xs) (append xs more)) more))))

(defthm fn-cpc-read-bytes-of-encoding
  (implies (and (fn-cbor-octet-listp xs) (<= (len xs) *fn-cbor-max-bytes*)
                (fn-cbor-octet-listp more))
           (equal (fn-cpc-read-bytes
                   (append (fn-cbor-encode (cons :bytes xs)) more))
                  (fn-record-parse-ok xs more)))
  :hints (("Goal"
           :use ((:instance fn-cpc-decode-argument-of-encoding
                            (major 2) (n (len xs)) (more (append xs more)))
                 (:instance fn-cpc-encode-argument-head-bounds
                            (major 2) (n (len xs))))
           :in-theory (e/d (fn-cpc-read-item fn-cbor-encode fn-cbor-valuep
                            fn-cbor-decode-bytes fn-cbor-ok
                            fn-cbor-result-okp fn-cbor-result-value
                            fn-cbor-result-rest
                            ; books/records.lisp, fn-record-guard-vocabulary:
                            ; the codecs cluster's own decode-domain lemmas,
                            ; cited here rather than enabled book-wide.
                            fn-record-cbor-decode-argument-success-domain
                            fn-record-cbor-decode-bytes-success-domain)
                           (fn-cbor-encode-argument fn-cbor-decode-argument
                            fn-cbor-canonical-argumentp take nthcdr))
           :do-not-induct t)))

; Tags are small immediates; ACL2 evaluates their encodings to constants, so
; both directions are also stated on a concrete head.
(defthm fn-cpc-read-uint-of-small-head
  (implies (and (natp n) (< n 24))
           (equal (fn-cpc-read-uint (cons n more))
                  (fn-record-parse-ok n more)))
  :hints (("Goal" :in-theory (e/d (fn-cpc-read-item fn-cbor-decode-unsigned
                                   fn-cbor-decode-argument
                                   fn-cbor-canonical-argumentp fn-cbor-ok
                                   fn-cbor-result-okp fn-cbor-result-value
                                   fn-cbor-result-rest)
                                  (fn-cbor-encode)))))

(defthm fn-cpc-read-uint-small-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-uint octets))
                (equal v (fn-record-parse-value (fn-cpc-read-uint octets)))
                (< v 24))
           (equal (cons v (fn-record-parse-rest (fn-cpc-read-uint octets)))
                  octets))
  :hints (("Goal"
           ; The value's natp and bound come from this book's own reader
           ; domain lemma, cited rather than re-derived: without it the
           ; proof inducted on OCTETS and generated a false goal
           ; (certify-20260920T041617Z-2375759:2347).
           :use (fn-cpc-read-uint-reencode fn-cpc-read-uint-domain)
           :in-theory (e/d (fn-cbor-encode fn-cbor-valuep fn-cbor-encode-argument)
                           (fn-cpc-read-uint-reencode fn-cpc-read-uint-domain
                            fn-cpc-read-uint))
           :do-not-induct t)))

(defthm fn-cpc-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-cpc-append-nil
  (implies (true-listp x) (equal (append x nil) x)))

; The schema magic is a constant, so its encoding is evaluated to octets
; wherever it appears; the reader is stated on those octets too.
(defthm fn-cpc-read-bytes-of-magic
  (equal (fn-cpc-read-bytes (cons 68 (cons 102 (cons 110 (cons 45 (cons 99 more))))))
         (fn-record-parse-ok *fn-cpc-magic* more))
  :hints (("Goal" :in-theory (e/d (fn-cpc-read-item fn-cbor-decode-bytes
                                   fn-cbor-decode-argument
                                   fn-cbor-canonical-argumentp fn-cbor-ok
                                   fn-cbor-result-okp fn-cbor-result-value
                                   fn-cbor-result-rest)
                                  (fn-cbor-encode)))))

(local
 (defthm fn-cpc-encode-argument-octets
   (implies (and (natp major) (< major 8) (natp n) (<= n *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-cbor-encode-argument major n)))
   :hints (("Goal" :cases ((< n 24) (< n 256) (< n 65536))
            :in-theory (e/d (fn-cbor-encode-argument)
                            (fn-cbor-u16-bytes fn-cbor-u32-bytes))))))

(defthm fn-cpc-encode-value-octets
  (implies (fn-cbor-valuep v)
           (fn-cbor-octet-listp (fn-cbor-encode v)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-encode fn-cbor-valuep)
                                  (fn-cbor-encode-argument)))))

(defthm fn-cpc-encode-value-true-listp
  (true-listp (fn-cbor-encode v))
  :hints (("Goal" :in-theory (e/d (fn-cbor-encode fn-cbor-encode-argument)
                                  (fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

; The encoder's definition is closed from here; its executable counterpart
; stays so that the constant tags and the schema magic evaluate.
(local (in-theory (disable fn-cpc-read-uint fn-cpc-read-bytes
                           (:definition fn-cbor-encode))))

; -----------------------------------------------------------------------------
; The node value universe and its tree codec

(defun fn-cpc-stringp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (fn-cbor-octet-listp (fn-record-string-octets x))
       (<= (len (fn-record-string-octets x)) *fn-cbor-max-bytes*)))

(defun fn-cpc-treep (x)
  (declare (xargs :guard t))
  (cond ((null x) t)
        ((natp x) (<= x *fn-cbor-max-uint*))
        ((stringp x) (fn-cpc-stringp x))
        ((symbolp x) (if (member-equal x *fn-cpc-symbols*) t nil))
        ((consp x)
         (if (fn-cbor-octet-listp x)
             (<= (len x) *fn-cbor-max-bytes*)
           (and (fn-cpc-treep (car x)) (fn-cpc-treep (cdr x)))))
        (t nil)))

(defun fn-cpc-depth (x)
  (declare (xargs :guard t))
  (if (and (consp x) (not (fn-cbor-octet-listp x)))
      (+ 1 (max (fn-cpc-depth (car x)) (fn-cpc-depth (cdr x))))
    1))

(defun fn-cpc-encode-tree (x)
  (declare (xargs :guard t))
  (cond ((null x) (fn-cbor-encode (cons :uint *fn-cpc-tag-nil*)))
        ((natp x) (append (fn-cbor-encode (cons :uint *fn-cpc-tag-nat*))
                          (fn-cbor-encode (cons :uint x))))
        ((stringp x) (append (fn-cbor-encode (cons :uint *fn-cpc-tag-string*))
                             (fn-cbor-encode
                              (cons :bytes (fn-record-string-octets x)))))
        ((symbolp x) (append (fn-cbor-encode (cons :uint *fn-cpc-tag-symbol*))
                             (fn-cbor-encode
                              (cons :uint (fn-frame-enum-index
                                           x *fn-cpc-symbols*)))))
        ((fn-cbor-octet-listp x)
         (append (fn-cbor-encode (cons :uint *fn-cpc-tag-octets*))
                 (fn-cbor-encode (cons :bytes x))))
        ; The recursion is guarded by CONSP.  A T clause here is not
        ; admissible: a character has ACL2-COUNT 0 and is none of the
        ; cases above, so the measure conjecture fails on it.  Nothing
        ; outside FN-CPC-TREEP has an encoding, which is what
        ; FN-CPC-ENCODABLEP already says, so the residue encodes to no
        ; octets; no keystone statement moves, since each carries
        ; FN-CPC-TREEP or FN-CPC-ENCODABLEP.
        ((consp x)
         (append (fn-cbor-encode (cons :uint *fn-cpc-tag-cons*))
                 (fn-cpc-encode-tree (car x))
                 (fn-cpc-encode-tree (cdr x))))
        (t nil)))

; The first item of a stream is the tag of an octet list (nil or bytes).
(defun fn-cpc-octet-list-tagp (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((tag (fn-cpc-read-uint octets)))
    (and (fn-record-parse-okp tag)
         (or (equal (fn-record-parse-value tag) *fn-cpc-tag-nil*)
             (equal (fn-record-parse-value tag) *fn-cpc-tag-octets*)))))

(defun fn-cpc-decode-tree (octets fuel)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (natp fuel))
                  :measure (nfix fuel)
                  :verify-guards nil))
  (if (zp fuel)
      (fn-record-parse-error :depth)
    (let ((tag (fn-cpc-read-uint octets)))
      (if (not (fn-record-parse-okp tag))
          tag
        (let ((code (fn-record-parse-value tag))
              (rest (fn-record-parse-rest tag)))
          (cond
           ((equal code *fn-cpc-tag-nil*) (fn-record-parse-ok nil rest))
           ((equal code *fn-cpc-tag-nat*) (fn-cpc-read-uint rest))
           ((equal code *fn-cpc-tag-string*)
            (let ((text (fn-cpc-read-bytes rest)))
              (if (not (fn-record-parse-okp text))
                  text
                (fn-record-parse-ok
                 (fn-record-octets-string (fn-record-parse-value text))
                 (fn-record-parse-rest text)))))
           ((equal code *fn-cpc-tag-symbol*)
            (let ((index (fn-cpc-read-uint rest)))
              (if (not (fn-record-parse-okp index))
                  index
                (let ((i (fn-record-parse-value index)))
                  (if (or (not (posp i)) (< (len *fn-cpc-symbols*) i))
                      (fn-record-parse-error :symbol)
                    (fn-record-parse-ok (fn-frame-item (- i 1) *fn-cpc-symbols*)
                                        (fn-record-parse-rest index)))))))
           ((equal code *fn-cpc-tag-octets*)
            (let ((bytes (fn-cpc-read-bytes rest)))
              (if (not (fn-record-parse-okp bytes))
                  bytes
                (if (not (consp (fn-record-parse-value bytes)))
                    (fn-record-parse-error :noncanonical)
                  bytes))))
           ((equal code *fn-cpc-tag-cons*)
            (let ((head (fn-cpc-decode-tree rest (- fuel 1))))
              (if (not (fn-record-parse-okp head))
                  head
                (let ((tail (fn-cpc-decode-tree (fn-record-parse-rest head)
                                                (- fuel 1))))
                  (if (not (fn-record-parse-okp tail))
                      tail
                    ; A cons whose car is an octet and whose cdr is an octet
                    ; list has a bytes encoding; the cons form is refused.
                    (if (and (fn-cbor-octetp (fn-record-parse-value head))
                             (fn-cpc-octet-list-tagp
                              (fn-record-parse-rest head)))
                        (fn-record-parse-error :noncanonical)
                      (fn-record-parse-ok
                       (cons (fn-record-parse-value head)
                             (fn-record-parse-value tail))
                       (fn-record-parse-rest tail))))))))
           (t (fn-record-parse-error :tag))))))))

(defthm fn-cpc-decode-tree-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-decode-tree octets fuel)))
           (fn-cbor-octet-listp
            (fn-record-parse-rest (fn-cpc-decode-tree octets fuel))))
  :hints (("Goal" :induct (fn-cpc-decode-tree octets fuel))))

(verify-guards fn-cpc-decode-tree)

; -- string and symbol facts ---------------------------------------------------

(local
 (defthm fn-cpc-octets-chars-of-string-octets-aux
   (implies (character-listp chars)
            (equal (fn-record-octets-chars (fn-record-string-octets-aux chars))
                   chars))))

(defthm fn-cpc-octets-string-of-string-octets
  (implies (and (stringp x)
                (fn-cbor-octet-listp (fn-record-string-octets x)))
           (equal (fn-record-octets-string (fn-record-string-octets x)) x))
  :hints (("Goal" :in-theory (enable fn-record-octets-string
                                     fn-record-string-octets))))

(defthm fn-cpc-decoded-string-is-string
  (implies (fn-cbor-octet-listp octets)
           (and (stringp (fn-record-octets-string octets))
                (equal (fn-record-string-octets (fn-record-octets-string octets))
                       octets)))
  ; The second conjunct is the canonicality book's own round trip
  ; (fn-record-string-octets-of-octets-string, books/records-canonicality.lisp).
  ; It is cited by :use, not enabled: enabling it would leave it to match a
  ; goal in which FN-RECORD-OCTETS-STRING has already opened to COERCE.
  :hints (("Goal"
           :use fn-record-string-octets-of-octets-string
           :in-theory (e/d (fn-record-octets-string)
                           (fn-record-string-octets-of-octets-string)))))

(defthm fn-cpc-symbol-index-in-range
  (implies (member-equal x *fn-cpc-symbols*)
           (and (posp (fn-frame-enum-index x *fn-cpc-symbols*))
                (<= (fn-frame-enum-index x *fn-cpc-symbols*)
                    (len *fn-cpc-symbols*))))
  :hints (("Goal" :in-theory (enable fn-frame-enum-index))))

(defthm fn-cpc-symbol-item-is-symbol
  (implies (and (posp i) (<= i (len *fn-cpc-symbols*)))
           (and (member-equal (fn-frame-item (- i 1) *fn-cpc-symbols*)
                              *fn-cpc-symbols*)
                (symbolp (fn-frame-item (- i 1) *fn-cpc-symbols*))
                (fn-frame-item (- i 1) *fn-cpc-symbols*)))
  ; The table has three entries and I is symbolic, so FN-FRAME-ITEM cannot
  ; unwind; the three cases make each application a constant.  Without them
  ; the proof reverts to an induction it cannot finish.
  :hints (("Goal" :in-theory (enable fn-frame-item)
           :cases ((equal i 1) (equal i 2) (equal i 3)))))

(defthm fn-cpc-enum-index-of-symbol-item
  (implies (and (posp i) (<= i (len *fn-cpc-symbols*)))
           (equal (fn-frame-enum-index
                   (fn-frame-item (- i 1) *fn-cpc-symbols*) *fn-cpc-symbols*)
                  i))
  :hints (("Goal" :use ((:instance fn-frame-enum-index-of-item
                                   (keys *fn-cpc-symbols*) (n (- i 1))))
           :cases ((equal i 1) (equal i 2) (equal i 3)))))

; -- shape of encodings ----------------------------------------------------------

(defthm fn-cpc-encode-tree-octets
  (implies (fn-cpc-treep x)
           (fn-cbor-octet-listp (fn-cpc-encode-tree x)))
  :hints (("Goal" :induct (fn-cpc-encode-tree x)
           :in-theory (enable fn-cbor-encode fn-cbor-valuep))))

(defthm fn-cpc-encode-tree-true-listp
  (true-listp (fn-cpc-encode-tree x))
  :hints (("Goal" :in-theory (enable fn-cbor-encode))))

(local
 (defthm fn-cpc-encoding-nonempty
   (implies (and (natp n) (<= n *fn-cbor-max-uint*))
            (consp (fn-cbor-encode (cons :uint n))))
   :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-valuep
                                      fn-cbor-encode-argument)))))

(defthm fn-cpc-depth-below-encoding
  (implies (fn-cpc-treep x)
           (<= (fn-cpc-depth x) (len (fn-cpc-encode-tree x))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cpc-encode-tree x))))

(defthm fn-cpc-depth-positive
  (<= 1 (fn-cpc-depth x))
  :rule-classes :linear)

; -- the tag of an encoding ------------------------------------------------------

(defthm fn-cpc-octet-list-tagp-of-encoding
  (implies (and (fn-cpc-treep x) (fn-cbor-octet-listp more))
           (iff (fn-cpc-octet-list-tagp (append (fn-cpc-encode-tree x) more))
                (fn-cbor-octet-listp x)))
  :hints (("Goal" :in-theory (enable fn-cpc-octet-list-tagp)
           :do-not-induct t
           :expand ((fn-cpc-encode-tree x) (fn-cpc-treep x)))))

; -- KEYSTONE (value direction): an encoded tree decodes back, on a stream -------

; The stream after a subtree changes in the induction: the car is decoded
; against the cdr's encoding plus the remainder, so the scheme carries MORE.
(local
 (defun fn-cpc-tree-induct (x fuel more)
   (if (and (consp x) (not (fn-cbor-octet-listp x)))
       (list (fn-cpc-tree-induct (car x) (- fuel 1)
                                 (append (fn-cpc-encode-tree (cdr x)) more))
             (fn-cpc-tree-induct (cdr x) (- fuel 1) more))
     (list x fuel more))))

; The cons branch of the decoder refuses a head that is an octet whose tail
; is an octet list, because such a pair has a bytes encoding.  Enabling
; FN-CBOR-OCTETP for the form does not close it: the definition opens into
; (<= X 255) on a symbolic head and the induction survives into Subgoal
; *1/1.14' with (< 255 (car x)) as a live case.  The octet-ness of a decoded
; head is not something the proof has to decide: under the branch hypothesis
; (not (fn-cbor-octet-listp x)) it is REFUTED as soon as the tail is an octet
; list, which FN-CPC-OCTET-LIST-TAGP-OF-ENCODING supplies.  Stated here as
; its own rule, with the definition left closed everywhere else.
(local
 (defthm fn-cpc-car-of-non-octet-list-is-not-an-octet
   (implies (and (consp x) (not (fn-cbor-octet-listp x))
                 (fn-cbor-octet-listp (cdr x)))
            (not (fn-cbor-octetp (car x))))
   :hints (("Goal" :expand ((fn-cbor-octet-listp x))))))

(defthm fn-cpc-decode-tree-of-encoding
  (implies (and (fn-cpc-treep x)
                (fn-cbor-octet-listp more)
                (natp fuel)
                (<= (fn-cpc-depth x) fuel))
           (equal (fn-cpc-decode-tree (append (fn-cpc-encode-tree x) more) fuel)
                  (fn-record-parse-ok x more)))
  :hints (("Goal" :induct (fn-cpc-tree-induct x fuel more)
           :in-theory (e/d (fn-cpc-decode-tree)
                           (fn-cpc-octet-list-tagp fn-cbor-octetp)))))


(defthm fn-cpc-decode-tree-of-encoding-exact
  (implies (fn-cpc-treep x)
           (equal (fn-cpc-decode-tree (fn-cpc-encode-tree x)
                                      (len (fn-cpc-encode-tree x)))
                  (fn-record-parse-ok x nil)))
  :hints (("Goal" :use ((:instance fn-cpc-decode-tree-of-encoding
                                   (more nil) (fuel (len (fn-cpc-encode-tree x)))))
           :in-theory (disable fn-cpc-decode-tree-of-encoding
                               fn-cpc-decode-tree fn-cpc-encode-tree))))

; -- KEYSTONE (byte direction): an accepted tree is its own encoding ------------

; The symbol branch of the decoder returns a table item for a symbolic
; index, and the byte direction has to know that such an item is none of the
; other tags' values.  As with the octet head above, this is a fact about
; the three-entry table, not something the waterfall should decide inside
; the decoder's induction: it is stated here over the table's own index
; range, with the three cases taken once.
(local
 (defthm fn-cpc-symbol-item-is-none-of-the-other-tags
   (implies (and (posp i) (<= i (len *fn-cpc-symbols*)))
            (and (not (fn-cbor-octet-listp (fn-frame-item (- i 1) *fn-cpc-symbols*)))
                 (not (natp (fn-frame-item (- i 1) *fn-cpc-symbols*)))
                 (not (stringp (fn-frame-item (- i 1) *fn-cpc-symbols*)))))
   :hints (("Goal" :cases ((equal i 1) (equal i 2) (equal i 3))))))

; The byte direction must also know that a decoded NAT, STRING or SYMBOL is
; not an octet list -- the iff conjunct of the keystone says an octet list is
; decoded exactly under an octet-list tag.  Each is a fact about the decoded
; value's type, not about the decoder: stated over FN-CPC-READ-UINT's domain
; lemma and the two type recognizers, with FN-CBOR-OCTET-LISTP left closed in
; the keystone's own theory.
(local
 (defthm fn-cpc-read-uint-value-is-natural
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-uint octets)))
            (natp (fn-record-parse-value (fn-cpc-read-uint octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-record-parse-value (fn-cpc-read-uint octets)))))
   :hints (("Goal" :use fn-cpc-read-uint-domain
            :in-theory (disable fn-cpc-read-uint)))))

(local
 (defthm fn-cpc-read-uint-rest-is-octets-fc
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-uint octets)))
            (fn-cbor-octet-listp (fn-record-parse-rest (fn-cpc-read-uint octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-record-parse-rest (fn-cpc-read-uint octets)))))
   :hints (("Goal" :use fn-cpc-read-uint-domain
            :in-theory (disable fn-cpc-read-uint)))))

(local
 (defthm fn-cpc-natp-is-not-an-octet-list
   (implies (natp x) (not (fn-cbor-octet-listp x)))
   :hints (("Goal" :expand ((fn-cbor-octet-listp x))))))

(local
 (defthm fn-cpc-stringp-is-not-an-octet-list
   (implies (stringp x) (not (fn-cbor-octet-listp x)))
   :hints (("Goal" :expand ((fn-cbor-octet-listp x))))))

(defthm fn-cpc-decode-tree-accepted
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-decode-tree octets fuel)))
           (and (fn-cpc-treep
                 (fn-record-parse-value (fn-cpc-decode-tree octets fuel)))
                (iff (fn-cbor-octet-listp
                      (fn-record-parse-value (fn-cpc-decode-tree octets fuel)))
                     (fn-cpc-octet-list-tagp octets))
                (equal (append (fn-cpc-encode-tree
                                (fn-record-parse-value
                                 (fn-cpc-decode-tree octets fuel)))
                               (fn-record-parse-rest
                                (fn-cpc-decode-tree octets fuel)))
                       octets)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cpc-decode-tree octets fuel)
           :in-theory (enable fn-cpc-decode-tree fn-cpc-octet-list-tagp))))

(defthm fn-cpc-decode-tree-value-treep
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-decode-tree octets fuel)))
           (fn-cpc-treep (fn-record-parse-value (fn-cpc-decode-tree octets fuel))))
  :hints (("Goal" :use fn-cpc-decode-tree-accepted)))

(defthm fn-cpc-decode-tree-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-decode-tree octets fuel)))
           (equal (append (fn-cpc-encode-tree
                           (fn-record-parse-value (fn-cpc-decode-tree octets fuel)))
                          (fn-record-parse-rest (fn-cpc-decode-tree octets fuel)))
                  octets))
  :hints (("Goal" :use fn-cpc-decode-tree-accepted)))

(local (in-theory (disable fn-cpc-decode-tree fn-cpc-encode-tree fn-cpc-treep
                           fn-cpc-depth fn-cpc-octet-list-tagp)))

; -----------------------------------------------------------------------------
; Header fields: a run of uints and a run of strings

(defun fn-cpc-uint-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= (car xs) *fn-cbor-max-uint*)
           (fn-cpc-uint-listp (cdr xs)))
    (null xs)))

(defun fn-cpc-encode-uints (values)
  (declare (xargs :guard t))
  (if (consp values)
      (append (fn-cbor-encode (cons :uint (car values)))
              (fn-cpc-encode-uints (cdr values)))
    nil))

(defthm fn-cpc-encode-uints-true-listp
  (true-listp (fn-cpc-encode-uints values)))

(defthm fn-cpc-encode-uints-octets
  (implies (fn-cpc-uint-listp values)
           (fn-cbor-octet-listp (fn-cpc-encode-uints values)))
  :hints (("Goal" :in-theory (enable fn-cbor-valuep))))

(defun fn-cpc-read-uints (n octets)
  (declare (xargs :guard (and (natp n) (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (zp n)
      (fn-record-parse-ok nil octets)
    (let ((first (fn-cpc-read-uint octets)))
      (if (not (fn-record-parse-okp first))
          first
        (let ((rest (fn-cpc-read-uints (- n 1) (fn-record-parse-rest first))))
          (if (not (fn-record-parse-okp rest))
              rest
            (fn-record-parse-ok (cons (fn-record-parse-value first)
                                      (fn-record-parse-value rest))
                                (fn-record-parse-rest rest))))))))

(defthm fn-cpc-read-uints-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-uints n octets)))
           (and (fn-cpc-uint-listp
                 (fn-record-parse-value (fn-cpc-read-uints n octets)))
                (equal (len (fn-record-parse-value (fn-cpc-read-uints n octets)))
                       (nfix n))
                (fn-cbor-octet-listp
                 (fn-record-parse-rest (fn-cpc-read-uints n octets)))))
  :hints (("Goal" :induct (fn-cpc-read-uints n octets))))

(verify-guards fn-cpc-read-uints)

(defthm fn-cpc-read-uints-of-encoding
  (implies (and (fn-cpc-uint-listp values)
                (fn-cbor-octet-listp more))
           (equal (fn-cpc-read-uints (len values)
                                     (append (fn-cpc-encode-uints values) more))
                  (fn-record-parse-ok values more)))
  :hints (("Goal" :induct (fn-cpc-encode-uints values)
           :in-theory (enable fn-cpc-read-uints))))

(defthm fn-cpc-read-uints-of-encoding-count
  (implies (and (fn-cpc-uint-listp values)
                (fn-cbor-octet-listp more)
                (equal (len values) n))
           (equal (fn-cpc-read-uints n (append (fn-cpc-encode-uints values) more))
                  (fn-record-parse-ok values more))))

(defthm fn-cpc-read-uints-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-uints n octets)))
           (equal (append (fn-cpc-encode-uints
                           (fn-record-parse-value (fn-cpc-read-uints n octets)))
                          (fn-record-parse-rest (fn-cpc-read-uints n octets)))
                  octets))
  :hints (("Goal" :induct (fn-cpc-read-uints n octets))))

(defun fn-cpc-string-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cpc-stringp (car xs)) (fn-cpc-string-listp (cdr xs)))
    (null xs)))

(defun fn-cpc-encode-strings (values)
  (declare (xargs :guard t))
  (if (consp values)
      (append (fn-cbor-encode (cons :bytes (fn-record-string-octets (car values))))
              (fn-cpc-encode-strings (cdr values)))
    nil))

(defthm fn-cpc-encode-strings-true-listp
  (true-listp (fn-cpc-encode-strings values)))

(defthm fn-cpc-encode-strings-octets
  (implies (fn-cpc-string-listp values)
           (fn-cbor-octet-listp (fn-cpc-encode-strings values)))
  :hints (("Goal" :in-theory (enable fn-cbor-valuep))))

(defun fn-cpc-read-strings (n octets)
  (declare (xargs :guard (and (natp n) (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (zp n)
      (fn-record-parse-ok nil octets)
    (let ((first (fn-cpc-read-bytes octets)))
      (if (not (fn-record-parse-okp first))
          first
        (let ((rest (fn-cpc-read-strings (- n 1) (fn-record-parse-rest first))))
          (if (not (fn-record-parse-okp rest))
              rest
            (fn-record-parse-ok (cons (fn-record-octets-string
                                       (fn-record-parse-value first))
                                      (fn-record-parse-value rest))
                                (fn-record-parse-rest rest))))))))

(defthm fn-cpc-read-strings-domain
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-strings n octets)))
           (and (fn-cpc-string-listp
                 (fn-record-parse-value (fn-cpc-read-strings n octets)))
                (equal (len (fn-record-parse-value (fn-cpc-read-strings n octets)))
                       (nfix n))
                (fn-cbor-octet-listp
                 (fn-record-parse-rest (fn-cpc-read-strings n octets)))))
  :hints (("Goal" :induct (fn-cpc-read-strings n octets))))

(verify-guards fn-cpc-read-strings)

(defthm fn-cpc-read-strings-of-encoding
  (implies (and (fn-cpc-string-listp values)
                (fn-cbor-octet-listp more))
           (equal (fn-cpc-read-strings (len values)
                                       (append (fn-cpc-encode-strings values) more))
                  (fn-record-parse-ok values more)))
  :hints (("Goal" :induct (fn-cpc-encode-strings values)
           :in-theory (enable fn-cpc-read-strings))))

(defthm fn-cpc-read-strings-of-encoding-count
  (implies (and (fn-cpc-string-listp values)
                (fn-cbor-octet-listp more)
                (equal (len values) n))
           (equal (fn-cpc-read-strings n (append (fn-cpc-encode-strings values) more))
                  (fn-record-parse-ok values more))))

(defthm fn-cpc-read-strings-reencode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-record-parse-okp (fn-cpc-read-strings n octets)))
           (equal (append (fn-cpc-encode-strings
                           (fn-record-parse-value (fn-cpc-read-strings n octets)))
                          (fn-record-parse-rest (fn-cpc-read-strings n octets)))
                  octets))
  :hints (("Goal" :induct (fn-cpc-read-strings n octets))))

(defthm fn-cpc-uint-list-item
  (implies (and (fn-cpc-uint-listp xs) (natp n) (< n (len xs)))
           (and (natp (fn-frame-item n xs))
                (<= (fn-frame-item n xs) *fn-cbor-max-uint*)))
  :hints (("Goal" :in-theory (enable fn-frame-item))))

(local (in-theory (disable fn-cpc-read-uints fn-cpc-read-strings
                           fn-cpc-encode-uints fn-cpc-encode-strings)))

; -----------------------------------------------------------------------------
; The checkpoint codec

(defun fn-cpc-encodablep (x)
  (declare (xargs :guard t))
  (and (fn-checkpointp x)
       (fn-cpc-string-listp (fn-checkpoint-groups x))
       (<= (len (fn-checkpoint-groups x)) *fn-cpc-max-groups*)
       (fn-record-uint32p (fn-checkpoint-capacity x))
       (fn-record-uint32p (fn-checkpoint-sequence x))
       (fn-cpc-treep (fn-checkpoint-node x))))

(defun fn-cpc-encode-header (sequence frontier capacity groups)
  (declare (xargs :guard t))
  (append (fn-cbor-encode (cons :bytes *fn-cpc-magic*))
          (fn-cpc-encode-uints (list *fn-cpc-schema-version* sequence frontier
                                     capacity (len groups)))
          (fn-cpc-encode-strings groups)))

(defun fn-cpc-encode (x)
  (declare (xargs :guard t))
  (if (not (fn-cpc-encodablep x))
      nil
    (let ((octets (append (fn-cpc-encode-header (fn-checkpoint-sequence x)
                                                (fn-checkpoint-frontier x)
                                                (fn-checkpoint-capacity x)
                                                (fn-checkpoint-groups x))
                          (fn-cpc-encode-tree (fn-checkpoint-node x)))))
      (if (fn-cbor-at-mostp octets *fn-cpc-max-payload*) octets nil))))

(defun fn-cpc-assemble (groups capacity frontier sequence node)
  (declare (xargs :guard t))
  (list :fn-checkpoint 1 groups capacity frontier sequence node))

; The host entry point.  GROUPS and CAPACITY are the live configuration;
; MAX-FRONTIER and MAX-SEQUENCE are the observed durable allocator frontier
; and the number of durable records.  The header is compared with all four
; before the node item is parsed.
(defun fn-cpc-decode (octets groups capacity max-frontier max-sequence)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((not (fn-cbor-at-mostp octets *fn-cpc-max-payload*))
    (fn-record-parse-error :limit))
   ((not (fn-cbor-octet-listp octets))
    (fn-record-parse-error :malformed))
   (t
    (let ((magic (fn-cpc-read-bytes octets)))
      (if (not (fn-record-parse-okp magic))
          magic
        (if (not (equal (fn-record-parse-value magic) *fn-cpc-magic*))
            (fn-record-parse-error :magic)
          (let ((fields (fn-cpc-read-uints *fn-cpc-header-uints*
                                           (fn-record-parse-rest magic))))
            (if (not (fn-record-parse-okp fields))
                fields
              (let ((version (fn-frame-item 0 (fn-record-parse-value fields)))
                    (sequence (fn-frame-item 1 (fn-record-parse-value fields)))
                    (frontier (fn-frame-item 2 (fn-record-parse-value fields)))
                    (cap (fn-frame-item 3 (fn-record-parse-value fields)))
                    (count (fn-frame-item 4 (fn-record-parse-value fields))))
                (cond
                 ((not (equal version *fn-cpc-schema-version*))
                  (fn-record-parse-error :version))
                 ((not (and (natp max-sequence) (<= sequence max-sequence)))
                  (fn-record-parse-error :sequence))
                 ((not (and (natp max-frontier) (<= frontier max-frontier)))
                  (fn-record-parse-error :frontier))
                 ((not (equal cap capacity))
                  (fn-record-parse-error :configuration))
                 ((< *fn-cpc-max-groups* count)
                  (fn-record-parse-error :groups-limit))
                 (t
                  (let ((names (fn-cpc-read-strings
                                count (fn-record-parse-rest fields))))
                    (if (not (fn-record-parse-okp names))
                        names
                      (if (not (equal (fn-record-parse-value names) groups))
                          (fn-record-parse-error :configuration)
                        (let ((node (fn-cpc-decode-tree
                                     (fn-record-parse-rest names)
                                     (len (fn-record-parse-rest names)))))
                          (if (not (fn-record-parse-okp node))
                              node
                            (if (fn-record-parse-rest node)
                                (fn-record-parse-error :trailing)
                              (let ((checkpoint
                                     (fn-cpc-assemble
                                      groups capacity frontier sequence
                                      (fn-record-parse-value node))))
                                (if (not (fn-checkpointp checkpoint))
                                    (fn-record-parse-error :invalid)
                                  (list :ok checkpoint))))))))))))))))))))

; The guard of FN-CPC-DECODE reads the five header uints back with
; FN-FRAME-ITEM and compares them, so its conjecture asks for the numeric
; type of a list item -- twenty-three times, once per comparison.  That is a
; fact about FN-CPC-UINT-LISTP, not about the decoder: stated once, in the
; predicates the conjecture actually raises, so the waterfall backchains
; through FN-CPC-READ-UINTS-DOMAIN instead of opening the reader.
(local
 (defthm fn-cpc-uint-list-item-is-a-bounded-natural
   (implies (and (fn-cpc-uint-listp xs) (natp i) (< i (len xs)))
            (and (natp (fn-frame-item i xs))
                 (integerp (fn-frame-item i xs))
                 (rationalp (fn-frame-item i xs))
                 (acl2-numberp (fn-frame-item i xs))
                 (<= 0 (fn-frame-item i xs))
                 (<= (fn-frame-item i xs) *fn-cbor-max-uint*)))
   :hints (("Goal" :in-theory (enable fn-cpc-uint-listp fn-frame-item)))))

; The same fact at the term the conjecture actually raises, so the
; hypotheses it must relieve are the ones the guard already carries: the
; parse-okp of the read is literally a hypothesis there, and the octet-ness
; of its input comes from FN-CPC-READ-BYTES-DOMAIN.
(local
 (defthm fn-cpc-read-uints-item-is-a-bounded-natural
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-uints n octets))
                 (natp i) (< i (nfix n)))
            (and (natp (fn-frame-item
                        i (fn-record-parse-value (fn-cpc-read-uints n octets))))
                 (integerp (fn-frame-item
                            i (fn-record-parse-value (fn-cpc-read-uints n octets))))
                 (rationalp (fn-frame-item
                             i (fn-record-parse-value (fn-cpc-read-uints n octets))))
                 (acl2-numberp (fn-frame-item
                                i (fn-record-parse-value (fn-cpc-read-uints n octets))))
                 (<= 0 (fn-frame-item
                        i (fn-record-parse-value (fn-cpc-read-uints n octets))))
                 (<= (fn-frame-item
                      i (fn-record-parse-value (fn-cpc-read-uints n octets)))
                     *fn-cbor-max-uint*)))
   :hints (("Goal"
            :use (fn-cpc-read-uints-domain
                  (:instance fn-cpc-uint-list-item-is-a-bounded-natural
                             (xs (fn-record-parse-value
                                  (fn-cpc-read-uints n octets)))))
            :in-theory (disable fn-cpc-read-uints fn-frame-item
                                fn-cpc-read-uints-domain
                                fn-cpc-uint-list-item-is-a-bounded-natural)))))

(verify-guards fn-cpc-decode
  :hints (("Goal" :in-theory (disable fn-checkpointp fn-frame-item))))

(defun fn-cpc-result-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-cpc-result-value (x)
  (declare (xargs :guard t))
  (fn-frame-item 1 x))

(defthm fn-cpc-accepted-is-consp
  (implies (fn-cpc-result-okp
            (fn-cpc-decode octets groups capacity max-frontier max-sequence))
           (consp octets))
  :hints (("Goal" :in-theory (enable fn-cpc-read-bytes fn-cpc-read-item
                                     fn-cbor-octet-listp fn-cbor-at-mostp))))

; -- reassembly facts --------------------------------------------------------------

(defthm fn-cpc-checkpointp-reassembles
  (implies (fn-checkpointp x)
           (equal (fn-cpc-assemble (fn-checkpoint-groups x)
                                   (fn-checkpoint-capacity x)
                                   (fn-checkpoint-frontier x)
                                   (fn-checkpoint-sequence x)
                                   (fn-checkpoint-node x))
                  x))
  :hints (("Goal" :in-theory (enable fn-checkpointp fn-checkpoint-shapep
                                     fn-checkpoint-groups
                                     fn-checkpoint-capacity fn-checkpoint-frontier
                                     fn-checkpoint-sequence fn-checkpoint-node)
           :expand ((len x) (len (cdr x)) (len (cdr (cdr x)))
                    (len (cdr (cdr (cdr x)))) (len (cdr (cdr (cdr (cdr x)))))
                    (len (cdr (cdr (cdr (cdr (cdr x))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))

(defthm fn-cpc-assemble-accessors
  (and (equal (fn-checkpoint-groups (fn-cpc-assemble g c f s n)) g)
       (equal (fn-checkpoint-capacity (fn-cpc-assemble g c f s n)) c)
       (equal (fn-checkpoint-frontier (fn-cpc-assemble g c f s n)) f)
       (equal (fn-checkpoint-sequence (fn-cpc-assemble g c f s n)) s)
       (equal (fn-checkpoint-node (fn-cpc-assemble g c f s n)) n))
  :hints (("Goal" :in-theory (enable fn-checkpoint-groups fn-checkpoint-capacity
                                     fn-checkpoint-frontier fn-checkpoint-sequence
                                     fn-checkpoint-node))))

(local
 (defthm fn-cpc-five-uints-reassemble
   (implies (and (fn-cpc-uint-listp xs) (equal (len xs) 5))
            (equal (list (fn-frame-item 0 xs) (fn-frame-item 1 xs)
                         (fn-frame-item 2 xs) (fn-frame-item 3 xs)
                         (fn-frame-item 4 xs))
                   xs))
   :hints (("Goal" :in-theory (enable fn-frame-item)
            :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                     (len (cdr (cdr (cdr xs)))) (len (cdr (cdr (cdr (cdr xs)))))
                     (len (cdr (cdr (cdr (cdr (cdr xs)))))))))))

(local (in-theory (disable fn-checkpointp fn-checkpoint-groups
                           fn-checkpoint-capacity fn-checkpoint-frontier
                           fn-checkpoint-sequence fn-checkpoint-node
                           fn-cpc-assemble fn-frame-item fn-cbor-at-mostp
                           fn-cbor-octet-listp fn-record-uint32p)))

(local
 (defthm fn-cpc-uint32p-bridge
   (implies (fn-record-uint32p n) (and (natp n) (<= n *fn-cbor-max-uint*)))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

(local
 (defthm fn-cpc-uint32p-from-bounds
   (implies (and (natp n) (<= n *fn-cbor-max-uint*)) (fn-record-uint32p n))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

(local
 (defthm fn-cpc-frontier-is-uint32
   (implies (fn-checkpointp x) (fn-record-uint32p (fn-checkpoint-frontier x)))
   :hints (("Goal" :in-theory (enable fn-checkpointp)))))

(local
 (defthm fn-cpc-at-mostp-of-octets-is-len
   (implies (and (fn-cbor-octet-listp xs) (natp bound))
            (iff (fn-cbor-at-mostp xs bound) (<= (len xs) bound)))
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp fn-cbor-octet-listp)))))

(local
 (defthm fn-cpc-octet-listp-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-cpc-header-uints-are-uints
   (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                 (fn-record-uint32p capacity) (<= (len groups) *fn-cpc-max-groups*))
            (fn-cpc-uint-listp (list *fn-cpc-schema-version* sequence frontier
                                     capacity (len groups))))))

; -- KEYSTONE (value direction): the checkpoint the host encodes decodes back ------

(defthm fn-cpc-decode-of-encode
  (implies (and (fn-cpc-encodablep x)
                (fn-cpc-encode x)
                (natp max-frontier) (<= (fn-checkpoint-frontier x) max-frontier)
                (natp max-sequence) (<= (fn-checkpoint-sequence x) max-sequence))
           (equal (fn-cpc-decode (fn-cpc-encode x)
                                 (fn-checkpoint-groups x)
                                 (fn-checkpoint-capacity x)
                                 max-frontier max-sequence)
                  (list :ok x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-cpc-encode fn-cpc-encode-header
                            fn-cpc-encodablep fn-frame-item)
                           (fn-cpc-decode-tree-of-encoding))
           :use ((:instance fn-cpc-decode-tree-of-encoding-exact
                            (x (fn-checkpoint-node x)))))))

; -- KEYSTONE (byte direction): an accepted checkpoint is its own encoding ---------

; The byte direction of the whole checkpoint walks header, groups and tree
; in sequence, and every step needs its predecessor's REMAINDER to be
; octets.  Each reader's -domain lemma says so, but as a rewrite it is only
; reached by backchaining, and the remainders appear in hypotheses of the
; decoder's case split rather than in terms being rewritten.  Forward
; chaining on each reader's remainder is what carries the chain.
(local
 (defthm fn-cpc-read-bytes-rest-is-octets-fc
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-bytes octets)))
            (fn-cbor-octet-listp (fn-record-parse-rest (fn-cpc-read-bytes octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-record-parse-rest (fn-cpc-read-bytes octets)))))
   :hints (("Goal" :use fn-cpc-read-bytes-domain
            :in-theory (disable fn-cpc-read-bytes)))))
(local
 (defthm fn-cpc-read-uints-rest-is-octets-fc
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-uints n octets)))
            (fn-cbor-octet-listp (fn-record-parse-rest (fn-cpc-read-uints n octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-record-parse-rest (fn-cpc-read-uints n octets)))))
   :hints (("Goal" :use fn-cpc-read-uints-domain
            :in-theory (disable fn-cpc-read-uints)))))
(local
 (defthm fn-cpc-read-strings-rest-is-octets-fc
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-strings n octets)))
            (fn-cbor-octet-listp (fn-record-parse-rest (fn-cpc-read-strings n octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-record-parse-rest (fn-cpc-read-strings n octets)))))
   :hints (("Goal" :use fn-cpc-read-strings-domain
            :in-theory (disable fn-cpc-read-strings)))))

; The re-encoded payload must meet the same 4 MiB bound the decoder checked
; on its input.  Each reader consumes a prefix whose re-encoding is that
; prefix (the -reencode lemmas above), so the three encoded segments and the
; final remainder partition OCTETS.  Stated on LEN and cited at the two
; concrete instances: as a rewrite `(len octets)' on the left would match
; every length in the conjecture.
(local
 (defthm fn-cpc-read-uints-reencode-len
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-uints n octets)))
            (equal (+ (len (fn-cpc-encode-uints
                            (fn-record-parse-value (fn-cpc-read-uints n octets))))
                      (len (fn-record-parse-rest (fn-cpc-read-uints n octets))))
                   (len octets)))
   :rule-classes nil
   :hints (("Goal" :use fn-cpc-read-uints-reencode
            :in-theory (disable fn-cpc-read-uints-reencode)))))

(local
 (defthm fn-cpc-read-strings-reencode-len
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-record-parse-okp (fn-cpc-read-strings n octets)))
            (equal (+ (len (fn-cpc-encode-strings
                            (fn-record-parse-value (fn-cpc-read-strings n octets))))
                      (len (fn-record-parse-rest (fn-cpc-read-strings n octets))))
                   (len octets)))
   :rule-classes nil
   :hints (("Goal" :use fn-cpc-read-strings-reencode
            :in-theory (disable fn-cpc-read-strings-reencode)))))

(defthm fn-cpc-accepted-input-is-canonical
  (implies (fn-cpc-result-okp
            (fn-cpc-decode octets groups capacity max-frontier max-sequence))
           (equal (fn-cpc-encode
                   (fn-cpc-result-value
                    (fn-cpc-decode octets groups capacity max-frontier
                                   max-sequence)))
                  octets))
  ; FN-RECORD-PARSE-OKP is opened here, and only here, because the
  ; decoder's case split leaves subgoals that carry BOTH
  ; (not (fn-record-parse-okp (fn-cpc-read-bytes octets))) and
  ; (equal (car (fn-cpc-read-bytes octets)) :ok) -- vacuous, since an atom
  ; has a NIL car, but not visibly so while the recognizer is closed.
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-cpc-encode fn-cpc-encode-header
                            fn-cpc-encodablep fn-cpc-result-okp
                            fn-record-parse-okp fn-cbor-ag-car
                            fn-cpc-result-value fn-frame-item)
                           (fn-cpc-decode-tree-reencode))
           :use
           ((:instance fn-cpc-decode-tree-reencode
                       (octets
                        (fn-record-parse-rest
                         (fn-cpc-read-strings
                          (fn-frame-item
                           4 (fn-record-parse-value
                              (fn-cpc-read-uints
                               5 (fn-record-parse-rest
                                  (fn-cpc-read-bytes octets)))))
                          (fn-record-parse-rest
                           (fn-cpc-read-uints
                            5 (fn-record-parse-rest
                               (fn-cpc-read-bytes octets)))))))
                       (fuel
                        (len
                         (fn-record-parse-rest
                          (fn-cpc-read-strings
                           (fn-frame-item
                            4 (fn-record-parse-value
                               (fn-cpc-read-uints
                                5 (fn-record-parse-rest
                                   (fn-cpc-read-bytes octets)))))
                           (fn-record-parse-rest
                            (fn-cpc-read-uints
                             5 (fn-record-parse-rest
                                (fn-cpc-read-bytes octets)))))))))
            (:instance fn-cpc-five-uints-reassemble
                       (xs (fn-record-parse-value
                            (fn-cpc-read-uints
                             5 (fn-record-parse-rest
                                (fn-cpc-read-bytes octets))))))
            ; The remaining obligation is the FNCP schema magic rebuilt in
            ; front of the first reader's remainder.  This is exactly
            ; fn-cpc-read-bytes-reencode at OCTETS; under the branch
            ; hypothesis that the read value IS *fn-cpc-magic* its left side
            ; evaluates to (68 102 110 45 99) appended to that remainder.
            ; Cited at the instance (row 12b), never left to match.
            (:instance fn-cpc-read-bytes-reencode)
            ; ... and the payload bound on the re-encoding: the magic is five
            ; octets, and each of the two remaining readers consumes exactly
            ; what its encoder emits, so the segments sum to (len octets).
            (:instance fn-cpc-read-uints-reencode-len
                       (n 5)
                       (octets (fn-record-parse-rest (fn-cpc-read-bytes octets))))
            (:instance fn-cpc-read-strings-reencode-len
                       (n (fn-frame-item
                           4 (fn-record-parse-value
                              (fn-cpc-read-uints
                               5 (fn-record-parse-rest
                                  (fn-cpc-read-bytes octets))))))
                       (octets (fn-record-parse-rest
                                (fn-cpc-read-uints
                                 5 (fn-record-parse-rest
                                    (fn-cpc-read-bytes octets))))))))))

; -- hostile headers are refused before the node item is parsed --------------------
;
; Each theorem quantifies over an arbitrary TAIL in place of the node item:
; the verdict is fixed by the header alone, so nothing after it is examined.

(local
 (defthm fn-cpc-header-decodes
   (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                 (fn-record-uint32p capacity)
                 (fn-cpc-string-listp groups)
                 (<= (len groups) *fn-cpc-max-groups*)
                 (fn-cbor-octet-listp tail))
            (and (equal (fn-cpc-read-bytes
                         (append (fn-cpc-encode-header sequence frontier capacity
                                                       groups)
                                 tail))
                        (fn-record-parse-ok
                         *fn-cpc-magic*
                         (append (fn-cpc-encode-uints
                                  (list 0 sequence frontier capacity (len groups)))
                                 (append (fn-cpc-encode-strings groups) tail))))
                 (equal (fn-cpc-read-uints
                         5 (append (fn-cpc-encode-uints
                                    (list 0 sequence frontier capacity
                                          (len groups)))
                                   (append (fn-cpc-encode-strings groups) tail)))
                        (fn-record-parse-ok
                         (list 0 sequence frontier capacity (len groups))
                         (append (fn-cpc-encode-strings groups) tail)))
                 (equal (fn-cpc-read-strings
                         (len groups)
                         (append (fn-cpc-encode-strings groups) tail))
                        (fn-record-parse-ok groups tail))))
   :hints (("Goal" :in-theory (enable fn-cpc-encode-header)))))

(local
 (defthm fn-cpc-encode-header-octets
   (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                 (fn-record-uint32p capacity)
                 (fn-cpc-string-listp groups)
                 (<= (len groups) *fn-cpc-max-groups*))
            (and (fn-cbor-octet-listp
                  (fn-cpc-encode-header sequence frontier capacity groups))
                 (true-listp
                  (fn-cpc-encode-header sequence frontier capacity groups))))
   :hints (("Goal" :in-theory (enable fn-cpc-encode-header)))))

(defthm fn-cpc-decode-rejects-mismatched-capacity-before-node
  (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                (fn-record-uint32p capacity)
                (fn-cpc-string-listp groups)
                (<= (len groups) *fn-cpc-max-groups*)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-cpc-encode-header sequence frontier capacity groups)
                         tail)
                 *fn-cpc-max-payload*)
                (natp max-frontier) (<= frontier max-frontier)
                (natp max-sequence) (<= sequence max-sequence)
                (not (equal capacity expected)))
           (equal (fn-cpc-decode
                   (append (fn-cpc-encode-header sequence frontier capacity groups)
                           tail)
                   groups expected max-frontier max-sequence)
                  (fn-record-parse-error :configuration)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-frame-item) (fn-cpc-encode-header)))))

(defthm fn-cpc-decode-rejects-mismatched-groups-before-node
  (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                (fn-record-uint32p capacity)
                (fn-cpc-string-listp groups)
                (<= (len groups) *fn-cpc-max-groups*)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-cpc-encode-header sequence frontier capacity groups)
                         tail)
                 *fn-cpc-max-payload*)
                (natp max-frontier) (<= frontier max-frontier)
                (natp max-sequence) (<= sequence max-sequence)
                (not (equal groups expected)))
           (equal (fn-cpc-decode
                   (append (fn-cpc-encode-header sequence frontier capacity groups)
                           tail)
                   expected capacity max-frontier max-sequence)
                  (fn-record-parse-error :configuration)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-frame-item) (fn-cpc-encode-header)))))

(defthm fn-cpc-decode-rejects-frontier-ahead-before-node
  (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                (fn-record-uint32p capacity)
                (fn-cpc-string-listp groups)
                (<= (len groups) *fn-cpc-max-groups*)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-cpc-encode-header sequence frontier capacity groups)
                         tail)
                 *fn-cpc-max-payload*)
                (natp max-sequence) (<= sequence max-sequence)
                (natp max-frontier) (< max-frontier frontier))
           (equal (fn-cpc-decode
                   (append (fn-cpc-encode-header sequence frontier capacity groups)
                           tail)
                   groups capacity max-frontier max-sequence)
                  (fn-record-parse-error :frontier)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-frame-item) (fn-cpc-encode-header)))))

(defthm fn-cpc-decode-rejects-count-ahead-before-node
  (implies (and (fn-record-uint32p sequence) (fn-record-uint32p frontier)
                (fn-record-uint32p capacity)
                (fn-cpc-string-listp groups)
                (<= (len groups) *fn-cpc-max-groups*)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-cpc-encode-header sequence frontier capacity groups)
                         tail)
                 *fn-cpc-max-payload*)
                (natp max-sequence) (< max-sequence sequence))
           (equal (fn-cpc-decode
                   (append (fn-cpc-encode-header sequence frontier capacity groups)
                           tail)
                   groups capacity max-frontier max-sequence)
                  (fn-record-parse-error :sequence)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-decode fn-frame-item) (fn-cpc-encode-header)))))

; -----------------------------------------------------------------------------
; Binding: a decoded checkpoint that validates against a record prefix is the
; capture of that prefix

; Guard fact for the journal-interval clause below, local because natp of a
; field is not a rule any caller should carry (docs/proof-style.md s3).
(local
 (defthm fn-cpc-checkpointp-frontier-is-natural
   (implies (fn-checkpointp x) (natp (fn-checkpoint-frontier x)))
   :hints (("Goal" :in-theory (enable fn-checkpointp fn-record-uint32p)))))

; Validation replays the prefix and compares the actual result with the
; decoded value.  This is what the host's differential assertion computes.
;
; The journal-interval clause is not decoration.  FN-REPLAY carries a record's
; generation into FN-NODE-PREPARE and FN-NODE-COMPLETE without ever comparing
; it with the record's txid, so replay of a prefix whose generation field is
; corrupt returns the same node and sequence as replay of the sound prefix
; (measured: EQUAL of the two FN-REPLAY results is T on the witness in
; tests/acl2/checkpoint-codec-tests.lisp).  Without this clause the validator
; therefore accepted a prefix that FN-CHECKPOINT-CAPTURE refuses as
; (:ERROR :HISTORY), and the two owners of "is this prefix a journal" answered
; differently about the same bytes.  FN-CHECKPOINT-CAPTURE tests it as clause
; :history and FN-CHECKPOINT-RESTORE as clause :suffix; validation is the
; third member of that family and tests it here.
(defun fn-cpc-validp (checkpoint groups capacity prefix)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-checkpointp checkpoint)
       (equal groups (fn-checkpoint-groups checkpoint))
       (equal capacity (fn-checkpoint-capacity checkpoint))
       (fn-sf-record-listp prefix 0 0 (fn-checkpoint-frontier checkpoint))
       (let ((answer (fn-replay groups capacity prefix)))
         (and (fn-replay-okp answer)
              (equal (fn-replay-result-sequence answer)
                     (fn-checkpoint-sequence checkpoint))
              (equal (fn-replay-result-node answer)
                     (fn-checkpoint-node checkpoint))))))

(verify-guards fn-cpc-validp
  :hints (("Goal" :in-theory (disable fn-replay fn-replay-okp fn-checkpointp
                                      fn-sf-record-listp))))

; KEYSTONE: exact binding.  Every field of a validated checkpoint is fixed by
; the prefix: the node and sequence by replay, the configuration by the
; recognizer's binding of groups and capacity to the node, and the frontier by
; the value validated against.  So it is FN-CHECKPOINT-CAPTURE-VALUE of that
; prefix at that frontier, and nothing else.
; The journal-interval hypothesis this theorem used to carry is now a clause
; of FN-CPC-VALIDP and is deleted from the statement (deputy brief, micro
; discipline 4): with it restored as a hypothesis nothing in the test book
; could witness dropping it.
(defthm fn-cpc-valid-is-capture-value
  (implies (fn-cpc-validp checkpoint groups capacity prefix)
           (equal (fn-checkpoint-capture-value
                   (fn-checkpoint-capture groups capacity prefix
                                          (fn-checkpoint-frontier checkpoint)))
                  checkpoint))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpc-checkpointp-reassembles (x checkpoint)))
           :in-theory (e/d (fn-cpc-validp fn-checkpoint-capture
                            fn-checkpoint-capture-value fn-checkpoint-make
                            fn-checkpointp fn-cpc-assemble)
                           (fn-replay fn-replay-okp fn-replay-advance-okp
                            fn-sf-record-listp fn-node-statep
                            fn-replay-result-node fn-replay-result-sequence
                            fn-state-groups fn-retain-capacity
                            fn-node-acceptance fn-node-retention
                            fn-string-listp fn-no-duplicatesp)))))

; The refusal that the clause buys.  A prefix is a journal only if every one
; of its records binds the generation it consumed to the txid it consumed, so
; a single record whose generation does not match its txid is enough to make
; validation refuse the whole prefix, whatever checkpoint is offered against
; it and whatever configuration is offered with it.
(local
 (defthm fn-cpc-journal-generation-matches
   (implies (and (fn-sf-record-listp records sequence lower frontier)
                 (member-equal record records))
            (equal (fn-record-generation record) (fn-record-txid record)))
   :rule-classes nil))

; KEYSTONE: the validator refuses a corrupt generation binding.  RULE-CLASSES
; NIL deliberately: as a rewrite this would be a free-variable rule (RECORD
; occurs only in the hypotheses) that concludes NIL on a recognizer call, the
; shape the deputy brief names as a trap.  It is cited and witnessed, not
; applied by the rewriter.
(defthm fn-cpc-valid-refuses-generation-mismatch
  (implies (and (member-equal record prefix)
                (not (equal (fn-record-generation record)
                            (fn-record-txid record))))
           (not (fn-cpc-validp checkpoint groups capacity prefix)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cpc-journal-generation-matches
                            (records prefix) (sequence 0) (lower 0)
                            (frontier (fn-checkpoint-frontier checkpoint))))
           :in-theory (e/d (fn-cpc-validp)
                           (fn-replay fn-replay-okp fn-checkpointp
                            fn-sf-record-listp fn-record-generation
                            fn-record-txid)))))

; -----------------------------------------------------------------------------
; The frame that carries a checkpoint generation and its selection marker.
; Its magic and kind table are this book's; books/frame.lisp is not edited.

(defconst *fn-cpc-frame-magic* '(70 78 67 80))          ; FNCP
(defconst *fn-cpc-frame-kinds* '(:checkpoint :selection))
(defconst *fn-cpc-checkpoint-kind* 1)
(defconst *fn-cpc-selection-kind* 2)

(defthm fn-cpc-frame-kind-codes
  (and (equal (fn-frame-enum-index :checkpoint *fn-cpc-frame-kinds*)
              *fn-cpc-checkpoint-kind*)
       (equal (fn-frame-enum-index :selection *fn-cpc-frame-kinds*)
              *fn-cpc-selection-kind*)))

(defun fn-cpc-frame-protected (checkpoint)
  (declare (xargs :guard t :verify-guards nil))
  (let ((payload (fn-cpc-encode checkpoint)))
    (if (null payload)
        :bad
      (fn-frame-protected *fn-cpc-frame-magic* *fn-frame-version*
                          *fn-cpc-checkpoint-kind* payload))))

(defun fn-cpc-frame-encode (checkpoint digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((payload (fn-cpc-encode checkpoint)))
    (if (or (null payload) (not (fn-frame-digestp digest)))
        :bad
      (fn-frame-encode *fn-cpc-frame-magic* *fn-frame-version*
                       *fn-cpc-checkpoint-kind* payload digest))))

(defun fn-cpc-frame-seal (checkpoint)
  ; Specification form against A-CRYPTO; not executable.
  (declare (xargs :guard t :verify-guards nil))
  (let ((payload (fn-cpc-encode checkpoint)))
    (if (null payload)
        :bad
      (fn-frame-seal *fn-cpc-frame-magic* *fn-frame-version*
                     *fn-cpc-checkpoint-kind* payload))))

(defun fn-cpc-frame-decode (octets digest groups capacity max-frontier
                                   max-sequence)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-cpc-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-cpc-frame-magic*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)
                    (equal (fn-frame-result-kind frame) *fn-cpc-checkpoint-kind*)))
          (fn-frame-error :magic)
        (fn-cpc-decode (fn-frame-result-payload frame) groups capacity
                       max-frontier max-sequence)))))

(defun fn-cpc-frame-open (octets groups capacity max-frontier max-sequence)
  ; Specification form against A-CRYPTO; not executable.
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-cpc-frame-decode octets
                       (fn-frame-digest (fn-frame-protected-prefix octets))
                       groups capacity max-frontier max-sequence))

(defun fn-cpc-selection-protected (generation)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-record-uint32p generation))
      :bad
    (fn-frame-protected *fn-cpc-frame-magic* *fn-frame-version*
                        *fn-cpc-selection-kind*
                        (fn-cbor-encode (cons :uint generation)))))

(defun fn-cpc-selection-encode (generation digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-record-uint32p generation)) (not (fn-frame-digestp digest)))
      :bad
    (fn-frame-encode *fn-cpc-frame-magic* *fn-frame-version*
                     *fn-cpc-selection-kind*
                     (fn-cbor-encode (cons :uint generation)) digest)))

(defun fn-cpc-selection-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-cbor-max-input*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-cpc-frame-magic*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)
                    (equal (fn-frame-result-kind frame) *fn-cpc-selection-kind*)))
          (fn-frame-error :magic)
        (let ((item (fn-cbor-decode-exact (fn-frame-result-payload frame))))
          (if (not (fn-cbor-result-okp item))
              (fn-frame-error :selection)
            (let ((value (fn-cbor-result-value item)))
              (if (not (and (consp value) (equal (car value) :uint)))
                  (fn-frame-error :selection)
                (list :ok (cdr value))))))))))

(local
 (defthm fn-cpc-encode-octets
   (implies (fn-cpc-encode x)
            (and (fn-cbor-octet-listp (fn-cpc-encode x))
                 (<= (len (fn-cpc-encode x)) *fn-cpc-max-payload*)))
   :hints (("Goal" :in-theory (enable fn-cpc-encode fn-cpc-encode-header
                                      fn-cpc-encodablep)))))

; The two big-endian argument constructors are fixed-length lists.  Their
; definitions stay closed in the length lemma below (opening them there puts
; four floor/mod terms into an arithmetic goal that does not need them), so
; the lengths are stated once, here.
(local
 (defthm fn-cpc-u16-bytes-len
   (equal (len (fn-cbor-u16-bytes n)) 2)
   :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes)))))
(local
 (defthm fn-cpc-u32-bytes-len
   (equal (len (fn-cbor-u32-bytes n)) 4)
   :hints (("Goal" :in-theory (enable fn-cbor-u32-bytes)))))

; Every CBOR argument head is at most five octets (1 + u32).  The selection
; and frame guards ask for this bound on a symbolic major and value.
(local
 (defthm fn-cpc-encode-argument-len
   (<= (len (fn-cbor-encode-argument major n)) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode-argument)))))

(local
 (defthm fn-cpc-uint-encoding-len
   (implies (and (natp n) (<= n *fn-cbor-max-uint*))
            (<= (len (fn-cbor-encode (cons :uint n))) 5))
   :rule-classes :linear
   :hints (("Goal" :cases ((< n 24) (< n 256) (< n 65536))
            :in-theory (e/d (fn-cbor-encode fn-cbor-valuep fn-cbor-encode-argument)
                            (fn-cbor-u16-bytes fn-cbor-u32-bytes))))))

(verify-guards fn-cpc-frame-protected)
(verify-guards fn-cpc-frame-encode)
(verify-guards fn-cpc-frame-seal)
(verify-guards fn-cpc-frame-decode)
(verify-guards fn-cpc-frame-open)
(verify-guards fn-cpc-selection-protected
  :hints (("Goal" :in-theory (enable fn-record-uint32p fn-cbor-encode
                                     fn-cbor-valuep))))
(verify-guards fn-cpc-selection-encode
  :hints (("Goal" :in-theory (enable fn-record-uint32p fn-cbor-encode
                                     fn-cbor-valuep))))
(verify-guards fn-cpc-selection-decode)

(defthm fn-cpc-frame-decode-of-encode
  (implies (and (fn-cpc-encodablep x)
                (fn-cpc-encode x)
                (fn-frame-digestp digest)
                (natp max-frontier) (<= (fn-checkpoint-frontier x) max-frontier)
                (natp max-sequence) (<= (fn-checkpoint-sequence x) max-sequence))
           (equal (fn-cpc-frame-decode (fn-cpc-frame-encode x digest) digest
                                       (fn-checkpoint-groups x)
                                       (fn-checkpoint-capacity x)
                                       max-frontier max-sequence)
                  (list :ok x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpc-frame-decode fn-cpc-frame-encode
                            fn-frame-inputp fn-frame-magicp fn-frame-ok
                            fn-frame-result-okp fn-frame-result-magic
                            fn-frame-result-version fn-frame-result-kind
                            fn-frame-result-payload fn-frame-item)
                           (fn-cpc-decode fn-cpc-encode fn-frame-decode
                            fn-frame-encode)))))

(defthm fn-cpc-frame-open-of-seal
  (implies (and (fn-cpc-encodablep x)
                (fn-cpc-encode x)
                (natp max-frontier) (<= (fn-checkpoint-frontier x) max-frontier)
                (natp max-sequence) (<= (fn-checkpoint-sequence x) max-sequence))
           (equal (fn-cpc-frame-open (fn-cpc-frame-seal x)
                                     (fn-checkpoint-groups x)
                                     (fn-checkpoint-capacity x)
                                     max-frontier max-sequence)
                  (list :ok x)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-cpc-frame-magic*)
                            (version *fn-frame-version*)
                            (kind *fn-cpc-checkpoint-kind*)
                            (payload (fn-cpc-encode x))
                            (max-payload *fn-cpc-max-payload*)))
           :in-theory (e/d (fn-cpc-frame-open fn-cpc-frame-decode
                            fn-cpc-frame-seal fn-frame-open fn-frame-seal
                            fn-frame-inputp fn-frame-magicp fn-frame-ok
                            fn-frame-result-okp fn-frame-result-magic
                            fn-frame-result-version fn-frame-result-kind
                            fn-frame-result-payload fn-frame-item)
                           (fn-cpc-decode fn-cpc-encode fn-frame-decode
                            fn-frame-encode fn-frame-protected
                            fn-frame-protected-prefix fn-frame-open-of-seal)))))

; The empty payload is refused before anything else: fn-cpc-read-bytes of NIL
; is a parse error, so the frame keystone's degenerate branch is closed by
; evaluation once the decoder is open in this one fact.
(local
 (defthm fn-cpc-decode-of-nil-is-not-accepted
   (not (equal (car (fn-cpc-decode nil groups capacity max-frontier max-sequence))
               :ok))
   :hints (("Goal" :in-theory (enable fn-cpc-decode)))))

(defthm fn-cpc-frame-accepted-is-canonical
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cpc-result-okp
                 (fn-cpc-frame-decode octets digest groups capacity
                                      max-frontier max-sequence))
                (fn-frame-digestp digest))
           (equal (fn-cpc-frame-encode
                   (fn-cpc-result-value
                    (fn-cpc-frame-decode octets digest groups capacity
                                         max-frontier max-sequence))
                   digest)
                  octets))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-encode-of-decode
                            (max-payload *fn-cpc-max-payload*))
                 (:instance fn-cpc-accepted-input-is-canonical
                            (octets (fn-frame-result-payload
                                     (fn-frame-decode octets digest
                                                      *fn-cpc-max-payload*)))))
           ; FN-FRAME-RESULT-OKP is opened here for the reason row 12a
           ; opened FN-RECORD-PARSE-OKP: the case split leaves subgoals that
           ; carry BOTH (not (fn-frame-result-okp (fn-frame-decode ...))) and
           ; (equal (car (fn-frame-decode ...)) :ok), which is a contradiction
           ; the closed recognizer hides.
           :in-theory (e/d (fn-cpc-frame-decode fn-cpc-frame-encode
                            fn-frame-result-okp)
                           (fn-cpc-decode fn-cpc-encode fn-frame-decode
                            fn-frame-encode fn-cpc-accepted-input-is-canonical
                            fn-frame-encode-of-decode)))))

(defthm fn-cpc-selection-decode-of-encode
  (implies (and (fn-record-uint32p generation) (fn-frame-digestp digest))
           (equal (fn-cpc-selection-decode
                   (fn-cpc-selection-encode generation digest) digest)
                  (list :ok generation)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-encode
                            (magic *fn-cpc-frame-magic*)
                            (version *fn-frame-version*)
                            (kind *fn-cpc-selection-kind*)
                            (payload (fn-cbor-encode (cons :uint generation)))
                            (max-payload *fn-cbor-max-input*))
                 (:instance fn-cbor-uint32-round-trip (n generation)))
           :in-theory (e/d (fn-cpc-selection-decode fn-cpc-selection-encode
                            fn-frame-inputp fn-frame-magicp fn-frame-ok
                            fn-frame-result-okp fn-frame-result-magic
                            fn-frame-result-version fn-frame-result-kind
                            fn-frame-result-payload fn-frame-item
                            fn-record-uint32p fn-cbor-ok fn-cbor-result-okp
                            fn-cbor-result-value)
                           (fn-frame-decode fn-frame-encode fn-cbor-encode
                            fn-cbor-decode-exact fn-frame-decode-of-encode
                            fn-cbor-uint32-round-trip)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md s2).  Withdrawn under a name: every
; reader-domain, re-encoding, of-encoding and append fact these proofs induct
; with -- proof vocabulary, not a claim about the codec -- so a book above
; re-enables exactly this list in one line.  Withdrawn outright: the readers,
; the tree and header encoders and decoders, the encodability recognizer, the
; assembler, the whole-checkpoint codec, the validation predicate, and the
; frame and selection operations.  Enabled on include: the eleven keystones
; (the two tree directions, the two checkpoint directions, the four
; before-node rejections, exact binding, and the frame and selection round
; trips), the frame kind table, the reassembly lemmas FN-CPC-ASSEMBLE-
; ACCESSORS and FN-CPC-CHECKPOINTP-REASSEMBLES, and the two result
; projections the host dispatches on (glue over FN-FRAME-ITEM, which the
; codecs cluster keeps withdrawn).
(deftheory fn-checkpoint-codec-vocabulary
  '(fn-cpc-read-item-reencode fn-cpc-read-item-shrinks fn-cpc-read-item-domain
    fn-cpc-read-uint-domain fn-cpc-read-bytes-domain
    fn-cpc-read-uint-reencode fn-cpc-read-bytes-reencode
    fn-cpc-read-uint-of-encoding fn-cpc-read-bytes-of-encoding
    fn-cpc-read-uint-of-small-head fn-cpc-read-uint-small-reencode
    fn-cpc-append-assoc fn-cpc-append-nil fn-cpc-read-bytes-of-magic
    fn-cpc-encode-value-octets fn-cpc-encode-value-true-listp
    fn-cpc-decode-tree-rest-octets fn-cpc-octets-string-of-string-octets
    fn-cpc-decoded-string-is-string fn-cpc-symbol-index-in-range
    fn-cpc-symbol-item-is-symbol fn-cpc-enum-index-of-symbol-item
    fn-cpc-encode-tree-octets fn-cpc-encode-tree-true-listp
    fn-cpc-depth-below-encoding fn-cpc-depth-positive
    fn-cpc-octet-list-tagp-of-encoding
    fn-cpc-encode-uints-true-listp fn-cpc-encode-uints-octets
    fn-cpc-read-uints-domain fn-cpc-read-uints-of-encoding
    fn-cpc-read-uints-of-encoding-count fn-cpc-read-uints-reencode
    fn-cpc-encode-strings-true-listp fn-cpc-encode-strings-octets
    fn-cpc-read-strings-domain fn-cpc-read-strings-of-encoding
    fn-cpc-read-strings-of-encoding-count fn-cpc-read-strings-reencode
    fn-cpc-uint-list-item fn-cpc-accepted-is-consp))
(in-theory (disable fn-checkpoint-codec-vocabulary
                    fn-cpc-read-item fn-cpc-read-uint fn-cpc-read-bytes
                    fn-cpc-stringp fn-cpc-treep fn-cpc-depth
                    fn-cpc-encode-tree fn-cpc-octet-list-tagp
                    fn-cpc-decode-tree fn-cpc-uint-listp fn-cpc-encode-uints
                    fn-cpc-read-uints fn-cpc-string-listp
                    fn-cpc-encode-strings fn-cpc-read-strings
                    fn-cpc-encodablep fn-cpc-encode-header fn-cpc-encode
                    fn-cpc-assemble fn-cpc-decode fn-cpc-validp
                    fn-cpc-frame-protected fn-cpc-frame-encode
                    fn-cpc-frame-seal fn-cpc-frame-decode fn-cpc-frame-open
                    fn-cpc-selection-protected fn-cpc-selection-encode
                    fn-cpc-selection-decode))
