; Round-trip, canonicality and bound invariants for the fn frame grammar.
;
; Three things are proved here for every frame the host writes or reads.
;
;   Value direction      decode (encode v) = v for every accepted value.
;   Byte direction       encode (decode b) = b for every accepted b, so an
;                        accepted frame has exactly one spelling.
;   Bound direction      an input longer than the caller's cap is refused by
;                        the cons preflight, before octet validation and
;                        before any split allocates.
;
; The digest is A-CRYPTO.  `fn-frame-encode` and `fn-frame-decode` are the
; functions the host calls and they take the digest as an argument;
; `fn-frame-seal` and `fn-frame-open` are the same grammar with the
; constrained `fn-frame-digest` in place of that argument.  The two bridging
; theorems `fn-frame-encode-is-seal` and `fn-frame-decode-is-open` say exactly
; what the host must supply for the executable pair to be the specification
; pair, and they name `fn-frame-digest` in their hypotheses.

(in-package "ACL2")
(include-book "frame")

; This is the frame cluster's proof book: every theorem here is about the
; definitions in `frame-octets', `frame-fields', `frame-journal' and `frame',
; so it opens them locally, together with the CBOR list vocabulary.  The
; splitter shape rules are re-disabled by hand below, where 3.1b of
; planning/lanes/LANEDUMP-twins-into-acl2.md says they must be.
(local (in-theory (enable fn-cbor-invariants-vocabulary
                          fn-cbor-codec-vocabulary
                          fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-journal-vocabulary
                          fn-frame-record-vocabulary
                          fn-frame-codec-vocabulary
                          (:d fn-frame-split)
                          (:d fn-frame-u64-bytes))))
(local (include-book "arithmetic/top" :dir :system))

; The splitter is reasoned about through its lemmas, never by unrolling it on
; a literal length; the big-endian encoders likewise.
(local (in-theory (disable fn-frame-split)))

(defthm fn-frame-u16-bytes-true-listp
  (true-listp (fn-cbor-u16-bytes n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes) (floor mod)))))
(defthm fn-frame-u32-bytes-true-listp
  (true-listp (fn-cbor-u32-bytes n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod)))))
(defthm fn-frame-u16-bytes-of-u16-from
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 2))
           (equal (fn-cbor-u16-bytes (fn-cbor-u16-from xs)) xs))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes fn-cbor-u16-from
                                   fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod)))))

(defthm fn-frame-u32-bytes-of-u32-from
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 4))
           (equal (fn-cbor-u32-bytes (fn-cbor-u32-from xs)) xs))
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes fn-cbor-u32-from
                                   fn-cbor-octet-listp fn-cbor-octetp)
                                  (floor mod)))))

(defthm fn-frame-u16-from-bounded
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 2))
           (< (fn-cbor-u16-from xs) 65536))
  :hints (("Goal" :in-theory (enable fn-cbor-u16-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes :linear)

(defthm fn-frame-u32-from-is-integerp
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 4))
           (integerp (fn-cbor-u32-from xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-u32-from-is-natural
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 4))
           (natp (fn-cbor-u32-from xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-u32-from-bounded
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 4))
           (< (fn-cbor-u32-from xs) 4294967296))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes :linear)

(defthm fn-frame-u16-from-is-natural
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 2))
           (natp (fn-cbor-u16-from xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-u16-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes (:rewrite :type-prescription))
(defthm fn-frame-u16-from-nonnegative
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 2))
           (<= 0 (fn-cbor-u16-from xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-u16-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes :linear)

(defthm fn-frame-u32-from-nonnegative
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 4))
           (<= 0 (fn-cbor-u32-from xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-u32-from fn-cbor-octet-listp
                                     fn-cbor-octetp)))
  :rule-classes :linear)

(defthm fn-frame-u64-from-of-u64-bytes
  (implies (and (natp n) (<= n *fn-frame-max-nat*))
           (equal (fn-frame-u64-from (fn-frame-u64-bytes n)) n))
  :hints (("Goal" :in-theory (e/d (fn-frame-u64-from fn-frame-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes))
           :use ((:instance floor-mod-elim (x n) (y 4294967296))))))

(local
 (defthm fn-frame-mod-halves
   (implies (and (natp a) (natp b) (< b 4294967296))
            (equal (mod (+ (* 4294967296 a) b) 4294967296) b))))

(local
 (defthm fn-frame-floor-halves
   (implies (and (natp a) (natp b) (< b 4294967296))
            (equal (floor (+ (* 4294967296 a) b) 4294967296) a))
   :hints (("Goal" :in-theory (e/d () (floor mod))
            :use ((:instance floor-mod-elim
                             (x (+ (* 4294967296 a) b)) (y 4294967296))
                  fn-frame-mod-halves)))))

; The two halves, stated over variables so that the octet facts about each
; are hypotheses rather than things to be dug out of a split.

(local
 (defthm fn-frame-u64-halves-natural
   (implies (and (fn-cbor-octet-listp a) (equal (len a) 4)
                 (fn-cbor-octet-listp b) (equal (len b) 4))
            (natp (fn-frame-u64-from (append a b))))
   :hints (("Goal" :in-theory (e/d (fn-frame-u64-from natp)
                                   (fn-cbor-u32-from))))))

(local
 (defthm fn-frame-u64-bytes-of-u64-from-halves
   (implies (and (fn-cbor-octet-listp a) (equal (len a) 4)
                 (fn-cbor-octet-listp b) (equal (len b) 4))
            (equal (fn-frame-u64-bytes (fn-frame-u64-from (append a b)))
                   (append a b)))
   :hints (("Goal" :in-theory (e/d (fn-frame-u64-from fn-frame-u64-bytes)
                                   (floor mod fn-cbor-u32-bytes
                                    fn-cbor-u32-from))
            :do-not-induct t))))

(defthm fn-frame-u64-from-is-natural
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
           (natp (fn-frame-u64-from xs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-frame-u64-from)
           :use ((:instance fn-frame-u64-halves-natural
                            (a (car (fn-frame-split 4 xs)))
                            (b (cdr (fn-frame-split 4 xs))))
                 (:instance fn-frame-split-reassembles (n 4)))))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-u64-bytes-of-u64-from
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
           (equal (fn-frame-u64-bytes (fn-frame-u64-from xs)) xs))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-frame-u64-from fn-frame-u64-bytes)
           :use ((:instance fn-frame-u64-bytes-of-u64-from-halves
                            (a (car (fn-frame-split 4 xs)))
                            (b (cdr (fn-frame-split 4 xs))))
                 (:instance fn-frame-split-reassembles (n 4))))))

(defthm fn-frame-u64-from-bounded
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
           (<= (fn-frame-u64-from xs) *fn-frame-max-nat*))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-u64-from) (fn-cbor-u32-from))
           :use ((:instance fn-frame-u32-from-bounded
                            (xs (car (fn-frame-split 4 xs))))
                 (:instance fn-frame-u32-from-bounded
                            (xs (cdr (fn-frame-split 4 xs)))))))
  :rule-classes :linear)

(defthm fn-frame-u64-from-nonnegative
  (implies (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
           (<= 0 (fn-frame-u64-from xs)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-frame-u64-from)))
  :rule-classes :linear)

; Four rules exported by `books/frame` rewrite every `(consp x)` in every goal
; by backchaining into `len`, and the two value predicates open into the
; wildmat decoder and `fn-cbor-at-mostp`.  Together they made plain append
; associativity take minutes.  All are closed from here; the facts they carry
; are re-stated below on the specific terms that need them.
(local (in-theory (disable fn-frame-len-2-conses fn-frame-len-4-conses
                           fn-frame-len-8-conses fn-frame-not-consp-when-len-zero
                           fn-cbor-u16-bytes fn-cbor-u32-bytes fn-frame-u64-bytes
                           fn-frame-textp fn-frame-blobp)))
(defthm fn-frame-item-of-enum-index
  (implies (not (equal (fn-frame-enum-index value keys) 0))
           (equal (fn-frame-item (- (fn-frame-enum-index value keys) 1) keys)
                  value)))

; Stated on the index rather than on membership: a rewrite rule whose left
; side is `member-equal` would fire on every membership in the book and
; backchain into this function each time.
(defthm fn-frame-enum-index-zero-when-not-member
  (implies (not (member-equal value keys))
           (equal (fn-frame-enum-index value keys) 0)))

(defthm fn-frame-item-is-member
  (implies (and (natp n) (< n (len keys)))
           (member-equal (fn-frame-item n keys) keys))
  :hints (("Goal" :induct (fn-frame-item n keys))))

; Stated on the zero-based position so the induction does not have to carry a
; `(- code 1)` through every step.
(defthm fn-frame-enum-index-of-item
  (implies (and (no-duplicatesp-equal keys)
                (natp n)
                (< n (len keys)))
           (equal (fn-frame-enum-index (fn-frame-item n keys) keys)
                  (+ 1 n)))
  :hints (("Goal" :induct (fn-frame-item n keys))))

; Shape facts about the two value predicates, forward-chaining only.  As
; rewrite or linear rules on `(consp x)`, `(fn-cbor-octet-listp x)` or
; `(len x)` they fire in every goal of every book that includes this one and
; backchain into the predicates; where `fn-frame-textp` is enabled that
; unrolls `fn-cbor-at-mostp` to its literal bound.  The two proofs that need
; these facts as hypotheses `:use` them.

(defthm fn-frame-textp-is-octets
  (implies (fn-frame-textp value) (fn-cbor-octet-listp value))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-textp))))
(defthm fn-frame-textp-is-consp
  (implies (fn-frame-textp value) (consp value))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-textp))))
(defthm fn-frame-textp-len-bound
  (implies (fn-frame-textp value) (<= (len value) *fn-frame-max-text*))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-textp))))
(defthm fn-frame-blobp-is-octets
  (implies (fn-frame-blobp value) (fn-cbor-octet-listp value))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-blobp))))
(defthm fn-frame-blobp-is-consp
  (implies (fn-frame-blobp value) (consp value))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-blobp))))
(defthm fn-frame-blobp-len-bound
  (implies (fn-frame-blobp value) (<= (len value) *fn-frame-max-blob*))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-frame-blobp))))

; List and splitter helpers, each proved in a minimal theory.
(local
 (defthm fn-frame-append-assoc
   (equal (append (append a b) c) (append a (append b c)))
   :hints (("Goal" :induct (binary-append a b)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(binary-append car-cons cdr-cons))))))
(local
 (defthm fn-frame-append-nil
   (implies (true-listp x) (equal (append x nil) x))
   :hints (("Goal" :induct (binary-append x nil)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(binary-append true-listp
                                         car-cons cdr-cons))))))
(local
 (defthm fn-frame-len-not-zero-when-consp
   (implies (consp x) (not (equal (len x) 0)))
   :hints (("Goal" :expand ((len x))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '((:type-prescription len)))))))
(local
 (defthm fn-frame-at-mostp-when-len-bounded
   (implies (and (natp bound) (<= (len xs) bound))
            (fn-cbor-at-mostp xs bound))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-cbor-at-mostp len zp natp
                                         (:type-prescription len)))))))
(local
 (defthm fn-frame-split-prefix-consp
   (implies (and (not (zp n)) (fn-frame-split n xs))
            (consp (car (fn-frame-split n xs))))
   :hints (("Goal" :do-not-induct t :expand ((fn-frame-split n xs))))))
(local
 (defthm fn-frame-split-whole
   (implies (and (true-listp xs) (equal (len xs) (nfix n)))
            (equal (fn-frame-split n xs) (cons xs nil)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-split-of-append (a xs) (b nil)))))))
(local
 (defthm fn-frame-split-prefix-when-no-suffix
   (implies (and (true-listp xs) (fn-frame-split n xs)
                 (not (cdr (fn-frame-split n xs))))
            (equal (car (fn-frame-split n xs)) xs))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-split-reassembles))))))
(local
 (defthm fn-frame-split-2-of-cons-cons
   (equal (fn-frame-split 2 (cons a (cons b c))) (cons (list a b) c))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-frame-split zp
                                                car-cons cdr-cons))))))
(local
 (defthm fn-frame-item-1-of-two
   (implies (and (true-listp xs) (equal (len xs) 2))
            (equal (fn-frame-item 1 xs) (car (cdr xs))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-frame-item fn-frame-len-2-conses)))))
(local
 (defthm fn-frame-true-listp-of-append
   (equal (true-listp (append a b)) (true-listp b))
   :hints (("Goal" :induct (binary-append a b)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(binary-append true-listp
                                         car-cons cdr-cons))))))
; A two-element list spelled out is that list appended to its tail.  The
; `syntaxp` keeps the rule off explicit lists such as the head-fields record,
; whose positional reads must still see their conses.
(local
 (defthm fn-frame-two-list
   (implies (and (syntaxp (not (and (consp rest) (eq (car rest) 'cons))))
                 (true-listp xs) (equal (len xs) 2))
            (equal (cons (car xs) (cons (car (cdr xs)) rest))
                   (append xs rest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-frame-len-2-conses)
            :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                     (true-listp xs) (true-listp (cdr xs))
                     (true-listp (cdr (cdr xs))))))))
(defthm fn-frame-parse-okp-of-parse-ok
  (fn-frame-parse-okp (fn-frame-parse-ok value rest)))
(defthm fn-frame-parse-okp-of-parse-error
  (not (fn-frame-parse-okp (fn-frame-parse-error reason))))
(defthm fn-frame-parse-value-of-parse-ok
  (equal (fn-frame-parse-value (fn-frame-parse-ok value rest)) value))
(defthm fn-frame-parse-rest-of-parse-ok
  (equal (fn-frame-parse-rest (fn-frame-parse-ok value rest)) rest))
(local (in-theory (disable fn-frame-parse-ok fn-frame-parse-error
                           fn-frame-parse-okp fn-frame-parse-value
                           fn-frame-parse-rest fn-frame-item)))

; The counted tail once, over a variable length; then one case per spec
; shape, each a straight-line rewrite under an explicit theory.
(defthm fn-frame-parse-counted-of-append
  (implies (and (true-listp value) (consp value)
                (natp maximum) (<= (len value) maximum))
           (equal (fn-frame-parse-counted (append value rest) (len value) maximum)
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-parse-counted fn-frame-split-of-append
                         fn-frame-len-not-zero-when-consp
                         nfix natp (:type-prescription len)
                         car-cons cdr-cons)))))

(defthm fn-frame-field-parse-of-octets-text
  (implies (and (fn-frame-textp value)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   :text (append (fn-frame-field-octets :text value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-textp-is-octets)
                 (:instance fn-frame-textp-is-consp)
                 (:instance fn-frame-textp-len-bound))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-field-parse fn-frame-field-octets
                         fn-frame-append-assoc fn-frame-split-of-append
                         fn-frame-u16-bytes-len fn-frame-u16-bytes-true-listp
                         fn-cbor-u16-from-u16-bytes
                         fn-frame-parse-counted-of-append
                         fn-frame-textp-is-octets fn-frame-textp-is-consp
                         fn-frame-textp-len-bound
                         fn-frame-octet-listp-true-listp
                         fn-frame-parse-okp-of-parse-ok
                         fn-frame-parse-value-of-parse-ok
                         nfix natp (:type-prescription len)
                         car-cons cdr-cons)))))

(defthm fn-frame-field-parse-of-octets-blob
  (implies (and (fn-frame-blobp value)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   :blob (append (fn-frame-field-octets :blob value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-blobp-is-octets)
                 (:instance fn-frame-blobp-is-consp)
                 (:instance fn-frame-blobp-len-bound))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-field-parse fn-frame-field-octets
                         fn-frame-append-assoc fn-frame-split-of-append
                         fn-frame-u32-bytes-len fn-frame-u32-bytes-true-listp
                         fn-cbor-u32-from-u32-bytes
                         fn-frame-parse-counted-of-append
                         fn-frame-blobp-is-octets fn-frame-blobp-is-consp
                         fn-frame-blobp-len-bound
                         fn-frame-octet-listp-true-listp
                         nfix natp (:type-prescription len)
                         car-cons cdr-cons)))))

(defthm fn-frame-field-parse-of-octets-nat
  (implies (and (fn-frame-natp value)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   :nat (append (fn-frame-field-octets :nat value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-field-parse fn-frame-field-octets
                         fn-frame-natp fn-frame-split-of-append
                         fn-frame-u64-bytes-len fn-frame-u64-bytes-are-octets
                         fn-frame-u64-from-of-u64-bytes
                         fn-frame-octet-listp-true-listp
                         nfix natp (:type-prescription len)
                         car-cons cdr-cons)))))

(defthm fn-frame-field-parse-of-octets-enum
  (implies (and (fn-frame-enum-specp spec)
                (not (equal (fn-frame-enum-index value (cdr spec)) 0))
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   spec (append (fn-frame-field-octets spec value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-field-parse fn-frame-field-octets
                         fn-frame-enum-specp binary-append
                         fn-frame-enum-index-natp fn-frame-enum-index-bound
                         fn-frame-item-of-enum-index
                         posp natp (:type-prescription len)
                         car-cons cdr-cons)))))

(defthm fn-frame-field-parse-of-octets
  (implies (and (fn-frame-specp spec)
                (fn-frame-field-okp spec value)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-field-parse
                   spec (append (fn-frame-field-octets spec value) rest))
                  (fn-frame-parse-ok value rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-frame-specp fn-frame-field-okp
                         fn-frame-field-parse-of-octets-text
                         fn-frame-field-parse-of-octets-blob
                         fn-frame-field-parse-of-octets-nat
                         fn-frame-field-parse-of-octets-enum)))))


; -----------------------------------------------------------------------------
; One field, the byte direction: a parsed field re-encodes to the octets it
; consumed, and its value satisfies the field predicate.  The big-endian
; readers stay closed so that the width lemmas can match their images.

(defthm fn-frame-field-octets-of-parse
  (implies (and (fn-frame-specp spec)
                (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-field-parse spec octets)))
           (equal (append (fn-frame-field-octets
                           spec (fn-frame-parse-value
                                 (fn-frame-field-parse spec octets)))
                          (fn-frame-parse-rest (fn-frame-field-parse spec octets)))
                  octets))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-field-parse fn-frame-field-octets
                            fn-frame-parse-counted fn-frame-specp
                            fn-frame-enum-specp)
                           (fn-cbor-u16-from fn-cbor-u32-from
                            fn-frame-u64-from floor mod)))))

(defthm fn-frame-field-parse-value-okp
  (implies (and (fn-frame-specp spec)
                (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-field-parse spec octets)))
           (fn-frame-field-okp
            spec (fn-frame-parse-value (fn-frame-field-parse spec octets))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-field-parse fn-frame-field-okp
                            fn-frame-parse-counted fn-frame-specp
                            fn-frame-enum-specp fn-frame-blobp fn-frame-natp)
                           (fn-cbor-u16-from fn-cbor-u32-from
                            fn-frame-u64-from floor mod)))))

; -----------------------------------------------------------------------------
; A record's fields, both directions.  The single-field rules do the work, so
; the field grammar stays closed here.

(defthm fn-frame-fields-parse-aux-of-octets
  (implies (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values)
                (fn-cbor-octet-listp rest))
           (equal (fn-frame-fields-parse-aux
                   specs (append (fn-frame-fields-octets specs values) rest))
                  (fn-frame-parse-ok values rest)))
  :hints (("Goal" :induct (fn-frame-values-okp specs values)
           :in-theory (e/d (fn-frame-fields-parse-aux fn-frame-fields-octets
                            fn-frame-values-okp fn-frame-spec-listp)
                           (fn-frame-field-parse fn-frame-field-octets
                            fn-frame-parse-counted)))))

(defthm fn-frame-fields-parse-of-octets
  (implies (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))
           (equal (fn-frame-fields-parse
                   specs (fn-frame-fields-octets specs values))
                  (fn-frame-parse-ok values nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-fields-parse)
                           (fn-frame-fields-parse-aux fn-frame-fields-octets
                            fn-frame-field-parse fn-frame-field-octets))
           :use ((:instance fn-frame-fields-parse-aux-of-octets (rest nil))))))

(defthm fn-frame-fields-parse-aux-round-trip
  (implies (and (fn-frame-spec-listp specs)
                (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-fields-parse-aux specs octets)))
           (and (fn-frame-values-okp
                 specs (fn-frame-parse-value
                        (fn-frame-fields-parse-aux specs octets)))
                (equal (append (fn-frame-fields-octets
                                specs (fn-frame-parse-value
                                       (fn-frame-fields-parse-aux specs octets)))
                               (fn-frame-parse-rest
                                (fn-frame-fields-parse-aux specs octets)))
                       octets)))
  :hints (("Goal" :induct (fn-frame-fields-parse-aux specs octets)
           :in-theory (e/d (fn-frame-fields-parse-aux fn-frame-fields-octets
                            fn-frame-values-okp fn-frame-spec-listp)
                           (fn-frame-field-parse fn-frame-field-octets
                            fn-frame-parse-counted)))))

(defthm fn-frame-fields-octets-of-parse
  (implies (and (fn-frame-spec-listp specs)
                (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-fields-parse specs octets)))
           (equal (fn-frame-fields-octets
                   specs (fn-frame-parse-value
                          (fn-frame-fields-parse specs octets)))
                  octets))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-fields-parse)
                           (fn-frame-fields-parse-aux fn-frame-fields-octets
                            fn-frame-field-parse fn-frame-field-octets))
           :use ((:instance fn-frame-fields-parse-aux-round-trip)))))

; -----------------------------------------------------------------------------
; Shape facts the frame theorems need.  `fn-frame-header` and
; `fn-frame-protected` are then read only through these, so that the splitter
; lemma sees a ten-octet header and not its four parts.

(defthm fn-frame-header-octets
  (implies (and (fn-frame-magicp magic) (fn-cbor-octetp version)
                (fn-cbor-octetp kind) (natp length)
                (<= length *fn-cbor-max-uint*))
           (and (fn-cbor-octet-listp (fn-frame-header magic version kind length))
                (equal (len (fn-frame-header magic version kind length)) 10)))
  :hints (("Goal" :in-theory (enable fn-frame-header fn-frame-magicp))))

(defthm fn-frame-head-fields-of-header
  (implies (and (fn-frame-magicp magic) (fn-cbor-octetp version)
                (fn-cbor-octetp kind) (natp length)
                (<= length *fn-cbor-max-uint*))
           (equal (fn-frame-head-fields
                   (fn-frame-header magic version kind length))
                  (list magic version kind (fn-cbor-u32-bytes length))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-frame-head-fields fn-frame-header
                              fn-frame-magicp fn-frame-item))))

(defthm fn-frame-protected-true-listp
  (implies (true-listp payload)
           (true-listp (fn-frame-protected magic version kind payload)))
  :hints (("Goal" :in-theory (e/d (fn-frame-protected) (fn-frame-header)))))

; The trailer split of a frame that is known to be an encoding.  Stated on a
; separate variable `xs` so that the equation can be substituted into the
; split; the theorem below instantiates `xs` with the decoded octets.
(local
 (defthm fn-frame-split-tail-of-encode
   (implies (and (true-listp payload)
                 (fn-frame-digestp digest)
                 (equal (fn-frame-encode magic version kind payload digest) xs))
            (equal (fn-frame-split (- (len xs) *fn-frame-trailer-octets*) xs)
                   (cons (fn-frame-protected magic version kind payload)
                         digest)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-frame-encode fn-frame-digestp)
                            (fn-frame-protected fn-frame-header))))))

; -----------------------------------------------------------------------------
; KEYSTONE: the value direction.  Everything the host encodes decodes back.

(defthm fn-frame-decode-of-encode
  (implies (and (fn-frame-inputp magic version kind payload max-payload)
                (fn-frame-digestp digest))
           (equal (fn-frame-decode
                   (fn-frame-encode magic version kind payload digest)
                   digest max-payload)
                  (fn-frame-ok magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-decode fn-frame-encode
                            fn-frame-protected fn-frame-inputp
                            fn-frame-magicp fn-frame-digestp fn-frame-item)
                           (fn-frame-header fn-frame-head-fields
                            fn-cbor-u32-from floor mod)))))

; KEYSTONE: the byte direction.  An accepted frame has exactly one spelling,
; so a decode followed by an encode is the identity on accepted octets.

(defthm fn-frame-encode-of-decode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-digestp digest)
                (fn-frame-result-okp (fn-frame-decode octets digest
                                                      max-payload)))
           (equal (fn-frame-encode
                   (fn-frame-result-magic (fn-frame-decode octets digest
                                                           max-payload))
                   (fn-frame-result-version (fn-frame-decode octets digest
                                                             max-payload))
                   (fn-frame-result-kind (fn-frame-decode octets digest
                                                          max-payload))
                   (fn-frame-result-payload (fn-frame-decode octets digest
                                                             max-payload))
                   digest)
                  octets))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-decode fn-frame-encode
                            fn-frame-protected fn-frame-header
                            fn-frame-head-fields fn-frame-digestp fn-frame-item)
                           (fn-cbor-u32-from floor mod)))))

; KEYSTONE: the bound direction.  An input longer than the caller's cap is
; refused by the cons preflight: the conclusion holds with no hypothesis about
; `octets` at all, so neither octet validation nor any split has run.

(defthm fn-frame-decode-refuses-oversize-before-validation
  (implies (and (natp max-payload)
                (<= max-payload *fn-frame-max-payload*)
                (not (fn-cbor-at-mostp octets
                                       (+ *fn-frame-overhead-octets*
                                          max-payload))))
           (equal (fn-frame-decode octets digest max-payload)
                  (fn-frame-error :limit)))
  :hints (("Goal" :in-theory (enable fn-frame-decode))))

(defthm fn-frame-decode-bounds-its-payload
  (implies (and (natp max-payload)
                (<= max-payload *fn-frame-max-payload*)
                (fn-frame-result-okp (fn-frame-decode octets digest
                                                      max-payload)))
           (<= (len (fn-frame-result-payload
                     (fn-frame-decode octets digest max-payload)))
               max-payload))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-decode fn-frame-item)
                           (fn-frame-head-fields fn-cbor-u32-from floor mod))))
  :rule-classes :linear)

; KEYSTONE: an accepted frame's stored trailer is the digest the caller
; supplied.  This is what makes the byte direction above a real statement
; about integrity rather than about layout alone.

(defthm fn-frame-decode-trailer-is-the-supplied-digest
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-digestp digest)
                (fn-frame-result-okp (fn-frame-decode octets digest
                                                      max-payload)))
           (equal (fn-frame-split (- (len octets) *fn-frame-trailer-octets*)
                                  octets)
                  (cons (fn-frame-protected
                         (fn-frame-result-magic
                          (fn-frame-decode octets digest max-payload))
                         (fn-frame-result-version
                          (fn-frame-decode octets digest max-payload))
                         (fn-frame-result-kind
                          (fn-frame-decode octets digest max-payload))
                         (fn-frame-result-payload
                          (fn-frame-decode octets digest max-payload)))
                        digest)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-encode-of-decode)
                 (:instance fn-frame-split-tail-of-encode
                            (xs octets)
                            (magic (fn-frame-result-magic
                                    (fn-frame-decode octets digest max-payload)))
                            (version (fn-frame-result-version
                                      (fn-frame-decode octets digest max-payload)))
                            (kind (fn-frame-result-kind
                                   (fn-frame-decode octets digest max-payload)))
                            (payload (fn-frame-result-payload
                                      (fn-frame-decode octets digest max-payload)))))
           :in-theory (disable fn-frame-encode-of-decode fn-frame-decode
                               fn-frame-encode fn-frame-protected
                               fn-frame-split-tail-of-encode
                               fn-frame-result-okp fn-frame-result-magic
                               fn-frame-result-version fn-frame-result-kind
                               fn-frame-result-payload))))

; -----------------------------------------------------------------------------
; A-CRYPTO: relating the functions the host calls to the specification
;
; The host computes the trailer.  These two theorems say precisely what the
; host must have computed for `fn-frame-encode`/`fn-frame-decode` to be
; `fn-frame-seal`/`fn-frame-open`, and they mention `fn-frame-digest`, the
; constrained function that stands for SHA-256, in their hypotheses.

(defthm fn-frame-digestp-of-fn-frame-digest
  (fn-frame-digestp (fn-frame-digest octets))
  :hints (("Goal" :in-theory (enable fn-frame-digestp))))

(defthm fn-frame-protected-prefix-of-encode
  (implies (and (fn-frame-inputp magic version kind payload max-payload)
                (fn-frame-digestp digest))
           (equal (fn-frame-protected-prefix
                   (fn-frame-encode magic version kind payload digest))
                  (fn-frame-protected magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-protected-prefix fn-frame-encode
                            fn-frame-inputp fn-frame-digestp)
                           (fn-frame-protected fn-frame-header)))))

(defthm fn-frame-encode-is-seal
  (implies (equal digest
                  (fn-frame-digest
                   (fn-frame-protected magic version kind payload)))
           (equal (fn-frame-encode magic version kind payload digest)
                  (fn-frame-seal magic version kind payload)))
  :hints (("Goal" :in-theory (enable fn-frame-seal))))

(defthm fn-frame-decode-is-open
  (implies (equal digest (fn-frame-digest (fn-frame-protected-prefix octets)))
           (equal (fn-frame-decode octets digest max-payload)
                  (fn-frame-open octets max-payload)))
  :hints (("Goal" :in-theory (enable fn-frame-open))))

; The two bridging theorems are exported disabled: each is the inverse of
; opening its specification function, and as an enabled rewrite rule it loops
; against that definition in any book where `fn-frame-open` or
; `fn-frame-seal` appears.  A proof that needs one names it in a hint.
(in-theory (disable fn-frame-encode-is-seal fn-frame-decode-is-open))

; KEYSTONE under A-CRYPTO: the sealed frame opens to the value that was
; sealed.  Both sides use the constrained digest; no host obligation remains.

(defthm fn-frame-open-of-seal
  (implies (fn-frame-inputp magic version kind payload max-payload)
           (equal (fn-frame-open (fn-frame-seal magic version kind payload)
                                 max-payload)
                  (fn-frame-ok magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-open fn-frame-seal)
                           (fn-frame-encode fn-frame-protected
                            fn-frame-protected-prefix fn-frame-inputp
                            fn-frame-decode)))))

; -----------------------------------------------------------------------------
; The journal record entry points, both directions

(defthm fn-frame-store-decode-of-encode
  (implies (and (fn-cbor-octet-listp record)
                (fn-cbor-at-mostp record *fn-frame-max-store-payload*)
                (fn-frame-digestp digest))
           (equal (fn-frame-store-decode
                   (fn-frame-store-encode record digest) digest)
                  (fn-frame-ok *fn-frame-magic-store* *fn-frame-version*
                               *fn-frame-store-kind* record)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-store-encode fn-frame-store-decode
                            fn-frame-inputp fn-frame-magicp fn-frame-item)
                           (fn-frame-decode fn-frame-encode)))))

(defthm fn-frame-workflow-decode-of-encode
  (implies (and (fn-frame-workflow-record-okp kind values)
                (fn-frame-digestp digest)
                (<= (len (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-workflow-specs*)
                          values))
                    *fn-frame-max-workflow-payload*))
           (equal (fn-frame-workflow-decode
                   (fn-frame-workflow-encode kind values digest) digest)
                  (fn-frame-ok *fn-frame-magic-workflow* *fn-frame-version*
                               kind values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-workflow-encode
                            fn-frame-workflow-decode
                            fn-frame-workflow-record-okp
                            fn-frame-inputp fn-frame-magicp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

(defthm fn-frame-receipt-decode-of-encode
  (implies (and (fn-frame-receipt-record-okp kind values)
                (fn-frame-digestp digest)
                (<= (len (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-receipt-specs*)
                          values))
                    *fn-frame-max-receipt-payload*))
           (equal (fn-frame-receipt-decode
                   (fn-frame-receipt-encode kind values digest) digest)
                  (fn-frame-ok *fn-frame-magic-receipt* *fn-frame-version*
                               kind values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-receipt-encode
                            fn-frame-receipt-decode
                            fn-frame-receipt-record-okp
                            fn-frame-inputp fn-frame-magicp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

; -----------------------------------------------------------------------------
; What the host is allowed to do with the protected prefix
;
; `tools/frame_bridge.py` asks ACL2 for the protected prefix, appends 32 digest
; octets and writes the result.  These theorems are why that is the same byte
; string as `fn-frame-encode`: the host contributes the trailer and nothing
; else.  Each is the justification for one line of `FrameSession.seal`.

(defthm fn-frame-store-encode-is-protected-plus-digest
  (implies (and (fn-cbor-octet-listp record)
                (fn-cbor-at-mostp record *fn-frame-max-store-payload*)
                (fn-frame-digestp digest))
           (equal (fn-frame-store-encode record digest)
                  (append (fn-frame-store-protected record) digest)))
  :hints (("Goal" :in-theory (e/d (fn-frame-store-encode
                                   fn-frame-store-protected
                                   fn-frame-encode)
                                  (fn-frame-protected)))))

(defthm fn-frame-workflow-encode-is-protected-plus-digest
  (implies (and (fn-frame-workflow-record-okp kind values)
                (fn-cbor-at-mostp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-frame-workflow-specs*) values)
                 *fn-frame-max-workflow-payload*)
                (fn-frame-digestp digest))
           (equal (fn-frame-workflow-encode kind values digest)
                  (append (fn-frame-workflow-protected kind values) digest)))
  :hints (("Goal" :in-theory (e/d (fn-frame-workflow-encode
                                   fn-frame-workflow-protected
                                   fn-frame-encode)
                                  (fn-frame-protected fn-frame-fields-octets)))))

(defthm fn-frame-receipt-encode-is-protected-plus-digest
  (implies (and (fn-frame-receipt-record-okp kind values)
                (fn-cbor-at-mostp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-frame-receipt-specs*) values)
                 *fn-frame-max-receipt-payload*)
                (fn-frame-digestp digest))
           (equal (fn-frame-receipt-encode kind values digest)
                  (append (fn-frame-receipt-protected kind values) digest)))
  :hints (("Goal" :in-theory (e/d (fn-frame-receipt-encode
                                   fn-frame-receipt-protected
                                   fn-frame-encode)
                                  (fn-frame-protected fn-frame-fields-octets)))))

; The inbound case, where the host also concatenates the bundle.  The head it
; sends back is a bounded prefix of the stored frame, which is why `tail` is
; arbitrary here: everything the opener decides comes out of the prefix.

(local
 (defthm fn-frame-text-field-octets-len
   (implies (fn-frame-textp bid)
            (equal (len (fn-frame-field-octets :text bid)) (+ 2 (len bid))))
   :hints (("Goal" :in-theory (enable fn-frame-field-octets)))))

(defthm fn-frame-inbound-open-of-prefix
  (implies (and (fn-frame-textp bid)
                (fn-frame-blobp ident)
                (<= (len ident) *fn-frame-max-identity*)
                (natp bundle-length)
                (<= (+ 2 (len bid) 4 (len ident) bundle-length)
                    *fn-frame-max-inbound-payload*)
                (fn-cbor-octet-listp tail)
                (fn-cbor-at-mostp
                 (append (fn-frame-inbound-prefix bid ident bundle-length)
                         tail)
                 (+ *fn-frame-header-octets* 2 *fn-frame-max-text* 4
                    *fn-frame-max-identity*))
                (fn-frame-digestp digest))
           (equal (fn-frame-inbound-open
                   (append (fn-frame-inbound-prefix bid ident bundle-length)
                           tail)
                   (+ *fn-frame-overhead-octets* 2 (len bid) 4 (len ident)
                      bundle-length)
                   digest digest)
                  (fn-frame-ok *fn-frame-magic-inbound* *fn-frame-version*
                               (list bid ident) bundle-length)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-frame-inbound-open fn-frame-inbound-prefix
                            fn-frame-magicp fn-frame-digestp fn-frame-item)
                           (fn-frame-header fn-frame-head-fields
                            fn-frame-field-octets fn-frame-field-parse
                            fn-frame-parse-counted fn-cbor-u32-from
                            fn-cbor-u16-from floor mod)))))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave this book enabled: the two round trips, the two bound
; theorems, the trailer theorem, the seal/open bridge and the four journal
; round trips.  Everything else is arithmetic, enum and field vocabulary,
; including the shape lemmas whose hypotheses unroll `fn-cbor-at-mostp' -- the
; rules that made one `append' goal cost 108 s and `fn-id-hex-octets-are-
; octets' 619 s before they were disabled by hand (3.1b of
; planning/lanes/LANEDUMP-twins-into-acl2.md).  They no longer reach an
; includer at all.

(deftheory fn-frame-invariants-vocabulary
  '(    fn-frame-u16-bytes-true-listp fn-frame-u32-bytes-true-listp
    fn-frame-u16-bytes-of-u16-from fn-frame-u32-bytes-of-u32-from
    fn-frame-u16-from-bounded fn-frame-u32-from-is-integerp
    fn-frame-u32-from-is-natural fn-frame-u32-from-bounded
    fn-frame-u16-from-is-natural fn-frame-u16-from-nonnegative
    fn-frame-u32-from-nonnegative fn-frame-u64-from-of-u64-bytes
    fn-frame-u64-from-is-natural fn-frame-u64-bytes-of-u64-from
    fn-frame-u64-from-bounded fn-frame-u64-from-nonnegative
    fn-frame-item-of-enum-index fn-frame-enum-index-zero-when-not-member
    fn-frame-item-is-member fn-frame-enum-index-of-item
    fn-frame-textp-is-octets fn-frame-textp-is-consp
    fn-frame-textp-len-bound fn-frame-blobp-is-octets
    fn-frame-blobp-is-consp fn-frame-blobp-len-bound
    fn-frame-parse-okp-of-parse-ok fn-frame-parse-okp-of-parse-error
    fn-frame-parse-value-of-parse-ok fn-frame-parse-rest-of-parse-ok
    fn-frame-parse-counted-of-append fn-frame-field-parse-of-octets-text
    fn-frame-field-parse-of-octets-blob fn-frame-field-parse-of-octets-nat
    fn-frame-field-parse-of-octets-enum fn-frame-field-parse-of-octets
    fn-frame-field-octets-of-parse fn-frame-field-parse-value-okp
    fn-frame-fields-parse-aux-of-octets fn-frame-fields-parse-of-octets
    fn-frame-fields-parse-aux-round-trip fn-frame-fields-octets-of-parse
    fn-frame-header-octets fn-frame-head-fields-of-header
    fn-frame-protected-true-listp))

(in-theory (disable fn-frame-u16-bytes-true-listp fn-frame-u32-bytes-true-listp
             fn-frame-u16-bytes-of-u16-from fn-frame-u32-bytes-of-u32-from
             fn-frame-u16-from-bounded fn-frame-u32-from-is-integerp
             fn-frame-u32-from-is-natural fn-frame-u32-from-bounded
             fn-frame-u16-from-is-natural fn-frame-u16-from-nonnegative
             fn-frame-u32-from-nonnegative fn-frame-u64-from-of-u64-bytes
             fn-frame-u64-from-is-natural fn-frame-u64-bytes-of-u64-from
             fn-frame-u64-from-bounded fn-frame-u64-from-nonnegative
             fn-frame-item-of-enum-index
             fn-frame-enum-index-zero-when-not-member
             fn-frame-item-is-member fn-frame-enum-index-of-item
             fn-frame-textp-is-octets fn-frame-textp-is-consp
             fn-frame-textp-len-bound fn-frame-blobp-is-octets
             fn-frame-blobp-is-consp fn-frame-blobp-len-bound
             fn-frame-parse-okp-of-parse-ok
             fn-frame-parse-okp-of-parse-error
             fn-frame-parse-value-of-parse-ok
             fn-frame-parse-rest-of-parse-ok
             fn-frame-parse-counted-of-append
             fn-frame-field-parse-of-octets-text
             fn-frame-field-parse-of-octets-blob
             fn-frame-field-parse-of-octets-nat
             fn-frame-field-parse-of-octets-enum
             fn-frame-field-parse-of-octets fn-frame-field-octets-of-parse
             fn-frame-field-parse-value-okp
             fn-frame-fields-parse-aux-of-octets
             fn-frame-fields-parse-of-octets
             fn-frame-fields-parse-aux-round-trip
             fn-frame-fields-octets-of-parse fn-frame-header-octets
             fn-frame-head-fields-of-header fn-frame-protected-true-listp))
