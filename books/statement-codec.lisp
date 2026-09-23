; fn: the statement item codec's implementation.
;
; `fn-stmt-encode-items-impl' concatenates each item's CBOR encoding;
; `fn-stmt-decode-items-bounded-impl' and
; `fn-stmt-decode-prefix-items-bounded-impl' parse a bounded, octet-checked
; input back into items, one bounded CBOR item at a time, the first exactly
; and the second up to a declared count, returning the untouched rest.  No
; book above the codec calls these: `books/statement-seam.lisp' constrains
; `fn-stmt-encode-items', `fn-stmt-decode-items-bounded' and
; `fn-stmt-decode-prefix-items-bounded' by the properties proved of these
; below, and `books/statement-attach.lisp' attaches them for evaluation
; (plan 2026-09-22 §4.1, step T1).  The proofs below are the item-sequence
; half of what `statement-invariants' proved before the seam, moved here
; unchanged apart from the names.

(in-package "ACL2")
(include-book "statement-items")



;; Convergence: the codecs cluster withdraws its proof vocabulary on export;
;; re-open it locally (agreed on the deputy board, codecs ANSWER to substrate).
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals)))


(defun fn-stmt-encode-items-impl (items)
  (declare (xargs :guard (fn-stmt-item-listp items)))
  (if (consp items)
      (append (fn-cbor-encode (car items))
              (fn-stmt-encode-items-impl (cdr items)))
    nil))

(defthm fn-stmt-impl-encode-items-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-encode-items-impl items))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-impl-encode-items-is-true-list
  (true-listp (fn-stmt-encode-items-impl items)))

; The one-item decoder always returns a list, so its accessors are guarded.
(defthm fn-stmt-cbor-decode-argument-true-listp
  (true-listp (fn-cbor-decode-argument additional xs)))
(defthm fn-stmt-cbor-decode-unsigned-true-listp
  (true-listp (fn-cbor-decode-unsigned additional tail)))
(defthm fn-stmt-cbor-decode-bytes-true-listp
  (true-listp (fn-cbor-decode-bytes additional tail)))
(defthm fn-stmt-cbor-decode-bounded-true-listp
  (true-listp (fn-cbor-decode-bounded octets input-budget item-budget)))
(defthm fn-stmt-cbor-decode-prechecked-true-listp
  (true-listp (fn-cbor-decode-prechecked octets item-budget)))
(defthm fn-stmt-cbor-decode-true-listp
  (true-listp (fn-cbor-decode octets)))

; Parse exactly COUNT items from an already validated bounded octet list.  It
; returns the untouched remainder and performs no whole-suffix preflight.
(defun fn-stmt-decode-prefix-items-prechecked (count octets item-budget)
  (declare (xargs :guard (and (natp count)
                              (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :measure (nfix count)))
  (if (zp count)
      (fn-stmt-ok2 nil octets)
    (let ((first (fn-cbor-decode-prechecked octets item-budget)))
      (if (not (fn-cbor-result-okp first))
          (fn-stmt-error (fn-stmt-value first))
        (let ((tail (fn-stmt-decode-prefix-items-prechecked
                     (1- count) (fn-cbor-result-rest first) item-budget)))
          (if (not (fn-stmt-okp tail))
              tail
            (fn-stmt-ok2 (cons (fn-cbor-result-value first)
                               (fn-stmt-value tail))
                         (fn-stmt-rest tail))))))))

(defun fn-stmt-decode-prefix-items-bounded-impl
  (count octets outer-budget item-budget)
  (declare (xargs :guard (and (natp count) (natp outer-budget)
                              (natp item-budget))))
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (fn-stmt-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-stmt-error :malformed)
      (fn-stmt-decode-prefix-items-prechecked count octets item-budget))))

(defun fn-stmt-decode-items-prechecked (fuel octets item-budget)
  (declare (xargs :guard (and (natp fuel)
                              (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :measure (nfix fuel)))
  (if (atom octets)
      (fn-stmt-ok nil)
    (if (zp fuel)
        (fn-stmt-error :too-many-items)
      (let ((first (fn-cbor-decode-prechecked octets item-budget)))
        (if (not (fn-cbor-result-okp first))
            (fn-stmt-error (fn-stmt-value first))
          (let ((tail (fn-stmt-decode-items-prechecked
                       (1- fuel) (fn-cbor-result-rest first) item-budget)))
            (if (not (fn-stmt-okp tail))
                tail
              (fn-stmt-ok (cons (fn-cbor-result-value first)
                                (fn-stmt-value tail))))))))))

; Decode at most `fuel` items and require the input to be consumed exactly.
; `fuel` bounds the number of allocations; each item is bounded by the
; primitive decoder.  An atom that is not NIL is malformed, so a successful
; decode always re-encodes to its input (statement-invariants).
(defun fn-stmt-decode-items-bounded-impl (fuel octets outer-budget item-budget)
  (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                              (natp item-budget))))
  ; One bounded preflight and octet validation occur before recursive parsing.
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (fn-stmt-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-stmt-error :malformed)
      (fn-stmt-decode-items-prechecked fuel octets item-budget))))

(defun fn-stmt-decode-items-impl (fuel octets)
  (declare (xargs :guard (natp fuel)))
  ; Compatibility wrapper for every pre-existing statement caller.
  (fn-stmt-decode-items-bounded-impl fuel octets
                                *fn-cbor-max-input* *fn-cbor-max-bytes*))



; The result algebra of statement-invariants, local here: the item proofs
; below use it and the book above proves it again for its includers.
; -----------------------------------------------------------------------------
; Result algebra

(local (defthm fn-stmt-okp-of-ok
  (fn-stmt-okp (fn-stmt-ok v))))
(local (defthm fn-stmt-value-of-ok
  (equal (fn-stmt-value (fn-stmt-ok v)) v)))
(local (defthm fn-stmt-okp-of-ok2
  (fn-stmt-okp (fn-stmt-ok2 v r))))
(local (defthm fn-stmt-value-of-ok2
  (equal (fn-stmt-value (fn-stmt-ok2 v r)) v)))
(local (defthm fn-stmt-rest-of-ok2
  (equal (fn-stmt-rest (fn-stmt-ok2 v r)) r)))
(local (defthm fn-stmt-error-is-not-ok
  (not (fn-stmt-okp (fn-stmt-error c)))))
(local (defthm fn-stmt-ok-is-not-error-shaped
  (and (not (equal (fn-stmt-ok v) (fn-stmt-error c)))
       (not (equal (fn-stmt-ok2 v r) (fn-stmt-error c))))))


; -----------------------------------------------------------------------------
; The item-sequence codec

(local (defthm fn-stmt-encode-value-consp
  (implies (fn-cbor-valuep v)
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-argument)))))

(local (defthm fn-stmt-encode-uint-item-consp
  (implies (and (consp v) (equal (car v) :uint)
                (natp (cdr v)) (<= (cdr v) *fn-cbor-max-uint*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode)))))

(local (defthm fn-stmt-encode-bytes-item-consp
  (implies (and (consp v) (equal (car v) :bytes)
                (fn-cbor-octet-listp (cdr v))
                (<= (len (cdr v)) *fn-cbor-max-bytes*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode)))))

(local (defthm fn-stmt-consp-of-append
  (implies (consp a)
           (consp (append a b)))))

(local (defthm fn-stmt-cbor-stream-round-trip
  (implies (and (fn-cbor-valuep v)
                (fn-cbor-octet-listp rest)
                (<= (+ (len (fn-cbor-encode v)) (len rest)) *fn-cbor-max-input*))
           (equal (fn-cbor-decode (append (fn-cbor-encode v) rest))
                  (fn-cbor-ok v rest)))
  :hints (("Goal"
           :use ((:instance fn-record-cbor-stream-uint-round-trip (n (cdr v)))
                 (:instance fn-record-cbor-stream-bytes-round-trip (xs (cdr v))))
           :in-theory (e/d (fn-record-uint32p)
                           (fn-cbor-decode fn-cbor-encode
                            fn-record-cbor-stream-uint-round-trip
                            fn-record-cbor-stream-bytes-round-trip))))))

(local (defun fn-stmt-items-fuel-induct (fuel items)
  (if (consp items)
      (fn-stmt-items-fuel-induct (1- fuel) (cdr items))
    (list fuel items))))

(defthm fn-stmt-impl-encode-items-of-append
  (equal (fn-stmt-encode-items-impl (append a b))
         (append (fn-stmt-encode-items-impl a) (fn-stmt-encode-items-impl b)))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

; The streaming primitive is the old one-item decoder after its caller has
; discharged the legacy outer bound and octet-list checks.  Keeping this
; bridge opaque lets the established sequence proofs reason about one CBOR
; item at a time without expanding the bounded preflight implementation.
(defthm fn-stmt-decode-prechecked-is-legacy
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*))
           (equal (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*)
                  (fn-cbor-decode octets)))
  :hints (("Goal"
           :use ((:instance fn-cbor-at-mostp-from-length
                            (xs octets)
                            (bound *fn-cbor-max-input*)))
           :in-theory (enable fn-cbor-decode fn-cbor-decode-bounded))))

(defthm fn-stmt-prechecked-reencode-prefix
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*)
                (fn-cbor-result-okp
                 (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*)))
           (equal (append
                   (fn-cbor-encode
                    (fn-cbor-result-value
                     (fn-cbor-decode-prechecked
                      octets *fn-cbor-max-bytes*)))
                   (fn-cbor-result-rest
                    (fn-cbor-decode-prechecked
                     octets *fn-cbor-max-bytes*)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-cbor-decode-reencode-prefix))
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-decode-prechecked))))

(defthm fn-stmt-octet-listp-of-append-right
  (implies (fn-cbor-octet-listp (append a b))
           (fn-cbor-octet-listp b))
  :hints (("Goal" :induct (append a b)))
  :rule-classes nil)

(defthm fn-stmt-prechecked-rest-is-octet-list
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*)
                (fn-cbor-result-okp
                 (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*)))
           (fn-cbor-octet-listp
            (fn-cbor-result-rest
             (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*))))
  :hints (("Goal"
           :use ((:instance fn-stmt-prechecked-reencode-prefix)
                 (:instance fn-stmt-octet-listp-of-append-right
                  (a (fn-cbor-encode
                      (fn-cbor-result-value
                       (fn-cbor-decode-prechecked
                        octets *fn-cbor-max-bytes*))))
                  (b (fn-cbor-result-rest
                      (fn-cbor-decode-prechecked
                       octets *fn-cbor-max-bytes*)))))
           :in-theory (disable fn-cbor-decode fn-cbor-decode-bounded
                               fn-cbor-decode-prechecked fn-cbor-encode
                               fn-stmt-decode-prechecked-is-legacy
                               fn-stmt-prechecked-reencode-prefix))))

(defthm fn-stmt-prechecked-rest-length-bound
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*)
                (fn-cbor-result-okp
                 (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*)))
           (<= (len (fn-cbor-result-rest
                     (fn-cbor-decode-prechecked
                      octets *fn-cbor-max-bytes*)))
               *fn-cbor-max-input*))
  :hints (("Goal"
           :use ((:instance fn-stmt-prechecked-reencode-prefix))
           :in-theory (disable fn-cbor-decode fn-cbor-decode-bounded
                               fn-cbor-decode-prechecked fn-cbor-encode
                               fn-stmt-decode-prechecked-is-legacy
                               fn-stmt-prechecked-reencode-prefix)))
  :rule-classes :linear)

(defthm fn-stmt-prechecked-value-is-cbor-value
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp
                 (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*)))
           (fn-cbor-valuep
            (fn-cbor-result-value
             (fn-cbor-decode-prechecked octets *fn-cbor-max-bytes*))))
  :hints (("Goal"
           :in-theory (enable fn-cbor-decode-prechecked
                              fn-cbor-decode-unsigned
                              fn-cbor-decode-bytes-bounded
                              fn-cbor-valuep fn-cbor-valuep-bounded))))

(defthm fn-stmt-impl-decode-items-of-encode-items
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items-impl items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items-impl fuel (fn-stmt-encode-items-impl items))
                  (fn-stmt-ok items)))
  :hints (("Goal" :induct (fn-stmt-items-fuel-induct fuel items)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-decode-prechecked
                               fn-cbor-decode-bounded))))

(defthm fn-stmt-encode-items-of-decode-items-prechecked
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*)
                (fn-stmt-okp
                 (fn-stmt-decode-items-prechecked
                  fuel octets *fn-cbor-max-bytes*)))
           (equal (fn-stmt-encode-items-impl
                   (fn-stmt-value
                    (fn-stmt-decode-items-prechecked
                     fuel octets *fn-cbor-max-bytes*)))
                  octets))
  :hints (("Goal" :induct (fn-stmt-decode-items-prechecked
                            fuel octets *fn-cbor-max-bytes*)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-decode-prechecked
                               fn-cbor-decode-bounded
                               fn-stmt-decode-prechecked-is-legacy
                               fn-cbor-result-okp fn-cbor-result-value
                               fn-cbor-result-rest
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

(defthm fn-stmt-impl-encode-items-of-decode-items
  (implies (fn-stmt-okp (fn-stmt-decode-items-impl fuel octets))
           (equal (fn-stmt-encode-items-impl
                   (fn-stmt-value (fn-stmt-decode-items-impl fuel octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items-prechecked))
           :in-theory (enable fn-stmt-decode-items-impl
                              fn-stmt-decode-items-bounded-impl))))

(local (defthm fn-stmt-decode-ok-implies-octets
  (implies (fn-cbor-result-okp (fn-cbor-decode octets))
           (fn-cbor-octet-listp octets))
  :hints (("Goal" :in-theory (enable fn-cbor-decode)))))

(defthm fn-stmt-decode-items-prechecked-value-is-item-list
  (implies (and (fn-cbor-octet-listp octets)
                (<= (len octets) *fn-cbor-max-input*)
                (fn-stmt-okp
                 (fn-stmt-decode-items-prechecked
                  fuel octets *fn-cbor-max-bytes*)))
           (fn-stmt-item-listp
            (fn-stmt-value
             (fn-stmt-decode-items-prechecked
              fuel octets *fn-cbor-max-bytes*))))
  :hints (("Goal" :induct (fn-stmt-decode-items-prechecked
                            fuel octets *fn-cbor-max-bytes*)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-decode-prechecked
                               fn-cbor-decode-bounded
                               fn-stmt-decode-prechecked-is-legacy
                               fn-cbor-result-okp fn-cbor-result-value
                               fn-cbor-result-rest
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

(defthm fn-stmt-impl-decode-items-value-is-item-list
  (implies (fn-stmt-okp (fn-stmt-decode-items-impl fuel octets))
           (fn-stmt-item-listp
            (fn-stmt-value (fn-stmt-decode-items-impl fuel octets))))
  :hints (("Goal"
           :use ((:instance
                  fn-stmt-decode-items-prechecked-value-is-item-list))
           :in-theory (enable fn-stmt-decode-items-impl
                              fn-stmt-decode-items-bounded-impl))))

; These streaming bridge rules are local proof machinery.  Leaving them active
; after the three public sequence theorems makes unrelated statement proofs
; backchain into decoder length arithmetic.
(local (in-theory (disable fn-stmt-decode-prechecked-is-legacy
                           fn-stmt-prechecked-reencode-prefix
                           fn-stmt-prechecked-rest-is-octet-list
                           fn-stmt-prechecked-rest-length-bound
                           fn-stmt-prechecked-value-is-cbor-value
                           fn-stmt-encode-items-of-decode-items-prechecked
                           fn-stmt-decode-items-prechecked-value-is-item-list)))


; -----------------------------------------------------------------------------
; The implementation's side of the seam.  books/statement-seam.lisp
; constrains the item codec by five properties; these are the same five of
; the implementation, stated at the bounded decoder the seam constrains.  The
; seam's local witness and books/statement-attach.lisp's `defattach' both cite
; them, so the item codec's proofs are done once, here.

(defthm fn-stmt-impl-encode-items-of-atom
  (implies (not (consp items))
           (equal (fn-stmt-encode-items-impl items) nil))
  :rule-classes nil)

(defthm fn-stmt-impl-encode-items-of-cons
  (equal (fn-stmt-encode-items-impl (cons item items))
         (append (fn-cbor-encode item) (fn-stmt-encode-items-impl items)))
  :rule-classes nil
  ; One unfolding of the list encoder; the item encoder stays closed.  Open,
  ; it split on the item's kind and argument width (2.0 million steps, 9 s).
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-impl-decode-items-bounded-of-encode
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items-impl items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items-bounded-impl
                   fuel (fn-stmt-encode-items-impl items)
                   *fn-cbor-max-input* *fn-cbor-max-bytes*)
                  (fn-stmt-ok items)))
  :hints (("Goal" :use fn-stmt-impl-decode-items-of-encode-items
           :in-theory (e/d (fn-stmt-decode-items-impl)
                           (fn-stmt-impl-decode-items-of-encode-items
                            fn-stmt-decode-items-bounded-impl))))
  :rule-classes nil)

(defthm fn-stmt-impl-decode-items-bounded-canonical
  (implies (fn-stmt-okp (fn-stmt-decode-items-bounded-impl
                         fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
           (equal (fn-stmt-encode-items-impl
                   (fn-stmt-value (fn-stmt-decode-items-bounded-impl
                                   fuel octets
                                   *fn-cbor-max-input* *fn-cbor-max-bytes*)))
                  octets))
  :hints (("Goal" :use fn-stmt-impl-encode-items-of-decode-items
           :in-theory (e/d (fn-stmt-decode-items-impl)
                           (fn-stmt-impl-encode-items-of-decode-items
                            fn-stmt-decode-items-bounded-impl))))
  :rule-classes nil)

(defthm fn-stmt-impl-decode-items-bounded-items
  (implies (fn-stmt-okp (fn-stmt-decode-items-bounded-impl
                         fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
           (fn-stmt-item-listp
            (fn-stmt-value (fn-stmt-decode-items-bounded-impl
                            fuel octets
                            *fn-cbor-max-input* *fn-cbor-max-bytes*))))
  :hints (("Goal" :use fn-stmt-impl-decode-items-value-is-item-list
           :in-theory (e/d (fn-stmt-decode-items-impl)
                           (fn-stmt-impl-decode-items-value-is-item-list
                            fn-stmt-decode-items-bounded-impl))))
  :rule-classes nil)
