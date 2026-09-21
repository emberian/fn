; fn: statements, the block-shaped signed unit every portable fact is made of.
;
; A statement header mirrors the dregg blocklace `Block` (creator, sequence,
; predecessors, payload, signature; ~/dev/breadstuffs/blocklace/src/lib.rs
; `pub struct Block`, and Dregg2/Authority/Blocklace.lean:58 `structure Block`)
; with two fn additions: an explicit origin `incarnation` (D10) and a `kind`.
;   header = (creator incarnation sequence preds kind ref)
;     creator     32-octet principal id (books/principal.lisp)
;     incarnation uint32, the creator's restore/clone generation
;     sequence    uint32, the creator's counter within an incarnation
;     preds       list of at most 16 distinct 32-octet content ids
;     kind        one of :article :policy :receipt :succession
;     ref         32-octet payload reference, fn-digest-tagged of the payload
;   statement = (header payload signature)
;
; Bytes.  Every structure is a sequence of items from the bounded CBOR profile
; of books/cbor.lisp (uint32 and definite byte strings), concatenated.  One
; generic item-sequence codec (`fn-stmt-encode-items` / `fn-stmt-decode-items`)
; turns bytes into a list of items under an explicit item budget and input
; cap; each structure is then a pure projection to and from an item list.
; Header layout, in order:
;   uint 1 (schema)  bstr creator  uint incarnation  uint sequence
;   uint pred-count  bstr pred[0..count-1]  uint kind-code  bstr ref
; A whole statement appends  bstr payload  bstr signature.
;
; Identity and signing (mirrors `Block::id` and `Block::sign_by`, lib.rs):
;   content id        = fn-digest-tagged "fn-statement-v1" (header bytes)
;   signing preimage  = "fn-statement-sig-v1" tag || content id
;   signature         = fn-sig-sign sk (signing preimage)
; The signature covers the header only; the header binds the payload through
; `ref`.  Whether a second payload with the same `ref` exists is A-CRYPTO.
;
; Receipts (kind :receipt) carry a payload naming the subject, the obligation
; and the POLICY TERM (policy statement id, evidence digest) that authorised
; them, never a boolean; see books/policy.lisp and specs/policy.md.
;
; No definition here reads external Lisp data; bounds are checked before any
; item is parsed or allocated.

(in-package "ACL2")
(include-book "crypto-seam")


;; Convergence: the codecs cluster withdraws its proof vocabulary on export;
;; re-open it locally (agreed on the deputy board, codecs ANSWER to substrate).
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals)))

; -----------------------------------------------------------------------------
; Bounds and tags

(defconst *fn-stmt-schema-version* 1)
(defconst *fn-stmt-max-preds* 16)
(defconst *fn-stmt-max-header-items* 24)
(defconst *fn-stmt-max-header-octets* 1024)
(defconst *fn-stmt-max-payload-octets* 8192)
(defconst *fn-stmt-max-items* 26)
(defconst *fn-stmt-max-octets* 16384)
(defconst *fn-stmt-max-obligation-octets* 256)
(defconst *fn-stmt-max-receipt-octets* 512)

(defconst *fn-stmt-id-tag* (fn-record-string-octets "fn-statement-v1"))
(defconst *fn-stmt-sig-tag* (fn-record-string-octets "fn-statement-sig-v1"))
(defconst *fn-stmt-payload-tag* (fn-record-string-octets "fn-payload-v1"))

; -----------------------------------------------------------------------------
; Result records.  (:ok value) / (:ok value rest) / (:error code).  Accessors
; are total so every consumer has guard T.

(defun fn-stmt-ok (value)
  (declare (xargs :guard t))
  (list :ok value))
(defun fn-stmt-ok2 (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))
(defun fn-stmt-error (code)
  (declare (xargs :guard t))
  (list :error code))
(defun fn-stmt-okp (r)
  (declare (xargs :guard t))
  (and (consp r) (equal (car r) :ok)))
(defun fn-stmt-value (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r))) (car (cdr r)) nil))
(defun fn-stmt-rest (r)
  (declare (xargs :guard t))
  (if (and (consp r) (consp (cdr r)) (consp (cdr (cdr r))))
      (car (cdr (cdr r)))
    nil))

; -----------------------------------------------------------------------------
; Item sequences

(defun fn-stmt-item-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-valuep (car xs))
           (fn-stmt-item-listp (cdr xs)))
    (null xs)))

(defun fn-stmt-encode-items (items)
  (declare (xargs :guard (fn-stmt-item-listp items)))
  (if (consp items)
      (append (fn-cbor-encode (car items))
              (fn-stmt-encode-items (cdr items)))
    nil))

(defthm fn-stmt-encode-items-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-encode-items items))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-encode-items-is-true-list
  (true-listp (fn-stmt-encode-items items)))

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

(defun fn-stmt-decode-prefix-items-bounded
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
(defun fn-stmt-decode-items-bounded (fuel octets outer-budget item-budget)
  (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                              (natp item-budget))))
  ; One bounded preflight and octet validation occur before recursive parsing.
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (fn-stmt-error :limit)
    (if (atom octets)
        (if (null octets)
            (fn-stmt-ok nil)
          (fn-stmt-error :malformed))
      (fn-stmt-decode-items-prechecked fuel octets item-budget))))

(defun fn-stmt-decode-items (fuel octets)
  (declare (xargs :guard (natp fuel)))
  ; Compatibility wrapper for every pre-existing statement caller.
  (fn-stmt-decode-items-bounded fuel octets
                                *fn-cbor-max-input* *fn-cbor-max-bytes*))


; -----------------------------------------------------------------------------
; Item shapes

(defun fn-stmt-uint-item-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) :uint)
       (fn-record-uint32p (cdr x))))

(defun fn-stmt-bytes-item-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) :bytes)
       (fn-cbor-octet-listp (cdr x))))

(defun fn-stmt-id-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-digest-octetsp (car xs))
           (fn-stmt-id-listp (cdr xs)))
    (null xs)))

(defun fn-stmt-no-duplicatesp (xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-stmt-no-duplicatesp (cdr xs)))
    t))

(defthm fn-stmt-id-listp-implies-true-listp
  (implies (fn-stmt-id-listp xs) (true-listp xs)))

(defun fn-stmt-id-items (ids)
  (declare (xargs :guard (true-listp ids)))
  (if (consp ids)
      (cons (cons :bytes (car ids))
            (fn-stmt-id-items (cdr ids)))
    nil))

; Take exactly n 32-octet byte items: (:ok ids rest) or (:error code).
(defun fn-stmt-take-id-items (n items)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (fn-stmt-ok2 nil items)
    (if (not (and (consp items)
                  (fn-stmt-bytes-item-p (car items))
                  (fn-digest-octetsp (cdr (car items)))))
        (fn-stmt-error :id-item)
      (let ((tail (fn-stmt-take-id-items (1- n) (cdr items))))
        (if (not (fn-stmt-okp tail))
            tail
          (fn-stmt-ok2 (cons (cdr (car items)) (fn-stmt-value tail))
                       (fn-stmt-rest tail)))))))

(defthm fn-stmt-take-id-items-value-is-true-list
  (implies (fn-stmt-okp (fn-stmt-take-id-items n items))
           (true-listp (fn-stmt-value (fn-stmt-take-id-items n items)))))

; -----------------------------------------------------------------------------
; Kinds

(defconst *fn-stmt-kinds*
  '((:article . 1) (:policy . 2) (:receipt . 3) (:succession . 4)))

(defun fn-stmt-kindp (k)
  (declare (xargs :guard t))
  (if (assoc-equal k *fn-stmt-kinds*) t nil))

(defun fn-stmt-kind-code (k)
  (declare (xargs :guard (fn-stmt-kindp k)))
  (cdr (assoc-equal k *fn-stmt-kinds*)))

(defun fn-stmt-kind-of-code (n)
  (declare (xargs :guard t))
  (cond ((equal n 1) :article)
        ((equal n 2) :policy)
        ((equal n 3) :receipt)
        ((equal n 4) :succession)
        (t nil)))

(defthm fn-stmt-kindp-is-non-nil
  (implies (fn-stmt-kindp k) k)
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; Header

(defun fn-stmt-make-header (creator incarnation sequence preds kind ref)
  (declare (xargs :guard t))
  (list creator incarnation sequence preds kind ref))

(defun fn-stmt-header-creator (h)
  (declare (xargs :guard (true-listp h)))
  (car h))
(defun fn-stmt-header-incarnation (h)
  (declare (xargs :guard (true-listp h)))
  (car (cdr h)))
(defun fn-stmt-header-sequence (h)
  (declare (xargs :guard (true-listp h)))
  (car (cdr (cdr h))))
(defun fn-stmt-header-preds (h)
  (declare (xargs :guard (true-listp h)))
  (car (cdr (cdr (cdr h)))))
(defun fn-stmt-header-kind (h)
  (declare (xargs :guard (true-listp h)))
  (car (cdr (cdr (cdr (cdr h))))))
(defun fn-stmt-header-ref (h)
  (declare (xargs :guard (true-listp h)))
  (car (cdr (cdr (cdr (cdr (cdr h)))))))

(defun fn-stmt-predsp (preds)
  (declare (xargs :guard t))
  (and (fn-stmt-id-listp preds)
       (<= (len preds) *fn-stmt-max-preds*)
       (fn-stmt-no-duplicatesp preds)))

(defun fn-stmt-headerp (h)
  (declare (xargs :guard t))
  (and (true-listp h)
       (equal (len h) 6)
       (fn-digest-octetsp (fn-stmt-header-creator h))
       (fn-record-uint32p (fn-stmt-header-incarnation h))
       (fn-record-uint32p (fn-stmt-header-sequence h))
       (fn-stmt-predsp (fn-stmt-header-preds h))
       (fn-stmt-kindp (fn-stmt-header-kind h))
       (fn-digest-octetsp (fn-stmt-header-ref h))))

(defun fn-stmt-header-items (h)
  (declare (xargs :guard (fn-stmt-headerp h)))
  (append (list (cons :uint *fn-stmt-schema-version*)
                (cons :bytes (fn-stmt-header-creator h))
                (cons :uint (fn-stmt-header-incarnation h))
                (cons :uint (fn-stmt-header-sequence h))
                (cons :uint (len (fn-stmt-header-preds h))))
          (fn-stmt-id-items (fn-stmt-header-preds h))
          (list (cons :uint (fn-stmt-kind-code (fn-stmt-header-kind h)))
                (cons :bytes (fn-stmt-header-ref h)))))

; Parse a header off the front of an item list: (:ok header rest).
(defun fn-stmt-header-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-stmt-okp fn-stmt-value fn-stmt-rest
                                                     fn-stmt-take-id-items
                                                     fn-digest-octetsp
                                                     fn-record-uint32p
                                                     fn-cbor-octet-listp
                                                     fn-stmt-kind-of-code
                                                     fn-stmt-no-duplicatesp
                                                     fn-stmt-make-header)))))
  (if (not (and (consp items)
                (equal (car items) (cons :uint *fn-stmt-schema-version*))))
      (fn-stmt-error :unknown-version)
    (let ((i1 (cdr items)))
      (if (not (and (consp i1)
                    (fn-stmt-bytes-item-p (car i1))
                    (fn-digest-octetsp (cdr (car i1)))))
          (fn-stmt-error :creator)
        (let ((creator (cdr (car i1)))
              (i2 (cdr i1)))
          (if (not (and (consp i2) (fn-stmt-uint-item-p (car i2))))
              (fn-stmt-error :incarnation)
            (let ((incarnation (cdr (car i2)))
                  (i3 (cdr i2)))
              (if (not (and (consp i3) (fn-stmt-uint-item-p (car i3))))
                  (fn-stmt-error :sequence)
                (let ((sequence (cdr (car i3)))
                      (i4 (cdr i3)))
                  (if (not (and (consp i4)
                                (fn-stmt-uint-item-p (car i4))
                                (<= (cdr (car i4)) *fn-stmt-max-preds*)))
                      (fn-stmt-error :pred-count)
                    (let ((taken (fn-stmt-take-id-items (cdr (car i4))
                                                        (cdr i4))))
                      (if (not (fn-stmt-okp taken))
                          taken
                        (let ((preds (fn-stmt-value taken))
                              (i5 (fn-stmt-rest taken)))
                          (if (not (fn-stmt-no-duplicatesp preds))
                              (fn-stmt-error :duplicate-pred)
                            (if (not (and (consp i5)
                                          (fn-stmt-uint-item-p (car i5))
                                          (fn-stmt-kind-of-code
                                           (cdr (car i5)))))
                                (fn-stmt-error :kind)
                              (let ((kind (fn-stmt-kind-of-code
                                           (cdr (car i5))))
                                    (i6 (cdr i5)))
                                (if (not (and (consp i6)
                                              (fn-stmt-bytes-item-p (car i6))
                                              (fn-digest-octetsp
                                               (cdr (car i6)))))
                                    (fn-stmt-error :ref)
                                  (fn-stmt-ok2
                                   (fn-stmt-make-header
                                    creator incarnation sequence
                                    preds kind (cdr (car i6)))
                                   (cdr i6)))))))))))))))))))

(defthm fn-stmt-id-items-of-id-list-are-items
  (implies (fn-stmt-id-listp ids)
           (fn-stmt-item-listp (fn-stmt-id-items ids))))

(defthm fn-stmt-item-listp-of-append
  (implies (true-listp a)
           (equal (fn-stmt-item-listp (append a b))
                  (and (fn-stmt-item-listp a)
                       (fn-stmt-item-listp b)))))

(defthm fn-stmt-header-items-are-items
  (implies (fn-stmt-headerp h)
           (fn-stmt-item-listp (fn-stmt-header-items h)))
  :hints (("Goal" :in-theory (enable fn-stmt-kind-code))))

(defthm fn-stmt-header-items-is-true-list
  (true-listp (fn-stmt-header-items h)))

(defun fn-stmt-header-encode (h)
  (declare (xargs :guard t))
  (if (fn-stmt-headerp h)
      (fn-stmt-encode-items (fn-stmt-header-items h))
    nil))

(defun fn-stmt-header-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stmt-max-header-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items *fn-stmt-max-header-items* octets)))
      (if (not (fn-stmt-okp items))
          items
        (let ((parsed (fn-stmt-header-of-items (fn-stmt-value items))))
          (if (not (fn-stmt-okp parsed))
              parsed
            (if (not (null (fn-stmt-rest parsed)))
                (fn-stmt-error :trailing)
              (fn-stmt-ok (fn-stmt-value parsed)))))))))

; -----------------------------------------------------------------------------
; Identity, payload binding and signing

(defthm fn-stmt-header-encode-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-header-encode h))
  :hints (("Goal" :in-theory (disable fn-cbor-encode fn-stmt-header-items
                                      fn-stmt-headerp))))

(defun fn-stmt-content-id (h)
  (declare (xargs :guard t))
  (fn-digest-tagged *fn-stmt-id-tag* (fn-stmt-header-encode h)))

(defthm fn-stmt-content-id-is-digest
  (and (fn-digest-octetsp (fn-stmt-content-id h))
       (fn-cbor-octet-listp (fn-stmt-content-id h))
       (true-listp (fn-stmt-content-id h))))

(defun fn-stmt-signing-preimage (h)
  (declare (xargs :guard t))
  (fn-digest-tagged-preimage *fn-stmt-sig-tag* (fn-stmt-content-id h)))

(defthm fn-stmt-signing-preimage-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-signing-preimage h))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defun fn-stmt-payloadp (p)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp p)
       (<= (len p) *fn-stmt-max-payload-octets*)))

(defun fn-stmt-payload-ref (payload)
  (declare (xargs :guard (fn-cbor-octet-listp payload)))
  (fn-digest-tagged *fn-stmt-payload-tag* payload))

(defun fn-stmt-make (header payload signature)
  (declare (xargs :guard t))
  (list header payload signature))

(defun fn-stmt-header (s)
  (declare (xargs :guard (true-listp s)))
  (car s))
(defun fn-stmt-payload (s)
  (declare (xargs :guard (true-listp s)))
  (car (cdr s)))
(defun fn-stmt-signature (s)
  (declare (xargs :guard (true-listp s)))
  (car (cdr (cdr s))))

(defun fn-stmt-p (s)
  (declare (xargs :guard t))
  (and (true-listp s)
       (equal (len s) 3)
       (fn-stmt-headerp (fn-stmt-header s))
       (fn-stmt-payloadp (fn-stmt-payload s))
       (equal (fn-stmt-payload-ref (fn-stmt-payload s))
              (fn-stmt-header-ref (fn-stmt-header s)))
       (fn-sig-signature-p (fn-stmt-signature s))))

(defun fn-stmt-creator (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-header-creator (fn-stmt-header s)))
(defun fn-stmt-incarnation (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-header-incarnation (fn-stmt-header s)))
(defun fn-stmt-sequence (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-header-sequence (fn-stmt-header s)))
(defun fn-stmt-preds (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-header-preds (fn-stmt-header s)))
(defun fn-stmt-kind (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-header-kind (fn-stmt-header s)))
(defun fn-stmt-id (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (fn-stmt-content-id (fn-stmt-header s)))

; Build a header whose ref binds `payload`, then sign it with seed `sk`.
(defun fn-stmt-sign (sk creator incarnation sequence preds kind payload)
  (declare (xargs :guard (fn-cbor-octet-listp payload)))
  (let ((header (fn-stmt-make-header creator incarnation sequence preds kind
                                     (fn-stmt-payload-ref payload))))
    (fn-stmt-make header payload
                  (fn-sig-sign sk (fn-stmt-signing-preimage header)))))

; A statement is verified under public key `pk` when it is well formed and
; its signature verifies under pk over its signing preimage.  Which pk is
; the creator's is the principal layer's job (books/principal.lisp).
(defun fn-stmt-verifiedp (s pk)
  (declare (xargs :guard t))
  (and (fn-stmt-p s)
       (fn-sig-public-key-p pk)
       (fn-sig-verify pk
                      (fn-stmt-signing-preimage (fn-stmt-header s))
                      (fn-stmt-signature s))))

; -----------------------------------------------------------------------------
; Whole-statement bytes: header items, then payload and signature.

(defun fn-stmt-items (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (append (fn-stmt-header-items (fn-stmt-header s))
          (list (cons :bytes (fn-stmt-payload s))
                (cons :bytes (fn-stmt-signature s)))))

(defthm fn-stmt-items-are-items
  (implies (fn-stmt-p s)
           (fn-stmt-item-listp (fn-stmt-items s)))
  :hints (("Goal" :in-theory (disable fn-stmt-header-items
                                      fn-stmt-headerp))))

(defun fn-stmt-encode (s)
  (declare (xargs :guard t))
  (if (fn-stmt-p s)
      (fn-stmt-encode-items (fn-stmt-items s))
    nil))

(defun fn-stmt-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-stmt-okp fn-stmt-value fn-stmt-rest
                                                     fn-stmt-header-of-items
                                                     fn-stmt-payloadp
                                                     fn-sig-signature-p
                                                     fn-stmt-p
                                                     fn-stmt-make
                                                     fn-cbor-octet-listp)))))
  (let ((parsed (fn-stmt-header-of-items items)))
    (if (not (fn-stmt-okp parsed))
        parsed
      (let ((header (fn-stmt-value parsed))
            (i1 (fn-stmt-rest parsed)))
        (if (not (and (consp i1)
                      (fn-stmt-bytes-item-p (car i1))
                      (fn-stmt-payloadp (cdr (car i1)))))
            (fn-stmt-error :payload)
          (let ((payload (cdr (car i1)))
                (i2 (cdr i1)))
            (if (not (and (consp i2)
                          (fn-stmt-bytes-item-p (car i2))
                          (fn-sig-signature-p (cdr (car i2)))))
                (fn-stmt-error :signature)
              (if (not (null (cdr i2)))
                  (fn-stmt-error :trailing)
                (let ((s (fn-stmt-make header payload (cdr (car i2)))))
                  (if (not (fn-stmt-p s))
                      (fn-stmt-error :payload-ref)
                    (fn-stmt-ok s)))))))))))

(defun fn-stmt-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stmt-max-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items *fn-stmt-max-items* octets)))
      (if (not (fn-stmt-okp items))
          items
        (fn-stmt-of-items (fn-stmt-value items))))))

; -----------------------------------------------------------------------------
; Receipt payloads: (subject obligation policy-id evidence)
;   subject    32-octet content id of what was accepted
;   obligation 1..256 octets, the obligation identity
;   policy-id  32-octet content id of the policy statement in force
;   evidence   32-octet digest of the evidence used to resolve that policy
; (policy-id . evidence) is the policy term (books/policy.lisp).  There is no
; decision field: the receipt says which policy authorised it, not "yes".

(defun fn-stmt-termp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (fn-digest-octetsp (car x))
       (fn-digest-octetsp (cdr x))))

(defun fn-stmt-make-receipt (subject obligation policy-id evidence)
  (declare (xargs :guard t))
  (list subject obligation policy-id evidence))
(defun fn-stmt-receipt-subject (r)
  (declare (xargs :guard (true-listp r)))
  (car r))
(defun fn-stmt-receipt-obligation (r)
  (declare (xargs :guard (true-listp r)))
  (car (cdr r)))
(defun fn-stmt-receipt-policy-id (r)
  (declare (xargs :guard (true-listp r)))
  (car (cdr (cdr r))))
(defun fn-stmt-receipt-evidence (r)
  (declare (xargs :guard (true-listp r)))
  (car (cdr (cdr (cdr r)))))

(defun fn-stmt-obligationp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (consp x)
       (<= (len x) *fn-stmt-max-obligation-octets*)))

(defun fn-stmt-receipt-p (r)
  (declare (xargs :guard t))
  (and (true-listp r)
       (equal (len r) 4)
       (fn-digest-octetsp (fn-stmt-receipt-subject r))
       (fn-stmt-obligationp (fn-stmt-receipt-obligation r))
       (fn-digest-octetsp (fn-stmt-receipt-policy-id r))
       (fn-digest-octetsp (fn-stmt-receipt-evidence r))))

(defun fn-stmt-receipt-term (r)
  (declare (xargs :guard (true-listp r)))
  (cons (fn-stmt-receipt-policy-id r) (fn-stmt-receipt-evidence r)))

(defun fn-stmt-receipt-items (r)
  (declare (xargs :guard (fn-stmt-receipt-p r)))
  (list (cons :bytes (fn-stmt-receipt-subject r))
        (cons :bytes (fn-stmt-receipt-obligation r))
        (cons :bytes (fn-stmt-receipt-policy-id r))
        (cons :bytes (fn-stmt-receipt-evidence r))))

(defun fn-stmt-receipt-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-stmt-okp fn-stmt-value fn-stmt-rest
                                                     fn-digest-octetsp
                                                     fn-cbor-octet-listp
                                                     fn-stmt-obligationp
                                                     fn-stmt-make-receipt)))))
  (if (not (and (consp items)
                (fn-stmt-bytes-item-p (car items))
                (fn-digest-octetsp (cdr (car items)))))
      (fn-stmt-error :subject)
    (let ((i1 (cdr items)))
      (if (not (and (consp i1)
                    (fn-stmt-bytes-item-p (car i1))
                    (fn-stmt-obligationp (cdr (car i1)))))
          (fn-stmt-error :obligation)
        (let ((i2 (cdr i1)))
          (if (not (and (consp i2)
                        (fn-stmt-bytes-item-p (car i2))
                        (fn-digest-octetsp (cdr (car i2)))))
              (fn-stmt-error :policy-id)
            (let ((i3 (cdr i2)))
              (if (not (and (consp i3)
                            (fn-stmt-bytes-item-p (car i3))
                            (fn-digest-octetsp (cdr (car i3)))))
                  (fn-stmt-error :evidence)
                (if (not (null (cdr i3)))
                    (fn-stmt-error :trailing)
                  (fn-stmt-ok (fn-stmt-make-receipt
                               (cdr (car items)) (cdr (car i1))
                               (cdr (car i2)) (cdr (car i3)))))))))))))

(defun fn-stmt-receipt-encode (r)
  (declare (xargs :guard t))
  (if (fn-stmt-receipt-p r)
      (fn-stmt-encode-items (fn-stmt-receipt-items r))
    nil))

(defun fn-stmt-receipt-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stmt-max-receipt-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items 4 octets)))
      (if (not (fn-stmt-okp items))
          items
        (fn-stmt-receipt-of-items (fn-stmt-value items))))))

; -----------------------------------------------------------------------------
; Record lemmas (docs/proof-style.md section 1).  Accessor of constructor,
; one per field, so nothing above this book opens a record.

(defthm fn-stmt-header-creator-of-fn-stmt-make-header
  (equal (fn-stmt-header-creator (fn-stmt-make-header creator incarnation sequence preds kind ref))
         creator))
(defthm fn-stmt-header-incarnation-of-fn-stmt-make-header
  (equal (fn-stmt-header-incarnation (fn-stmt-make-header creator incarnation sequence preds kind ref))
         incarnation))
(defthm fn-stmt-header-sequence-of-fn-stmt-make-header
  (equal (fn-stmt-header-sequence (fn-stmt-make-header creator incarnation sequence preds kind ref))
         sequence))
(defthm fn-stmt-header-preds-of-fn-stmt-make-header
  (equal (fn-stmt-header-preds (fn-stmt-make-header creator incarnation sequence preds kind ref))
         preds))
(defthm fn-stmt-header-kind-of-fn-stmt-make-header
  (equal (fn-stmt-header-kind (fn-stmt-make-header creator incarnation sequence preds kind ref))
         kind))
(defthm fn-stmt-header-ref-of-fn-stmt-make-header
  (equal (fn-stmt-header-ref (fn-stmt-make-header creator incarnation sequence preds kind ref))
         ref))

(defthm fn-stmt-header-of-fn-stmt-make
  (equal (fn-stmt-header (fn-stmt-make header payload signature))
         header))
(defthm fn-stmt-payload-of-fn-stmt-make
  (equal (fn-stmt-payload (fn-stmt-make header payload signature))
         payload))
(defthm fn-stmt-signature-of-fn-stmt-make
  (equal (fn-stmt-signature (fn-stmt-make header payload signature))
         signature))

(defthm fn-stmt-receipt-subject-of-fn-stmt-make-receipt
  (equal (fn-stmt-receipt-subject (fn-stmt-make-receipt subject obligation policy-id evidence))
         subject))
(defthm fn-stmt-receipt-obligation-of-fn-stmt-make-receipt
  (equal (fn-stmt-receipt-obligation (fn-stmt-make-receipt subject obligation policy-id evidence))
         obligation))
(defthm fn-stmt-receipt-policy-id-of-fn-stmt-make-receipt
  (equal (fn-stmt-receipt-policy-id (fn-stmt-make-receipt subject obligation policy-id evidence))
         policy-id))
(defthm fn-stmt-receipt-evidence-of-fn-stmt-make-receipt
  (equal (fn-stmt-receipt-evidence (fn-stmt-make-receipt subject obligation policy-id evidence))
         evidence))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; Records (header, statement, receipt), the parse-result vocabulary,
; the codec and the derived accessors are withdrawn; the item-list vocabulary
; the round-trip proofs induct on stays.
;
; Only the `:definition' rune is withdrawn, so type prescriptions and
; executable counterparts still decide ground terms.  A book inside this
; cluster that must open one of these enables `fn-stmt-internals' locally.

; The `true-listp'/`consp' backchaining rules below are withdrawn with the
; definitions: an includer that inherits them pays for them on every goal
; shaped like a list (docs/proof-style.md section 8).

(deftheory fn-stmt-internals
  '(
    (:d fn-stmt-ok)
    (:d fn-stmt-ok2)
    (:d fn-stmt-error)
    (:d fn-stmt-okp)
    (:d fn-stmt-value)
    (:d fn-stmt-rest)
    (:d fn-stmt-uint-item-p)
    (:d fn-stmt-bytes-item-p)
    (:d fn-stmt-kindp)
    (:d fn-stmt-kind-code)
    (:d fn-stmt-kind-of-code)
    (:d fn-stmt-make-header)
    (:d fn-stmt-header-creator)
    (:d fn-stmt-header-incarnation)
    (:d fn-stmt-header-sequence)
    (:d fn-stmt-header-preds)
    (:d fn-stmt-header-kind)
    (:d fn-stmt-header-ref)
    (:d fn-stmt-predsp)
    (:d fn-stmt-headerp)
    (:d fn-stmt-header-items)
    (:d fn-stmt-header-of-items)
    (:d fn-stmt-header-encode)
    (:d fn-stmt-header-decode-exact)
    (:d fn-stmt-content-id)
    (:d fn-stmt-signing-preimage)
    (:d fn-stmt-payloadp)
    (:d fn-stmt-payload-ref)
    (:d fn-stmt-make)
    (:d fn-stmt-header)
    (:d fn-stmt-payload)
    (:d fn-stmt-signature)
    (:d fn-stmt-p)
    (:d fn-stmt-creator)
    (:d fn-stmt-incarnation)
    (:d fn-stmt-sequence)
    (:d fn-stmt-preds)
    (:d fn-stmt-kind)
    (:d fn-stmt-id)
    (:d fn-stmt-sign)
    (:d fn-stmt-verifiedp)
    (:d fn-stmt-items)
    (:d fn-stmt-encode)
    (:d fn-stmt-of-items)
    (:d fn-stmt-decode-exact)
    (:d fn-stmt-termp)
    (:d fn-stmt-make-receipt)
    (:d fn-stmt-receipt-subject)
    (:d fn-stmt-receipt-obligation)
    (:d fn-stmt-receipt-policy-id)
    (:d fn-stmt-receipt-evidence)
    (:d fn-stmt-obligationp)
    (:d fn-stmt-receipt-p)
    (:d fn-stmt-receipt-term)
    (:d fn-stmt-receipt-items)
    (:d fn-stmt-receipt-of-items)
    (:d fn-stmt-receipt-encode)
    (:d fn-stmt-receipt-decode-exact)
    fn-stmt-id-listp-implies-true-listp
    fn-stmt-encode-items-is-true-list
    fn-stmt-header-items-is-true-list
    fn-stmt-take-id-items-value-is-true-list))

(in-theory (disable fn-stmt-internals))
