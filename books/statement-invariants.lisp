; Codec and signing invariants for fn statements (books/statement.lisp).
;
; Keystones:
;   fn-stmt-decode-items-of-encode-items / fn-stmt-encode-items-of-decode-items
;     the generic item-sequence codec is a round trip and every accepted input
;     re-encodes to itself (hypothesis-free canonicality);
;   fn-stmt-header-round-trip / fn-stmt-header-accepted-input-is-canonical
;   fn-stmt-round-trip / fn-stmt-accepted-input-is-canonical
;   fn-stmt-receipt-round-trip / fn-stmt-receipt-accepted-input-is-canonical
;     the same two directions lifted to headers, statements and receipts;
;   fn-stmt-sign-is-verified
;     a statement signed with seed sk verifies under (fn-sig-public-key sk),
;     the only use of the seam's correctness constraint;
;   fn-stmt-receipt-bytes-determine-term
;     equal receipt payload bytes carry equal policy terms.
; Nothing here relates two DIFFERENT byte strings with equal digests; that is
; A-CRYPTO and stays outside the logic.

(in-package "ACL2")
(include-book "statement")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals)))

;; Convergence (board, codecs ANSWER to substrate): re-open the codecs vocabulary this codec is built on.
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Result algebra

(defthm fn-stmt-okp-of-ok
  (fn-stmt-okp (fn-stmt-ok v)))
(defthm fn-stmt-value-of-ok
  (equal (fn-stmt-value (fn-stmt-ok v)) v))
(defthm fn-stmt-okp-of-ok2
  (fn-stmt-okp (fn-stmt-ok2 v r)))
(defthm fn-stmt-value-of-ok2
  (equal (fn-stmt-value (fn-stmt-ok2 v r)) v))
(defthm fn-stmt-rest-of-ok2
  (equal (fn-stmt-rest (fn-stmt-ok2 v r)) r))
(defthm fn-stmt-error-is-not-ok
  (not (fn-stmt-okp (fn-stmt-error c))))
(defthm fn-stmt-ok-is-not-error-shaped
  (and (not (equal (fn-stmt-ok v) (fn-stmt-error c)))
       (not (equal (fn-stmt-ok2 v r) (fn-stmt-error c)))))

(defthm fn-stmt-append-nil
  (implies (true-listp x)
           (equal (append x nil) x)))

(defthm fn-stmt-bytes-item-reconstruct
  (implies (fn-stmt-bytes-item-p x)
           (equal (cons :bytes (cdr x)) x)))

(defthm fn-stmt-uint-item-reconstruct
  (implies (fn-stmt-uint-item-p x)
           (equal (cons :uint (cdr x)) x)))

; A recognized item is a pair, so a consumer that has just checked one may
; take its `cdr'.  Both recognizers are withdrawn (`fn-stmt-internals'), so
; without these the check a caller makes in its own branch test does not
; decide the guard of the conjunct after it: measured on 2026-09-22, where
; `fn-hsig-article-event-snapshot-bindsp' (books/hybrid-store) checks
; `fn-stmt-bytes-item-p' and then takes the `cdr' of the same item.  Forward
; chaining, and outside the vocabulary below: the fact is wanted in the
; context of whatever goal already carries the check, and it puts no new rule
; on `consp' goals.
(defthm fn-stmt-uint-item-p-implies-consp
  (implies (fn-stmt-uint-item-p x) (consp x))
  :rule-classes :forward-chaining)

(defthm fn-stmt-bytes-item-p-implies-consp
  (implies (fn-stmt-bytes-item-p x) (consp x))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; The item-sequence codec

(defthm fn-stmt-encode-value-consp
  (implies (fn-cbor-valuep v)
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-argument))))

(defthm fn-stmt-encode-uint-item-consp
  (implies (and (consp v) (equal (car v) :uint)
                (natp (cdr v)) (<= (cdr v) *fn-cbor-max-uint*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode))))

(defthm fn-stmt-encode-bytes-item-consp
  (implies (and (consp v) (equal (car v) :bytes)
                (fn-cbor-octet-listp (cdr v))
                (<= (len (cdr v)) *fn-cbor-max-bytes*))
           (consp (fn-cbor-encode v)))
  :hints (("Goal" :use fn-stmt-encode-value-consp
           :in-theory (disable fn-stmt-encode-value-consp fn-cbor-encode))))

(defthm fn-stmt-consp-of-append
  (implies (consp a)
           (consp (append a b))))

(defthm fn-stmt-cbor-stream-round-trip
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
                            fn-record-cbor-stream-bytes-round-trip)))))

(defun fn-stmt-items-fuel-induct (fuel items)
  (if (consp items)
      (fn-stmt-items-fuel-induct (1- fuel) (cdr items))
    (list fuel items)))

(defthm fn-stmt-decode-ok-implies-octets
  (implies (fn-cbor-result-okp (fn-cbor-decode octets))
           (fn-cbor-octet-listp octets))
  :hints (("Goal" :in-theory (enable fn-cbor-decode))))

; The item-sequence codec's own facts -- the streaming round trip, its
; canonicality, the item-list shape of what it decodes -- are the constraints
; of books/statement-seam.lisp now, proved of the implementation in
; books/statement-codec.lisp; they keep their names there.

; -----------------------------------------------------------------------------
; Predecessor lists

(defthm fn-stmt-take-id-items-of-id-items
  (implies (fn-stmt-id-listp ids)
           (equal (fn-stmt-take-id-items (len ids)
                                         (append (fn-stmt-id-items ids) rest))
                  (fn-stmt-ok2 ids rest)))
  :hints (("Goal" :induct (fn-stmt-id-items ids))))

(defthm fn-stmt-take-id-items-reconstruct
  (implies (fn-stmt-okp (fn-stmt-take-id-items n items))
           (and (equal (append (fn-stmt-id-items
                                (fn-stmt-value (fn-stmt-take-id-items n items)))
                               (fn-stmt-rest (fn-stmt-take-id-items n items)))
                       items)
                (equal (len (fn-stmt-value (fn-stmt-take-id-items n items)))
                       (nfix n))
                (fn-stmt-id-listp
                 (fn-stmt-value (fn-stmt-take-id-items n items)))))
  :hints (("Goal" :induct (fn-stmt-take-id-items n items))))

(defthm fn-stmt-encode-items-of-id-items-bound
  (implies (fn-stmt-id-listp ids)
           (<= (len (fn-stmt-encode-items (fn-stmt-id-items ids)))
               (* 35 (len ids))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-stmt-id-items ids)
           :in-theory (disable fn-cbor-encode))))

; -----------------------------------------------------------------------------
; Kinds and header reconstruction

(defthm fn-stmt-kind-of-code-of-kind-code
  (implies (fn-stmt-kindp k)
           (equal (fn-stmt-kind-of-code (fn-stmt-kind-code k)) k)))

(defthm fn-stmt-kind-code-of-kind-of-code
  (implies (fn-stmt-kind-of-code n)
           (and (fn-stmt-kindp (fn-stmt-kind-of-code n))
                (equal (fn-stmt-kind-code (fn-stmt-kind-of-code n)) n))))

(defthm fn-stmt-kind-code-is-uint32
  (implies (fn-stmt-kindp k)
           (fn-record-uint32p (fn-stmt-kind-code k))))

(defthm fn-stmt-header-reconstruct
  (implies (and (true-listp h) (equal (len h) 6))
           (equal (fn-stmt-make-header
                   (fn-stmt-header-creator h) (fn-stmt-header-incarnation h)
                   (fn-stmt-header-sequence h) (fn-stmt-header-preds h)
                   (fn-stmt-header-kind h) (fn-stmt-header-ref h))
                  h))
  :hints (("Goal" :do-not-induct t
           :expand ((len h) (len (cdr h)) (len (cddr h)) (len (cdddr h))
                    (len (cddddr h)) (len (cdr (cddddr h)))
                    (len (cddr (cddddr h)))))))

(defthm fn-stmt-id-items-length
  (equal (len (fn-stmt-id-items ids)) (len ids))
  :hints (("Goal" :induct (fn-stmt-id-items ids))))

(defthm fn-stmt-header-items-length
  (implies (fn-stmt-headerp h)
           (equal (len (fn-stmt-header-items h))
                  (+ 7 (len (fn-stmt-header-preds h))))))

; -----------------------------------------------------------------------------
; Header: items both ways

(defthm fn-stmt-headerp-preds-bound
  (implies (fn-stmt-headerp h)
           (<= (len (fn-stmt-header-preds h)) *fn-stmt-max-preds*))
  :rule-classes :linear)

(defthm fn-stmt-header-of-items-of-header-items
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-of-items
                   (append (fn-stmt-header-items h) rest))
                  (fn-stmt-ok2 h rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stmt-take-id-items fn-stmt-id-items
                               fn-stmt-kind-of-code fn-stmt-kind-code
                               fn-stmt-make-header fn-stmt-kindp
                               fn-stmt-header-creator fn-stmt-header-incarnation
                               fn-stmt-header-sequence fn-stmt-header-preds
                               fn-stmt-header-kind fn-stmt-header-ref))))

(defthm fn-stmt-header-of-items-of-header-items-exact
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-of-items (fn-stmt-header-items h))
                  (fn-stmt-ok2 h nil)))
  :hints (("Goal"
           :use ((:instance fn-stmt-header-of-items-of-header-items (rest nil)))
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp
                               fn-stmt-header-of-items-of-header-items))))

(defthm fn-stmt-header-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-header-of-items items))
           (and (fn-stmt-headerp (fn-stmt-value (fn-stmt-header-of-items items)))
                (equal (append (fn-stmt-header-items
                                (fn-stmt-value (fn-stmt-header-of-items items)))
                               (fn-stmt-rest (fn-stmt-header-of-items items)))
                       items)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stmt-take-id-items fn-stmt-id-items
                               fn-stmt-kind-of-code fn-stmt-kind-code
                               fn-stmt-kindp
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

; -----------------------------------------------------------------------------
; Header bytes

(defthm fn-stmt-header-encoding-bound
  (implies (fn-stmt-headerp h)
           (<= (len (fn-stmt-encode-items (fn-stmt-header-items h))) 655))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-header-round-trip
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-decode-exact (fn-stmt-header-encode h))
                  (fn-stmt-ok h)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-header-items h))
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-encoding-bound)
                 (:instance fn-stmt-header-items-length)
                 (:instance fn-stmt-headerp-preds-bound))
           :in-theory (disable fn-stmt-header-items fn-stmt-headerp
                               fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-header-encoding-bound
                               fn-stmt-header-items-length))))

(defthm fn-stmt-header-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-header-decode-exact octets))
           (equal (fn-stmt-header-encode
                   (fn-stmt-value (fn-stmt-header-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-header-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-header-items fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                               fn-stmt-headerp
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-header-of-items-sound))))

(defthm fn-stmt-header-encode-injective
  (implies (and (fn-stmt-headerp h1)
                (fn-stmt-headerp h2)
                (equal (fn-stmt-header-encode h1) (fn-stmt-header-encode h2)))
           (equal h1 h2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-stmt-header-round-trip (h h1))
                 (:instance fn-stmt-header-round-trip (h h2)))
           :in-theory (disable fn-stmt-header-round-trip
                               fn-stmt-header-decode-exact
                               fn-stmt-header-encode fn-stmt-headerp))))

; The content id is, by definition, the tagged digest of the canonical header
; bytes.  Stated so the name says exactly that and nothing more.
(defthm fn-stmt-content-id-unfolds
  (equal (fn-stmt-content-id h)
         (fn-digest (fn-digest-tagged-preimage *fn-stmt-id-tag*
                                               (fn-stmt-header-encode h)))))

; -----------------------------------------------------------------------------
; Whole statement

(defthm fn-stmt-reconstruct
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (fn-stmt-make (fn-stmt-header s) (fn-stmt-payload s)
                                (fn-stmt-signature s))
                  s))
  :hints (("Goal" :do-not-induct t
           :expand ((len s) (len (cdr s)) (len (cddr s))
                    (len (cdddr s))))))

(defthm fn-stmt-items-length
  (implies (fn-stmt-p s)
           (<= (len (fn-stmt-items s)) 25))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-stmt-header-items fn-stmt-headerp
                                      fn-stmt-header fn-stmt-header-preds))))

(defthm fn-stmt-encoding-bound
  (implies (fn-stmt-p s)
           (<= (len (fn-stmt-encode-items (fn-stmt-items s))) 12949))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode fn-stmt-header-items
                                      fn-stmt-headerp fn-stmt-header
                                      fn-stmt-header-preds))))

(defthm fn-stmt-of-items-of-items
  (implies (fn-stmt-p s)
           (equal (fn-stmt-of-items (fn-stmt-items s))
                  (fn-stmt-ok s)))
    :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp fn-stmt-payload-ref
                               fn-stmt-make fn-stmt-header fn-stmt-payload
                               fn-stmt-signature fn-stmt-header-ref
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

(defthm fn-stmt-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stmt-decode-exact (fn-stmt-encode s))
                  (fn-stmt-ok s)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-items s))
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-encoding-bound)
                 (:instance fn-stmt-items-length))
           :in-theory (disable fn-stmt-items fn-stmt-p
                               fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-encoding-bound
                               fn-stmt-items-length))))

; Generic list facts used by the parser soundness proofs: a list known to have
; exactly two (four) elements is the list of them.
(local (defthm fn-stmt-two-list-reconstruct
  (implies (and (consp x) (consp (cdr x)) (not (cddr x)))
           (equal (list (car x) (cadr x)) x))))

(local (defthm fn-stmt-four-list-reconstruct
  (implies (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))
                (not (cddddr x)))
           (equal (list (car x) (cadr x) (caddr x) (cadddr x)) x))))

(defthm fn-stmt-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-of-items items))
           (and (fn-stmt-p (fn-stmt-value (fn-stmt-of-items items)))
                (equal (fn-stmt-items (fn-stmt-value (fn-stmt-of-items items)))
                       items)))
  :hints (("Goal"
           :use ((:instance fn-stmt-header-of-items-sound))
           :in-theory (disable fn-stmt-header-of-items fn-stmt-header-items
                               fn-stmt-headerp fn-stmt-payload-ref
                               fn-stmt-header-of-items-sound))))

(defthm fn-stmt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-decode-exact octets))
           (equal (fn-stmt-encode (fn-stmt-value (fn-stmt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-items fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp fn-stmt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-of-items-sound))))

; -----------------------------------------------------------------------------
; Signing

(defthm fn-stmt-payload-ref-is-digest
  (fn-digest-octetsp (fn-stmt-payload-ref payload))
  :hints (("Goal" :in-theory (e/d (fn-stmt-payload-ref fn-digest-tagged)
                                  (fn-digest-tagged-preimage fn-digest-octetsp)))))

(defthm fn-stmt-sign-is-verified
  (implies (and (fn-sig-seed-p sk)
                (fn-digest-octetsp creator)
                (fn-record-uint32p incarnation)
                (fn-record-uint32p sequence)
                (fn-stmt-predsp preds)
                (fn-stmt-kindp kind)
                (fn-stmt-payloadp payload))
           (fn-stmt-verifiedp
            (fn-stmt-sign sk creator incarnation sequence preds kind payload)
            (fn-sig-public-key sk)))
  :hints (("Goal"
           :in-theory (disable fn-digest-tagged fn-digest-tagged-preimage
                               fn-stmt-header-encode fn-stmt-content-id
                               fn-stmt-signing-preimage fn-stmt-payload-ref
                               fn-digest-octetsp fn-stmt-predsp fn-stmt-kindp
                               fn-record-uint32p fn-sig-signature-p))))

; -----------------------------------------------------------------------------
; Receipts

(defthm fn-stmt-receipt-reconstruct
  (implies (and (true-listp r) (equal (len r) 4))
           (equal (fn-stmt-make-receipt
                   (fn-stmt-receipt-subject r) (fn-stmt-receipt-obligation r)
                   (fn-stmt-receipt-policy-id r) (fn-stmt-receipt-evidence r))
                  r))
  :hints (("Goal" :do-not-induct t
           :expand ((len r) (len (cdr r)) (len (cddr r)) (len (cdddr r))
                    (len (cddddr r))))))

(defthm fn-stmt-receipt-items-are-items
  (implies (fn-stmt-receipt-p r)
           (fn-stmt-item-listp (fn-stmt-receipt-items r))))

(defthm fn-stmt-receipt-encoding-bound
  (implies (fn-stmt-receipt-p r)
           (<= (len (fn-stmt-encode-items (fn-stmt-receipt-items r))) 364))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-stmt-receipt-of-items-of-receipt-items
  (implies (fn-stmt-receipt-p r)
           (equal (fn-stmt-receipt-of-items (fn-stmt-receipt-items r))
                  (fn-stmt-ok r)))
    :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stmt-make-receipt fn-stmt-receipt-subject
                               fn-stmt-receipt-obligation
                               fn-stmt-receipt-policy-id
                               fn-stmt-receipt-evidence
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))

(defthm fn-stmt-receipt-items-length
  (equal (len (fn-stmt-receipt-items r)) 4))

(defthm fn-stmt-receipt-round-trip
  (implies (fn-stmt-receipt-p r)
           (equal (fn-stmt-receipt-decode-exact (fn-stmt-receipt-encode r))
                  (fn-stmt-ok r)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-receipt-items r))
                            (fuel 4))
                 (:instance fn-stmt-receipt-encoding-bound))
           :in-theory (disable fn-stmt-receipt-items fn-stmt-receipt-p
                               fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-receipt-encoding-bound))))

(defthm fn-stmt-receipt-of-items-sound
  (implies (fn-stmt-okp (fn-stmt-receipt-of-items items))
           (and (fn-stmt-receipt-p
                 (fn-stmt-value (fn-stmt-receipt-of-items items)))
                (equal (fn-stmt-receipt-items
                        (fn-stmt-value (fn-stmt-receipt-of-items items)))
                       items))))

(defthm fn-stmt-receipt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-receipt-decode-exact octets))
           (equal (fn-stmt-receipt-encode
                   (fn-stmt-value (fn-stmt-receipt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items (fuel 4))
                 (:instance fn-stmt-receipt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items 4 octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-receipt-items fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                               fn-stmt-receipt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-receipt-of-items-sound))))

(defthm fn-stmt-receipt-encode-injective
  (implies (and (fn-stmt-receipt-p r1)
                (fn-stmt-receipt-p r2)
                (equal (fn-stmt-receipt-encode r1) (fn-stmt-receipt-encode r2)))
           (equal r1 r2))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-stmt-receipt-round-trip (r r1))
                 (:instance fn-stmt-receipt-round-trip (r r2)))
           :in-theory (disable fn-stmt-receipt-round-trip
                               fn-stmt-receipt-decode-exact
                               fn-stmt-receipt-encode fn-stmt-receipt-p))))

; A receipt's payload bytes fix its policy term: the same bytes never carry two
; terms.  The step from payload bytes to the header's `ref` is a digest and
; therefore A-CRYPTO; see specs/policy.md.
(defthm fn-stmt-receipt-bytes-determine-term
  (implies (and (fn-stmt-receipt-p r1)
                (fn-stmt-receipt-p r2)
                (equal (fn-stmt-receipt-encode r1) (fn-stmt-receipt-encode r2)))
           (equal (fn-stmt-receipt-term r1) (fn-stmt-receipt-term r2)))
  :rule-classes nil
  :hints (("Goal" :use fn-stmt-receipt-encode-injective
           :in-theory (disable fn-stmt-receipt-encode fn-stmt-receipt-p))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The keystones below stay enabled on include; everything else this book
; proves is proof vocabulary and is withdrawn under `fn-stmt-invariants-vocabulary',
; which a book inside this cluster enables locally in one line.
;
; * fn-stmt-header-round-trip
; * fn-stmt-header-accepted-input-is-canonical
; * fn-stmt-round-trip
; * fn-stmt-accepted-input-is-canonical
; * fn-stmt-receipt-round-trip
; * fn-stmt-receipt-accepted-input-is-canonical
; * fn-stmt-sign-is-verified
; * fn-stmt-header-encoding-bound
; * fn-stmt-encoding-bound
; * fn-stmt-receipt-encoding-bound
; * fn-stmt-header-of-items-sound
; * fn-stmt-of-items-sound
; * fn-stmt-receipt-of-items-sound
; * fn-stmt-payload-ref-is-digest

(deftheory fn-stmt-invariants-vocabulary
  '(
    fn-stmt-okp-of-ok
    fn-stmt-value-of-ok
    fn-stmt-okp-of-ok2
    fn-stmt-value-of-ok2
    fn-stmt-rest-of-ok2
    fn-stmt-error-is-not-ok
    fn-stmt-ok-is-not-error-shaped
    fn-stmt-append-nil
    fn-stmt-bytes-item-reconstruct
    fn-stmt-uint-item-reconstruct
    fn-stmt-encode-value-consp
    fn-stmt-encode-uint-item-consp
    fn-stmt-encode-bytes-item-consp
    fn-stmt-consp-of-append
    fn-stmt-cbor-stream-round-trip
    fn-stmt-encode-items-of-append
    fn-stmt-decode-items-of-encode-items
    fn-stmt-encode-items-of-decode-items
    fn-stmt-decode-ok-implies-octets
    fn-stmt-decode-items-value-is-item-list
    fn-stmt-decode-items-bounded-of-encode
    fn-stmt-decode-items-bounded-canonical
    fn-stmt-decode-items-bounded-items
    fn-stmt-take-id-items-of-id-items
    fn-stmt-take-id-items-reconstruct
    fn-stmt-encode-items-of-id-items-bound
    fn-stmt-kind-of-code-of-kind-code
    fn-stmt-kind-code-of-kind-of-code
    fn-stmt-kind-code-is-uint32
    fn-stmt-header-reconstruct
    fn-stmt-id-items-length
    fn-stmt-header-items-length
    fn-stmt-headerp-preds-bound
    fn-stmt-header-of-items-of-header-items
    fn-stmt-header-of-items-of-header-items-exact
    fn-stmt-content-id-unfolds
    fn-stmt-reconstruct
    fn-stmt-items-length
    fn-stmt-of-items-of-items
    fn-stmt-receipt-reconstruct
    fn-stmt-receipt-items-are-items
    fn-stmt-receipt-of-items-of-receipt-items
    fn-stmt-receipt-items-length
    (:d fn-stmt-items-fuel-induct)))

(in-theory (disable fn-stmt-invariants-vocabulary))
