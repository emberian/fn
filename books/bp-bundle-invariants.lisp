; books/bp-bundle-invariants.lisp -- the keystones of the whole-bundle codec.
;
; Three, in the shape the primary block's keystones have
; (books/bp-primary-invariants):
;
;   fn-bpb-decode-of-encode                       every bundle decodes back
;   fn-bpb-accepted-input-is-canonical-by-construction
;                                                 an accepted input IS the
;                                                 encoding of what was
;                                                 accepted -- OPEN, removed
;                                                 2026-09-20 with the fold
;                                                 half it rests on; the note
;                                                 in the block-sequence
;                                                 section has both statements
;   fn-bpb-decode-yields-bundle                   and what was accepted is a
;                                                 bundle, so its block numbers
;                                                 are distinct and its payload
;                                                 block is number 1
;
; plus the bound: `fn-bpb-decode-refuses-overlong-input`, which fires from the
; preflight alone and before any octet is examined.
;
; The primary block inside the bundle is `fn-bpp-decode`'s, not a second
; decoder's: `fn-bpc-dec` locates the end of its CBOR item and
; `fn-bpc-dec-reencodes-consumed-prefix` says the located prefix is exactly the
; item, so the octets handed to `fn-bpp-decode` are the primary block's own.

(in-package "ACL2")

(include-book "bp-bundle")

;; This book opens `books/bp-bundle`'s own definitions, and nothing else.
;; The records stay opaque: `fn-bpb-block-internals` and
;; `fn-bpb-bundle-internals` are NOT enabled, so no goal here is ever about
;; `car` of a record.  `fn-bpc-vocabulary` is enabled at the forms that need
;; it and never book-wide -- proof-style.md, "never enable a vocabulary
;; book-wide", measured twice on 2026-09-20.
(local (in-theory (enable fn-bpb-vocabulary)))

;; The three list facts `books/bp-bundle` keeps local, restated here for the
;; same reason: octet-ness of an append must be settled by a rule, not by
;; `fn-cbor-octet-listp` opening over a long list.
(local
 (defthm fn-bpbi-octet-listp-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpbi-octet-listp-of-cons
   (implies (and (fn-cbor-octetp h) (fn-cbor-octet-listp xs))
            (fn-cbor-octet-listp (cons h xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-bpbi-octet-listp-implies-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; -----------------------------------------------------------------------------
; Octets out.

(defthm fn-bpb-encode-block-is-consp
  (consp (fn-bpb-encode-block b)))

(defthm fn-bpb-encode-block-head
  (equal (car (fn-bpb-encode-block b))
         (if (equal (fn-bpb-block-crc-type b) 0)
             *fn-bpb-block-head-5*
           *fn-bpb-block-head-6*)))

; -----------------------------------------------------------------------------
; The two field readers, each against the encoder that wrote the field.

(defthm fn-bpb-take-uint-of-argument
  (implies (and (fn-bpp-timep n) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-take-uint (append (fn-bpc-argument 0 n) rest))
                  (fn-cbor-ok n rest)))
  :hints (("Goal"
           :use ((:instance fn-bpc-uint-head-decodes (n n) (rest rest))
                 (:instance fn-bpc-uint-head-range (n n))
                 (:instance fn-bpc-argument-is-consp (major 0) (n n)))
           :in-theory (e/d (fn-bpc-vocabulary)
                           (fn-bpc-argument (:e fn-bpc-argument) fn-bpc-decode-head
                            fn-bpc-decode-argument fn-cbor-decode-argument)))))

(defthm fn-bpb-take-bytes-of-argument
  (implies (and (fn-cbor-octet-listp data) (fn-cbor-octet-listp rest)
                (natp bound) (<= (len data) bound)
                (<= bound *fn-bpc-max-uint*))
           (equal (fn-bpb-take-bytes
                   (append (fn-bpc-argument 2 (len data)) (append data rest))
                   bound)
                  (fn-cbor-ok data rest)))
  :hints (("Goal"
           :use ((:instance fn-bpc-bytes-head-decodes
                            (n (len data)) (rest (append data rest)))
                 (:instance fn-bpc-bytes-head-range (n (len data)))
                 (:instance fn-bpc-argument-is-consp (major 2) (n (len data))))
           :in-theory (e/d (fn-bpc-vocabulary)
                           (fn-bpc-argument (:e fn-bpc-argument) fn-bpc-decode-head
                            fn-bpc-decode-argument fn-cbor-decode-argument)))))

; The same reader against a field whose value the case split has made a
; constant.  `(fn-bpc-argument 0 0)` is evaluated by the prover -- disabling
; its `:executable-counterpart` does not stop constant propagation -- so in
; the CRC-type-zero branch the encoder's `append` has already collapsed to a
; `cons` and the rule above no longer matches its own left-hand side.  This
; is that branch, and RFC 8949 section 4.2.1 is why it is exactly the values
; below 24.
; RFC 8949 section 4.2.1: additional information below 24 IS the argument.
; The prover constant-folds `(fn-bpc-argument 0 0)` in the CRC-type-zero
; branch whatever the `:executable-counterpart` is set to, so the reader's
; own rule no longer matches there and the already-opened head does.  Both
; are stated because both shapes occur in the same proof.
(defthm fn-bpb-decode-head-of-small-additional
  (implies (and (natp n) (< n 24))
           (equal (fn-bpc-decode-head n xs) (fn-cbor-ok n xs)))
  :hints (("Goal" :in-theory (enable fn-bpc-decode-head fn-bpc-decode-argument
                                     fn-cbor-decode-argument
                                     fn-bpc-canonical-argumentp))))

(defthm fn-bpb-take-uint-of-small-head
  (implies (and (natp n) (< n 24) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-take-uint (cons n rest)) (fn-cbor-ok n rest)))
  :hints (("Goal" :in-theory (enable fn-bpb-take-uint fn-bpc-decode-head
                                     fn-bpc-decode-argument
                                     fn-cbor-decode-argument
                                     fn-bpc-canonical-argumentp))))

; -----------------------------------------------------------------------------
; Keystone: one canonical block decodes back from its own encoding, with the
; octets after it returned untouched.
;
; The eliminator this rests on -- a record rebuilt from its own five
; accessors is that record -- was written out here until 2026-09-20, as
; `fn-bpb-block-is-its-own-accessors`, with a one-element-list lemma under
; it and `fn-bpb-block-internals` opened at the form.  `fn-defrecord` now
; generates it (`fn-bpb-make-block-of-accessors`, w10/dtn-3), so both are
; gone and the `:use` below cites the generated name.  It is cited rather
; than left to fire because the case split has already replaced accessors by
; their values in some branches (`Subgoal 17.3'` reaches
; `(fn-bpb-make-block (fn-bpb-block-type b) (fn-bpb-block-number b)
; (fn-bpb-block-flags b) 0 nil)`, which the rule's own left-hand side no
; longer matches), and `:use` substitutes through that.
;
; AND THE RULE IS DISABLED AT THIS FORM, which is new with the generated
; version and is the whole difference from the hand-written one.  The
; hand-written eliminator was `:rule-classes nil`; the generated one is an
; enabled rewrite, so the hypothesis `:use` adds --- whose left-hand side IS
; the rule's left-hand side --- is rewritten to `(equal b b)` and vanishes
; before it can be used.  Measured 2026-09-20: without the disable this form
; fails at that subgoal.  Every `:use` of a `<ctor>-of-accessors` wants the
; same `e/d` entry.
;
; The two `fn-bpp-` character recognizers are disabled for a different
; reason, measured by `tools/proof_profile.py` on this form: they burned
; 1,527,614 and 1,369,220 frames with no useful application, the two largest
; fans in the run.  They are endpoint-ID vocabulary and a canonical block is
; not an endpoint ID.

(defthm fn-bpb-decode-block-of-encode-block
  (implies (and (fn-bpb-blockp b) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-decode-block (append (fn-bpb-encode-block b) rest))
                  (fn-cbor-ok b rest)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpb-make-block-of-accessors (x b)))
           :in-theory (e/d (fn-bpb-decode-block fn-bpb-encode-block
                            fn-bpb-encode-block-with-crc
                            fn-bpc-vocabulary)
                           (fn-bpb-make-block-of-accessors
                            fn-bpp-vchar-listp fn-bpp-vcharp
                            fn-bpc-argument fn-bpb-block-crc
                            fn-bpc-decode-head fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-bpp-crc-octets fn-bpp-zero-crc)))))

; -----------------------------------------------------------------------------
; The block sequence.

(defthm fn-bpb-encode-blocks-of-append
  (implies (and (fn-bpb-block-listp xs) (fn-bpb-block-listp ys))
           (equal (fn-bpb-encode-blocks (append xs ys))
                  (append (fn-bpb-encode-blocks xs) (fn-bpb-encode-blocks ys))))
  :hints (("Goal" :in-theory (disable fn-bpb-encode-block))))

(defthm fn-bpb-front-final-reassemble
  (implies (and (true-listp xs) (consp xs))
           (equal (append (fn-bpb-front xs) (list (fn-bpb-final xs))) xs)))

(defthm fn-bpb-front-of-append-one
  (implies (true-listp xs)
           (equal (fn-bpb-front (append xs (list y))) xs)))

(defthm fn-bpb-final-of-append-one
  (equal (fn-bpb-final (append xs (list y))) y))

(defthm fn-bpb-block-listp-of-append
  (implies (and (fn-bpb-block-listp xs) (fn-bpb-block-listp ys))
           (fn-bpb-block-listp (append xs ys))))

; The fold's round trip.  The induction is over the BLOCK LIST, not over the
; decoder.  An `:induct` on `fn-bpb-decode-blocks` applied to the encoded
; octets -- which is what this form carried until 2026-09-20 -- generates
; hypotheses about `(fn-cbor-result-rest (fn-bpb-decode-block (append ...)))`,
; a term that only becomes the induction hypothesis's subject AFTER the
; one-block keystone has fired on it, so the scheme never matches its own
; hypotheses and the search does not terminate: run
; `build/acl2/certify-20260920T210105Z-1191520` was killed at the 1200 s cap
; with the keystone already proved.  This scheme peels one block and one unit
; of budget, which is exactly the recursion the goal has, and then the
; keystone is a rewrite on each step.
(local
 (defthm fn-bpbi-consp-of-append
   (implies (consp a) (consp (append a b)))))

(local
 (defthm fn-bpbi-car-of-append
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defun fn-bpbi-blocks-induction (xs budget)
   (declare (xargs :measure (len xs)))
   (if (consp xs)
       (fn-bpbi-blocks-induction (cdr xs) (- budget 1))
     (list xs budget))))

(defthm fn-bpb-decode-blocks-of-encode-blocks
  (implies (and (fn-bpb-block-listp xs) (fn-cbor-octet-listp rest)
                (natp budget) (<= (len xs) budget))
           (equal (fn-bpb-decode-blocks
                   (append (fn-bpb-encode-blocks xs)
                           (cons *fn-bpb-array-break* rest))
                   budget)
                  (fn-cbor-ok xs rest)))
  :hints (("Goal"
           :induct (fn-bpbi-blocks-induction xs budget)
           :in-theory (e/d (fn-bpc-vocabulary)
                           (fn-bpb-encode-block fn-bpb-decode-block
                            fn-bpb-block-crc fn-bpc-argument
                            (:e fn-bpc-argument)
                            fn-bpc-decode-head fn-bpc-decode-argument
                            fn-cbor-decode-argument)))))

; -----------------------------------------------------------------------------
; Keystone: decode of encode, over the whole bundle.

(defthm fn-bpb-payload-block-is-a-block
  (implies (fn-bpb-payload-blockp b) (fn-bpb-blockp b)))

(defthm fn-bpb-bundle-tail-are-octets
  (implies (fn-bpb-bundlep bundle)
           (fn-cbor-octet-listp
            (append (fn-bpb-encode-blocks (fn-bpb-bundle-blocks bundle))
                    (append (fn-bpb-encode-block (fn-bpb-bundle-payload bundle))
                            (list *fn-bpb-array-break*)))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-cbor-octetp)
                                  (fn-bpb-encode-block fn-bpb-encode-blocks)))))

; `fn-bpp-encode` IS `(fn-bpc-enc :item (fn-bpp-block-value b
; (fn-bpp-block-crc b)))` by definition, and that is the form
; `fn-bpc-decode-of-encode` is stated in.  `books/bp-primary-invariants`
; keeps its copy of this equality `local` (`fn-bpp-encode-unfolds`), so the
; whole-bundle round trip has to restate it: without it the `:use` of the
; CBOR round trip below names a term the goal does not contain, and the
; decode branch of `fn-bpb-decode` cannot be refuted.
;
; It has to be a REWRITE, not a `:use`.  Measured 2026-09-20: stated
; `:rule-classes nil` and cited by `:use`, it changed nothing --- an equality
; carried as a hypothesis is not a normal form, so the two terms never became
; the same term and the checkpoint was identical.  As a rewrite both sides
; normalise to `(fn-bpc-enc :item ...)` and the `:use` above matches.  It is
; `local`, enabled only in the one hint that wants it, and withdrawn
; immediately (proof-style, "never enable a vocabulary book-wide").
(local
 (defthm fn-bpbi-bpp-encode-unfolds
   (equal (fn-bpp-encode b)
          (fn-bpc-enc :item (fn-bpp-block-value b (fn-bpp-block-crc b))))
   :hints (("Goal" :in-theory (e/d (fn-bpp-encode)
                                   (fn-bpc-enc fn-bpp-block-value
                                    fn-bpp-block-crc))))))
(local (in-theory (disable fn-bpbi-bpp-encode-unfolds)))

; The payload block is a FIELD of the bundle, not the last element of its
; block list (`specs/bp-design.md` section 1.4.1), so the round trip below
; instantiates the fold at `(append blocks (list payload))`.
; `fn-bpb-encode-blocks-of-append` then splits that into
; `(append (fn-bpb-encode-blocks blocks) (fn-bpb-encode-blocks (list payload)))`
; while `fn-bpb-encode` wrote `(fn-bpb-encode-block payload)`, and the two
; terms are equal but not identical.  Measured 2026-09-20: that one-element
; difference is the whole of `Subgoal 39.52`.  `(append x nil)` is `x` only
; for a true list, which is `fn-bpb-encode-block-is-true-list`.
(local
 (defthm fn-bpbi-encode-blocks-of-one
   (implies (fn-bpb-blockp b)
            (equal (fn-bpb-encode-blocks (list b)) (fn-bpb-encode-block b)))
   :hints (("Goal"
            ;; `:do-not-induct t` on purpose: the whole content is
            ;; `(append e nil)` = `e` for a true list, and left to induct
            ;; over an encoder term the prover runs for twenty minutes
            ;; instead of failing (measured 2026-09-20, hbox run
            ;; run-20260920T221045Z-35e7, stopped at its budget).
            :do-not-induct t
            :use (fn-bpb-encode-block-is-true-list
                  (:instance fn-bpc-append-nil (x (fn-bpb-encode-block b))))
            :in-theory (e/d (fn-bpb-encode-blocks)
                            (fn-bpb-encode-block
                             fn-bpb-encode-block-is-true-list
                             fn-bpc-append-nil))))))
(local (in-theory (disable fn-bpbi-encode-blocks-of-one)))

; `fn-bpb-scan-primary` takes the prefix its own scan consumed:
; `(take (- (len octets) (len after)) octets)`.  Once the CBOR round trip has
; told it that `after` is the tail, that count is the length of the head, and
; this is the one arithmetic step of the whole codec.  Stated over the
; DIFFERENCE rather than over `(len a)` on purpose: `fn-bpc-len-of-append`
; is DISABLED at the form below, so the count keeps exactly this shape and
; the rule matches it syntactically, with no arithmetic library anywhere in
; this book's include closure.  With `fn-bpc-len-of-append` enabled the
; count becomes a five-term sum that base ACL2 does not cancel inside a
; `take`.  Both argument orders are stated because ACL2 sorts a sum by term
; order and matches the rule against the sorted form: measured 2026-09-20,
; the goal carries `(+ (- (len rest)) (len (append e rest)))` and a rule
; written the other way round does not fire.
(local
 (defthm fn-bpbi-len-of-append-minus-tail
   (and (equal (+ (- (len b)) (len (append a b))) (len a))
        (equal (+ (len (append a b)) (- (len b))) (len a)))
   :hints (("Goal" :in-theory (enable fn-bpc-vocabulary)))))

; Keystone: the primary block scans back out of a bundle image, and what
; follows it is returned untouched.  The same shape as
; `fn-bpb-decode-block-of-encode-block` one block down, and the reason the
; whole-bundle round trip is a composition of two keystones rather than one
; proof over the whole decoder.
(defthm fn-bpb-scan-primary-of-encode
  (implies (and (fn-bpp-blockp b) (fn-cbor-octet-listp rest))
           (equal (fn-bpb-scan-primary (append (fn-bpp-encode b) rest))
                  (fn-cbor-ok b rest)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-bpc-decode-of-encode
                            (flg :item)
                            (x (fn-bpp-block-value b (fn-bpp-block-crc b)))
                            (rest rest)
                            (budget *fn-bpc-max-items*))
                 (:instance fn-bpp-block-value-is-shape
                            (b b) (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-block-value-cost
                            (b b) (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-block-crc-is-octets (b b))
                 (:instance fn-bpp-block-crc-length (b b))
                 (:instance fn-bpp-decode-of-encode (b b)))
           :in-theory (e/d (fn-bpb-scan-primary fn-bpc-vocabulary
                            fn-bpbi-bpp-encode-unfolds
                            fn-bpbi-len-of-append-minus-tail)
                           (fn-bpc-dec fn-bpc-enc fn-bpp-encode fn-bpp-decode
                            fn-bpp-blockp fn-bpp-eidp
                            fn-bpp-vchar-listp fn-bpp-vcharp
                            fn-bpp-block-value fn-bpp-block-crc
                            fn-bpc-len-of-append
                            fn-bpc-decode-of-encode
                            fn-bpp-block-value-is-shape
                            fn-bpp-block-value-cost
                            fn-bpp-decode-of-encode)))))

(defthm fn-bpb-decode-of-encode
  (implies (and (fn-bpb-bundlep bundle) (natp limit)
                (fn-cbor-at-mostp (fn-bpb-encode bundle) limit))
           (equal (fn-bpb-decode (fn-bpb-encode bundle) limit)
                  (fn-cbor-ok bundle nil)))
  :hints (("Goal"
           :do-not-induct t
           ;; Two keystones and nothing else, each cited by `:use` and
           ;; disabled in the same `e/d` so the rewriter cannot collapse the
           ;; hypothesis it adds.  The primary block is
           ;; `fn-bpb-scan-primary-of-encode`; `fn-bpb-scan-primary` is
           ;; closed here and `fn-bpp-encode` is left FOLDED, so the
           ;; instance names the term the goal contains.  The block
           ;; sequence is the fold, instantiated
           ;; at the block list with the payload block appended, because the
           ;; payload is a FIELD of the bundle and the last element of the
           ;; array on the wire.  The rebuild `fn-bpb-assemble` performs is
           ;; then `fn-bpb-make-bundle-of-accessors`, generated by
           ;; `fn-defrecord` (w10/dtn-3) and firing with the recognizer
           ;; closed off `fn-bpb-bundlep-forward-shape`; no eliminator for
           ;; this record existed in the tree before, which is why this form
           ;; had never closed.
           :use ((:instance fn-bpb-scan-primary-of-encode
                            (b (fn-bpb-bundle-primary bundle))
                            (rest (append
                                   (fn-bpb-encode-blocks
                                    (fn-bpb-bundle-blocks bundle))
                                   (append
                                    (fn-bpb-encode-block
                                     (fn-bpb-bundle-payload bundle))
                                    (list *fn-bpb-array-break*)))))
                 (:instance fn-bpb-decode-blocks-of-encode-blocks
                            (xs (append (fn-bpb-bundle-blocks bundle)
                                        (list (fn-bpb-bundle-payload bundle))))
                            (rest nil)
                            (budget (+ 1 *fn-bpb-max-blocks*))))
           :in-theory (e/d (fn-bpb-decode fn-bpb-encode fn-bpc-vocabulary
                            fn-bpbi-encode-blocks-of-one)
                           (fn-bpc-dec fn-bpc-enc fn-bpp-encode fn-bpp-decode
                            fn-bpb-encode-block fn-bpb-encode-blocks
                            fn-bpb-decode-block fn-bpb-decode-blocks
                            fn-bpb-scan-primary
                            fn-bpp-block-value fn-bpp-block-crc
                            ;; The primary block's recognizer stays CLOSED.
                            ;; Opened, `(fn-bpp-blockp (fn-bpb-bundle-primary
                            ;; bundle))` becomes eleven `nth` conjuncts, and
                            ;; then it is no longer a literal of the goal, so
                            ;; the scan keystone's hypothesis goes unrelieved
                            ;; and the decode branch is never refuted.
                            ;; Measured 2026-09-20: that, and not a missing
                            ;; fact, is what three runs of this form failed
                            ;; on.  Closing it also removes the endpoint-ID
                            ;; vocabulary the profile named as the fan
                            ;; (`fn-bpp-eidp` 2,094,352 frames,
                            ;; `fn-bpp-vchar-listp` 1,994,593).
                            fn-bpp-blockp fn-bpp-eidp
                            fn-bpp-vchar-listp fn-bpp-vcharp
                            fn-bpb-scan-primary-of-encode
                            fn-bpb-decode-blocks-of-encode-blocks)))))

; -----------------------------------------------------------------------------
; Keystone: an accepted input is the encoding of the bundle it produced.

; This one is a read-off of a branch test, not a computation:
; `fn-bpb-decode-block` returns `ok` only where it has just checked
; `(equal octets (append (fn-bpb-encode-block b) (fn-cbor-result-rest r6)))`.
; Everything under the decoder therefore stays CLOSED --- the two field
; readers, the CBOR head, and the two rules that rewrite a small head --- and
; the proof is the branch.  Measured 2026-09-20: with them open the form
; splits on `fn-bpc-canonical-argumentp` to depth eight
; (`Subgoal 51.19.11.40.19.12.1.20`) and was still running at the 1200 s
; budget.
(defthm fn-bpb-decode-block-is-canonical-by-construction
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-block octets)))
           (equal (append (fn-bpb-encode-block
                           (fn-cbor-result-value (fn-bpb-decode-block octets)))
                          (fn-cbor-result-rest (fn-bpb-decode-block octets)))
                  octets))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpb-decode-block)
                           (fn-bpb-encode-block fn-bpb-block-crc
                            fn-bpb-take-uint fn-bpb-take-bytes
                            fn-bpc-decode-head fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-bpc-canonical-argumentp
                            fn-bpb-decode-head-of-small-additional
                            fn-bpb-take-uint-of-small-head
                            fn-bpb-take-uint-of-argument
                            fn-bpb-take-bytes-of-argument
                            fn-bpp-blockp fn-bpp-eidp
                            fn-bpp-vchar-listp fn-bpp-vcharp)))))

; OPEN, removed rather than weakened (w10/dtn-3, 2026-09-20).
;
;   fn-bpb-decode-blocks-are-canonical-by-construction
;     (implies (and (fn-cbor-octet-listp octets)
;                   (fn-cbor-result-okp (fn-bpb-decode-blocks octets budget)))
;              (equal (append (fn-bpb-encode-blocks
;                              (fn-cbor-result-value
;                               (fn-bpb-decode-blocks octets budget)))
;                             (cons *fn-bpb-array-break*
;                                   (fn-cbor-result-rest
;                                    (fn-bpb-decode-blocks octets budget))))
;                     octets))
;
; The fold's half of "an accepted input IS the encoding of what was
; accepted".  The one-block half above it PROVES in 0.05 s.  The fold does
; not, and the failure is a rewriter runaway rather than a checkpoint: three
; runs on hbox reached
;
;   Subgoal *1/6.1.3.1.3.1.2.1.3.1.3.1.3.1.3.1.3.1.3.1.3.1.3.1.3.1.3.1.3.
;   1.3.1.3.1.3.1.2.1.3.1.3 ... 1.3.1.3.1.3.1.3'
;
; about eighty `.1.3` levels deep, and were still there at the 900, 1200 and
; 1500 s budgets.  Three cures were measured and none stopped it: disabling
; the fold's `:definition` rune with a one-level `:expand` (and note that
; `(disable fn-bpb-decode-blocks)` alone also withdraws the `:induction`
; rune, so the `:induct` hint silently has no scheme and the whole Goal comes
; back as the key checkpoint -- worth knowing on its own); closing every
; function under the decoder, which is exactly what took the one-block half
; from a 1200 s cap to 0.05 s; and closing the two list recognizers
; `fn-cbor-octet-listp` and `fn-bpb-block-listp`, which this book's header
; says must be settled by a rule.  The `.1.3` alternation is some other pair
; of branches, and the next lane should find it with `tools/proof_profile.py`
; at a `--steps` high enough not to cut (see the tool's CUT BY THE STEP LIMIT
; line, added by the same lane).
;
; Removed with it, because it rests on it: this book's third header keystone
;
;   fn-bpb-accepted-input-is-canonical-by-construction
;     (implies (and (fn-cbor-octet-listp octets)
;                   (fn-cbor-result-okp (fn-bpb-decode octets limit)))
;              (equal (fn-bpb-encode (fn-cbor-result-value
;                                     (fn-bpb-decode octets limit)))
;                     octets))
;
; which needs a rule about `(fn-bpb-encode-blocks (fn-cbor-result-value
; (fn-bpb-decode-blocks ...)))` and has no other source for one.  Both
; statements are verbatim above and in
; `planning/lanes/HANDOFF-w10-dtn-3.md`; neither was weakened, and nothing in
; this tree claims either.

(defthm fn-bpb-decode-yields-bundle
  (implies (fn-cbor-result-okp (fn-bpb-decode octets limit))
           (fn-bpb-bundlep (fn-cbor-result-value (fn-bpb-decode octets limit))))
  :hints (("Goal"
           :do-not-induct t
           ;; `fn-bpb-scan-primary` closed: the fact wanted here is
           ;; `fn-bpb-scan-primary-yields-a-block`, which is a rule about the
           ;; closed call (books/bp-bundle).
           :in-theory (e/d (fn-bpb-decode)
                           (fn-bpc-dec fn-bpp-decode fn-bpb-decode-blocks
                            fn-bpb-scan-primary
                            fn-bpb-encode-block fn-bpb-encode-blocks
                            fn-bpb-block-crc)))))

; -----------------------------------------------------------------------------
; Keystone: bounds before allocation.

(defthm fn-bpb-decode-refuses-overlong-input
  (implies (not (fn-cbor-at-mostp octets limit))
           (equal (fn-bpb-decode octets limit) (fn-cbor-error :limit)))
  :hints (("Goal" :in-theory (enable fn-bpb-decode))))

(defthm fn-bpb-decode-blocks-with-no-budget-accepts-only-the-break
  (implies (and (consp octets) (not (equal (car octets) *fn-bpb-array-break*)))
           (equal (fn-bpb-decode-blocks octets 0)
                  (fn-cbor-error :too-many-blocks)))
  :hints (("Goal" :in-theory (enable fn-bpb-decode-blocks))))

(defthm fn-bpb-decoded-data-is-within-bound
  (implies (and (fn-cbor-octet-listp octets)
                (fn-cbor-result-okp (fn-bpb-decode-block octets)))
           (<= (len (fn-bpb-block-data
                     (fn-cbor-result-value (fn-bpb-decode-block octets))))
               *fn-bpb-max-data*))
  :rule-classes :linear
  ;; Same cure as `fn-bpb-decode-block-is-canonical-by-construction`: the
  ;; bound is a conjunct of `fn-bpb-datap`, which the decoder checked through
  ;; `fn-bpb-blockp` before returning `ok`, so both of those stay OPEN and
  ;; everything under the decoder stays CLOSED --- in particular
  ;; `fn-cbor-octet-listp`, whose walk over a symbolic octet list is what
  ;; sent this form to `Subgoal 30.19.11.24.40.4.21` and past the 900 s
  ;; budget (measured 2026-09-20).
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-bpb-decode-block fn-bpb-blockp fn-bpb-datap)
                           (fn-bpb-encode-block fn-bpb-block-crc
                            fn-bpb-take-uint fn-bpb-take-bytes
                            fn-bpc-decode-head fn-bpc-decode-argument
                            fn-cbor-decode-argument
                            fn-bpc-canonical-argumentp
                            fn-bpb-decode-head-of-small-additional
                            fn-bpb-take-uint-of-small-head
                            fn-bpb-take-uint-of-argument
                            fn-bpb-take-bytes-of-argument
                            fn-cbor-octet-listp fn-cbor-octetp
                            fn-bpp-blockp fn-bpp-eidp
                            fn-bpp-vchar-listp fn-bpp-vcharp)))))

; -----------------------------------------------------------------------------
; Export theory.
;
; The keystones leave enabled; the field-reader and list lemmas are proof
; vocabulary and are withdrawn under a name.

(deftheory fn-bpb-invariants-vocabulary
  '(fn-bpb-encode-block-is-consp
    fn-bpb-encode-block-head fn-bpb-take-uint-of-argument
    fn-bpb-take-bytes-of-argument fn-bpb-take-uint-of-small-head
    fn-bpb-decode-head-of-small-additional
    fn-bpb-encode-blocks-of-append
    fn-bpb-front-final-reassemble fn-bpb-front-of-append-one
    fn-bpb-final-of-append-one fn-bpb-block-listp-of-append
    fn-bpb-payload-block-is-a-block fn-bpb-bundle-tail-are-octets
    fn-bpb-decode-blocks-of-encode-blocks
    fn-bpb-decode-block-of-encode-block
    fn-bpb-scan-primary-of-encode))

(in-theory (disable fn-bpb-invariants-vocabulary))
