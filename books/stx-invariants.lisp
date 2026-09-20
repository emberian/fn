; fn: the carrier and verdict keystones.
;
; S1-1 (specs/substrate-transport.md section 6, PRF-019): the field codec is
; canonical.  Two theorems, and the second is the one that matters -- every
; accepted field value has exactly one canonical form, so a middle box cannot
; produce a second value that decodes to the same statement and split a
; reader population.  The canonical form is the whitespace-stripped value:
; RFC 5536 section 2.2 folding is legal and books/article.lisp's unfolded
; value retains the continuation WSP, so the field parser strips WSP and the
; theorem is stated about the stripped value.  Everything else about an
; accepted value -- alphabet, quantum, padding, padding bits, the detached
; item sequence -- is pinned exactly.
;
; S2-1 (PRF-020, in part): the verdict is computed from the statement's own
; octets.  fn-stx-verified-implies-signature-over-own-octets is the grounding
; theorem: a :verified verdict is backed by a key NAMED IN THIS NODE'S OWN
; KEYRING (the member-equal conjunct), a signature check over the statement's
; own signing preimage, and a `ref` recomputed from the receiver's own
; projection of the received octets.  The peer is not an argument to
; fn-stx-verdict, so no peer verdict can enter.
;
; What is NOT proved here, and is recorded open rather than weakened:
;   * the fn-peer-transfer companion of S2-1 (the host line).  It needs K1's
;     transit path, which does not exist at this revision; PRF-020 stays
;     planned.
;   * HEAD returns FN-Statement byte-identical.  The statement layer is pure
;     -- no transition in this cluster touches the stored octets -- but the
;     other half is a theorem in the nntp cluster about HEAD emitting the
;     retained header octets unchanged, and this lane edits no nntp book.
;     Board CHANGE w7/substrate-s1.
;   * the equality of fn-stx-authored-source with w4/post's injector-side
;     projection, which does not exist yet.
; What IS proved about the carrier's soundness is
; fn-stx-payload-ignores-the-carrier-field: attaching FN-Statement (or any
; field the injecting agent adds) anywhere in the header leaves the payload
; the signature covers unchanged, which is why attaching the field after
; signing is sound at all.

(in-package "ACL2")
(include-book "stx-verify")

; -----------------------------------------------------------------------------
; The detached encoding is the fn-stmt- encoding with the payload item removed.
; The wire adds base64 and folding ABOVE fn-stmt-encode and changes nothing
; below it (specs/substrate-transport.md section 1.2).

(defthm fn-stx-detached-encode-is-fn-stmt-encode-without-the-payload
  (implies (fn-stmt-p s)
           (and (equal (fn-stmt-encode s)
                       (append (fn-stmt-encode-items
                                (fn-stmt-header-items (fn-stmt-header s)))
                               (append (fn-cbor-encode (cons :bytes (fn-stmt-payload s)))
                                       (fn-cbor-encode (cons :bytes (fn-stmt-signature s))))))
                (equal (fn-stx-detached-encode s)
                       (append (fn-stmt-encode-items
                                (fn-stmt-header-items (fn-stmt-header s)))
                               (fn-cbor-encode (cons :bytes (fn-stmt-signature s)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stmt-encode) (:d fn-stmt-items) (:d fn-stmt-p)
                            (:d fn-stx-detached-encode)
                            (:d fn-stx-detached-encode-parts)
                            (:d fn-stx-detached-items)
                            fn-stmt-encode-items-of-append)
                           (fn-cbor-encode)))))

(defthm fn-stx-reattach-of-the-detached-parts
  (implies (fn-stmt-p s)
           (equal (fn-stx-reattach (fn-stmt-header s) (fn-stmt-signature s)
                                   (fn-stmt-payload s))
                  s))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable (:d fn-stx-reattach) (:d fn-stmt-p))
           :use ((:instance fn-stmt-reconstruct)))))

; -----------------------------------------------------------------------------
; Bounds, checked before any item is parsed.

(local (defthm fn-stx-len-of-append
         (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-stx-detached-items-length
  (implies (fn-stmt-headerp header)
           (<= (len (fn-stx-detached-items header signature))
               *fn-stx-max-detached-items*))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-detached-items)
                            fn-stmt-header-items-length
                            fn-stmt-headerp-preds-bound)
                           (fn-stmt-header-items fn-stmt-headerp)))))

(defthm fn-stx-detached-encoding-bound
  (implies (and (fn-stmt-headerp header) (fn-sig-signature-p signature))
           (<= (len (fn-stx-detached-encode-parts header signature)) 4760))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-detached-encode-parts)
                            (:d fn-stx-detached-items)
                            (:d fn-sig-signature-p)
                            fn-stmt-encode-items-of-append
                            fn-stmt-header-encoding-bound
                            fn-record-cbor-byte-encoding-bound)
                           (fn-cbor-encode fn-stmt-header-items fn-stmt-headerp)))))

(defthm fn-stx-detached-encode-parts-is-octet-list
  (fn-cbor-octet-listp (fn-stx-detached-encode-parts header signature))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-detached-encode-parts)) (fn-cbor-encode)))))

(defthm fn-stx-detached-encode-is-octet-list
  (fn-cbor-octet-listp (fn-stx-detached-encode s))
  :hints (("Goal" :in-theory (enable (:d fn-stx-detached-encode)))))

; -----------------------------------------------------------------------------
; The detached codec, both ways.

(defthm fn-stx-detached-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stx-detached-decode-exact (fn-stx-detached-encode s))
                  (fn-stx-ok (list (fn-stmt-header s) (fn-stmt-signature s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-detached-encode)
                            (:d fn-stx-detached-encode-parts)
                            (:d fn-stx-detached-decode-exact)
                            (:d fn-stx-detached-of-items)
                            (:d fn-stx-detached-items)
                            (:d fn-stmt-p)
                            (:d fn-stmt-bytes-item-p)
                            fn-cbor-at-mostp-from-length
                            fn-stmt-header-of-items-of-header-items
                            fn-stmt-okp-of-ok fn-stmt-value-of-ok
                            fn-stmt-okp-of-ok2 fn-stmt-value-of-ok2
                            fn-stmt-rest-of-ok2)
                           (fn-cbor-encode fn-stmt-header-items fn-stmt-headerp
                            fn-stmt-decode-items fn-stmt-header-of-items
                            fn-stmt-encode-items))
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stx-detached-items (fn-stmt-header s)
                                                          (fn-stmt-signature s)))
                            (fuel *fn-stx-max-detached-items*))
                 (:instance fn-stx-detached-encoding-bound
                            (header (fn-stmt-header s))
                            (signature (fn-stmt-signature s)))
                 (:instance fn-stx-detached-items-length
                            (header (fn-stmt-header s))
                            (signature (fn-stmt-signature s)))))))

(defthm fn-stx-detached-accepted-input-is-canonical
  (implies (fn-stx-okp (fn-stx-detached-decode-exact octets))
           (equal (fn-stx-detached-encode-parts
                   (fn-stx-val (fn-stx-detached-decode-exact octets))
                   (fn-stx-val2 (fn-stx-detached-decode-exact octets)))
                  octets))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-detached-decode-exact)
                            (:d fn-stx-detached-of-items)
                            (:d fn-stx-detached-encode-parts)
                            (:d fn-stx-detached-items)
                            (:d fn-stmt-bytes-item-p)
                            fn-stmt-okp-of-ok fn-stmt-value-of-ok)
                           (fn-cbor-encode fn-stmt-header-items fn-stmt-headerp
                            fn-stmt-decode-items fn-stmt-header-of-items
                            fn-stmt-encode-items))
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stx-max-detached-items*))
                 (:instance fn-stmt-header-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stx-max-detached-items* octets))))))))

; -----------------------------------------------------------------------------
; S1-1.  The field codec is canonical (PRF-019).

(defthm fn-stx-header-value-fits-the-field-bound
  (implies (fn-stmt-p s)
           (fn-cbor-at-mostp (fn-stx-header-value s) *fn-stx-max-field-octets*))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-header-value)
                            (:d fn-stmt-p)
                            fn-cbor-at-mostp-from-length)
                           (fn-stx-b64-encode fn-stx-detached-encode
                            fn-stmt-headerp))
           :use ((:instance fn-stx-b64-encode-length
                            (octets (fn-stx-detached-encode s)))
                 (:instance fn-stx-detached-encoding-bound
                            (header (fn-stmt-header s))
                            (signature (fn-stmt-signature s)))
                 (:instance fn-stx-detached-encode
                            (s s))))))

(defthm fn-stx-field-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stx-parse-header (fn-stx-header-value s))
                  (fn-stx-ok (list (fn-stmt-header s) (fn-stmt-signature s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-parse-header) (:d fn-stx-header-value))
                           (fn-stx-b64-encode fn-stx-b64-decode-exact
                            fn-stx-detached-encode fn-stx-detached-decode-exact
                            fn-stx-strip-wsp fn-stmt-p))
           :use ((:instance fn-stx-header-value-fits-the-field-bound)
                 (:instance fn-stx-strip-wsp-of-b64-encode
                            (octets (fn-stx-detached-encode s)))
                 (:instance fn-stx-b64-round-trip
                            (octets (fn-stx-detached-encode s)))
                 (:instance fn-stx-detached-round-trip)))))

(defthm fn-stx-field-accepted-input-is-canonical
  (implies (fn-stx-okp (fn-stx-parse-header v))
           (equal (fn-stx-header-value-parts
                   (fn-stx-val (fn-stx-parse-header v))
                   (fn-stx-val2 (fn-stx-parse-header v)))
                  (fn-stx-strip-wsp v)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-parse-header) (:d fn-stx-header-value-parts))
                           (fn-stx-b64-encode fn-stx-b64-decode-exact
                            fn-stx-detached-encode-parts
                            fn-stx-detached-decode-exact fn-stx-strip-wsp))
           :use ((:instance fn-stx-b64-accepted-input-is-canonical
                            (chars (fn-stx-strip-wsp v)))
                 (:instance fn-stx-detached-accepted-input-is-canonical
                            (octets (fn-stx-val
                                     (fn-stx-b64-decode-exact
                                      (fn-stx-strip-wsp v)))))))))

; -----------------------------------------------------------------------------
; The carrier is invisible to the payload it carries.  A statement cannot sign
; the field that carries it, so the authored-source projection subtracts
; FN-Statement along with every field the injecting agent adds; this says that
; inserting such a field ANYWHERE in the header changes nothing the signature
; covers.  It is why attaching the field after signing is sound.

(defthm fn-stx-authored-header-of-append
  (equal (fn-stx-authored-header (append a b))
         (append (fn-stx-authored-header a) (fn-stx-authored-header b)))
  :hints (("Goal" :induct (fn-stx-authored-header a)
           :in-theory (enable (:d fn-stx-authored-header)))))

(defthm fn-stx-payload-ignores-the-carrier-field
  (implies (or (not (true-listp field))
               (fn-stx-injected-namep (fn-article-field-name field)))
           (equal (fn-stx-authored-header (append before (cons field after)))
                  (fn-stx-authored-header (append before after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-authored-header))
                           (fn-stx-injected-namep))
           :use ((:instance fn-stx-authored-header-of-append
                            (a before) (b (cons field after)))
                 (:instance fn-stx-authored-header-of-append
                            (a before) (b after))))))

(defthm fn-stx-authored-source-ignores-the-carrier-field
  (implies (or (not (true-listp field))
               (fn-stx-injected-namep (fn-article-field-name field)))
           (equal (fn-stx-authored-source
                   (fn-article-make header body (append before (cons field after))))
                  (fn-stx-authored-source
                   (fn-article-make header body (append before after)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-authored-source))
                           (fn-stx-authored-header fn-stx-injected-namep
                            fn-stx-field-octets))
           :use ((:instance fn-stx-payload-ignores-the-carrier-field)))))

; -----------------------------------------------------------------------------
; S2-1.  The verdict is computed from the statement's own octets.

(local (defthm fn-stx-key-for-is-named-in-the-keyring
         (implies (fn-prin-key-for id keyring)
                  (member-equal (cons id (fn-prin-key-for id keyring)) keyring))
         :hints (("Goal" :induct (fn-prin-key-for id keyring)
                  :in-theory (enable (:d fn-prin-key-for))))))

(defthm fn-stx-verified-implies-signature-over-own-octets
  (implies (equal (fn-stx-verdict-token (fn-stx-verdict article keyring generation))
                  :verified)
           (let ((s (fn-stx-statement-of article)))
             (and (fn-stmt-p s)
                  (equal (fn-stmt-payload s)
                         (fn-stx-payload-for article (fn-stmt-header s)))
                  (equal (fn-stmt-header-ref (fn-stmt-header s))
                         (fn-digest-tagged *fn-stmt-payload-tag*
                                           (fn-stx-payload-for article
                                                               (fn-stmt-header s))))
                  (fn-sig-verify (fn-prin-key-for (fn-stmt-creator s) keyring)
                                 (fn-stmt-signing-preimage (fn-stmt-header s))
                                 (fn-stmt-signature s))
                  (member-equal (cons (fn-stmt-creator s)
                                      (fn-prin-key-for (fn-stmt-creator s) keyring))
                                keyring))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-verdict) (:d fn-stx-statement-of)
                            (:d fn-stx-reattach) (:d fn-prin-verifiedp)
                            (:d fn-stmt-verifiedp) (:d fn-stmt-p)
                            (:d fn-stmt-make) (:d fn-sig-public-key-p)
                            (:d fn-stmt-header)
                            (:d fn-stmt-payload) (:d fn-stmt-signature)
                            (:d fn-stmt-creator) (:d fn-stmt-payload-ref))
                           (fn-stx-parse-header fn-stx-payload-for
                            fn-stx-field fn-digest-tagged
                            fn-stmt-signing-preimage fn-stmt-headerp)))))

; Three outcomes, and no fourth: the verdict is total, typed, and never a
; refusal (D13, SUB-002).
(defthm fn-stx-verdict-is-typed
  (member-equal (fn-stx-verdict-token (fn-stx-verdict article keyring generation))
                *fn-stx-verdicts*)
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-verdict))
                                  (fn-stx-parse-header fn-stx-payload-for
                                   fn-stx-field fn-stx-reattach
                                   fn-prin-verifiedp)))))

; A verdict without the keyring generation it was computed under is not
; reproducible, so the generation is carried in the record (SUB-002).
(defthm fn-stx-verdict-records-its-keyring-generation
  (equal (fn-stx-verdict-generation (fn-stx-verdict article keyring generation))
         generation)
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-verdict))
                                  (fn-stx-parse-header fn-stx-payload-for
                                   fn-stx-field fn-stx-reattach
                                   fn-prin-verifiedp)))))

; The subject of the grounding theorem is the statement the article carries,
; and it is a function of the article alone -- no keyring, no peer.
(defthm fn-stx-verified-is-the-statement-the-article-carries
  (implies (equal (fn-stx-verdict-token (fn-stx-verdict article keyring generation))
                  :verified)
           (and (fn-stx-statement-of article)
                (fn-prin-verifiedp (fn-stx-statement-of article) keyring)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ((:d fn-stx-verdict) (:d fn-stx-statement-of))
                           (fn-stx-parse-header fn-stx-payload-for
                            fn-stx-field fn-stx-reattach fn-prin-verifiedp)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  Everything this book proves
; is a keystone or a shape fact an includer needs; the two append/length
; lemmas are proof vocabulary and are withdrawn under a name.

(deftheory fn-stx-invariants-vocabulary
  '(fn-stx-authored-header-of-append
    fn-stx-detached-items-length
    fn-stx-detached-encoding-bound))

(in-theory (disable fn-stx-invariants-vocabulary))
