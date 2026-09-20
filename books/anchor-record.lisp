; fn: the durable anchor record family, FNAN.
;
; A new family over books/frame's grammar; frame.lisp is untouched.  Kind 1 is
; an observed anchor, kind 2 is an incarnation advance and the anchor it
; advanced under.
;
; This book exists so that `books/anchor.lisp' does not include `frame' at
; all.  Opening frame's field grammar (`fn-frame-values-okp',
; `fn-frame-field-okp') over a nine-field spec is an unbounded case split --
; it ran `(verify-guards fn-anchor-encode)' for over five minutes at 2 GB in
; the lane that first wrote these books -- and it never needs to open: the
; guard of `fn-frame-fields-octets' IS `fn-frame-values-okp', which is already
; a conjunct of `fn-anchor-record-okp'.  So the grammar stays closed here and
; the two frame entry points are discharged from named `:rule-classes nil'
; guard lemmas, the shape books/frame-journal.lisp uses for its own three
; families.

(in-package "ACL2")
(include-book "anchor")
(include-book "frame")
; `fn-anchor-decode-of-encode' rests on frame's own round trip.
(include-book "frame-invariants")
(local (include-book "arithmetic/top" :dir :system))

; Local vocabulary re-enable (docs/proof-style.md sec. 2).  This is the ONLY
; book of the anchor cluster that opens anything of frame's, and it opens the
; small predicates and the two result records, never the field grammar
; (`fn-frame-values-okp', `fn-frame-field-okp', `fn-frame-fields-octets',
; `fn-frame-fields-parse'), never the splitter (`fn-frame-split') and never
; `fn-frame-encode'/`fn-frame-decode' themselves.
; `fn-frame-record-vocabulary' is deliberately NOT enabled: opening the frame
; result accessors turns `(fn-frame-result-payload r)' into `(fn-frame-item 4
; r)' and `fn-frame-decode-payload-octets', which is stated in accessor
; vocabulary, can no longer fire.
(local (in-theory (enable fn-frame-fields-vocabulary
                          fn-frame-octet-vocabulary
                          (:d fn-frame-magicp) (:d fn-frame-spec-for)
                          (:d fn-frame-specp) (:d fn-frame-spec-listp)
                          (:d fn-frame-digestp))))

; -----------------------------------------------------------------------------
; The family

(defconst *fn-anchor-magic* '(70 78 65 78))   ; FNAN
(defconst *fn-anchor-max-payload* 1024)

(defconst *fn-anchor-kinds* '(:observed :incarnation))

(defconst *fn-anchor-specs*
  (list (cons :observed
              '(:blob :blob :nat :nat :blob :nat :nat :blob :blob))
        (cons :incarnation
              '(:nat :blob :blob :nat :nat :blob :nat :nat :blob :blob))))

(defthm fn-anchor-spec-for-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-anchor-specs*) :none))
           (fn-frame-spec-listp (fn-frame-spec-for kind *fn-anchor-specs*))))

(defun fn-anchor-record-anchor (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((base (if (equal kind :observed) 0 1)))
    (fn-anchor (fn-frame-item base values)
               (fn-frame-item (+ base 1) values)
               (fn-frame-item (+ base 2) values)
               (fn-frame-item (+ base 3) values)
               (fn-frame-item (+ base 4) values)
               (fn-frame-item (+ base 5) values)
               (fn-frame-item (+ base 6) values)
               (fn-frame-item (+ base 7) values)
               (fn-frame-item (+ base 8) values))))

(verify-guards fn-anchor-record-anchor)

; The field grammar admits any blob; the anchor grammar admits only the exact
; Roughtime field widths, so a record cannot hold a 31-octet "public key".
(defun fn-anchor-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-anchor-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values)
         (fn-anchor-p (fn-anchor-record-anchor kind values)))))

(verify-guards fn-anchor-record-okp)

(defun fn-anchor-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-anchor-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-anchor-kinds*)))
      (if (equal code 0)
          :bad
        (let ((payload (fn-frame-fields-octets
                        (fn-frame-spec-for kind *fn-anchor-specs*) values)))
          (if (not (fn-cbor-at-mostp payload *fn-anchor-max-payload*))
              :bad
            (fn-frame-encode *fn-anchor-magic* *fn-frame-version* code
                             payload digest)))))))


(defun fn-anchor-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-anchor-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-anchor-magic*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-anchor-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1) *fn-anchor-kinds*))
                   (spec (fn-frame-spec-for kind *fn-anchor-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (if (not (fn-anchor-record-okp
                              kind (fn-frame-parse-value parsed)))
                        (fn-frame-error :anchor-field)
                      (fn-frame-ok *fn-anchor-magic* *fn-frame-version* kind
                                   (fn-frame-parse-value parsed)))))))))))))

; -----------------------------------------------------------------------------
; The two frame entry points, discharged from named guard lemmas
;
; Each is an equality that exists to discharge a guard, so it is
; `:rule-classes nil' and is used by `:use' (docs/proof-style.md sec. 3).

(defthm fn-anchor-encode-frame-guard
  (implies (fn-anchor-record-okp kind values)
           (and (fn-frame-spec-listp (fn-frame-spec-for kind *fn-anchor-specs*))
                (fn-frame-values-okp (fn-frame-spec-for kind *fn-anchor-specs*)
                                     values)
                (fn-cbor-octet-listp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-anchor-specs*) values))
                (fn-frame-magicp *fn-anchor-magic*)
                (fn-cbor-octetp *fn-frame-version*)
                (fn-cbor-octetp (fn-frame-enum-index kind *fn-anchor-kinds*))))
  :rule-classes nil)

(verify-guards fn-anchor-encode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-anchor-encode-frame-guard)))))

(defthm fn-anchor-decode-frame-guard
  (implies (fn-frame-result-okp
            (fn-frame-decode octets digest *fn-anchor-max-payload*))
           (fn-cbor-octet-listp
            (fn-frame-result-payload
             (fn-frame-decode octets digest *fn-anchor-max-payload*))))
  :rule-classes nil)

(verify-guards fn-anchor-decode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-anchor-decode-frame-guard)))))

; -----------------------------------------------------------------------------
; The record and the round trip

; `fn-anchor-record-anchor-is-an-anchor' is the third conjunct of
; `fn-anchor-record-okp' restated with that predicate as its hypothesis: it is
; true by definition and is not a registry event (docs/proof-style.md sec. 7).
(defthm fn-anchor-record-anchor-is-an-anchor
  (implies (fn-anchor-record-okp kind values)
           (fn-anchor-p (fn-anchor-record-anchor kind values)))
  :rule-classes nil)

; KEYSTONE: the value direction for FNAN.  Everything the host encodes decodes
; back to the kind and the field values it started from.
(defthm fn-anchor-decode-of-encode
  (implies (and (fn-anchor-record-okp kind values)
                (fn-frame-digestp digest)
                (not (equal (fn-anchor-encode kind values digest) :bad)))
           (equal (fn-anchor-decode (fn-anchor-encode kind values digest)
                                    digest)
                  (fn-frame-ok *fn-anchor-magic* *fn-frame-version* kind
                               values)))
  ; Only the three rules of `fn-frame-invariants-vocabulary' this round trip
  ; needs are named: enabling that whole theory here ran for over ten minutes.
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-anchor-encode fn-anchor-decode
                            fn-frame-fields-parse-of-octets
                            fn-frame-item-of-enum-index
                            fn-frame-enum-index-of-item
                            fn-frame-inputp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md sec. 2)
;
; What leaves this book enabled: `fn-anchor-decode-of-encode'.  The codec, the
; record projection and the spec-shape lemma are withdrawn; a book that must
; open one enables `fn-anchor-record-vocabulary' locally and says why.

(deftheory fn-anchor-record-vocabulary
  '((:d fn-anchor-record-anchor) (:d fn-anchor-record-okp)
    (:d fn-anchor-encode) (:d fn-anchor-decode)
    fn-anchor-spec-for-is-spec-list))

(in-theory (disable (:d fn-anchor-record-anchor) (:d fn-anchor-record-okp)
             (:d fn-anchor-encode) (:d fn-anchor-decode)
             fn-anchor-spec-for-is-spec-list))
