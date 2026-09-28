; fn: the reader of the format before this one (format 9), for the open's
; refusal by name and for `store import' (lane format-bump-10; D34, D38 as
; proposed 2026-09-27: a layout or format change ships a reader for the
; previous one's archive, with a witness).
;
; Format 9 (`fn-store-9') sealed its metadata frames under SHA-256: the
; trailer of every FNSM frame it wrote (config.json, the configuration
; records, the allocation frontier an archive carries) is SHA-256 of the
; protected prefix, whatever the image's digest seam is attached to now
; (books/crypto-attach.lisp; format 10's digest is BLAKE3 once lane
; blake3-digest's attachment lands).  So this reader opens a format-9 frame
; under `fn-sha256' BY NAME, never through the seam: the one place format 10
; reads SHA-256 is the previous format's bytes, and only to name them (the
; open's `:store-format-9') or to translate them once (`store import').
;
; Its profile was two texts -- the format word and the allocation
; frontier's format word -- and sixteen u64 naturals, of which field 14 (the
; committed-history marker, D31) was carried and never read on the record
; log (`init' refused `required').  Format 10 drops both (books/byte-store-
; frame.lisp): `fn-f9-profile-of' is the one map, keeping every other field
; in order, and the import refuses a format-9 profile whose marker is not 0
; or whose second text is not the frontier word, by name, rather than drop
; a value it does not understand.
(in-package "ACL2")
(include-book "byte-store-frame")
(include-book "sha256")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))

; -----------------------------------------------------------------------------
; A format-9 frame: FNSM (or any family) under the SHA-256 trailer.

; The protected prefix's SHA-256 (books/sha256.lisp's list model: the word
; stobj went with the BLAKE3 attachment; a profile frame is a few hundred
; octets, and the import reads each archive entry once).
(defun fn-f9-trailer (octets)
  (declare (xargs :guard t))
  (fn-sha256 octets))

(local
 (defthm fn-f9-cbor-octet-listp-is-sha256-octet-listp
   (equal (fn-cbor-octet-listp xs)
          (fn-sha256-octet-listp xs))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

(defun fn-f9-frame-open (octets max-payload)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-frame-decode octets
                   (fn-f9-trailer (fn-frame-protected-prefix octets))
                   max-payload))

; What a format-9 release sealed: the frame with its SHA-256 trailer.
(defun fn-f9-frame-seal (magic version kind payload)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-encode magic version kind payload
                   (fn-f9-trailer (fn-frame-protected magic version kind payload))))

(defthm fn-f9-trailer-is-a-digest
  (fn-frame-digestp (fn-f9-trailer octets))
  :hints (("Goal" :in-theory (enable fn-frame-digestp))))

(defthm fn-f9-trailer-is-octets
  (and (fn-cbor-octet-listp (fn-f9-trailer octets))
       (equal (len (fn-f9-trailer octets)) 32))
  :hints (("Goal" :use fn-f9-trailer-is-a-digest
           :in-theory (e/d (fn-frame-digestp) (fn-f9-trailer-is-a-digest)))))

(defthm fn-f9-frame-open-of-seal
  (implies (fn-frame-inputp magic version kind payload max-payload)
           (equal (fn-f9-frame-open (fn-f9-frame-seal magic version kind payload)
                                    max-payload)
                  (fn-frame-ok magic version kind payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-protected-prefix-of-encode
                            (digest (fn-f9-trailer
                                     (fn-frame-protected magic version kind payload))))
                 (:instance fn-frame-decode-of-encode
                            (digest (fn-f9-trailer
                                     (fn-frame-protected magic version kind payload)))))
           :in-theory (e/d (fn-f9-frame-open fn-f9-frame-seal)
                           (fn-frame-protected-prefix-of-encode
                            fn-frame-decode-of-encode fn-f9-trailer
                            fn-frame-encode fn-frame-protected
                            fn-frame-protected-prefix fn-frame-inputp
                            fn-frame-decode)))))

; -----------------------------------------------------------------------------
; The format-9 profile

(defconst *fn-f9-frontier-word*                 ; fn-store-allocation-frontier-2
  '(102 110 45 115 116 111 114 101 45 97 108 108 111 99 97 116 105
    111 110 45 102 114 111 110 116 105 101 114 45 50))

(defconst *fn-f9-profile-spec*
  '(:text :text :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat
    :nat :nat :nat))

; The format-9 field of the committed-history marker.
(defconst *fn-f9-history-marker* 14)

; The frame a format-9 `init' or `store import' wrote for VALUES9.
(defun fn-f9-config-frame (values9)
  (declare (xargs :guard t :verify-guards nil))
  (fn-f9-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                    *fn-bs-meta-config-kind*
                    (fn-frame-fields-octets *fn-f9-profile-spec* values9)))

; The format word of a sealed format-9 profile frame (its first text), valid
; profile or not; NIL for octets that do not open as one under SHA-256.
(defun fn-f9-saved-format-word (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-f9-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((word (fn-frame-field-parse :text (fn-frame-result-payload frame))))
          (if (fn-frame-parse-okp word)
              (fn-frame-parse-value word)
            nil))))))

; The eighteen values of a sealed format-9 profile frame, or NIL.
(defun fn-f9-profile-values (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-f9-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((parsed (fn-frame-fields-parse *fn-f9-profile-spec*
                                             (fn-frame-result-payload frame))))
          (if (fn-frame-parse-okp parsed)
              (fn-frame-parse-value parsed)
            nil))))))

(defun fn-f9-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (if (consp xs) (car xs) nil)
          (fn-f9-take (1- n) (if (consp xs) (cdr xs) nil)))))

; The format-10 profile of format-9 values: the word 10, fields 2 to 13,
; then fields 15 to 17 (the two dropped fields are 1, the frontier word,
; and 14, the committed-history marker).
(defun fn-f9-profile-of (values9)
  (declare (xargs :guard t))
  (cons *fn-bs-meta-format-10*
        (append (fn-f9-take 12 (nthcdr 2 (true-list-fix values9)))
                (fn-f9-take 3 (nthcdr 15 (true-list-fix values9))))))

; Why a format-9 profile does not translate, by name, or NIL when it does:
; the translation is a valid format-10 profile and nothing it drops carried
; a value.
(defun fn-f9-profile-refusal (values9)
  (declare (xargs :guard t))
  (cond ((not (fn-frame-values-okp *fn-f9-profile-spec* values9)) :layout)
        ((not (equal (fn-bs-meta-nth 0 values9) *fn-bs-meta-format-9*))
         :store-format)
        ((not (equal (fn-bs-meta-nth 1 values9) *fn-f9-frontier-word*))
         :frontier-format)
        ((not (equal (fn-bs-meta-nth *fn-f9-history-marker* values9) 0))
         :history-marker-required)
        ((fn-bs-profile-invalid-reason (fn-f9-profile-of values9))
         (fn-bs-profile-invalid-reason (fn-f9-profile-of values9)))
        (t nil)))

; The format-10 profile an archive's format-9 config.json translates to, or
; NIL.
(defun fn-f9-config-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((values9 (fn-f9-profile-values octets)))
    (if (and values9 (null (fn-f9-profile-refusal values9)))
        (fn-f9-profile-of values9)
      nil)))

(defthm fn-f9-config-decode-is-valid
  (implies (fn-f9-config-decode octets)
           (fn-bs-profile-validp (fn-f9-config-decode octets)))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp)
                                  (fn-f9-profile-values fn-f9-profile-of
                                   fn-bs-profile-invalid-reason)))))

; -----------------------------------------------------------------------------
; The round trip of the previous release's frame (the witness of D38's rule):
; every format-9 profile that translates reads back, from the frame the
; format-9 encoder sealed, as its translation.

(local
 (defun fn-f9-all-nat-specp (specs)
   (if (consp specs)
       (and (equal (car specs) :nat) (fn-f9-all-nat-specp (cdr specs)))
     t)))

(local
 (defthm fn-f9-all-nat-fields-octets-len
   (implies (and (fn-f9-all-nat-specp specs)
                 (fn-frame-values-okp specs values))
            (equal (len (fn-frame-fields-octets specs values))
                   (* 8 (len specs))))
   :hints (("Goal" :induct (fn-frame-values-okp specs values)
            :in-theory (enable fn-frame-field-octets fn-frame-values-okp
                               fn-frame-fields-octets fn-frame-field-okp
                               fn-frame-natp fn-frame-u64-bytes-len)))))

(local
 (defthm fn-f9-fields-octets-len
   (implies (and (fn-frame-values-okp *fn-f9-profile-spec* values9)
                 (equal (fn-bs-meta-nth 0 values9) *fn-bs-meta-format-9*)
                 (equal (fn-bs-meta-nth 1 values9) *fn-f9-frontier-word*))
            (equal (len (fn-frame-fields-octets *fn-f9-profile-spec* values9))
                   (+ (len (fn-frame-field-octets :text *fn-bs-meta-format-9*))
                      (len (fn-frame-field-octets :text *fn-f9-frontier-word*))
                      128)))
   :hints (("Goal"
            :use ((:instance fn-f9-all-nat-fields-octets-len
                             (specs (cddr *fn-f9-profile-spec*))
                             (values (cddr values9))))
            :expand ((fn-frame-fields-octets *fn-f9-profile-spec* values9)
                     (fn-frame-fields-octets (cdr *fn-f9-profile-spec*)
                                             (cdr values9))
                     (fn-frame-values-okp *fn-f9-profile-spec* values9)
                     (fn-frame-values-okp (cdr *fn-f9-profile-spec*)
                                          (cdr values9))
                     (fn-bs-meta-nth 0 values9) (fn-bs-meta-nth 1 values9)
                     (fn-bs-meta-nth 0 (cdr values9)))
            :in-theory (disable fn-f9-all-nat-fields-octets-len
                                fn-frame-field-octets)))))

(local
 (defthm fn-f9-seal-inputp
   (implies (and (fn-frame-values-okp *fn-f9-profile-spec* values9)
                 (equal (fn-bs-meta-nth 0 values9) *fn-bs-meta-format-9*)
                 (equal (fn-bs-meta-nth 1 values9) *fn-f9-frontier-word*))
            (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-frame-fields-octets *fn-f9-profile-spec* values9)
                             *fn-bs-meta-max-config-payload*))
   :hints (("Goal"
            :use ((:instance fn-f9-fields-octets-len)
                  (:instance fn-frame-fields-octets-are-octets
                             (specs *fn-f9-profile-spec*) (values values9)))
            :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                            (fn-f9-fields-octets-len
                             fn-frame-fields-octets-are-octets))))))

(local
 (defthm fn-f9-seal-octet-listp
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (fn-cbor-octet-listp (fn-f9-frame-seal magic version kind payload)))
   :hints (("Goal"
            :use ((:instance fn-f9-trailer-is-a-digest
                             (octets (fn-frame-protected magic version kind payload)))
                  (:instance fn-cbor-u32-bytes-are-octets (n (len payload))))
            :in-theory (e/d (fn-f9-frame-seal fn-frame-encode fn-frame-protected
                             fn-frame-header fn-frame-inputp fn-frame-magicp
                             fn-frame-digestp fn-cbor-octet-listp-append)
                            (fn-f9-trailer-is-a-digest fn-f9-trailer
                             fn-cbor-u32-bytes-are-octets))))))

(defthm fn-f9-profile-values-of-config-frame
  (implies (and (fn-frame-values-okp *fn-f9-profile-spec* values9)
                (equal (fn-bs-meta-nth 0 values9) *fn-bs-meta-format-9*)
                (equal (fn-bs-meta-nth 1 values9) *fn-f9-frontier-word*))
           (equal (fn-f9-profile-values (fn-f9-config-frame values9))
                  values9))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-f9-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-f9-profile-spec* values9))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-f9-seal-octet-listp
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-f9-profile-spec* values9))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-f9-seal-inputp)
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-f9-profile-spec*) (values values9)))
           :in-theory (e/d (fn-f9-profile-values fn-f9-config-frame
                            fn-bs-meta-frame-okp fn-frame-inputp)
                           (fn-f9-frame-open-of-seal fn-f9-seal-octet-listp
                            fn-f9-seal-inputp fn-f9-frame-open fn-f9-frame-seal
                            fn-frame-fields-parse-of-octets)))))

; KEYSTONE (D38's witness, format 9 -> 10).  The profile `store import' reads
; from the config.json a format-9 release sealed is exactly the format-10
; translation of its values, whenever they translate (no refusal by name):
; every field but the two dropped ones, in order, under the word
; fn-store-10, and a valid format-10 profile.
(defthm fn-f9-config-decode-of-a-format-9-frame
  (implies (null (fn-f9-profile-refusal values9))
           (and (equal (fn-f9-config-decode (fn-f9-config-frame values9))
                       (fn-f9-profile-of values9))
                (fn-bs-profile-validp (fn-f9-profile-of values9))))
  :hints (("Goal" :use (fn-f9-profile-values-of-config-frame)
           :in-theory (e/d (fn-f9-config-decode fn-bs-profile-validp)
                           (fn-f9-profile-values-of-config-frame
                            fn-f9-profile-values fn-f9-config-frame
                            fn-f9-profile-of fn-bs-profile-invalid-reason
                            fn-frame-values-okp)))))

; The word the open's refusal reads is the one the format-9 encoder wrote.
(defthm fn-f9-saved-format-word-of-config-frame
  (implies (and (fn-frame-values-okp *fn-f9-profile-spec* values9)
                (equal (fn-bs-meta-nth 0 values9) *fn-bs-meta-format-9*)
                (equal (fn-bs-meta-nth 1 values9) *fn-f9-frontier-word*))
           (equal (fn-f9-saved-format-word (fn-f9-config-frame values9))
                  *fn-bs-meta-format-9*))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-f9-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-f9-profile-spec* values9))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-f9-seal-octet-listp
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-f9-profile-spec* values9))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-f9-seal-inputp)
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-f9-profile-spec*) (values values9)))
           :expand ((fn-frame-fields-parse *fn-f9-profile-spec*
                                           (fn-frame-fields-octets
                                            *fn-f9-profile-spec* values9))
                    (fn-frame-fields-parse-aux *fn-f9-profile-spec*
                                               (fn-frame-fields-octets
                                                *fn-f9-profile-spec* values9)))
           :in-theory (e/d (fn-f9-saved-format-word fn-f9-config-frame
                            fn-bs-meta-frame-okp fn-frame-inputp fn-bs-meta-nth)
                           (fn-f9-frame-open-of-seal fn-f9-seal-octet-listp
                            fn-f9-seal-inputp fn-f9-frame-open fn-f9-frame-seal
                            fn-frame-fields-parse-of-octets
                            fn-frame-fields-parse fn-frame-field-parse)))))

; A frame that opens under both digests is the same frame: the digest decides
; only whether it opens, never what it opens to.  So a word read under
; SHA-256 and a word read under the seam never disagree.
(defthm fn-f9-frame-open-agrees-with-the-seam
  (implies (and (fn-frame-result-okp (fn-f9-frame-open octets max-payload))
                (fn-frame-result-okp (fn-frame-open octets max-payload)))
           (equal (fn-f9-frame-open octets max-payload)
                  (fn-frame-open octets max-payload)))
  :hints (("Goal" :in-theory (e/d (fn-f9-frame-open fn-frame-open fn-frame-decode)
                                  (fn-f9-trailer fn-frame-protected-prefix
                                   fn-cbor-u32-from fn-frame-head-fields)))))

(local
 (defthm fn-f9-fields-parse-car
   (implies (and (consp specs)
                 (fn-frame-parse-okp (fn-frame-fields-parse specs octets)))
            (and (fn-frame-parse-okp (fn-frame-field-parse (car specs) octets))
                 (equal (car (fn-frame-parse-value (fn-frame-fields-parse specs octets)))
                        (fn-frame-parse-value (fn-frame-field-parse (car specs) octets)))))
   :hints (("Goal" :in-theory (enable fn-frame-fields-parse)
            :expand ((fn-frame-fields-parse-aux specs octets))))))

(local
 (defthm fn-f9-valid-names-format-10
   (implies (fn-bs-profile-validp values)
            (equal (car values) *fn-bs-meta-format-10*))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp fn-bs-profile-invalid-reason
                                    fn-bs-meta-nth fn-bs-meta-formatp)
                                   (fn-bs-pf fn-frame-values-okp
                                    fn-record-encoded-octets-ceiling))))))

; KEYSTONE (the two formats never meet).  A config.json whose word, read under
; format 9's SHA-256, is fn-store-9 is never a profile this format decodes:
; the digest decides only whether a frame opens, never its payload
; (fn-f9-frame-open-agrees-with-the-seam), and every profile this format
; decodes names fn-store-10.  So the open's `:store-format-9' and the
; import's format-9 reader never take a format-10 store for the previous one,
; under any attachment of the seam.
(defthm fn-f9-format-9-frame-does-not-decode
  (implies (equal (fn-f9-saved-format-word octets) *fn-bs-meta-format-9*)
           (not (fn-bs-config-decode octets)))
  :hints (("Goal"
           :use ((:instance fn-f9-fields-parse-car
                            (specs *fn-bs-meta-profile-spec*)
                            (octets (fn-frame-result-payload
                                     (fn-frame-open octets
                                                    *fn-bs-meta-max-config-payload*))))
                 (:instance fn-f9-valid-names-format-10
                            (values (fn-frame-parse-value
                                     (fn-frame-fields-parse
                                      *fn-bs-meta-profile-spec*
                                      (fn-frame-result-payload
                                       (fn-frame-open octets
                                                      *fn-bs-meta-max-config-payload*))))))
                 (:instance fn-f9-frame-open-agrees-with-the-seam
                            (max-payload *fn-bs-meta-max-config-payload*)))
           :in-theory (e/d (fn-f9-saved-format-word fn-bs-config-decode
                            fn-bs-meta-frame-okp)
                           (fn-f9-fields-parse-car fn-f9-valid-names-format-10
                            fn-f9-frame-open-agrees-with-the-seam
                            fn-bs-profile-validp fn-frame-fields-parse
                            fn-frame-field-parse fn-frame-open fn-f9-frame-open)))))

(verify-guards fn-f9-frame-open)
(verify-guards fn-f9-saved-format-word)
(verify-guards fn-f9-profile-values)
(verify-guards fn-f9-config-decode)

(in-theory (disable fn-f9-frame-open fn-f9-frame-seal fn-f9-trailer
                    fn-f9-saved-format-word fn-f9-profile-values
                    fn-f9-config-decode fn-f9-config-frame))
