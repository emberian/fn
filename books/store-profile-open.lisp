; fn: the open of a store's saved profile, and its refusals by name
; (PKT-471, the coordinator's decision of 2026-09-26; D34; format 10, lane
; format-bump-10).
;
; D34 makes the store format one format: format 10 (books/byte-store-frame
; .lisp *fn-bs-meta-format-10*, the record log with its genesis).  A profile
; frame of any other format is refused at the open by name and never
; translated:
;
;   * a format-9 store (`fn-store-9', the release before format 10) is
;     refused `:store-format-9', and the line names the way out: export it
;     with the release that made it, then `store import' here (the import
;     reads the format-9 archive, books/store-export.lisp
;     fn-sxp-config-decode-archive, and writes a format-10 store with its
;     own genesis);
;   * a sealed profile frame of any other word (format 8, 7, ...) is refused
;     `:store-format';
;   * a format-10 frame whose run of u64 fields has another width (a store
;     made by an older or newer release of the same word) is refused
;     `:profile-layout' with the width (PKT-705);
;   * anything else that does not decode (a corrupted file) is the host's
;     fault, `(:rejected)', as before.
;
; The open the host calls is `fn-spo-config-open' (host/native/io.lisp
; `fnn-metadata-config-decode', through host/store-host.lisp
; `fn-store-metadata-config-open'; every open reads the profile there:
; `fnn-load-config' from `fnn-acquire', so owner start, `store recover',
; `inspect', `checkpoint', `status' and the offline `health').
;
; The PKT-467 window refusal (a profile saved before that arm with R in the
; 355 octets above the poll reply) and its frozen relations (the v2 relation
; here and books/byte-store-profile-v1.lisp) are gone with format 9: every
; format-10 profile was written by a format-10 `init' or `store import' under
; the current relation (`fn-bs-profile-invalid-reason', which carries that
; arm), so no format-10 store can hold one.
(in-package "ACL2")
(include-book "store-profile-facts")
(include-book "store-format-9")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))

; -----------------------------------------------------------------------------
; The format word of a sealed profile frame

; The format word of a sealed profile frame (its first text field), valid
; profile or not; NIL for octets that do not open as one.
(defun fn-spo-saved-format-word (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((word (fn-frame-field-parse :text (fn-frame-result-payload frame))))
          (if (fn-frame-parse-okp word)
              (fn-frame-parse-value word)
            nil))))))

; A sealed profile frame of the format before this one: its word, read under
; the SHA-256 trailer format 9 sealed with (books/store-format-9.lisp).
(defun fn-spo-format-9p (octets)
  (declare (xargs :guard t))
  (equal (fn-f9-saved-format-word octets) *fn-bs-meta-format-9*))

; A sealed profile frame of any other format, under this format's digest or
; the SHA-256 of the formats before it: neither this one (10) nor the one
; before it (9).
(defun fn-spo-foreign-formatp (octets)
  (declare (xargs :guard t))
  (let ((word (or (fn-spo-saved-format-word octets)
                  (fn-f9-saved-format-word octets))))
    (and word
         (not (fn-bs-meta-formatp word))
         (not (equal word *fn-bs-meta-format-9*))
         t)))

; -----------------------------------------------------------------------------
; The layout (PKT-705): the number of u64 fields after the format word.

(defun fn-spo-nat-specs (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons :nat (fn-spo-nat-specs (1- n)))))

; The profile layout of N u64 fields after the format word: the spec a
; release of this format whose profile had N fields sealed its config.json
; under.  (fn-spo-layout-spec 15) is *fn-bs-meta-profile-spec*.
(defun fn-spo-layout-spec (n)
  (declare (xargs :guard (natp n)))
  (cons :text (fn-spo-nat-specs n)))

(defconst *fn-spo-release-layout-fields*
  (- (len *fn-bs-meta-profile-spec*) 1))

; The frame a release whose profile layout has N fields wrote for VALUES.
(defun fn-spo-layout-frame (n values)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                 *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets (fn-spo-layout-spec (nfix n)) values)))

; The layout of a config.json: the number of u64 fields after this format's
; word, when the sealed profile frame is exactly that; NIL for any other
; octets (no sealed profile frame, another format word, or a tail that is
; no run of u64 fields).
(defun fn-spo-layout-fields (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((head (fn-frame-field-parse :text (fn-frame-result-payload frame))))
          (if (not (and (fn-frame-parse-okp head)
                        (fn-bs-meta-formatp (fn-frame-parse-value head))))
              nil
            (let ((width (len (fn-frame-parse-rest head))))
              (if (equal (mod width 8) 0)
                  (floor width 8)
                nil))))))))

; -----------------------------------------------------------------------------
; The open the host calls (host/native/io.lisp `fnn-metadata-config-decode').

(defun fn-spo-config-open (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bs-config-decode octets)))
    (cond (decoded (list :opened decoded))
          ((fn-spo-format-9p octets) (list :refused :store-format-9))
          ((fn-spo-foreign-formatp octets) (list :refused :store-format))
          (t (let ((fields (fn-spo-layout-fields octets)))
               (if (and fields (not (equal fields *fn-spo-release-layout-fields*)))
                   (list :refused :profile-layout fields)
                 (list :rejected)))))))

(local
 (defthm fn-spo-explode-is-characters
   (implies (character-listp acc)
            (character-listp (explode-nonnegative-integer n base acc)))
   :hints (("Goal" :in-theory (disable floor mod)))))

(defun fn-spo-decimal (n)
  (declare (xargs :guard (natp n)))
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

(defun fn-spo-profile-layout-refusalp (verdict)
  (declare (xargs :guard t))
  (and (true-listp verdict)
       (equal (len verdict) 3)
       (equal (first verdict) :refused)
       (equal (second verdict) :profile-layout)
       (natp (third verdict))))

; The line every open path prints for the refusal (the pre-C1 pattern:
; ACL2 renders it, the host carries it).
(defun fn-spo-refusal-text (verdict)
  (declare (xargs :guard t))
  (cond ((equal verdict (list :refused :store-format-9))
         "open refused reason=store-format-9: a format-9 store (made by the release before format 10); export it with that release (store ROOT export DIR), then import it here (store NEWROOT import DIR); no store is upgraded in place (D34)")
        ((equal verdict (list :refused :store-format))
         "open refused reason=store-format: reinstall from the release and import")
        ((fn-spo-profile-layout-refusalp verdict)
         (let ((older (< (third verdict) *fn-spo-release-layout-fields*)))
           (concatenate 'string
                        "open refused reason="
                        (if older "older-release" "newer-release")
                        ": store made by "
                        (if older "an older" "a newer")
                        " release (profile layout "
                        (fn-spo-decimal (third verdict))
                        " fields, this release expects "
                        (fn-spo-decimal *fn-spo-release-layout-fields*)
                        "): export it with the release that made it, then import it here")))
        (t nil)))

; -----------------------------------------------------------------------------
; A decoded frame names this format

(local
 (defthm fn-spo-fields-parse-car
   (implies (and (consp specs)
                 (fn-frame-parse-okp (fn-frame-fields-parse specs octets)))
            (and (fn-frame-parse-okp (fn-frame-field-parse (car specs) octets))
                 (equal (car (fn-frame-parse-value (fn-frame-fields-parse specs octets)))
                        (fn-frame-parse-value (fn-frame-field-parse (car specs) octets)))))
   :hints (("Goal" :in-theory (enable fn-frame-fields-parse)
            :expand ((fn-frame-fields-parse-aux specs octets))))))

(local
 (defthm fn-spo-valid-names-format-10
   (implies (fn-bs-profile-validp values)
            (equal (car values) *fn-bs-meta-format-10*))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp fn-bs-profile-invalid-reason
                                    fn-bs-meta-nth fn-bs-meta-formatp)
                                   (fn-bs-pf fn-frame-values-okp
                                    fn-record-encoded-octets-ceiling))))))

(local
 (defthm fn-spo-decoded-is-valid
   (implies (fn-bs-config-decode octets)
            (fn-bs-profile-validp (fn-bs-config-decode octets)))
   :hints (("Goal" :in-theory (e/d (fn-bs-config-decode)
                                   (fn-bs-profile-validp))))))

; The word of a frame the decoder decodes is this format's.
(local
 (defthm fn-spo-decoded-names-format-10
   (implies (fn-bs-config-decode octets)
            (equal (fn-spo-saved-format-word octets) *fn-bs-meta-format-10*))
   :hints (("Goal"
            :use ((:instance fn-spo-fields-parse-car
                             (specs *fn-bs-meta-profile-spec*)
                             (octets (fn-frame-result-payload
                                      (fn-frame-open octets
                                                     *fn-bs-meta-max-config-payload*))))
                  fn-spo-decoded-is-valid
                  (:instance fn-spo-valid-names-format-10
                             (values (fn-bs-config-decode octets))))
            :in-theory (e/d (fn-spo-saved-format-word)
                            (fn-spo-fields-parse-car fn-spo-decoded-is-valid
                             fn-spo-valid-names-format-10
                             fn-bs-profile-validp fn-frame-fields-parse
                             fn-frame-field-parse fn-frame-open
                             fn-bs-meta-frame-okp))
            :expand ((fn-bs-config-decode octets))))))

; A word read under SHA-256 and a word read under the seam never disagree
; (books/store-format-9.lisp fn-f9-frame-open-agrees-with-the-seam).
(local
 (defthm fn-spo-saved-words-agree
   (implies (and (fn-spo-saved-format-word octets)
                 (fn-f9-saved-format-word octets))
            (equal (fn-f9-saved-format-word octets)
                   (fn-spo-saved-format-word octets)))
   :hints (("Goal" :use ((:instance fn-f9-frame-open-agrees-with-the-seam
                                    (max-payload *fn-bs-meta-max-config-payload*)))
            :in-theory (e/d (fn-spo-saved-format-word fn-f9-saved-format-word
                             fn-bs-meta-frame-okp)
                            (fn-f9-frame-open-agrees-with-the-seam
                             fn-f9-frame-open fn-frame-open fn-frame-field-parse))))))

(local
 (defthm fn-spo-format-9-is-not-decoded
   (implies (fn-spo-format-9p octets)
            (not (fn-bs-config-decode octets)))
   :hints (("Goal" :use (fn-spo-decoded-names-format-10 fn-spo-saved-words-agree)
            :in-theory (e/d (fn-spo-format-9p)
                            (fn-spo-decoded-names-format-10 fn-spo-saved-words-agree
                             fn-bs-config-decode fn-spo-saved-format-word
                             fn-f9-saved-format-word))))))

(local
 (defthm fn-spo-foreign-is-neither
   (implies (fn-spo-foreign-formatp octets)
            (and (not (fn-bs-config-decode octets))
                 (not (fn-spo-format-9p octets))))
   :hints (("Goal" :use (fn-spo-decoded-names-format-10 fn-spo-saved-words-agree)
            :in-theory (e/d (fn-spo-format-9p fn-spo-foreign-formatp fn-bs-meta-formatp)
                            (fn-spo-decoded-names-format-10 fn-spo-saved-words-agree
                             fn-bs-config-decode fn-spo-saved-format-word
                             fn-f9-saved-format-word))))))

; -----------------------------------------------------------------------------
; KEYSTONE (the open of what `init' and `store import' write).  Every valid
; profile's frame -- the frame `init' (fn-bs-config-frame-for-profile) and
; `store import' (books/store-export.lisp) seal -- opens as itself.
(defthm fn-spo-open-of-a-valid-profile-opens-it
  (implies (fn-bs-profile-validp values)
           (equal (fn-spo-config-open (fn-bs-config-encode values))
                  (list :opened values)))
  :hints (("Goal" :use fn-bs-config-decode-of-encode
           :in-theory (e/d (fn-spo-config-open)
                           (fn-bs-config-decode-of-encode fn-bs-config-decode
                            fn-bs-config-encode fn-bs-profile-validp
                            fn-spo-format-9p fn-spo-foreign-formatp
                            fn-spo-layout-fields)))))

; KEYSTONE (D34, the release before, by name).  Every sealed profile frame
; whose format word is fn-store-9 -- what every format-9 `init' and `store
; import' wrote, of any layout -- is refused at the open the host calls as
; `:store-format-9', whose line names the way out (export with that release,
; import here); never opened, never translated, never the generic fault.
(defthm fn-spo-open-of-a-format-9-frame-refuses-by-name
  (implies (fn-spo-format-9p octets)
           (equal (fn-spo-config-open octets)
                  (list :refused :store-format-9)))
  :hints (("Goal" :use fn-spo-format-9-is-not-decoded
           :in-theory (e/d (fn-spo-config-open)
                           (fn-spo-format-9-is-not-decoded fn-bs-config-decode
                            fn-spo-format-9p fn-spo-foreign-formatp
                            fn-spo-layout-fields)))))

; KEYSTONE (D34, one format).  The open answers `:store-format' exactly for a
; sealed profile frame naming a word other than fn-store-10 and fn-store-9.
(defthm fn-spo-config-open-store-format-is-exactly-a-foreign-frame
  (equal (equal (fn-spo-config-open octets) (list :refused :store-format))
         (fn-spo-foreign-formatp octets))
  :hints (("Goal" :use fn-spo-foreign-is-neither
           :in-theory (e/d (fn-spo-config-open)
                           (fn-spo-foreign-is-neither fn-bs-config-decode
                            fn-spo-format-9p fn-spo-foreign-formatp
                            fn-spo-layout-fields)))))

; -----------------------------------------------------------------------------
; The layout

(local
 (defun fn-spo-all-nat-specp (specs)
   (if (consp specs)
       (and (equal (car specs) :nat) (fn-spo-all-nat-specp (cdr specs)))
     t)))

(local
 (defthm fn-spo-nat-specs-all-nat
   (fn-spo-all-nat-specp (fn-spo-nat-specs n))
   :hints (("Goal" :induct (fn-spo-nat-specs n)
            :in-theory (disable floor mod)))))

(local
 (defthm fn-spo-nat-specs-spec-listp
   (fn-frame-spec-listp (fn-spo-nat-specs n))
   :hints (("Goal" :induct (fn-spo-nat-specs n)
            :in-theory '(fn-spo-nat-specs fn-frame-spec-listp
                         (:e fn-frame-specp) car-cons cdr-cons
                         (:t fn-spo-nat-specs) (:e fn-frame-spec-listp))))))

(local
 (defthm fn-spo-nat-specs-len
   (equal (len (fn-spo-nat-specs n)) (nfix n))
   :hints (("Goal" :induct (fn-spo-nat-specs n)
            :in-theory (disable floor mod)))))

(local
 (defthm fn-spo-nat-field-octets-len
   (implies (fn-frame-field-okp :nat v)
            (equal (len (fn-frame-field-octets :nat v)) 8))
   :hints (("Goal" :in-theory (enable fn-frame-field-octets fn-frame-field-okp
                                      fn-frame-natp fn-frame-u64-bytes-len)))))

(local
 (defthm fn-spo-all-nat-fields-octets-len
   (implies (and (fn-spo-all-nat-specp specs)
                 (fn-frame-values-okp specs values))
            (equal (len (fn-frame-fields-octets specs values))
                   (* 8 (len specs))))
   :hints (("Goal" :induct (fn-frame-values-okp specs values)
            :in-theory (e/d (fn-frame-values-okp fn-frame-fields-octets)
                            (fn-frame-field-octets fn-frame-field-okp))))))

(local
 (encapsulate ()
   (local (include-book "arithmetic/top" :dir :system))
   (defthm fn-spo-eight-fields-width
     (implies (natp n)
              (and (equal (mod (* 8 n) 8) 0)
                   (equal (floor (* 8 n) 8) n))))))

(local
 (defthm fn-spo-split-eight-len
   (implies (fn-frame-split 8 x)
            (equal (len (cdr (fn-frame-split 8 x))) (- (len x) 8)))
   :hints (("Goal" :use ((:instance fn-frame-split-suffix-len (n 8) (xs x)))
            :in-theory (disable fn-frame-split-suffix-len fn-frame-split)))))

; A run of u64 fields consumes eight octets a field.
(local
 (defthm fn-spo-nat-parse-consumes-eight
   (implies (fn-frame-parse-okp (fn-frame-field-parse :nat x))
            (equal (len x)
                   (+ 8 (len (fn-frame-parse-rest (fn-frame-field-parse :nat x))))))
   :hints (("Goal" :use ((:instance fn-frame-split-suffix-len (n 8) (xs x)))
            :in-theory (e/d (fn-frame-field-parse)
                            (fn-frame-split-suffix-len fn-frame-split))))))

(local
 (defthm fn-spo-nat-run-consumes-eight-a-field
   (implies (and (fn-spo-all-nat-specp specs)
                 (fn-frame-parse-okp (fn-frame-fields-parse-aux specs x)))
            (equal (len x)
                   (+ (* 8 (len specs))
                      (len (fn-frame-parse-rest
                            (fn-frame-fields-parse-aux specs x))))))
   :hints (("Goal" :induct (fn-frame-fields-parse-aux specs x)
            :in-theory (e/d (fn-frame-fields-parse-aux) (fn-frame-field-parse))))))

; Every frame the profile decoder decodes has this release's layout.
(local
 (defthm fn-spo-layout-fields-of-a-decoded-frame
   (implies (fn-bs-config-decode octets)
            (equal (fn-spo-layout-fields octets)
                   *fn-spo-release-layout-fields*))
   :hints (("Goal"
            :use ((:instance fn-spo-fields-parse-car
                             (specs *fn-bs-meta-profile-spec*)
                             (octets (fn-frame-result-payload
                                      (fn-frame-open octets
                                                     *fn-bs-meta-max-config-payload*))))
                  fn-spo-decoded-is-valid
                  (:instance fn-spo-valid-names-format-10
                             (values (fn-bs-config-decode octets)))
                  (:instance fn-spo-nat-run-consumes-eight-a-field
                             (specs (cdr *fn-bs-meta-profile-spec*))
                             (x (fn-frame-parse-rest
                                 (fn-frame-field-parse
                                  :text (fn-frame-result-payload
                                         (fn-frame-open
                                          octets *fn-bs-meta-max-config-payload*)))))))
            :expand ((fn-bs-config-decode octets)
                     (fn-frame-fields-parse *fn-bs-meta-profile-spec*
                                            (fn-frame-result-payload
                                             (fn-frame-open
                                              octets *fn-bs-meta-max-config-payload*)))
                     (fn-frame-fields-parse-aux *fn-bs-meta-profile-spec*
                                                (fn-frame-result-payload
                                                 (fn-frame-open
                                                  octets *fn-bs-meta-max-config-payload*))))
            :in-theory (e/d (fn-spo-layout-fields fn-bs-meta-formatp)
                            (fn-spo-fields-parse-car fn-spo-decoded-is-valid
                             fn-spo-valid-names-format-10
                             fn-spo-nat-run-consumes-eight-a-field
                             fn-bs-profile-validp fn-frame-fields-parse
                             fn-frame-fields-parse-aux
                             fn-frame-field-parse fn-frame-open
                             fn-bs-meta-frame-okp))))))

; The frame of N u64 fields reads back as N fields.
(local
 (defthm fn-spo-layout-spec-spec-listp
   (fn-frame-spec-listp (fn-spo-layout-spec n))
   :hints (("Goal" :in-theory '(fn-spo-layout-spec fn-frame-spec-listp
                                (:e fn-frame-specp) car-cons cdr-cons
                                fn-spo-nat-specs-spec-listp)))))

(local
 (defthm fn-spo-seal-octet-listp
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (fn-cbor-octet-listp (fn-frame-seal magic version kind payload)))
   :hints (("Goal"
            :use ((:instance fn-frame-digestp-of-fn-frame-digest
                             (octets (fn-frame-protected magic version kind payload)))
                  (:instance fn-cbor-u32-bytes-are-octets (n (len payload))))
            :in-theory (e/d (fn-frame-seal fn-frame-encode fn-frame-protected
                             fn-frame-header fn-frame-inputp fn-frame-magicp
                             fn-frame-digestp fn-cbor-octet-listp-append)
                            (fn-frame-digestp-of-fn-frame-digest
                             fn-cbor-u32-bytes-are-octets))))))

(local
 (defthm fn-spo-layout-frame-inputp
   (implies (and (fn-frame-values-okp (fn-spo-layout-spec n) values)
                 (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                     *fn-bs-meta-max-config-payload*))
            (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-frame-fields-octets (fn-spo-layout-spec n) values)
                             *fn-bs-meta-max-config-payload*))
   :hints (("Goal"
            :use ((:instance fn-frame-fields-octets-are-octets
                             (specs (fn-spo-layout-spec n))))
            :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                            (fn-frame-fields-octets-are-octets
                             fn-spo-layout-spec fn-frame-fields-octets
                             fn-frame-values-okp))))))

(local
 (defthm fn-spo-layout-frame-opens
   (implies (and (natp n)
                 (fn-frame-values-okp (fn-spo-layout-spec n) values)
                 (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                     *fn-bs-meta-max-config-payload*))
            (and (fn-cbor-octet-listp (fn-spo-layout-frame n values))
                 (equal (fn-frame-open (fn-spo-layout-frame n values)
                                       *fn-bs-meta-max-config-payload*)
                        (fn-frame-ok *fn-bs-meta-magic* *fn-bs-meta-version*
                                     *fn-bs-meta-config-kind*
                                     (fn-frame-fields-octets
                                      (fn-spo-layout-spec n) values)))))
   :hints (("Goal"
            :use ((:instance fn-spo-layout-frame-inputp)
                  (:instance fn-frame-open-of-seal
                             (magic *fn-bs-meta-magic*)
                             (version *fn-bs-meta-version*)
                             (kind *fn-bs-meta-config-kind*)
                             (payload (fn-frame-fields-octets
                                       (fn-spo-layout-spec n) values))
                             (max-payload *fn-bs-meta-max-config-payload*))
                  (:instance fn-spo-seal-octet-listp
                             (magic *fn-bs-meta-magic*)
                             (version *fn-bs-meta-version*)
                             (kind *fn-bs-meta-config-kind*)
                             (payload (fn-frame-fields-octets
                                       (fn-spo-layout-spec n) values))
                             (max-payload *fn-bs-meta-max-config-payload*)))
            :in-theory '(fn-spo-layout-frame nfix natp)))))

; The head (the format word) of a layout frame's payload, and its rest: the
; run of N u64 fields.
(local
 (defthm fn-spo-head-of-a-layout-frame-payload
   (implies (fn-frame-values-okp (fn-spo-layout-spec n) values)
            (equal (fn-frame-field-parse
                    :text (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                   (fn-frame-parse-ok
                    (car values)
                    (fn-frame-fields-octets (fn-spo-nat-specs n) (cdr values)))))
   :hints (("Goal"
            :use ((:instance fn-frame-field-parse-of-octets-text
                             (value (car values))
                             (rest (fn-frame-fields-octets (fn-spo-nat-specs n)
                                                           (cdr values))))
                  (:instance fn-frame-fields-octets-are-octets
                             (specs (fn-spo-nat-specs n)) (values (cdr values))))
            :expand ((fn-frame-fields-octets (cons :text (fn-spo-nat-specs n)) values)
                     (fn-frame-values-okp (cons :text (fn-spo-nat-specs n)) values)
                     (fn-frame-field-okp :text (car values)))
            :in-theory (e/d (fn-spo-layout-spec)
                            (fn-frame-field-parse-of-octets-text
                             fn-frame-fields-octets-are-octets
                             fn-frame-field-parse fn-frame-field-octets
                             fn-frame-fields-octets fn-frame-values-okp
                             fn-frame-field-okp))))))

(local
 (defthm fn-spo-layout-values-tail
   (implies (fn-frame-values-okp (fn-spo-layout-spec n) values)
            (fn-frame-values-okp (fn-spo-nat-specs n) (cdr values)))
   :hints (("Goal"
            :expand ((fn-frame-values-okp (cons :text (fn-spo-nat-specs n)) values))
            :in-theory '(fn-spo-layout-spec car-cons cdr-cons)))))

(defthm fn-spo-layout-fields-of-a-layout-frame
  (implies (and (natp n)
                (fn-frame-values-okp (fn-spo-layout-spec n) values)
                (fn-bs-meta-formatp (car values))
                (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                    *fn-bs-meta-max-config-payload*))
           (equal (fn-spo-layout-fields (fn-spo-layout-frame n values)) n))
  :hints (("Goal"
           :in-theory (e/d (fn-spo-layout-fields fn-bs-meta-frame-okp)
                           (fn-spo-layout-spec fn-spo-layout-frame
                            fn-frame-fields-octets fn-frame-fields-parse-aux
                            fn-frame-field-parse
                            fn-frame-seal fn-frame-open fn-frame-values-okp
                            floor mod)))))

; The word of a layout frame is its first value.
(local
 (defthm fn-spo-saved-format-word-of-a-layout-frame
   (implies (and (natp n)
                 (fn-frame-values-okp (fn-spo-layout-spec n) values)
                 (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                     *fn-bs-meta-max-config-payload*))
            (equal (fn-spo-saved-format-word (fn-spo-layout-frame n values))
                   (car values)))
   :hints (("Goal"
            :in-theory (e/d (fn-spo-saved-format-word fn-bs-meta-frame-okp)
                            (fn-spo-layout-spec fn-spo-layout-frame
                             fn-frame-fields-octets fn-frame-field-parse
                             fn-frame-seal fn-frame-open fn-frame-values-okp))))))

;; KEYSTONE (PKT-705, the layout).  Every format-10 profile frame a release
;; wrote under a layout of N u64 fields other than this release's is refused
;; at the open the host calls by the name of its layout, with N; never the
;; generic fault (:rejected), and never opened or translated (D34).
(defthm fn-spo-open-of-another-layout-refuses-by-name
  (implies (and (natp n)
                (not (equal n *fn-spo-release-layout-fields*))
                (fn-frame-values-okp (fn-spo-layout-spec n) values)
                (fn-bs-meta-formatp (car values))
                (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                    *fn-bs-meta-max-config-payload*))
           (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                  (list :refused :profile-layout n)))
  :hints (("Goal" :use (fn-spo-layout-fields-of-a-layout-frame
                        fn-spo-saved-format-word-of-a-layout-frame
                        (:instance fn-spo-saved-words-agree
                                   (octets (fn-spo-layout-frame n values)))
                        (:instance fn-spo-layout-fields-of-a-decoded-frame
                                   (octets (fn-spo-layout-frame n values))))
           :in-theory (e/d (fn-spo-config-open fn-spo-format-9p
                            fn-spo-foreign-formatp fn-bs-meta-formatp)
                           (fn-spo-layout-fields-of-a-layout-frame
                            fn-spo-saved-format-word-of-a-layout-frame
                            fn-spo-saved-words-agree fn-f9-saved-format-word
                            fn-spo-layout-fields-of-a-decoded-frame
                            fn-spo-layout-fields fn-spo-layout-frame
                            fn-spo-saved-format-word
                            fn-spo-layout-spec fn-bs-config-decode
                            fn-frame-values-okp fn-frame-fields-octets)))))

; KEYSTONE (the refinement, PKT-705).  No refusal is a frame the decoder
; decodes: every store the open opens is opened, whatever its word or layout.
(defthm fn-spo-config-open-refuses-no-decoded-frame
  (implies (fn-bs-config-decode octets)
           (equal (fn-spo-config-open octets)
                  (list :opened (fn-bs-config-decode octets))))
  :hints (("Goal" :in-theory (e/d (fn-spo-config-open)
                                  (fn-bs-config-decode fn-spo-format-9p
                                   fn-spo-foreign-formatp fn-spo-layout-fields)))))

; The generic fault is left to octets with this release's layout or with no
; layout (no sealed fn-store-10 profile frame whose tail is a run of u64
; fields): a corrupted file, as before.
(defthm fn-spo-config-open-rejected-has-this-layout-or-none-by-definition
  (implies (equal (fn-spo-config-open octets) '(:rejected))
           (or (not (fn-spo-layout-fields octets))
               (equal (fn-spo-layout-fields octets)
                      *fn-spo-release-layout-fields*)))
  :hints (("Goal" :in-theory (e/d (fn-spo-config-open)
                                  (fn-spo-layout-fields fn-bs-config-decode
                                   fn-spo-format-9p fn-spo-foreign-formatp)))))

(in-theory (disable fn-spo-config-open fn-spo-saved-format-word
                    fn-spo-layout-fields fn-spo-layout-frame
                    fn-spo-format-9p fn-spo-foreign-formatp))
