; fn: the open of a store's saved profile, and its refusals by name
; (PKT-471, the coordinator's decision of 2026-09-26; D34).
;
; PKT-467 added one arm to the profile relation (books/byte-store-frame.lisp
; `fn-bs-profile-invalid-reason'): a record bound R above
; *fn-stxa-max-octets*, the widest report a kind-6 consumer poll reply can
; carry, is refused as `:max-record-octets-above-the-poll-reply'.  A store
; saved before that arm with R in the 355-octet window between the poll
; reply's ceiling and the codec's u32 no longer decodes, and the open used to
; answer the host's generic fault ("ACL2 rejected durable configuration
; frame", exit 4).  The decision: the open refuses such a store BY NAME.
; D34 (fresh deploys, no migrations) removed the in-place repair that
; lowered R: the refusal names the way out, a reinstall and an import.
; Nothing is translated at open.
;
; D34 also makes the store format one format: a profile frame whose format
; word is not fn-store-9 (a format-8 store of the per-file layout, a format-7
; store, or any other) is refused at the open by name, `:store-format', never
; translated (lane log-recovery: the format-8 scaffold of PKT-COL-1 is gone;
; a format-8 history travels by `store export' on the release that made it
; and `store import' here, books/store-export.lisp fn-sxp-log-profile).
;
;   * `fn-spo-config-open' OCTETS: the open of config.json the host calls
;     (host/native/io.lisp `fnn-metadata-config-decode', through
;     host/store-host.lisp `fn-store-metadata-config-open'; every open reads
;     the profile there: `fnn-load-config' from `fnn-acquire', so owner
;     start, `store recover', `inspect', `checkpoint', `status' and the
;     offline `health').  It answers (:opened VALUES), the profile the store
;     runs under; (:refused :max-record-octets-above-the-poll-reply), a
;     format-8 profile in the window; (:refused :store-format), a sealed
;     profile frame of another format; or (:rejected), a frame that is no
;     saved profile at all (a corrupted file: the host's fault, as before).
;
; The saved profiles are those the format-8 encoder wrote under the relation
; before PKT-467: `fn-bs-profile-v2-invalid-reason' below, the text of
; `fn-bs-profile-invalid-reason' at dev ea35ba7b without that one arm.  Every
; profile the current relation admits is among them
; (`fn-bs-profile-valid-is-v2-valid'), and so is every profile the image
; before P6 saved (books/byte-store-profile-v1.lisp, whose relation reads the
; article record at a larger overhead than this one).
(in-package "ACL2")
(include-book "store-profile-facts")
(include-book "byte-store-profile-v1")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))

; -----------------------------------------------------------------------------
; The relation the saved profiles met (before PKT-467), frozen

(defun fn-bs-profile-v2-invalid-reason (values)
  (declare (xargs :guard t))
  (let ((tx (fn-bs-pf 2 values)) (h (fn-bs-pf 3 values))
        (r (fn-bs-pf 4 values)) (a (fn-bs-pf 5 values))
        (g (fn-bs-pf 6 values)) (n (fn-bs-pf 7 values))
        (k (fn-bs-pf 8 values)))
    (cond ((not (fn-frame-values-okp *fn-bs-meta-profile-spec* values))
           :layout)
          ((not (fn-bs-meta-formatp (fn-bs-meta-nth 0 values)))
           :format)
          ((not (equal (fn-bs-meta-nth 1 values) *fn-bs-meta-frontier-format*))
           :frontier-format)
          ((or (< tx 1) (< *fn-bs-profile-transaction-ceiling* tx))
           :max-transactions-outside-txid-width)
          ((< h r) :max-history-octets-below-max-record-octets)
          ((< r *fn-bs-profile-min-record-octets*)
           :max-record-octets-below-an-event-kind)
          ((< *fn-bs-profile-record-ceiling-codec* r)
           :max-record-octets-above-codec)
          ((or (< a 1) (< *fn-bs-profile-article-ceiling-codec* a))
           :max-article-octets-outside-codec)
          ((or (< g 1) (< *fn-bs-profile-groups-ceiling-codec* g))
           :max-groups-per-article-outside-codec)
          ((or (< n 1) (< *fn-bs-profile-group-name-ceiling-codec* n))
           :max-group-name-octets-outside-codec)
          ((< r (fn-record-encoded-octets-ceiling a g))
           :max-record-octets-below-the-article-record)
          ((or (< k 1) (< tx k)) :max-open-suffix-outside-transactions)
          ((not (and (fn-bs-profile-countp (fn-bs-pf 9 values))
                     (fn-bs-profile-countp (fn-bs-pf 10 values))
                     (fn-bs-profile-countp (fn-bs-pf 11 values))
                     (fn-bs-profile-countp (fn-bs-pf 12 values))
                     (fn-bs-profile-countp (fn-bs-pf 13 values))))
           :namespace-count-outside-width)
          ((< 1 (fn-bs-pf 14 values)) :history-marker-not-a-word)
          ; The header-limit arms (lane header-limits-profile): the layout
          ; grew three fields under D34, so every relation over it reads them
          ; as `fn-bs-profile-invalid-reason' does.
          ((or (< (fn-bs-pf 15 values) 1)
               (< (fn-bs-pf 16 values) (fn-bs-pf 15 values)))
           :max-header-fields-outside-lines)
          ((< (fn-bs-pf 17 values) (fn-bs-pf 16 values))
           :max-header-lines-above-octets)
          ((< *fn-bs-profile-article-ceiling-codec* (fn-bs-pf 17 values))
           :max-header-octets-above-codec)
          (t nil))))

(defun fn-bs-profile-v2-validp (values)
  (declare (xargs :guard t))
  (not (fn-bs-profile-v2-invalid-reason values)))

; The frame the format-8 encoder writes for VALUES: `fn-bs-config-encode''s
; body without its validator, which is the part PKT-467 changed.
(defun fn-spo-saved-frame (values)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                 *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets *fn-bs-meta-profile-spec* values)))

; -----------------------------------------------------------------------------
; The open

; The format-8 values a config.json frame holds, valid or not: the steps of
; `fn-bs-config-decode''s format-8 branch without its validator; NIL for a
; frame that does not open or does not parse as format 8.
(defun fn-spo-saved-format-8 (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bs-meta-profile-spec*
                       (fn-frame-result-payload frame))))
          (if (fn-frame-parse-okp parsed)
              (fn-frame-parse-value parsed)
            nil))))))

; The format word of a sealed profile frame (its first text field), valid
; profile or not; NIL for a frame that does not open as one.
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

; D34: a sealed profile frame whose format is not a format this image opens
; (9, and 8 while PKT-830 stands).
(defun fn-spo-foreign-formatp (octets)
  (declare (xargs :guard t))
  (let ((word (fn-spo-saved-format-word octets)))
    (and word (not (fn-bs-meta-formatp word)) t)))

(defun fn-spo-in-the-windowp (saved)
  (declare (xargs :guard t))
  (equal (fn-bs-profile-invalid-reason saved)
         :max-record-octets-above-the-poll-reply))

;; PKT-705 (D34): the profile's layout.  A store's config.json is a sealed
;; profile frame of the format word fn-store-8 followed by the frontier text and
;; a run of u64 fields; header-limits-profile (batch AS) grew that run from
;; 13 fields to 16 under the same word, so the width of the run is how the open
;; tells a store made by another release.  No such store is translated
;; (D34): it is refused by name, with the way out.

(defun fn-spo-nat-specs (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons :nat (fn-spo-nat-specs (1- n)))))

; The profile layout of N u64 fields: the spec a release whose profile had N
; fields sealed its config.json under.  (fn-spo-layout-spec 16) is
; *fn-bs-meta-profile-spec*; (fn-spo-layout-spec 13) is the layout before
; batch AS.
(defun fn-spo-layout-spec (n)
  (declare (xargs :guard (natp n)))
  (list* :text :text (fn-spo-nat-specs n)))

(defconst *fn-spo-release-layout-fields*
  (- (len *fn-bs-meta-profile-spec*) 2))

; The frame a release whose profile layout has N fields wrote for VALUES.
(defun fn-spo-layout-frame (n values)
  (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                 *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets (fn-spo-layout-spec (nfix n)) values)))

; The layout of a config.json: the number of u64 fields after a format word
; (fn-store-8 or fn-store-9, lane commit-onto-log) and a second text field, when the sealed profile frame is exactly
; that; NIL for any other octets (no sealed profile frame, another format
; word, or a tail that is no run of u64 fields).
(defun fn-spo-layout-fields (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-config-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-config-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-config-payload*))
          nil
        (let ((head (fn-frame-fields-parse-aux
                     '(:text :text) (fn-frame-result-payload frame))))
          (if (not (and (fn-frame-parse-okp head)
                        (consp (fn-frame-parse-value head))
                        (fn-bs-meta-formatp (car (fn-frame-parse-value head)))))
              nil
            (let ((width (len (fn-frame-parse-rest head))))
              (if (equal (mod width 8) 0)
                  (floor width 8)
                nil))))))))

; The open the host calls (host/native/io.lisp `fnn-metadata-config-decode').
(defun fn-spo-config-open (octets)
  (declare (xargs :guard t))
  (let ((fields (fn-spo-layout-fields octets)))
    (if (and fields (not (equal fields *fn-spo-release-layout-fields*)))
        (list :refused :profile-layout fields)
      (let ((saved (fn-spo-saved-format-8 octets)))
        (if (and saved (fn-spo-in-the-windowp saved))
            (list :refused :max-record-octets-above-the-poll-reply)
          (let ((decoded (fn-bs-config-decode octets)))
            (cond ((and decoded (fn-bs-profile-admittedp decoded))
                   (if (fn-bs-profile-logp decoded)
                       (list :opened decoded)
                     (list :refused :store-format)))
                  ((fn-spo-foreign-formatp octets) (list :refused :store-format))
                  (t (list :rejected)))))))))

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
  (cond ((equal verdict (list :refused :max-record-octets-above-the-poll-reply))
         "open refused reason=max-record-octets-above-the-poll-reply: the profile record bound exceeds the poll reply width; reinstall from the release and import")
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
; The relation's half

(defthm fn-bs-profile-valid-is-v2-valid
  (implies (fn-bs-profile-validp values)
           (fn-bs-profile-v2-validp values))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp
                                   fn-bs-profile-invalid-reason)
                                  (fn-bs-pf fn-frame-values-okp
                                   fn-record-encoded-octets-ceiling)))))

; The image before P6 saved its profiles under the frozen relation of
; books/byte-store-profile-v1.lisp; each of them is a saved profile here too.
(defthm fn-bs-profile-v1-valid-is-v2-valid
  (implies (not (fn-bs-profile-v1-invalid-reason values))
           (fn-bs-profile-v2-validp values))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-v2-invalid-reason
                                   fn-record-encoded-octets-ceiling)
                                  (fn-bs-pf fn-frame-values-okp)))))

(defthm fn-bs-profile-v2-valid-within-the-width-is-valid
  (implies (and (fn-bs-profile-v2-validp values)
                (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*))
           (fn-bs-profile-validp values))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp
                                   fn-bs-profile-invalid-reason)
                                  (fn-bs-pf fn-frame-values-okp
                                   fn-record-encoded-octets-ceiling)))))

(defthm fn-bs-profile-v2-valid-above-the-width-is-in-the-window
  (implies (and (fn-bs-profile-v2-validp values)
                (< *fn-stxa-max-octets* (fn-bs-pf 4 values)))
           (fn-spo-in-the-windowp values))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-invalid-reason)
                                  (fn-bs-pf fn-frame-values-okp
                                   fn-record-encoded-octets-ceiling)))))

(local
 (defthm fn-bs-profile-v2-valid-shape
   (implies (fn-bs-profile-v2-validp values)
            (and (fn-frame-values-okp *fn-bs-meta-profile-spec* values)
                 (fn-bs-meta-formatp (fn-bs-meta-nth 0 values))
                 (equal (fn-bs-meta-nth 1 values)
                        *fn-bs-meta-frontier-format*)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable fn-bs-pf fn-frame-values-okp
                                       fn-record-encoded-octets-ceiling)))))

; -----------------------------------------------------------------------------
; The saved frame reads back to its values (under A-CRYPTO, through
; fn-frame-open-of-seal), for every value of the format-8 shape

(local
 (defun fn-spo-all-nat-specp (specs)
   (if (consp specs)
       (and (equal (car specs) :nat) (fn-spo-all-nat-specp (cdr specs)))
     t)))

(local
 (defthm fn-spo-all-nat-fields-octets-len
   (implies (and (fn-spo-all-nat-specp specs)
                 (fn-frame-values-okp specs values))
            (equal (len (fn-frame-fields-octets specs values))
                   (* 8 (len specs))))
   :hints (("Goal" :induct (fn-frame-values-okp specs values)
            :in-theory (enable fn-frame-field-octets fn-frame-values-okp
                               fn-frame-fields-octets fn-frame-field-okp
                               fn-frame-natp fn-frame-u64-bytes-len)))))

(local
 (defun fn-spo-shapep (values)
   (and (fn-frame-values-okp *fn-bs-meta-profile-spec* values)
        (fn-bs-meta-formatp (fn-bs-meta-nth 0 values))
        (equal (fn-bs-meta-nth 1 values) *fn-bs-meta-frontier-format*))))

(local
 (defthm fn-spo-fields-octets-len
   (implies (fn-spo-shapep values)
            (equal (len (fn-frame-fields-octets *fn-bs-meta-profile-spec*
                                                values))
                   (+ (len (fn-frame-field-octets :text *fn-bs-meta-format-8*))
                      (len (fn-frame-field-octets
                            :text *fn-bs-meta-frontier-format*))
                      128)))
   :hints (("Goal"
            :use ((:instance fn-spo-all-nat-fields-octets-len
                             (specs (cddr *fn-bs-meta-profile-spec*))
                             (values (cddr values))))
            :expand ((fn-frame-fields-octets *fn-bs-meta-profile-spec* values)
                     (fn-frame-fields-octets (cdr *fn-bs-meta-profile-spec*)
                                             (cdr values))
                     (fn-frame-values-okp *fn-bs-meta-profile-spec* values)
                     (fn-frame-values-okp (cdr *fn-bs-meta-profile-spec*)
                                          (cdr values))
                     (fn-bs-meta-nth 0 values) (fn-bs-meta-nth 1 values)
                     (fn-bs-meta-nth 0 (cdr values)))
            :in-theory (disable fn-spo-all-nat-fields-octets-len
                                fn-frame-field-octets)))))

(local
 (defthm fn-spo-frame-inputp
   (implies (fn-spo-shapep values)
            (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-frame-fields-octets *fn-bs-meta-profile-spec*
                                                     values)
                             *fn-bs-meta-max-config-payload*))
   :hints (("Goal"
            :use ((:instance fn-spo-fields-octets-len)
                  (:instance fn-frame-fields-octets-are-octets
                             (specs *fn-bs-meta-profile-spec*)))
            :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                            (fn-spo-fields-octets-len
                             fn-frame-fields-octets-are-octets))))))

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
 (defthm fn-spo-saved-format-8-of-saved-frame
   (implies (fn-spo-shapep values)
            (equal (fn-spo-saved-format-8 (fn-spo-saved-frame values))
                   values))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-open-of-seal
                             (magic *fn-bs-meta-magic*)
                             (version *fn-bs-meta-version*)
                             (kind *fn-bs-meta-config-kind*)
                             (payload (fn-frame-fields-octets
                                       *fn-bs-meta-profile-spec* values))
                             (max-payload *fn-bs-meta-max-config-payload*))
                  (:instance fn-spo-seal-octet-listp
                             (magic *fn-bs-meta-magic*)
                             (version *fn-bs-meta-version*)
                             (kind *fn-bs-meta-config-kind*)
                             (payload (fn-frame-fields-octets
                                       *fn-bs-meta-profile-spec* values))
                             (max-payload *fn-bs-meta-max-config-payload*))
                  (:instance fn-spo-frame-inputp)
                  (:instance fn-frame-fields-parse-of-octets
                             (specs *fn-bs-meta-profile-spec*)))
            :in-theory (e/d (fn-spo-saved-frame fn-bs-meta-frame-okp
                             fn-frame-inputp)
                            (fn-frame-open-of-seal fn-spo-seal-octet-listp
                             fn-spo-frame-inputp
                             fn-frame-fields-parse-of-octets))))))

(local
 (defthm fn-spo-saved-frame-of-valid-is-encode
   (implies (fn-bs-profile-validp values)
            (equal (fn-spo-saved-frame values) (fn-bs-config-encode values)))
   :hints (("Goal" :in-theory (e/d (fn-spo-saved-frame fn-bs-config-encode)
                                   (fn-bs-profile-validp))))))

(local
 (defthm fn-spo-v2-valid-is-shape
   (implies (fn-bs-profile-v2-validp values)
            (fn-spo-shapep values))
   :hints (("Goal" :use fn-bs-profile-v2-valid-shape
            :in-theory (e/d (fn-spo-shapep)
                            (fn-bs-profile-v2-validp fn-bs-meta-nth
                             fn-frame-values-okp fn-bs-profile-v2-valid-shape))))))

(local (in-theory (disable fn-spo-shapep)))

(local
 (defthm fn-spo-validp-is-admitted
   (implies (fn-bs-profile-validp values)
            (fn-bs-profile-admittedp values))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-admittedp fn-bs-profile-of)
                                   (fn-bs-profile-validp))))))

(local
 (defthm fn-spo-saved-format-8-of-encode
   (implies (fn-bs-profile-validp values)
            (equal (fn-spo-saved-format-8 (fn-bs-config-encode values))
                   values))
   :hints (("Goal" :use (fn-spo-saved-format-8-of-saved-frame
                         fn-spo-saved-frame-of-valid-is-encode
                         fn-bs-profile-valid-is-v2-valid
                         fn-spo-v2-valid-is-shape)
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-spo-valid-is-not-in-the-window
   (implies (fn-bs-profile-validp values)
            (not (fn-spo-in-the-windowp values)))
   :hints (("Goal" :in-theory '(fn-bs-profile-validp fn-spo-in-the-windowp)))))

;; -----------------------------------------------------------------------------
;; The layout (PKT-705): every frame the decoder reads has this release's
;; layout, and a frame of any other layout reads as that layout.

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
 (defthm fn-spo-nat-run-consumes-eight-a-field
   (implies (and (fn-spo-all-nat-specp specs)
                 (fn-frame-parse-okp (fn-frame-fields-parse-aux specs x)))
            (equal (len x)
                   (+ (* 8 (len specs))
                      (len (fn-frame-parse-rest
                            (fn-frame-fields-parse-aux specs x))))))
   :hints (("Goal" :induct (fn-frame-fields-parse-aux specs x)
            :in-theory (enable fn-frame-fields-parse-aux fn-frame-field-parse)))))

; The head (the two texts) of a payload that parses under this release's
; layout: the same format word, and 128 octets before the parse's rest.
(local
 (defthm fn-spo-head-of-a-profile-parse
   (implies (fn-frame-parse-okp
             (fn-frame-fields-parse-aux *fn-bs-meta-profile-spec* p))
            (and (fn-frame-parse-okp (fn-frame-fields-parse-aux '(:text :text) p))
                 (consp (fn-frame-parse-value
                         (fn-frame-fields-parse-aux '(:text :text) p)))
                 (equal (car (fn-frame-parse-value
                              (fn-frame-fields-parse-aux '(:text :text) p)))
                        (car (fn-frame-parse-value
                              (fn-frame-fields-parse-aux
                               *fn-bs-meta-profile-spec* p))))
                 (equal (len (fn-frame-parse-rest
                              (fn-frame-fields-parse-aux '(:text :text) p)))
                        (+ 128 (len (fn-frame-parse-rest
                                     (fn-frame-fields-parse-aux
                                      *fn-bs-meta-profile-spec* p)))))))
   :hints (("Goal"
            :expand ((fn-frame-fields-parse-aux *fn-bs-meta-profile-spec* p)
                     (fn-frame-fields-parse-aux (cdr *fn-bs-meta-profile-spec*)
                                                (fn-frame-parse-rest
                                                 (fn-frame-field-parse :text p)))
                     (fn-frame-fields-parse-aux '(:text :text) p)
                     (fn-frame-fields-parse-aux '(:text)
                                                (fn-frame-parse-rest
                                                 (fn-frame-field-parse :text p)))
                     (fn-frame-fields-parse-aux
                      nil
                      (fn-frame-parse-rest
                       (fn-frame-field-parse
                        :text (fn-frame-parse-rest (fn-frame-field-parse :text p))))))
            :use ((:instance fn-spo-nat-run-consumes-eight-a-field
                             (specs (cddr *fn-bs-meta-profile-spec*))
                             (x (fn-frame-parse-rest
                                 (fn-frame-field-parse
                                  :text (fn-frame-parse-rest
                                         (fn-frame-field-parse :text p)))))))
            :in-theory (disable fn-frame-fields-parse-aux fn-frame-field-parse
                                fn-spo-nat-run-consumes-eight-a-field)))))

; Every frame that parses under this release's layout with the format word
; fn-store-8 has this release's layout.
(local
 (defthm fn-spo-layout-fields-of-a-saved-format-8
   (implies (and (fn-spo-saved-format-8 octets)
                 (fn-bs-meta-formatp (car (fn-spo-saved-format-8 octets))))
            (equal (fn-spo-layout-fields octets)
                   *fn-spo-release-layout-fields*))
   :hints (("Goal"
            :use ((:instance fn-spo-head-of-a-profile-parse
                             (p (fn-frame-result-payload
                                 (fn-frame-open octets
                                                *fn-bs-meta-max-config-payload*)))))
            :in-theory (e/d (fn-spo-saved-format-8 fn-spo-layout-fields
                             fn-frame-fields-parse)
                            (fn-spo-head-of-a-profile-parse
                             fn-frame-fields-parse-aux fn-frame-open
                             fn-bs-meta-frame-okp))))))

(local
 (defthm fn-spo-decoded-is-saved-format-8
   (implies (fn-bs-config-decode octets)
            (equal (fn-spo-saved-format-8 octets) (fn-bs-config-decode octets)))
   :hints (("Goal" :in-theory (e/d (fn-spo-saved-format-8 fn-bs-config-decode)
                                   (fn-bs-profile-validp fn-frame-fields-parse
                                    fn-frame-open fn-bs-meta-frame-okp))))))

(local
 (defthm fn-spo-valid-names-format-8
   (implies (fn-bs-profile-validp values)
            (fn-bs-meta-formatp (car values)))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp fn-bs-profile-invalid-reason
                                    fn-bs-meta-nth)
                                   (fn-bs-pf fn-frame-values-okp
                                    fn-record-encoded-octets-ceiling))))))

(local
 (defthm fn-spo-decoded-is-valid
   (implies (fn-bs-config-decode octets)
            (fn-bs-profile-validp (fn-bs-config-decode octets)))
   :hints (("Goal" :in-theory (e/d (fn-bs-config-decode)
                                   (fn-bs-profile-validp))))))

; Every frame the profile decoder decodes has this release's layout.
(local
 (defthm fn-spo-layout-fields-of-a-decoded-frame
   (implies (fn-bs-config-decode octets)
            (equal (fn-spo-layout-fields octets)
                   *fn-spo-release-layout-fields*))
   :hints (("Goal" :use (fn-spo-decoded-is-saved-format-8
                         fn-spo-decoded-is-valid
                         (:instance fn-spo-valid-names-format-8
                                    (values (fn-bs-config-decode octets)))
                         fn-spo-layout-fields-of-a-saved-format-8)
            :in-theory (theory 'minimal-theory)))))

; A frame of another format word has no fn-store-8 layout.
(local
 (defthm fn-spo-foreign-frame-has-no-layout
   (implies (fn-spo-foreign-formatp octets)
            (not (fn-spo-layout-fields octets)))
   :hints (("Goal"
            :expand ((fn-frame-fields-parse-aux
                      '(:text :text)
                      (fn-frame-result-payload
                       (fn-frame-open octets *fn-bs-meta-max-config-payload*)))
                     (fn-frame-fields-parse-aux
                      '(:text)
                      (fn-frame-parse-rest
                       (fn-frame-field-parse
                        :text (fn-frame-result-payload
                               (fn-frame-open octets
                                              *fn-bs-meta-max-config-payload*)))))
                     (fn-frame-fields-parse-aux
                      nil
                      (fn-frame-parse-rest
                       (fn-frame-field-parse
                        :text
                        (fn-frame-parse-rest
                         (fn-frame-field-parse
                          :text (fn-frame-result-payload
                                 (fn-frame-open
                                  octets *fn-bs-meta-max-config-payload*))))))))
            :in-theory (e/d (fn-spo-foreign-formatp fn-spo-saved-format-word
                             fn-spo-layout-fields)
                            (fn-frame-fields-parse-aux fn-frame-field-parse
                             fn-frame-open fn-bs-meta-frame-okp))))))

; The frame of N u64 fields reads back as N fields.
(local
 (defthm fn-spo-layout-spec-spec-listp
   (fn-frame-spec-listp (fn-spo-layout-spec n))
   :hints (("Goal" :in-theory '(fn-spo-layout-spec fn-frame-spec-listp
                                (:e fn-frame-specp) car-cons cdr-cons
                                fn-spo-nat-specs-spec-listp)))))

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
 (defthm fn-spo-head-of-a-layout-payload
   (implies (and (fn-frame-spec-listp specs)
                 (fn-frame-values-okp (list* :text :text specs) values))
            (equal (fn-frame-fields-parse-aux
                    '(:text :text)
                    (fn-frame-fields-octets (list* :text :text specs) values))
                   (fn-frame-parse-ok
                    (list (car values) (cadr values))
                    (fn-frame-fields-octets specs (cddr values)))))
   :hints (("Goal"
            :use ((:instance fn-frame-field-parse-of-octets-text
                             (value (car values))
                             (rest (append (fn-frame-field-octets :text (cadr values))
                                           (fn-frame-fields-octets specs (cddr values)))))
                  (:instance fn-frame-field-parse-of-octets-text
                             (value (cadr values))
                             (rest (fn-frame-fields-octets specs (cddr values))))
                  (:instance fn-frame-fields-octets-are-octets
                             (specs specs) (values (cddr values)))
                  (:instance fn-frame-field-octets-are-octets
                             (spec :text) (value (cadr values))))
            :expand ((fn-frame-fields-octets (list* :text :text specs) values)
                     (fn-frame-fields-octets (cons :text specs) (cdr values))
                     (fn-frame-fields-parse-aux
                      '(:text :text)
                      (append (fn-frame-field-octets :text (car values))
                              (fn-frame-field-octets :text (cadr values))
                              (fn-frame-fields-octets specs (cddr values))))
                     (fn-frame-fields-parse-aux
                      '(:text)
                      (append (fn-frame-field-octets :text (cadr values))
                              (fn-frame-fields-octets specs (cddr values))))
                     (fn-frame-fields-parse-aux
                      nil (fn-frame-fields-octets specs (cddr values)))
                     (fn-frame-values-okp (list* :text :text specs) values)
                     (fn-frame-values-okp (cons :text specs) (cdr values))
                     (fn-frame-field-okp :text (car values))
                     (fn-frame-field-okp :text (cadr values)))
            :in-theory (e/d (fn-cbor-octet-listp-append)
                            (fn-frame-field-parse-of-octets-text
                             fn-frame-fields-octets-are-octets
                             fn-frame-field-octets-are-octets
                             fn-frame-field-parse fn-frame-field-octets
                             fn-frame-fields-octets fn-frame-values-okp
                             fn-frame-field-okp fn-frame-fields-parse-aux))))))

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

(local
 (defthm fn-spo-head-of-a-layout-frame-payload
   (implies (fn-frame-values-okp (fn-spo-layout-spec n) values)
            (equal (fn-frame-fields-parse-aux
                    '(:text :text)
                    (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                   (fn-frame-parse-ok
                    (list (car values) (cadr values))
                    (fn-frame-fields-octets (fn-spo-nat-specs n) (cddr values)))))
   :hints (("Goal" :use ((:instance fn-spo-head-of-a-layout-payload
                                    (specs (fn-spo-nat-specs n))))
            :in-theory '(fn-spo-layout-spec fn-spo-nat-specs-spec-listp)))))

(local
 (defthm fn-spo-layout-values-tail
   (implies (fn-frame-values-okp (fn-spo-layout-spec n) values)
            (fn-frame-values-okp (fn-spo-nat-specs n) (cddr values)))
   :hints (("Goal"
            :expand ((fn-frame-values-okp (list* :text :text (fn-spo-nat-specs n))
                                          values)
                     (fn-frame-values-okp (cons :text (fn-spo-nat-specs n))
                                          (cdr values)))
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
                            fn-frame-seal fn-frame-open fn-frame-values-okp
                            floor mod)))))

(local
 (defthm fn-spo-open-of-a-valid-frame
   (implies (fn-bs-profile-validp values)
            (equal (fn-spo-config-open (fn-bs-config-encode values))
                   (if (fn-bs-profile-logp values)
                       (list :opened values)
                     (list :refused :store-format))))
   :hints (("Goal" :use (fn-spo-saved-format-8-of-encode
                         fn-bs-config-decode-of-encode
                         fn-spo-validp-is-admitted
                         fn-spo-valid-is-not-in-the-window
                         (:instance fn-spo-layout-fields-of-a-decoded-frame
                                    (octets (fn-bs-config-encode values))))
            :in-theory (union-theories '(fn-spo-config-open (:e fn-bs-profile-validp))
                                       (theory 'minimal-theory))))))

; A valid profile is a log profile exactly when its word is fn-store-9.
(local
 (defthm fn-spo-logp-of-valid
   (implies (fn-bs-profile-validp values)
            (equal (fn-bs-profile-logp values)
                   (equal (car values) *fn-bs-meta-format-9*)))
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-logp fn-bs-profile-of fn-bs-meta-nth)
                                   (fn-bs-profile-validp))))))

(local
 (defthm fn-spo-v2-valid-names-format-8
   (implies (fn-bs-profile-v2-validp values)
            (fn-bs-meta-formatp (car values)))
   :hints (("Goal" :use fn-bs-profile-v2-valid-shape
            :in-theory (e/d (fn-bs-meta-nth)
                            (fn-bs-profile-v2-valid-shape fn-bs-profile-v2-validp
                             fn-frame-values-okp))))))

(local
 (defthm fn-spo-open-of-a-window-frame
   (implies (and (fn-bs-profile-v2-validp values)
                 (< *fn-stxa-max-octets* (fn-bs-pf 4 values)))
            (equal (fn-spo-config-open (fn-spo-saved-frame values))
                   (list :refused :max-record-octets-above-the-poll-reply)))
   :hints (("Goal" :use (fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                         fn-spo-saved-format-8-of-saved-frame
                         fn-spo-v2-valid-is-shape
                         fn-spo-v2-valid-names-format-8
                         (:instance fn-spo-layout-fields-of-a-saved-format-8
                                    (octets (fn-spo-saved-frame values))))
            :in-theory (e/d (fn-spo-config-open)
                            (fn-spo-v2-valid-names-format-8
                             fn-spo-layout-fields-of-a-saved-format-8
                             fn-spo-layout-fields
                             fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                             fn-spo-saved-format-8-of-saved-frame
                             fn-spo-v2-valid-is-shape
                             fn-spo-in-the-windowp
                             fn-bs-config-decode fn-spo-saved-frame
                             fn-spo-saved-format-8 fn-bs-profile-v2-validp
                             fn-bs-pf))))))

; -----------------------------------------------------------------------------
; KEYSTONE (the open).  Every profile the encoder saved (under the relation
; before PKT-467) either opens, as itself, or is refused by name at the open
; the host calls; never the generic fault (:rejected).  At or below the poll
; reply's ceiling it opens when its word is fn-store-9 (so this is the old open
; there) and is refused `:store-format' otherwise (a format-8 store, D34);
; above it the refusal names the window.
(defthm fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name
  (implies (fn-bs-profile-v2-validp values)
           (equal (fn-spo-config-open (fn-spo-saved-frame values))
                  (if (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*)
                      (if (equal (car values) *fn-bs-meta-format-9*)
                          (list :opened values)
                        (list :refused :store-format))
                    (list :refused :max-record-octets-above-the-poll-reply))))
  :hints (("Goal" :do-not-induct t
           :cases ((<= (fn-bs-pf 4 values) *fn-stxa-max-octets*))
           :use (fn-bs-profile-v2-valid-within-the-width-is-valid
                 fn-spo-open-of-a-window-frame
                 (:instance fn-spo-open-of-a-valid-frame)
                 fn-spo-saved-frame-of-valid-is-encode
                 fn-spo-logp-of-valid)
           :in-theory (disable fn-bs-profile-v2-valid-within-the-width-is-valid
                               fn-spo-open-of-a-window-frame
                               fn-spo-open-of-a-valid-frame
                               fn-spo-logp-of-valid fn-bs-profile-logp
                               fn-spo-saved-frame-of-valid-is-encode
                               fn-bs-profile-v2-validp fn-bs-profile-validp
                               fn-spo-config-open fn-bs-config-encode
                               fn-spo-saved-frame fn-bs-pf))))

(local
 (defthm fn-spo-fields-parse-car
   (implies (and (consp specs)
                 (fn-frame-parse-okp (fn-frame-fields-parse specs octets)))
            (equal (car (fn-frame-parse-value (fn-frame-fields-parse specs octets)))
                   (fn-frame-parse-value (fn-frame-field-parse (car specs) octets))))
   :hints (("Goal" :in-theory (enable fn-frame-fields-parse)
            :expand ((fn-frame-fields-parse-aux specs octets))))))

(local
 (defthm fn-spo-window-names-format-8
   (implies (fn-spo-in-the-windowp values)
            (fn-bs-meta-formatp (car values)))
   :hints (("Goal" :in-theory (e/d (fn-spo-in-the-windowp fn-bs-profile-invalid-reason
                                    fn-bs-meta-nth)
                                   (fn-bs-pf fn-frame-values-okp
                                    fn-record-encoded-octets-ceiling))))))

(local
 (defthm fn-spo-window-is-not-valid
   (implies (fn-spo-in-the-windowp values)
            (not (fn-bs-profile-validp values)))
   :hints (("Goal" :in-theory '(fn-bs-profile-validp fn-spo-in-the-windowp)))))

; KEYSTONE (the refinement).  The open refuses by name only a frame the open
; before this change did not decode at all (it answered the generic fault
; there); every frame that open decoded is answered as it answered it.
(defthm fn-spo-config-open-refuses-only-what-the-old-open-rejected
  (implies (equal (fn-spo-config-open octets)
                  (list :refused :max-record-octets-above-the-poll-reply))
           (not (fn-bs-config-decode octets)))
  :hints (("Goal"
           :use ((:instance fn-spo-fields-parse-car
                            (specs *fn-bs-meta-profile-spec*)
                            (octets (fn-frame-result-payload
                                     (fn-frame-open octets
                                                    *fn-bs-meta-max-config-payload*))))
                 (:instance fn-spo-window-names-format-8
                            (values (fn-frame-parse-value
                                     (fn-frame-fields-parse
                                      *fn-bs-meta-profile-spec*
                                      (fn-frame-result-payload
                                       (fn-frame-open octets
                                                      *fn-bs-meta-max-config-payload*)))))))
           :in-theory (e/d (fn-spo-config-open fn-spo-saved-format-8
                                   fn-bs-config-decode)
                                  (fn-spo-in-the-windowp fn-bs-profile-validp
                                   fn-spo-foreign-formatp
                                   fn-spo-fields-parse-car
                                   fn-spo-window-names-format-8
                                   fn-frame-fields-parse fn-frame-field-parse
                                   fn-frame-open)))))

; KEYSTONE (D34, one format).  The open answers `:store-format' exactly for a
; frame outside the window that either the profile decoder decodes to a
; profile of the per-file layout (not fn-bs-profile-logp: a format-8 store) or
; the decoder does not decode and is a sealed profile frame naming a format
; other than fn-store-8 and fn-store-9.  So the open opens one format (9) and
; names every other; nothing is translated.
(defthm fn-spo-config-open-store-format-is-exactly-a-foreign-frame
  (equal (equal (fn-spo-config-open octets) (list :refused :store-format))
         (and (not (and (fn-spo-saved-format-8 octets)
                        (fn-spo-in-the-windowp (fn-spo-saved-format-8 octets))))
              (if (fn-bs-config-decode octets)
                  (not (fn-bs-profile-logp (fn-bs-config-decode octets)))
                (fn-spo-foreign-formatp octets))))
  :hints (("Goal" :use (fn-spo-decoded-is-valid
                        fn-spo-foreign-frame-has-no-layout
                        fn-spo-layout-fields-of-a-decoded-frame)
           :in-theory (e/d (fn-spo-config-open fn-bs-profile-admittedp
                            fn-bs-profile-of)
                           (fn-spo-in-the-windowp fn-spo-saved-format-8
                            fn-spo-foreign-formatp fn-bs-config-decode
                            fn-bs-profile-validp fn-spo-decoded-is-valid
                            fn-spo-foreign-frame-has-no-layout
                            fn-spo-layout-fields-of-a-decoded-frame
                            fn-spo-layout-fields fn-bs-profile-logp)))))

; KEYSTONE (D34 after PKT-COL-1).  Every valid profile of the per-file layout
; -- the frame a format-8 store's init or import wrote -- is refused at the
; open the host calls by name, `:store-format', on every image: it is never
; opened and never the generic fault.
(defthm fn-spo-open-of-a-format-8-profile-refuses-by-name
  (implies (and (fn-bs-profile-validp values)
                (not (equal (car values) *fn-bs-meta-format-9*)))
           (equal (fn-spo-config-open (fn-bs-config-encode values))
                  (list :refused :store-format)))
  :hints (("Goal" :use (fn-spo-open-of-a-valid-frame fn-spo-logp-of-valid)
           :in-theory (e/d () (fn-spo-open-of-a-valid-frame fn-spo-logp-of-valid
                               fn-spo-config-open fn-bs-config-encode
                               fn-bs-profile-validp fn-bs-profile-logp)))))

;; -----------------------------------------------------------------------------
;; KEYSTONE (PKT-705, the layout).  Every profile frame a release wrote under a
;; layout of N u64 fields other than this release's (13 before batch AS) is
;; refused at the open the host calls by the name of its layout, with N; never
;; the generic fault (:rejected), and never opened or translated (D34).  With
;; fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name (this
;; release's layout), a sealed fn-store-8 profile frame of any layout opens or
;; is refused by name.
(defthm fn-spo-open-of-another-layout-refuses-by-name
  (implies (and (natp n)
                (not (equal n *fn-spo-release-layout-fields*))
                (fn-frame-values-okp (fn-spo-layout-spec n) values)
                (fn-bs-meta-formatp (car values))
                (<= (len (fn-frame-fields-octets (fn-spo-layout-spec n) values))
                    *fn-bs-meta-max-config-payload*))
           (equal (fn-spo-config-open (fn-spo-layout-frame n values))
                  (list :refused :profile-layout n)))
  :hints (("Goal" :use fn-spo-layout-fields-of-a-layout-frame
           :in-theory (e/d (fn-spo-config-open)
                           (fn-spo-layout-fields-of-a-layout-frame
                            fn-spo-layout-fields fn-spo-layout-frame
                            fn-spo-layout-spec fn-spo-saved-format-8
                            fn-spo-in-the-windowp fn-bs-config-decode
                            fn-spo-foreign-formatp fn-frame-values-okp
                            fn-frame-fields-octets)))))

; KEYSTONE (the refinement, PKT-705).  The layout refusal is never a frame the
; decoder decodes: every store this release's open opened before opens the
; same.
(defthm fn-spo-config-open-layout-refusal-is-never-a-decoded-frame
  (implies (equal (fn-spo-config-open octets) (list :refused :profile-layout n))
           (not (fn-bs-config-decode octets)))
  :hints (("Goal" :use fn-spo-layout-fields-of-a-decoded-frame
           :in-theory (e/d (fn-spo-config-open)
                           (fn-spo-layout-fields-of-a-decoded-frame
                            fn-spo-layout-fields fn-spo-saved-format-8
                            fn-spo-in-the-windowp fn-bs-config-decode
                            fn-spo-foreign-formatp fn-bs-profile-admittedp)))))

; The generic fault is left to octets with this release's layout or with no
; layout (no sealed fn-store-8 profile frame whose tail is a run of u64
; fields): a corrupted file, as before.
(defthm fn-spo-config-open-rejected-has-this-layout-or-none-by-definition
  (implies (equal (fn-spo-config-open octets) '(:rejected))
           (or (not (fn-spo-layout-fields octets))
               (equal (fn-spo-layout-fields octets)
                      *fn-spo-release-layout-fields*)))
  :hints (("Goal" :in-theory (e/d (fn-spo-config-open)
                                  (fn-spo-layout-fields fn-spo-saved-format-8
                                   fn-spo-in-the-windowp fn-bs-config-decode
                                   fn-spo-foreign-formatp
                                   fn-bs-profile-admittedp)))))

(in-theory (disable fn-spo-config-open fn-spo-saved-format-word
                    fn-spo-layout-fields fn-spo-layout-frame
                    fn-spo-saved-format-8 fn-spo-saved-frame
                    fn-bs-profile-v2-invalid-reason))
