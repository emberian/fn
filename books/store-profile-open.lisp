; fn: the open of a store's saved profile, and its one refusal by name
; (PKT-471; D34: one store format, fresh deploys, no migrations).
;
; A store has one format: this build's (books/byte-store-frame.lisp
; `fn-bs-meta-formatp').  The open of config.json answers:
;
;   * (:opened VALUES) for a frame the profile decoder decodes;
;   * (:refused :store-format) for a sealed profile frame (under this build's
;     digest) whose format word is not this build's: not an fn store of this
;     release, and the line says so -- redeploy fresh (no store is upgraded,
;     translated or imported across formats);
;   * (:rejected) for anything else (a corrupted file): the host's fault.
;
; The open the host calls is `fn-spo-config-open' (host/native/io.lisp
; `fnn-metadata-config-decode', through host/store-host.lisp
; `fn-store-metadata-config-open'; every open reads the profile there:
; `fnn-load-config' from `fnn-acquire', so owner start, `store recover',
; `inspect', `checkpoint', `status' and the offline `health').
(in-package "ACL2")
(include-book "byte-store-frame")
(local (include-book "store-profile-facts"))
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

; A sealed profile frame whose word is not this build's.
(defun fn-spo-foreign-formatp (octets)
  (declare (xargs :guard t))
  (let ((word (fn-spo-saved-format-word octets)))
    (and word (not (fn-bs-meta-formatp word)) t)))

; -----------------------------------------------------------------------------
; The open the host calls (host/native/io.lisp `fnn-metadata-config-decode').

(defun fn-spo-config-open (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-bs-config-decode octets)))
    (cond (decoded (list :opened decoded))
          ((fn-spo-foreign-formatp octets) (list :refused :store-format))
          (t (list :rejected)))))

; The line every open path prints for the refusal (ACL2 renders it, the host
; carries it).
(defun fn-spo-refusal-text (verdict)
  (declare (xargs :guard t))
  (if (equal verdict (list :refused :store-format))
      "open refused reason=store-format: not an fn store of this release: redeploy fresh"
    nil))

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
 (defthm fn-spo-valid-names-this-format
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
 (defthm fn-spo-decoded-names-this-format
   (implies (fn-bs-config-decode octets)
            (equal (fn-spo-saved-format-word octets) *fn-bs-meta-format-10*))
   :hints (("Goal"
            :use ((:instance fn-spo-fields-parse-car
                             (specs *fn-bs-meta-profile-spec*)
                             (octets (fn-frame-result-payload
                                      (fn-frame-open octets
                                                     *fn-bs-meta-max-config-payload*))))
                  fn-spo-decoded-is-valid
                  (:instance fn-spo-valid-names-this-format
                             (values (fn-bs-config-decode octets))))
            :in-theory (e/d (fn-spo-saved-format-word)
                            (fn-spo-fields-parse-car fn-spo-decoded-is-valid
                             fn-spo-valid-names-this-format
                             fn-bs-profile-validp fn-frame-fields-parse
                             fn-frame-field-parse fn-frame-open
                             fn-bs-meta-frame-okp))
            :expand ((fn-bs-config-decode octets))))))

(local
 (defthm fn-spo-foreign-is-not-decoded
   (implies (fn-spo-foreign-formatp octets)
            (not (fn-bs-config-decode octets)))
   :hints (("Goal" :use fn-spo-decoded-names-this-format
            :in-theory (e/d (fn-spo-foreign-formatp fn-bs-meta-formatp)
                            (fn-spo-decoded-names-this-format
                             fn-bs-config-decode fn-spo-saved-format-word))))))

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
                            fn-spo-foreign-formatp)))))

; KEYSTONE (D34, one format).  The open answers `:store-format' -- whose line
; is "not an fn store of this release: redeploy fresh" -- exactly for a
; sealed profile frame naming a word other than this build's: never opened,
; never translated, never the generic fault.
(defthm fn-spo-config-open-store-format-is-exactly-a-foreign-frame
  (equal (equal (fn-spo-config-open octets) (list :refused :store-format))
         (fn-spo-foreign-formatp octets))
  :hints (("Goal" :use fn-spo-foreign-is-not-decoded
           :in-theory (e/d (fn-spo-config-open)
                           (fn-spo-foreign-is-not-decoded fn-bs-config-decode
                            fn-spo-foreign-formatp)))))

(in-theory (disable fn-spo-config-open fn-spo-saved-format-word
                    fn-spo-foreign-formatp))
