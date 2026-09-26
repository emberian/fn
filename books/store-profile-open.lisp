; fn: the open of a store's saved profile, and the one repair that lowers it
; (PKT-471, the coordinator's decision of 2026-09-26).
;
; PKT-467 added one arm to the profile relation (books/byte-store-frame.lisp
; `fn-bs-profile-invalid-reason'): a record bound R above
; *fn-stxa-max-octets*, the widest report a kind-6 consumer poll reply can
; carry, is refused as `:max-record-octets-above-the-poll-reply'.  A store
; saved before that arm with R in the 355-octet window between the poll
; reply's ceiling and the codec's u32 no longer decodes, and the open used to
; answer the host's generic fault ("ACL2 rejected durable configuration
; frame", exit 4).  The decision: the open refuses such a store BY NAME, and
; `store upgrade-profile --max-record-octets W', W the poll reply's ceiling,
; is its explicit repair.  Nothing is translated at open: the store's saved
; profile keeps its meaning until the operator writes the repair.
;
;   * `fn-spo-config-open' OCTETS: the open of config.json the host calls
;     (host/native/io.lisp `fnn-metadata-config-decode', through
;     host/store-host.lisp `fn-store-metadata-config-open'; every open reads
;     the profile there: `fnn-load-config' from `fnn-acquire', so owner
;     start, `store recover', `inspect', `checkpoint', `status' and the
;     offline `health').  It answers (:opened VALUES), the profile the store
;     runs under; (:refused :max-record-octets-above-the-poll-reply), a
;     format-8 profile in the window; or (:rejected), a frame that is no
;     saved profile at all (a corrupted file: the host's fault, as before).
;   * `fn-spo-repair-verdict' OCTETS TARGET: the one lowering admitted, by
;     name.  It is a separate verdict, not an arm of `fn-profile-upgradep':
;     that relation's first conjunct is an admitted OLD, which a window
;     profile is not, and every `fn-profile-upgrade-keeps-*' theorem spends
;     it; the upgrade relation is unchanged, so none of them moves.
;
; The saved profiles are those the format-8 encoder wrote under the relation
; before PKT-467: `fn-bs-profile-v2-invalid-reason' below, the text of
; `fn-bs-profile-invalid-reason' at dev ea35ba7b without that one arm.  Every
; profile the current relation admits is among them
; (`fn-bs-profile-valid-is-v2-valid'), and so is every profile the image
; before P6 saved (books/byte-store-profile-v1.lisp, whose relation reads the
; article record at a larger overhead than this one).
(in-package "ACL2")
(include-book "store-profile-upgrade")
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
          ((not (equal (fn-bs-meta-nth 0 values) *fn-bs-meta-format-8*))
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

(defun fn-spo-in-the-windowp (saved)
  (declare (xargs :guard t))
  (equal (fn-bs-profile-invalid-reason saved)
         :max-record-octets-above-the-poll-reply))

; The open the host calls (host/native/io.lisp `fnn-metadata-config-decode').
(defun fn-spo-config-open (octets)
  (declare (xargs :guard t))
  (let ((saved (fn-spo-saved-format-8 octets)))
    (if (and saved (fn-spo-in-the-windowp saved))
        (list :refused :max-record-octets-above-the-poll-reply)
      (let ((decoded (fn-bs-config-decode octets)))
        (if (and decoded (fn-bs-profile-admittedp decoded))
            (list :opened decoded)
          (list :rejected))))))

; The line every open path prints for the refusal (the pre-C1 pattern:
; ACL2 renders it, the host carries it).
(defun fn-spo-refusal-text (verdict)
  (declare (xargs :guard t))
  (if (equal verdict (list :refused :max-record-octets-above-the-poll-reply))
      "profile record bound exceeds the poll reply width: run store upgrade-profile --max-record-octets 4294966940"
    nil))

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
                 (equal (fn-bs-meta-nth 0 values) *fn-bs-meta-format-8*)
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
        (equal (fn-bs-meta-nth 0 values) *fn-bs-meta-format-8*)
        (equal (fn-bs-meta-nth 1 values) *fn-bs-meta-frontier-format*))))

(local
 (defthm fn-spo-fields-octets-len
   (implies (fn-spo-shapep values)
            (equal (len (fn-frame-fields-octets *fn-bs-meta-profile-spec*
                                                values))
                   (+ (len (fn-frame-field-octets :text *fn-bs-meta-format-8*))
                      (len (fn-frame-field-octets
                            :text *fn-bs-meta-frontier-format*))
                      104)))
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
   :hints (("Goal" :in-theory (enable fn-spo-saved-frame fn-bs-config-encode)))))

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
   :hints (("Goal" :in-theory (enable fn-bs-profile-admittedp)))))

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

(local
 (defthm fn-spo-open-of-a-valid-frame
   (implies (fn-bs-profile-validp values)
            (equal (fn-spo-config-open (fn-bs-config-encode values))
                   (list :opened values)))
   :hints (("Goal" :use (fn-spo-saved-format-8-of-encode
                         fn-bs-config-decode-of-encode
                         fn-spo-validp-is-admitted
                         fn-spo-valid-is-not-in-the-window)
            :in-theory (union-theories '(fn-spo-config-open (:e fn-bs-profile-validp))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-spo-open-of-a-window-frame
   (implies (and (fn-bs-profile-v2-validp values)
                 (< *fn-stxa-max-octets* (fn-bs-pf 4 values)))
            (equal (fn-spo-config-open (fn-spo-saved-frame values))
                   (list :refused :max-record-octets-above-the-poll-reply)))
   :hints (("Goal" :use (fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                         fn-spo-saved-format-8-of-saved-frame
                         fn-spo-v2-valid-is-shape)
            :in-theory (e/d (fn-spo-config-open)
                            (fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                             fn-spo-saved-format-8-of-saved-frame
                             fn-spo-v2-valid-is-shape
                             fn-spo-in-the-windowp
                             fn-bs-config-decode fn-spo-saved-frame
                             fn-spo-saved-format-8 fn-bs-profile-v2-validp
                             fn-bs-pf))))))

; -----------------------------------------------------------------------------
; KEYSTONE (the open).  Every profile the format-8 encoder saved (under the
; relation before PKT-467) either opens, as itself, or is refused by name at
; the open the host calls; never the generic fault (:rejected).  At or below
; the poll reply's ceiling it opens (so this is the old open there); above it
; the refusal names the window.
(defthm fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name
  (implies (fn-bs-profile-v2-validp values)
           (equal (fn-spo-config-open (fn-spo-saved-frame values))
                  (if (<= (fn-bs-pf 4 values) *fn-stxa-max-octets*)
                      (list :opened values)
                    (list :refused :max-record-octets-above-the-poll-reply))))
  :hints (("Goal" :do-not-induct t
           :cases ((<= (fn-bs-pf 4 values) *fn-stxa-max-octets*))
           :use (fn-bs-profile-v2-valid-within-the-width-is-valid
                 fn-spo-open-of-a-window-frame
                 (:instance fn-spo-open-of-a-valid-frame)
                 fn-spo-saved-frame-of-valid-is-encode)
           :in-theory (disable fn-bs-profile-v2-valid-within-the-width-is-valid
                               fn-spo-open-of-a-window-frame
                               fn-spo-open-of-a-valid-frame
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
            (equal (car values) *fn-bs-meta-format-8*))
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
                 (:instance fn-spo-fields-parse-car
                            (specs *fn-bs-meta-format-7-spec*)
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
                                   fn-spo-fields-parse-car
                                   fn-spo-window-names-format-8
                                   fn-frame-fields-parse fn-frame-field-parse
                                   fn-frame-open)))))

; -----------------------------------------------------------------------------
; The repair: the one lowering admitted, by name

; The request `store upgrade-profile --max-record-octets 4294966940' parses to
; (books/native-operator.lisp fn-nop-parse-store; witnessed in the test book).
(defconst *fn-spo-repair-request*
  (list :current (list (cons *fn-bs-pf-max-record-octets* *fn-stxa-max-octets*))))

(defun fn-spo-repaired (saved)
  "SAVED with R lowered to the poll reply's ceiling; every other field kept."
  (declare (xargs :guard t))
  (fn-bs-profile-put *fn-bs-pf-max-record-octets* *fn-stxa-max-octets* saved))

; What `store upgrade-profile' does when the store's open refused by name.
;   (:repair OCTETS)   write OCTETS as config.json (the repaired profile)
;   (:refused REASON)  write nothing
(defun fn-spo-repair-verdict (octets target)
  (declare (xargs :guard t))
  (let ((saved (fn-spo-saved-format-8 octets)))
    (cond ((not (and saved (fn-spo-in-the-windowp saved)))
           (list :refused :not-above-the-poll-reply))
          ((not (equal target *fn-spo-repair-request*))
           (list :refused :repair-lowers-max-record-octets-to-the-poll-reply-only))
          ((not (fn-bs-profile-validp (fn-spo-repaired saved)))
           (list :refused (fn-bs-profile-invalid-reason (fn-spo-repaired saved))))
          (t (list :repair (fn-bs-config-encode (fn-spo-repaired saved)))))))

; The widest article record a profile can ask for fits the poll reply, so
; lowering R to the ceiling never breaks the article relation.
(defthm fn-spo-widest-article-record-fits-the-poll-reply
  (<= (fn-record-encoded-octets-ceiling *fn-bs-profile-article-ceiling-codec*
                                        *fn-bs-profile-groups-ceiling-codec*)
      *fn-stxa-max-octets*)
  :rule-classes nil)

(local
 (defun fn-spo-put-induct (i j values)
   (if (or (zp i) (zp j))
       (list i j values)
     (fn-spo-put-induct (1- i) (1- j) (if (consp values) (cdr values) nil)))))

(local
 (defthm fn-spo-nth-of-put
   (implies (and (natp i) (natp j))
            (equal (fn-bs-meta-nth j (fn-bs-profile-put i v values))
                   (if (equal i j) v (fn-bs-meta-nth j values))))
   :hints (("Goal" :induct (fn-spo-put-induct i j values)
            :in-theory (enable fn-bs-profile-put fn-bs-meta-nth)
            :expand ((fn-bs-profile-put i v values)
                     (fn-bs-meta-nth j values)
                     (:free (x) (fn-bs-meta-nth j x)))))))

(local
 (defthm fn-spo-pf-of-put
   (implies (and (natp i) (natp j))
            (equal (fn-bs-pf j (fn-bs-profile-put i v values))
                   (if (equal i j) (nfix v) (fn-bs-pf j values))))
   :hints (("Goal" :in-theory (enable fn-bs-pf)))))

(local
 (defun fn-spo-put-okp-induct (i specs values)
   (if (zp i)
       (list specs values)
     (fn-spo-put-okp-induct (1- i) (cdr specs)
                            (if (consp values) (cdr values) nil)))))

(local
 (defthm fn-spo-values-okp-of-put
   (implies (and (fn-frame-values-okp specs values)
                 (natp i) (< i (len specs))
                 (fn-frame-field-okp (nth i specs) v))
            (fn-frame-values-okp specs (fn-bs-profile-put i v values)))
   :hints (("Goal" :induct (fn-spo-put-okp-induct i specs values)
            :in-theory (e/d (fn-frame-values-okp fn-bs-profile-put)
                            (fn-frame-field-okp fn-spo-nth-of-put
                             fn-spo-pf-of-put))))))

(local
 (defthm fn-spo-put-4-values-okp
   (implies (and (fn-frame-values-okp *fn-bs-meta-profile-spec* values)
                 (natp v) (< v (expt 2 64)))
            (fn-frame-values-okp *fn-bs-meta-profile-spec*
                                 (fn-bs-profile-put 4 v values)))
   :hints (("Goal" :use ((:instance fn-spo-values-okp-of-put
                                    (specs *fn-bs-meta-profile-spec*) (i 4)))
            :in-theory (e/d (fn-frame-field-okp fn-frame-natp)
                            (fn-spo-values-okp-of-put fn-frame-values-okp
                             fn-bs-profile-put fn-spo-nth-of-put
                             fn-spo-pf-of-put))))))

; The lowering of a saved profile in the window is a valid profile.
(defthm fn-spo-repaired-of-the-window-is-valid
  (implies (and (fn-bs-profile-v2-validp saved)
                (< *fn-stxa-max-octets* (fn-bs-pf 4 saved)))
           (fn-bs-profile-validp (fn-spo-repaired saved)))
  :hints (("Goal" :use ((:instance fn-spo-widest-article-record-fits-the-poll-reply)
                        (:instance fn-spo-put-4-values-okp
                                   (values saved) (v *fn-stxa-max-octets*)))
           :in-theory (e/d (fn-bs-profile-validp fn-bs-profile-invalid-reason
                            fn-spo-repaired fn-record-encoded-octets-ceiling)
                           (fn-bs-pf fn-frame-values-okp fn-bs-profile-put
                            fn-spo-put-4-values-okp)))))

; KEYSTONE (the repair).  Over the frame of any saved profile, the verdict
; writes a frame exactly when the saved R is above the poll reply's ceiling
; and the operator's target is that ceiling; what it writes opens, at the
; open the host calls, as the saved profile with R lowered to the ceiling and
; every other field kept.  Every other target over such a store, and every
; target over a store that opens, is refused by name and writes nothing.
(defthm fn-spo-repair-admits-exactly-the-lowering-to-the-width
  (implies (fn-bs-profile-v2-validp saved)
           (and (equal (equal (car (fn-spo-repair-verdict
                                    (fn-spo-saved-frame saved) target))
                              :repair)
                       (and (< *fn-stxa-max-octets* (fn-bs-pf 4 saved))
                            (equal target *fn-spo-repair-request*)))
                (implies (equal (car (fn-spo-repair-verdict
                                      (fn-spo-saved-frame saved) target))
                                :repair)
                         (equal (fn-spo-config-open
                                 (cadr (fn-spo-repair-verdict
                                        (fn-spo-saved-frame saved) target)))
                                (list :opened (fn-spo-repaired saved))))))
  :hints (("Goal" :do-not-induct t
           :cases ((<= (fn-bs-pf 4 saved) *fn-stxa-max-octets*))
           :use ((:instance fn-bs-profile-v2-valid-within-the-width-is-valid
                            (values saved))
                 (:instance fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                            (values saved))
                 (:instance fn-spo-repaired-of-the-window-is-valid)
                 (:instance fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name
                            (values (fn-spo-repaired saved)))
                 (:instance fn-bs-profile-valid-is-v2-valid
                            (values (fn-spo-repaired saved)))
                 (:instance fn-spo-valid-is-not-in-the-window
                            (values saved)))
           :in-theory (e/d (fn-spo-repair-verdict)
                           (fn-bs-profile-v2-valid-within-the-width-is-valid
                            fn-bs-profile-v2-valid-above-the-width-is-in-the-window
                            fn-spo-repaired-of-the-window-is-valid
                            fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name
                            fn-bs-profile-valid-is-v2-valid
                            fn-spo-valid-is-not-in-the-window
                            fn-spo-in-the-windowp
                            fn-bs-profile-v2-validp fn-bs-profile-validp
                            fn-bs-profile-invalid-reason fn-spo-config-open
                            fn-bs-config-encode fn-spo-saved-frame
                            fn-spo-saved-format-8 fn-spo-shapep
                            fn-spo-repaired fn-bs-pf)))))

; The lowering changes R and nothing else.
(defthm fn-spo-repaired-keeps-every-other-field
  (implies (and (natp i) (<= 2 i) (<= i 14) (not (equal i 4)))
           (equal (fn-bs-pf i (fn-spo-repaired saved)) (fn-bs-pf i saved)))
  :hints (("Goal" :in-theory (e/d (fn-spo-repaired) (fn-bs-pf fn-bs-profile-put))
           :cases ((equal i 2) (equal i 3) (equal i 5) (equal i 6) (equal i 7)
                   (equal i 8) (equal i 9) (equal i 10) (equal i 11)
                   (equal i 12) (equal i 13) (equal i 14)))))

(in-theory (disable fn-spo-config-open fn-spo-repair-verdict
                    fn-spo-saved-format-8 fn-spo-saved-frame
                    fn-bs-profile-v2-invalid-reason))
