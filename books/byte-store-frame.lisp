; fn byte-store metadata frames: concrete frontier and configuration bytes.
;
; This is the P4 realization of the three constrained scan seams in
; `byte-store-scan'.  A frontier is a deterministic CBOR uint inside an FNSM
; frame.  The store profile is a bounded frame-field record of operator fields
; (format 8, below).  Both use
; the existing frame grammar and its ACL2-owned trailer; the host only moves
; the resulting octets to and from regular files.
;
; Older JSON metadata remains in place and is refused at normal open pending
; an explicit offline migration.  This book never interprets or rewrites it.

(in-package "ACL2")
(include-book "byte-store-scan")
(include-book "frame-trailer")
(local (include-book "arithmetic/top" :dir :system))

; FNSM = fn store metadata.  It is deliberately a separate frame family from
; FNST transactions, so a metadata file cannot be accepted as a transaction.
(defconst *fn-bs-meta-magic* '(70 78 83 77))
(defconst *fn-bs-meta-version* 1)
(defconst *fn-bs-meta-config-kind* 1)
(defconst *fn-bs-meta-frontier-kind* 2)
(defconst *fn-bs-meta-max-frontier-payload* 5)
(defconst *fn-bs-meta-max-config-payload* 600)

; All accepted configuration values have exactly this layout.  The text
; fields are ACL2 frame text (nonempty, bounded UTF-8); numeric fields are
; eight-octet frame naturals.  This is a local store profile, not an article
; envelope or an NNTP wire representation.
(defconst *fn-bs-meta-config-spec*
  '(:text :nat :nat :nat :nat :text))

; The frontier is one RFC 8949 deterministic uint in the existing bounded
; CBOR profile.  Naming this small length fact before the encoder keeps the
; frame guard proof about the concrete five-octet payload rather than asking
; ACL2 to rediscover the four CBOR argument cases through fn-frame-seal.
(local
 (defthm fn-bs-frontier-cbor-payload-bound
   (implies (and (natp n) (<= n *fn-cbor-max-uint*))
            (and (fn-cbor-octet-listp (fn-cbor-encode (cons :uint n)))
                 (<= (len (fn-cbor-encode (cons :uint n)))
                     *fn-bs-meta-max-frontier-payload*)))
   :hints (("Goal" :cases ((< n 24) (< n 256) (< n 65536))
            :use ((:instance fn-frame-u32-bytes-len (n n))
                  (:instance fn-frame-u16-bytes-len (n n)))
            ; `fn-cbor-encode-bounded' and `fn-cbor-valuep-bounded' too: the
            ; encoder became the bounded one and its definition is withdrawn
            ; on export (books/cbor), so without them this goal stops at
            ; (fn-cbor-octet-listp (fn-cbor-encode-bounded (cons :uint n)
            ; 65535)) with no rule to move it.
            :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded
                               fn-cbor-valuep fn-cbor-valuep-bounded
                               fn-cbor-encode-argument
                               fn-cbor-octet-listp fn-cbor-octetp)))))

; -----------------------------------------------------------------------------
; The store profile (D27: bound work, never data)
;
; A store's profile is the operator's: every bound on the data a store holds
; (transactions, history octets, one record, one article, groups per article,
; ...) is a field, set at `init' and raised offline by `store upgrade-profile'.
; What ACL2 fixes is not the values but the relations between them
; (`fn-bs-profile-validp') and the codec ceilings no field may pass, so that a
; profile the operator can write is one every codec can carry.
;
; Format 8 (`fn-store-8') is the layout written from now on.  Format 7
; (`fn-store-experiment-7', two fixed tuples) is still decoded, so an existing
; store opens and is served under its translation (`fn-bs-profile-of'); the
; upgrade verb rewrites it as format 8.  Format 6 is no longer decoded: its
; per-record ceiling (65538) is below the ceiling of the largest Store event
; kind, so no format-8 profile translates it.

(defconst *fn-bs-meta-format-development*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 55)) ; fn-store-experiment-7
(defconst *fn-bs-meta-format-8*
  '(102 110 45 115 116 111 114 101 45 56)) ; fn-store-8
(defconst *fn-bs-meta-frontier-format*
  '(102 110 45 115 116 111 114 101 45 97 108 108 111 99 97 116 105
    111 110 45 102 114 111 110 116 105 101 114 45 50))

; Format 7: format, capacity (never read; dropped in format 8), payload,
; aggregate replay octets, transactions, frontier format.
(defconst *fn-bs-meta-format-7-spec*
  '(:text :nat :nat :nat :nat :text))
(defconst *fn-bs-meta-format-7-development-values*
  (list *fn-bs-meta-format-development* 1048576 32768 25165824 128
        *fn-bs-meta-frontier-format*))
(defconst *fn-bs-meta-format-7-scale-values*
  (list *fn-bs-meta-format-development* 1048576 32768 805306368 4096
        *fn-bs-meta-frontier-format*))

(defun fn-bs-meta-format-7-valuesp (values)
  (declare (xargs :guard t))
  (or (equal values *fn-bs-meta-format-7-development-values*)
      (equal values *fn-bs-meta-format-7-scale-values*)))

(defun fn-bs-meta-nth (n values)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (if (consp values) (car values) nil)
    (fn-bs-meta-nth (1- n) (if (consp values) (cdr values) nil))))

; Format 8: two texts, then twelve eight-octet frame naturals, in this order.
(defconst *fn-bs-meta-profile-spec*
  '(:text :text :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat :nat))

(defconst *fn-bs-pf-max-transactions* 2)        ; T
(defconst *fn-bs-pf-max-history-octets* 3)      ; H
(defconst *fn-bs-pf-max-record-octets* 4)       ; R
(defconst *fn-bs-pf-max-article-octets* 5)      ; A
(defconst *fn-bs-pf-max-groups-per-article* 6)  ; G
(defconst *fn-bs-pf-max-group-name-octets* 7)
(defconst *fn-bs-pf-max-open-suffix* 8)         ; K
(defconst *fn-bs-pf-max-consumers* 9)
(defconst *fn-bs-pf-max-bp-rows* 10)
(defconst *fn-bs-pf-max-config-generations* 11)
(defconst *fn-bs-pf-max-credentials* 12)
(defconst *fn-bs-pf-max-policy-members* 13)

; The fields in order, with the operator's name for each (the `init' and
; `store upgrade-profile' flag is `--' followed by the name).
(defconst *fn-bs-profile-field-names*
  '((2 . "max-transactions") (3 . "max-history-octets")
    (4 . "max-record-octets") (5 . "max-article-octets")
    (6 . "max-groups-per-article") (7 . "max-group-name-octets")
    (8 . "max-open-suffix") (9 . "max-consumers") (10 . "max-bp-rows")
    (11 . "max-config-generations") (12 . "max-credentials")
    (13 . "max-policy-members")))

; The codec ceilings no field may pass.  Each is the width the codec that
; carries the bounded quantity accepts today; packet P2 (codec ceilings) and
; P6 (u64 width) raise the constants these name, and the profile follows.
(defconst *fn-bs-profile-transaction-ceiling* *fn-cbor-max-uint*)   ; txid width
(defconst *fn-bs-profile-record-ceiling-codec* *fn-frame-max-store-payload*)
(defconst *fn-bs-profile-article-ceiling-codec* *fn-record-max-payload*)
(defconst *fn-bs-profile-groups-ceiling-codec* *fn-record-max-groups*)
(defconst *fn-bs-profile-group-name-ceiling-codec* *fn-record-max-group-name*)
(defconst *fn-bs-profile-count-ceiling* *fn-cbor-max-uint*)

; Every Store event kind with a publication ceiling.  A kind not listed has
; ceiling 0 (`fn-store-publication-ceiling''s last branch).
(defconst *fn-bs-profile-event-kinds*
  '(:article :undertake :release :statement-verdict :keyring-snapshot
    :accepted-statement :consumer :topic-admin-install :topic-anchor
    :topic-admit))

(defun fn-bs-profile-max-kind-ceiling (kinds)
  (declare (xargs :guard t))
  (if (consp kinds)
      (max (fn-store-publication-ceiling (car kinds))
           (fn-bs-profile-max-kind-ceiling (cdr kinds)))
    0))

; The smallest record ceiling under which every kind is publishable.
(defconst *fn-bs-profile-min-record-octets*
  (fn-bs-profile-max-kind-ceiling *fn-bs-profile-event-kinds*))

(defthm fn-bs-profile-min-record-octets-covers-every-kind
  (<= (fn-store-publication-ceiling kind) *fn-bs-profile-min-record-octets*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-store-publication-ceiling))))

(defun fn-bs-pf (i values)
  "Field I of a format-8 VALUES list as a natural (raw: no validation)."
  (declare (xargs :guard (natp i)))
  (nfix (fn-bs-meta-nth i values)))

(defun fn-bs-profile-countp (n)
  (declare (xargs :guard t))
  (and (natp n) (<= 1 n) (<= n *fn-bs-profile-count-ceiling*)))

; The first relation VALUES fails, by name, or NIL when it is a valid
; format-8 profile.  Each is one comparison; the operator verb prints the name.
(defun fn-bs-profile-invalid-reason (values)
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
          (t nil))))

(defun fn-bs-profile-validp (values)
  (declare (xargs :guard t))
  (not (fn-bs-profile-invalid-reason values)))

; The format-7 translation: T = transactions, H = aggregate replay octets,
; A = payload, K = T, the namespace counts P1's defaults, G and the group name
; the codec ceilings (a translated store gets the large bounds a fresh init
; would; the coordinator's decision of 2026-09-25), and R the larger of H / T
; (the ceiling format 7 derived) and the article record of (A, G), so the
; translation meets the article relation: at A 32 768 and G 65 535 that record
; is 17 138 486 octets, within either tuple's H (24 MiB, 768 MiB), and H / T
; is 196 608.  R only grows, so every kind's budget is unchanged
; (`fn-profile-upgrade-format-7-to-8').  Both format-7
; tuples translate to the format-8 presets of the same name
; (`fn-bs-profile-format-7-translates-to-the-presets', in the test book).
(defconst *fn-bs-profile-default-namespace-count* 1048576)

(defun fn-bs-profile-from-format-7 (values)
  (declare (xargs :guard t))
  (let ((h (nfix (fn-bs-meta-nth 3 values)))
        (tx (nfix (fn-bs-meta-nth 4 values))))
    (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
          tx h
          (max (if (zp tx) 0 (floor h tx))
               (fn-record-encoded-octets-ceiling
                (nfix (fn-bs-meta-nth 2 values))
                *fn-bs-profile-groups-ceiling-codec*))
          (nfix (fn-bs-meta-nth 2 values))
          *fn-bs-profile-groups-ceiling-codec*
          *fn-bs-profile-group-name-ceiling-codec*
          tx
          *fn-bs-profile-default-namespace-count*
          *fn-bs-profile-default-namespace-count*
          *fn-bs-profile-default-namespace-count*
          *fn-bs-profile-default-namespace-count*
          *fn-bs-profile-default-namespace-count*)))

; The profile a store is run under: a valid format-8 profile as it is, a
; format-7 tuple as its translation, anything else NIL.
(defun fn-bs-profile-of (values)
  (declare (xargs :guard t))
  (cond ((fn-bs-profile-validp values) values)
        ((and (fn-bs-meta-format-7-valuesp values)
              (fn-bs-profile-validp (fn-bs-profile-from-format-7 values)))
         (fn-bs-profile-from-format-7 values))
        (t nil)))

(defthm fn-bs-profile-of-is-valid-or-nil
  (or (null (fn-bs-profile-of values))
      (fn-bs-profile-validp (fn-bs-profile-of values)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-profile-validp
                                      fn-bs-profile-from-format-7))))

(defun fn-bs-profile-admittedp (values)
  "VALUES is a profile a store may be opened and served under."
  (declare (xargs :guard t))
  (fn-bs-profile-validp (fn-bs-profile-of values)))

; The named accessors every consumer reads.  Each reads the profile the
; store runs under, so a format-7 store and its format-8 translation give
; the same answer, and a value that is neither gives 0.
(defun fn-bs-profile-field (i values)
  (declare (xargs :guard (natp i)))
  (fn-bs-pf i (fn-bs-profile-of values)))

(defun fn-bs-profile-max-transactions (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 2 values))
(defun fn-bs-profile-max-history-octets (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 3 values))
(defun fn-bs-profile-max-record-octets (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 4 values))
; P2 reads this one: the operator's article bound, which the served POST,
; feed, BP ingress and control-socket ceilings are to follow.
(defun fn-bs-profile-max-article-octets (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 5 values))
(defun fn-bs-profile-max-groups-per-article (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 6 values))
(defun fn-bs-profile-max-group-name-octets (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 7 values))
(defun fn-bs-profile-max-open-suffix (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field 8 values))

; Kept under its old name: the record ceiling is now field R itself.
(defun fn-bs-profile-record-ceiling (values)
  (declare (xargs :guard t))
  (fn-bs-profile-max-record-octets values))

(defun fn-bs-publication-admissiblep (values committed-count
                                             prospective-payload-octets)
  (declare (xargs :guard t))
  (and (fn-bs-profile-admittedp values)
       (natp committed-count)
       (natp prospective-payload-octets)
       (< committed-count (fn-bs-profile-max-transactions values))
       (<= prospective-payload-octets (fn-bs-profile-record-ceiling values))))

; The history bound at publication: the committed record octets plus the
; prospective record stay within H.  (`fn-bs-publication-admissiblep' is the
; count and single-record gate the host asserts at publish; this is the
; aggregate gate the owner's verdict adds, books/store-budget.lisp.)
(defun fn-bs-history-admissiblep (values committed-octets prospective-octets)
  (declare (xargs :guard t))
  (and (fn-bs-profile-admittedp values)
       (natp committed-octets) (natp prospective-octets)
       (<= (+ committed-octets prospective-octets)
           (fn-bs-profile-max-history-octets values))))

; -----------------------------------------------------------------------------
; Validity facts, and the codec keystone

(defthm fn-bs-profile-validp-facts
  (implies (fn-bs-profile-validp values)
           (and (fn-frame-values-okp *fn-bs-meta-profile-spec* values)
                (equal (fn-bs-meta-nth 0 values) *fn-bs-meta-format-8*)
                (equal (fn-bs-meta-nth 1 values) *fn-bs-meta-frontier-format*)
                (<= 1 (fn-bs-pf 2 values))
                (<= (fn-bs-pf 2 values) *fn-bs-profile-transaction-ceiling*)
                (<= (fn-bs-pf 4 values) (fn-bs-pf 3 values))
                (<= *fn-bs-profile-min-record-octets* (fn-bs-pf 4 values))
                (<= (fn-bs-pf 4 values) *fn-bs-profile-record-ceiling-codec*)
                (<= 1 (fn-bs-pf 5 values))
                (<= (fn-bs-pf 5 values) *fn-bs-profile-article-ceiling-codec*)
                (<= 1 (fn-bs-pf 6 values))
                (<= (fn-bs-pf 6 values) *fn-bs-profile-groups-ceiling-codec*)
                (<= 1 (fn-bs-pf 7 values))
                (<= (fn-bs-pf 7 values) *fn-bs-profile-group-name-ceiling-codec*)
                (<= (fn-record-encoded-octets-ceiling (fn-bs-pf 5 values)
                                                      (fn-bs-pf 6 values))
                    (fn-bs-pf 4 values))
                (<= 1 (fn-bs-pf 8 values))
                (<= (fn-bs-pf 8 values) (fn-bs-pf 2 values))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp
                                   fn-bs-profile-invalid-reason)
                                  (fn-bs-pf fn-frame-values-okp
                                   fn-record-encoded-octets-ceiling)))))

(defthm fn-bs-profile-of-valid
  (implies (fn-bs-profile-validp values)
           (equal (fn-bs-profile-of values) values)))

(defthm fn-bs-profile-validp-of-profile-of
  (implies (fn-bs-profile-admittedp values)
           (fn-bs-profile-validp (fn-bs-profile-of values)))
  :hints (("Goal" :in-theory (disable fn-bs-profile-of fn-bs-profile-validp))))

; KEYSTONE (codec widths never cap below a profile).  Every field of the
; profile a store runs under -- of any value, since a value that is not a
; profile reads as zero -- is one the codec that carries it accepts: a transaction ID
; below T is a CBOR uint, a record of at most R octets is within the FNST
; payload ceiling, an article of at most A octets and G groups of at most the
; name bound are within the record codec's fields -- and R is at least the
; publication ceiling of EVERY Store event kind, so no kind is unpublishable.
(defthm fn-bs-profile-validp-codecs-accept
  (and (<= (fn-bs-profile-max-transactions values) *fn-cbor-max-uint*)
       (<= (fn-bs-profile-max-record-octets values)
           *fn-frame-max-store-payload*)
       (<= (fn-bs-profile-max-record-octets values)
           (fn-bs-profile-max-history-octets values))
       (<= (fn-bs-profile-max-article-octets values) *fn-record-max-payload*)
       (<= (fn-bs-profile-max-groups-per-article values) *fn-record-max-groups*)
       (<= (fn-bs-profile-max-group-name-octets values)
           *fn-record-max-group-name*)
       (<= (fn-bs-profile-max-open-suffix values)
           (fn-bs-profile-max-transactions values))
       (implies (fn-bs-profile-admittedp values)
                (and (<= 1 (fn-bs-profile-max-transactions values))
                     (<= (fn-store-publication-ceiling kind)
                         (fn-bs-profile-max-record-octets values))
                     (<= 1 (fn-bs-profile-max-article-octets values))
                     (<= 1 (fn-bs-profile-max-groups-per-article values)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts
                                   (values (fn-bs-profile-of values)))
                        (:instance fn-bs-profile-of-is-valid-or-nil)
                        (:instance fn-bs-profile-min-record-octets-covers-every-kind))
           :in-theory (e/d (fn-bs-profile-admittedp fn-bs-profile-field
                            fn-bs-profile-max-transactions
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-max-history-octets
                            fn-bs-profile-max-article-octets
                            fn-bs-profile-max-groups-per-article
                            fn-bs-profile-max-group-name-octets
                            fn-bs-profile-max-open-suffix)
                           (fn-bs-profile-validp-facts
                            fn-bs-profile-of fn-bs-profile-validp
                            fn-store-publication-ceiling
                            fn-bs-profile-min-record-octets-covers-every-kind)))))

;  KEYSTONE (an article the profile admits is a record it publishes).  Under
; the profile a store runs under, every record whose payload is within the
; article field A and whose groups are within G encodes to at most the record
; field R: `fn-record-encode-length-bound' (records-seam) bounds the encoding
; by `fn-record-encoded-octets-ceiling' of its payload and group count, and
; validity requires R to hold that ceiling at (A, G).  So a POST the boundary
; admits (`fn-sbud-post-boundary', books/store-budget-naming) never reaches
; the publish gate's record check (`fn-bs-publication-admissiblep',
; asserted by host/native/io.lisp `fnn-publish') with a record it refuses.
(defthm fn-bs-profile-admits-every-article-record
  (implies (and (fn-bs-profile-admittedp values)
                (<= (len (fn-record-payload record))
                    (fn-bs-profile-max-article-octets values))
                (<= (len (fn-record-groups record))
                    (fn-bs-profile-max-groups-per-article values)))
           (<= (len (fn-record-encode record))
               (fn-bs-profile-max-record-octets values)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts
                                   (values (fn-bs-profile-of values)))
                        (:instance fn-record-encode-length-bound))
           :in-theory (e/d (fn-bs-profile-admittedp fn-bs-profile-field
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-max-article-octets
                            fn-bs-profile-max-groups-per-article
                            fn-record-encoded-octets-ceiling)
                           (fn-bs-profile-validp-facts
                            fn-record-encode-length-bound
                            fn-bs-profile-of fn-bs-profile-validp)))))

(defun fn-bs-meta-frame-okp (frame kind payload bound)
  (declare (xargs :guard t))
  (and (fn-frame-result-okp frame)
       (equal (fn-frame-result-magic frame) *fn-bs-meta-magic*)
       (equal (fn-frame-result-version frame) *fn-bs-meta-version*)
       (equal (fn-frame-result-kind frame) kind)
       (fn-cbor-octet-listp payload)
       (natp bound)
       (<= (len payload) bound)))

(defun fn-bs-frontier-encode-impl (n)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (natp n) (<= n *fn-cbor-max-uint*)))
      nil
    (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                   *fn-bs-meta-frontier-kind*
                   (fn-cbor-encode (cons :uint n)))))

(verify-guards fn-bs-frontier-encode-impl
  :hints (("Goal" :use ((:instance fn-bs-frontier-cbor-payload-bound
                                     (n n))))))

; The allocation ceiling is a codec decision: a frontier at the largest CBOR
; uint is a valid persisted value, but it has no successor.  Hosts ask this
; function before staging an allocator replacement, so no host range check
; can wrap or re-use an ID.
(defun fn-bs-frontier-next (n)
  (declare (xargs :guard t))
  (if (and (natp n) (< n *fn-cbor-max-uint*))
      (1+ n)
    nil))


(defun fn-bs-frontier-decode-impl (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((frame (fn-frame-open octets *fn-bs-meta-max-frontier-payload*)))
      (if (not (fn-bs-meta-frame-okp frame *fn-bs-meta-frontier-kind*
                                      (fn-frame-result-payload frame)
                                      *fn-bs-meta-max-frontier-payload*))
          nil
        (let ((decoded (fn-cbor-decode-exact
                        (fn-frame-result-payload frame))))
          (if (and (fn-cbor-result-okp decoded)
                   (equal (fn-cbor-ag-car
                           (fn-cbor-result-value decoded))
                          :uint)
                   (natp (fn-cbor-ag-cdr
                           (fn-cbor-result-value decoded))))
              (fn-cbor-ag-cdr (fn-cbor-result-value decoded))
            nil))))))

(defthm fn-bs-frontier-frame-inputp
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                            *fn-bs-meta-frontier-kind*
                            (fn-cbor-encode (cons :uint n))
                            *fn-bs-meta-max-frontier-payload*))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-cbor-payload-bound (n n)))
           :in-theory (enable fn-frame-inputp fn-frame-magicp))))

(defthm fn-bs-frontier-payload-fits-frame-length
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (<= (len (fn-cbor-encode (cons :uint n)))
               *fn-cbor-max-uint*))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-cbor-payload-bound (n n))))))

(defthm fn-bs-frontier-open-of-encode
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-frame-open
                   (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                                  *fn-bs-meta-frontier-kind*
                                  (fn-cbor-encode (cons :uint n)))
                   *fn-bs-meta-max-frontier-payload*)
                  (fn-frame-ok *fn-bs-meta-magic* *fn-bs-meta-version*
                               *fn-bs-meta-frontier-kind*
                               (fn-cbor-encode (cons :uint n)))))
  :hints (("Goal"
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-frontier-kind*)
                            (payload (fn-cbor-encode (cons :uint n)))
                            (max-payload *fn-bs-meta-max-frontier-payload*))
                 (:instance fn-bs-frontier-frame-inputp (n n))))))

(defthm fn-bs-frontier-protected-octet-listp
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (fn-cbor-octet-listp
            (fn-frame-protected *fn-bs-meta-magic* *fn-bs-meta-version*
                                *fn-bs-meta-frontier-kind*
                                (fn-cbor-encode (cons :uint n)))))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-cbor-payload-bound (n n))
                 (:instance fn-bs-frontier-payload-fits-frame-length (n n))
                 (:instance fn-cbor-u32-bytes-are-octets
                            (n (len (fn-cbor-encode (cons :uint n)))))
                 (:instance fn-cbor-octet-listp-append
                            (xs (fn-cbor-u32-bytes
                                 (len (fn-cbor-encode (cons :uint n)))))
                            (ys (fn-cbor-encode (cons :uint n))))
                 (:instance fn-cbor-octet-listp-append
                            (xs *fn-bs-meta-magic*)
                            (ys (cons *fn-bs-meta-version*
                                      (cons *fn-bs-meta-frontier-kind*
                                            (append
                                             (fn-cbor-u32-bytes
                                              (len (fn-cbor-encode
                                                    (cons :uint n))))
                                             (fn-cbor-encode
                                              (cons :uint n))))))))
           :in-theory (enable fn-frame-protected fn-frame-header))))

(defthm fn-bs-frontier-seal-octet-listp
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (fn-cbor-octet-listp
            (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                           *fn-bs-meta-frontier-kind*
                           (fn-cbor-encode (cons :uint n)))))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-protected-octet-listp (n n))
                 (:instance fn-frame-digestp-of-fn-frame-digest
                            (octets
                             (fn-frame-protected
                              *fn-bs-meta-magic* *fn-bs-meta-version*
                              *fn-bs-meta-frontier-kind*
                              (fn-cbor-encode (cons :uint n)))))
                 (:instance fn-cbor-octet-listp-append
                            (xs (fn-frame-protected
                                 *fn-bs-meta-magic* *fn-bs-meta-version*
                                 *fn-bs-meta-frontier-kind*
                                 (fn-cbor-encode (cons :uint n))))
                            (ys (fn-frame-digest
                                 (fn-frame-protected
                                  *fn-bs-meta-magic* *fn-bs-meta-version*
                                  *fn-bs-meta-frontier-kind*
                                  (fn-cbor-encode (cons :uint n)))))))
           :in-theory (enable fn-frame-seal fn-frame-encode))))

(defthm fn-bs-frontier-cbor-round-trip
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-cbor-decode-exact (fn-cbor-encode (cons :uint n)))
                  (fn-cbor-ok (cons :uint n) nil)))
  :hints (("Goal"
           :use ((:instance fn-cbor-value-round-trip
                            (value (cons :uint n))))
           :in-theory (enable fn-cbor-valuep))))

(defthm fn-bs-frontier-decode-impl-nat-or-nil
  (or (natp (fn-bs-frontier-decode-impl octets))
      (null (fn-bs-frontier-decode-impl octets)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable fn-bs-frontier-decode-impl
                              fn-bs-meta-frame-okp))))

(defthm fn-bs-frontier-impl-round-trip
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-bs-frontier-decode-impl
                   (fn-bs-frontier-encode-impl n))
                  n))
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-open-of-encode (n n))
                 (:instance fn-bs-frontier-seal-octet-listp (n n))
                 (:instance fn-bs-frontier-cbor-round-trip (n n)))
           :in-theory (enable fn-bs-frontier-encode-impl
                              fn-bs-frontier-decode-impl
                              fn-bs-meta-frame-okp))))

; -----------------------------------------------------------------------------
; The profile frame

; A valid profile's payload: two fixed texts and twelve eight-octet naturals.
(local
 (defun fn-bs-all-nat-specp (specs)
   (if (consp specs)
       (and (equal (car specs) :nat) (fn-bs-all-nat-specp (cdr specs)))
     t)))

(local
 (defthm fn-bs-all-nat-fields-octets-len
   (implies (and (fn-bs-all-nat-specp specs)
                 (fn-frame-values-okp specs values))
            (equal (len (fn-frame-fields-octets specs values))
                   (* 8 (len specs))))
   :hints (("Goal" :induct (fn-frame-values-okp specs values)
            :in-theory (enable fn-frame-field-octets fn-frame-values-okp
                               fn-frame-fields-octets fn-frame-field-okp
                               fn-frame-natp fn-frame-u64-bytes-len)))))

(local
 (defthm fn-bs-profile-fields-octets-len
   (implies (fn-bs-profile-validp values)
            (equal (len (fn-frame-fields-octets *fn-bs-meta-profile-spec*
                                                values))
                   (+ (len (fn-frame-field-octets :text *fn-bs-meta-format-8*))
                      (len (fn-frame-field-octets
                            :text *fn-bs-meta-frontier-format*))
                      96)))
   :hints (("Goal"
            :use ((:instance fn-bs-profile-validp-facts)
                  (:instance fn-bs-all-nat-fields-octets-len
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
            :in-theory (disable fn-bs-profile-validp-facts
                                fn-bs-all-nat-fields-octets-len
                                fn-frame-field-octets
                                fn-bs-profile-validp)))))

(defthm fn-bs-profile-frame-inputp
  (implies (fn-bs-profile-validp values)
           (fn-frame-inputp *fn-bs-meta-magic* *fn-bs-meta-version*
                            *fn-bs-meta-config-kind*
                            (fn-frame-fields-octets *fn-bs-meta-profile-spec*
                                                    values)
                            *fn-bs-meta-max-config-payload*))
  :hints (("Goal"
           :use ((:instance fn-bs-profile-validp-facts)
                 (:instance fn-bs-profile-fields-octets-len)
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-bs-meta-profile-spec*)))
           :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                           (fn-bs-profile-validp-facts
                            fn-bs-profile-fields-octets-len
                            fn-frame-fields-octets-are-octets
                            fn-bs-profile-validp)))))

(defun fn-bs-config-encode (values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bs-profile-validp values))
      nil
    (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                   *fn-bs-meta-config-kind*
                   (fn-frame-fields-octets *fn-bs-meta-profile-spec* values))))

(verify-guards fn-bs-config-encode
  :hints (("Goal" :use ((:instance fn-bs-profile-frame-inputp)
                        (:instance fn-bs-profile-validp-facts))
           :in-theory (e/d (fn-frame-inputp)
                           (fn-bs-profile-frame-inputp
                            fn-bs-profile-validp-facts
                            fn-bs-profile-validp)))))

; The decoder at every open.  A format-8 frame decodes to its values when
; they are a valid profile; a format-7 frame to one of its two tuples (the
; store then runs under the translation, `fn-bs-profile-of').  Anything else
; is NIL, and the open refuses the store.
(defun fn-bs-config-decode (octets)
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
          (if (and (fn-frame-parse-okp parsed)
                   (fn-bs-profile-validp (fn-frame-parse-value parsed)))
              (fn-frame-parse-value parsed)
            (let ((old (fn-frame-fields-parse
                        *fn-bs-meta-format-7-spec*
                        (fn-frame-result-payload frame))))
              (if (and (fn-frame-parse-okp old)
                       (fn-bs-meta-format-7-valuesp (fn-frame-parse-value old)))
                  (fn-frame-parse-value old)
                nil))))))))

(defun fn-bs-config-okp-impl (octets)
  (declare (xargs :guard t))
  (if (fn-bs-config-decode octets) t nil))

; The constrained functions remain the scan's public names.  Attachment gives
; a concrete executable interpretation without changing any theorem proved
; against their deliberately weak P3 constraints.
(defattach (fn-bs-frontier-encode fn-bs-frontier-encode-impl)
           (fn-bs-frontier-decode fn-bs-frontier-decode-impl)
           :hints (("Goal" :use fn-bs-frontier-impl-round-trip)))
(defattach fn-bs-config-okp fn-bs-config-okp-impl)

; -----------------------------------------------------------------------------
; Presets, defaults and the operator's request

; `development' and `scale' stay names for two fixed profiles, so existing
; stores and tests keep their witnesses; they are the format-7 tuples'
; translations.  The defaults are what `init' writes with no flag: the D27
; figures (2^32-1 transactions, 1 TiB of history, 64 MiB records, 16 MiB
; articles, 4096 groups, 460-octet names, 65536 open suffix, 2^20 per
; namespace), each capped at the codec ceiling it must not pass.  With P2's
; ceilings every figure but the name is below its cap, so the defaults are
; R 67 108 864, A 16 777 216, G 4096 and names 256 (460 capped at the
; configuration label's width, `fn-cfg-labelp-of-record-group-name'); the
; article record for (A, G) is 17 847 355 octets, within R.
(defconst *fn-bs-profile-development*
  (fn-bs-profile-from-format-7 *fn-bs-meta-format-7-development-values*))
(defconst *fn-bs-profile-scale*
  (fn-bs-profile-from-format-7 *fn-bs-meta-format-7-scale-values*))
(defconst *fn-bs-profile-defaults*
  (list *fn-bs-meta-format-8* *fn-bs-meta-frontier-format*
        *fn-bs-profile-transaction-ceiling*
        1099511627776
        (min 67108864 *fn-bs-profile-record-ceiling-codec*)
        (min 16777216 *fn-bs-profile-article-ceiling-codec*)
        (min 4096 *fn-bs-profile-groups-ceiling-codec*)
        (min 460 *fn-bs-profile-group-name-ceiling-codec*)
        65536
        *fn-bs-profile-default-namespace-count*
        *fn-bs-profile-default-namespace-count*
        *fn-bs-profile-default-namespace-count*
        *fn-bs-profile-default-namespace-count*
        *fn-bs-profile-default-namespace-count*))

(defun fn-bs-config-for-profile (profile)
  (declare (xargs :guard t))
  (cond ((equal profile :development) *fn-bs-profile-development*)
        ((equal profile :scale) *fn-bs-profile-scale*)
        ((equal profile :default) *fn-bs-profile-defaults*)
        (t nil)))

; An operator request: a base (`:default', `:development', `:scale', or
; `:current' for the store's own profile) and an alist of field overrides
; (field index . natural), as `init' and `store upgrade-profile' parse them.
(defun fn-bs-profile-put (i v values)
  "VALUES with position I replaced by V (a total `update-nth')."
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (zp i)
      (cons v (if (consp values) (cdr values) nil))
    (cons (if (consp values) (car values) nil)
          (fn-bs-profile-put (1- i) v (if (consp values) (cdr values) nil)))))

(defun fn-bs-profile-set-fields (values overrides)
  (declare (xargs :guard t :measure (len overrides)))
  (if (consp overrides)
      (let ((o (car overrides)))
        (if (and (consp o) (natp (car o)) (<= 2 (car o))
                 (< (car o) (len *fn-bs-meta-profile-spec*)))
            (fn-bs-profile-set-fields (fn-bs-profile-put (car o) (cdr o) values)
                                      (cdr overrides))
          :bad))
    values))

(defun fn-bs-profile-requestp (request)
  (declare (xargs :guard t))
  (and (true-listp request) (equal (len request) 2)
       (member-equal (car request) '(:default :development :scale :current))
       (alistp (cadr request))))

(defthm fn-bs-profile-requestp-alistp
  (implies (fn-bs-profile-requestp request)
           (alistp (cadr request)))
  :rule-classes :forward-chaining)

; The profile REQUEST names, over CURRENT (the profile a store runs under, or
; NIL at `init'): its values, or (:invalid REASON).
(defun fn-bs-profile-resolve (request current)
  (declare (xargs :guard t))
  (if (not (fn-bs-profile-requestp request))
      (list :invalid :request)
    (let* ((base (if (equal (car request) :current)
                     (fn-bs-profile-of current)
                   (fn-bs-config-for-profile (car request))))
           (values (if (null base) :bad
                     (fn-bs-profile-set-fields base (cadr request)))))
      (let ((values (if (or (equal values :bad)
                            (assoc-equal *fn-bs-pf-max-open-suffix*
                                         (cadr request)))
                        values
                      ; K follows a lowered T unless the operator named K.
                      (fn-bs-profile-put
                       *fn-bs-pf-max-open-suffix*
                       (min (fn-bs-pf 8 values) (fn-bs-pf 2 values))
                       values))))
      (cond ((equal values :bad) (list :invalid :request))
            ((fn-bs-profile-invalid-reason values)
             (list :invalid (fn-bs-profile-invalid-reason values)))
            (t values))))))

; What `init' writes for REQUEST (a preset word, or the operator's request
; of base and field overrides, resolved over no current profile):
;   (:init OCTETS)       the frame of the resolved profile
;   (:refused REASON)    the relation it fails by name, or :request
(defun fn-bs-profile-init-verdict (request)
  (declare (xargs :guard t))
  (let ((values (fn-bs-profile-resolve (if (symbolp request)
                                           (list request nil)
                                         request)
                                       nil)))
    (if (and (consp values) (equal (car values) :invalid))
        (list :refused (if (consp (cdr values)) (cadr values) :request))
      (list :init (fn-bs-config-encode values)))))

(defun fn-bs-config-frame-for-profile (profile)
  "The frame `init' writes for PROFILE, a preset word or a request, or NIL."
  (declare (xargs :guard t))
  (let ((verdict (fn-bs-profile-init-verdict profile)))
    (if (equal (car verdict) :init) (cadr verdict) nil)))

; The operator's view of the profile a store runs under: the format it is
; persisted in (8, or 7 for a store not yet upgraded) and every field by its
; operator name, read through `fn-bs-profile-of' (0 for a value that is not
; a profile).  `operator status' prints it; the host formats, never computes.
(defun fn-bs-profile-report-fields (names values)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((entry (car names)))
        (if (and (consp entry) (natp (car entry)))
            (cons (cons (cdr entry) (fn-bs-profile-field (car entry) values))
                  (fn-bs-profile-report-fields (cdr names) values))
          (fn-bs-profile-report-fields (cdr names) values)))
    nil))

(defun fn-bs-profile-report (values)
  (declare (xargs :guard t))
  (cons (cons "format"
              (cond ((fn-bs-profile-validp values) 8)
                    ((fn-bs-meta-format-7-valuesp values) 7)
                    (t 0)))
        (fn-bs-profile-report-fields *fn-bs-profile-field-names* values)))

; These stay functions rather than defconsts: ACL2 deliberately ignores a
; defattach while evaluating a defconst, whereas the serving bridge evaluates
; these ground calls through the SHA-256 attachment.
(defun fn-bs-initial-config-octets ()
  (fn-bs-config-frame-for-profile :development))

(defun fn-bs-initial-frontier-octets ()
  (fn-bs-frontier-encode-impl 0))

; These are concrete correspondence facts for the host calls.  The allocator
; and this CBOR profile share the uint32 domain; only fn-bs-frontier-next
; refuses its maximum because that value has no successor.
(defthm fn-bs-frontier-encode-impl-unfolds
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-bs-frontier-encode-impl n)
                  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                                 *fn-bs-meta-frontier-kind*
                                 (fn-cbor-encode (cons :uint n))))))

(defthm fn-bs-frontier-next-is-successor
  (implies (and (natp n) (< n *fn-cbor-max-uint*))
           (equal (fn-bs-frontier-next n) (1+ n))))
