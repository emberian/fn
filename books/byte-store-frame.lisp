; fn byte-store metadata frames: concrete frontier and configuration bytes.
;
; This is the P4 realization of the three constrained scan seams in
; `byte-store-scan'.  A frontier is a deterministic CBOR uint inside an FNSM
; frame.  The store profile is a fixed, bounded frame-field record.  Both use
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
            :in-theory (enable fn-cbor-encode fn-cbor-valuep
                               fn-cbor-encode-argument
                               fn-cbor-octet-listp fn-cbor-octetp)))))

(defconst *fn-bs-meta-format-legacy*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 54)) ; fn-store-experiment-6
(defconst *fn-bs-meta-format-development*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 55)) ; fn-store-experiment-7
(defconst *fn-bs-meta-frontier-format*
  '(102 110 45 115 116 111 114 101 45 97 108 108 111 99 97 116 105
    111 110 45 102 114 111 110 116 105 101 114 45 50))

(defconst *fn-bs-meta-legacy-development-values*
  (list *fn-bs-meta-format-legacy* 1048576 32768 8388864 128
        *fn-bs-meta-frontier-format*))
(defconst *fn-bs-meta-legacy-scale-values*
  (list *fn-bs-meta-format-legacy* 1048576 32768 268443648 4096
        *fn-bs-meta-frontier-format*))
(defconst *fn-bs-meta-development-values*
  (list *fn-bs-meta-format-development* 1048576 32768 25165824 128
        *fn-bs-meta-frontier-format*))
(defconst *fn-bs-meta-scale-values*
  (list *fn-bs-meta-format-development* 1048576 32768 805306368 4096
        *fn-bs-meta-frontier-format*))

(defun fn-bs-meta-config-valuesp (values)
  (declare (xargs :guard t))
  (or (equal values *fn-bs-meta-legacy-development-values*)
      (equal values *fn-bs-meta-legacy-scale-values*)
      (equal values *fn-bs-meta-development-values*)
      (equal values *fn-bs-meta-scale-values*)))

(defun fn-bs-meta-nth (n values)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (if (consp values) (car values) nil)
    (fn-bs-meta-nth (1- n) (if (consp values) (cdr values) nil))))

(defun fn-bs-profile-record-ceiling (values)
  (declare (xargs :guard t))
  (if (not (fn-bs-meta-config-valuesp values)) 0
    (floor (fn-bs-meta-nth 3 values) (fn-bs-meta-nth 4 values))))

(defun fn-bs-publication-admissiblep (values committed-count
                                             committed-octets prospective-octets)
  (declare (xargs :guard t))
  (and (fn-bs-meta-config-valuesp values)
       (natp committed-count) (natp committed-octets)
       (natp prospective-octets)
       (< committed-count (fn-bs-meta-nth 4 values))
       (<= prospective-octets (fn-bs-profile-record-ceiling values))
       (<= (+ committed-octets prospective-octets)
           (fn-bs-meta-nth 3 values))))

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

(defun fn-bs-config-encode (values)
  (declare (xargs :guard t))
  (if (not (fn-bs-meta-config-valuesp values))
      nil
    (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                   *fn-bs-meta-config-kind*
                   (fn-frame-fields-octets *fn-bs-meta-config-spec* values))))

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
                       *fn-bs-meta-config-spec*
                       (fn-frame-result-payload frame))))
          (if (and (fn-frame-parse-okp parsed)
                   (fn-bs-meta-config-valuesp (fn-frame-parse-value parsed)))
              (fn-frame-parse-value parsed)
            nil))))))

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

; ACL2 calls these two values from host/store-host.lisp.  A request outside
; the named profiles is refused before a byte string reaches the filesystem.
(defun fn-bs-config-for-profile (profile)
  (declare (xargs :guard t))
  (cond ((equal profile :development) *fn-bs-meta-development-values*)
        ((equal profile :scale) *fn-bs-meta-scale-values*)
        (t nil)))

(defun fn-bs-config-frame-for-profile (profile)
  (declare (xargs :guard t))
  (fn-bs-config-encode (fn-bs-config-for-profile profile)))

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
