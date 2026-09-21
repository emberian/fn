; fn byte-store metadata frames: concrete frontier and configuration bytes.
;
; This is the P4 realization of the three constrained scan seams in
; `byte-store-scan'.  A frontier is a deterministic CBOR uint inside an FNSM
; frame.  The store profile is a fixed, bounded frame-field record.  Both use
; the existing frame grammar and its ACL2-owned trailer; the host only moves
; the resulting octets to and from regular files.
;
; The old JSON files remain a read-only migration input in tools/run_store.py.
; This book never interprets them and never rewrites an old store.

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

(defconst *fn-bs-meta-format-development*
  '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
    101 110 116 45 54)) ; fn-store-experiment-6
(defconst *fn-bs-meta-frontier-format*
  '(102 110 45 115 116 111 114 101 45 97 108 108 111 99 97 116 105
    111 110 45 102 114 111 110 116 105 101 114 45 50))

(defconst *fn-bs-meta-development-values*
  (list *fn-bs-meta-format-development* 1048576 32768 8388864 128
        *fn-bs-meta-frontier-format*))
(defconst *fn-bs-meta-scale-values*
  (list *fn-bs-meta-format-development* 1048576 32768 268443648 4096
        *fn-bs-meta-frontier-format*))

(defun fn-bs-meta-config-valuesp (values)
  (declare (xargs :guard t))
  (or (equal values *fn-bs-meta-development-values*)
      (equal values *fn-bs-meta-scale-values*)))

(defun fn-bs-meta-frame-okp (frame kind payload bound)
  (declare (xargs :guard t))
  (and (fn-frame-result-okp frame)
       (equal (fn-frame-result-magic frame) *fn-bs-meta-magic*)
       (equal (fn-frame-result-version frame) *fn-bs-meta-version*)
       (equal (fn-frame-result-kind frame) kind)
       (fn-cbor-octet-listp payload)
       (<= (len payload) bound)))

(defun fn-bs-frontier-encode-impl (n)
  (declare (xargs :guard t))
  (if (not (and (natp n) (<= n *fn-cbor-max-uint*)))
      nil
    (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                   *fn-bs-meta-frontier-kind*
                   (fn-cbor-encode (cons :uint n)))))

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
                   (equal (car (fn-cbor-result-value decoded)) :uint))
              (cdr (fn-cbor-result-value decoded))
            nil))))))

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
(defattach fn-bs-frontier-encode fn-bs-frontier-encode-impl)
(defattach fn-bs-frontier-decode fn-bs-frontier-decode-impl)
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

; These are concrete correspondence facts for the host calls.  The bounded
; domain is the actual uint32 allocator domain used by run_store, a strict
; subset of the CBOR uint profile.
(defthm fn-bs-frontier-decode-impl-nat-or-nil
  (or (natp (fn-bs-frontier-decode-impl octets))
      (null (fn-bs-frontier-decode-impl octets)))
  :rule-classes :type-prescription)

(defthm fn-bs-frontier-encode-impl-unfolds
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (equal (fn-bs-frontier-encode-impl n)
                  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                                 *fn-bs-meta-frontier-kind*
                                 (fn-cbor-encode (cons :uint n))))))

(defthm fn-bs-frontier-next-is-successor
  (implies (and (natp n) (< n *fn-cbor-max-uint*))
           (equal (fn-bs-frontier-next n) (1+ n))))
