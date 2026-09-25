; The signed-receipt carrier (lane signed-receipts, 2026-09-25).  A receipt
; ADU (books/bp-adu.lisp) stays exactly what it was; a signed receipt is the
; same canonical ADU octets carried with the issuer's 32-octet principal and
; the two hybrid signatures over `fn-bpsr-signed-preimage'
; (books/bp-release-authority.lisp).  This book only frames and unframes the
; octets: it decides no signature and names no key width, which is
; books/hybrid-signature.lisp's alone.
;
;   bytes "FN-BP-SRCPT"  uint 0  bytes ADU  bytes PRINCIPAL  bytes ED25519
;   bytes ML-DSA-65
;
; Six canonical CBOR items and nothing after them.  The magic differs from
; the ADU magic "FN-BP-ADU", so a bare ADU is never a signed receipt.
(in-package "ACL2")
(include-book "bp-adu")

(defconst *fn-bpsr-magic* '(70 78 45 66 80 45 83 82 67 80 84)) ; "FN-BP-SRCPT"
(defconst *fn-bpsr-version* 0)
; Each signature field is bounded here only so the frame is bounded; the
; exact widths (64 and 3309) are `fn-hsig-signatures-p''s.
(defconst *fn-bpsr-max-signature-octets* 4096)
(defconst *fn-bpsr-max-octets* 16384)

(defun fn-bpsr-boundedp (x n)
  (declare (xargs :guard (natp n)))
  (and (fn-cbor-octet-listp x) (consp x) (fn-cbor-at-mostp x n)))

; (:signed-receipt ADU-OCTETS PRINCIPAL ED25519-SIGNATURE ML-DSA-65-SIGNATURE)
(defun fn-bpsr-make (adu principal ed ml)
  (declare (xargs :guard t))
  (list :signed-receipt adu principal ed ml))

(defun fn-bpsr-adu (x) (declare (xargs :guard t)) (fn-bpa-nth 1 x))
(defun fn-bpsr-principal (x) (declare (xargs :guard t)) (fn-bpa-nth 2 x))
(defun fn-bpsr-ed25519 (x) (declare (xargs :guard t)) (fn-bpa-nth 3 x))
(defun fn-bpsr-ml-dsa-65 (x) (declare (xargs :guard t)) (fn-bpa-nth 4 x))

; The signatures in the shape `fn-hsig-signatures-p' reads.
(defun fn-bpsr-signatures (x)
  (declare (xargs :guard t))
  (list (cons :ed25519 (fn-bpsr-ed25519 x))
        (cons :ml-dsa-65 (fn-bpsr-ml-dsa-65 x))))

; The inner ADU is a canonical receipt ADU (at most 4096 octets; a receipt's
; nine metadata fields are at most 256 each), the principal is 32 octets and
; each signature is a bounded non-empty octet string.
(defun fn-bpsr-signedp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal x (fn-bpsr-make (fn-bpsr-adu x) (fn-bpsr-principal x)
                              (fn-bpsr-ed25519 x) (fn-bpsr-ml-dsa-65 x)))
       (let ((decoded (fn-bpa-decode-exact (fn-bpsr-adu x))))
         (and (fn-bpsr-boundedp (fn-bpsr-adu x) *fn-bpsr-max-signature-octets*)
              (fn-bpa-result-okp decoded)
              (fn-bpa-receiptp (fn-bpa-result-message decoded))))
       (fn-cbor-octet-listp (fn-bpsr-principal x))
       (equal (len (fn-bpsr-principal x)) 32)
       (fn-bpsr-boundedp (fn-bpsr-ed25519 x) *fn-bpsr-max-signature-octets*)
       (fn-bpsr-boundedp (fn-bpsr-ml-dsa-65 x)
                         *fn-bpsr-max-signature-octets*)))

(defun fn-bpsr-encode (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpsr-signedp x))
      nil
    (append (fn-cbor-encode (cons :bytes *fn-bpsr-magic*))
            (fn-cbor-encode (cons :uint *fn-bpsr-version*))
            (fn-bpa-encode-fields
             (list (fn-bpsr-adu x) (fn-bpsr-principal x)
                   (fn-bpsr-ed25519 x) (fn-bpsr-ml-dsa-65 x))))))

; The decoder reads the six items, requires nothing after them, and accepts
; only a frame its own encoder reproduces exactly: the answer is the signed
; receipt, or nil.
(defun fn-bpsr-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-at-mostp octets *fn-bpsr-max-octets*)
                (fn-cbor-octet-listp octets)))
      nil
    (let ((magic (fn-record-read-bytes octets)))
      (if (not (and (fn-record-parse-okp magic)
                    (equal (fn-record-parse-value magic) *fn-bpsr-magic*)))
          nil
        (let ((version (fn-record-read-uint (fn-record-parse-rest magic))))
          (if (not (and (fn-record-parse-okp version)
                        (equal (fn-record-parse-value version)
                               *fn-bpsr-version*)))
              nil
            (let ((fields (fn-bpa-read-fields
                           4 (fn-record-parse-rest version))))
              (if (not (and (fn-record-parse-okp fields)
                            (null (fn-record-parse-rest fields))))
                  nil
                (let* ((values (fn-record-parse-value fields))
                       (signed (fn-bpsr-make (fn-bpa-nth 0 values)
                                             (fn-bpa-nth 1 values)
                                             (fn-bpa-nth 2 values)
                                             (fn-bpa-nth 3 values))))
                  (if (and (fn-bpsr-signedp signed)
                           (equal (fn-bpsr-encode signed) octets))
                      signed
                    nil))))))))))

; The receipt ADU octets a payload carries: the inner ADU of a signed
; receipt, otherwise the payload itself.  Every reader of a delivered or
; queued receipt reads through this one function.
(defun fn-bpsr-adu-octets (payload)
  (declare (xargs :guard t :verify-guards nil))
  (let ((signed (fn-bpsr-decode payload)))
    (if signed (fn-bpsr-adu signed) payload)))

(defthm fn-bpsr-decode-is-signed
  (implies (fn-bpsr-decode octets)
           (and (fn-bpsr-signedp (fn-bpsr-decode octets))
                (equal (fn-bpsr-encode (fn-bpsr-decode octets)) octets)))
  :hints (("Goal" :in-theory (e/d (fn-bpsr-decode)
                                  (fn-bpsr-signedp fn-bpsr-encode
                                   fn-record-read-bytes fn-record-read-uint
                                   fn-bpa-read-fields fn-cbor-at-mostp
                                   fn-cbor-octet-listp)))))

(defthm fn-bpsr-adu-octets-of-unsigned
  (implies (not (fn-bpsr-decode payload))
           (equal (fn-bpsr-adu-octets payload) payload))
  :hints (("Goal" :in-theory '(fn-bpsr-adu-octets))))

(in-theory (disable fn-bpsr-signedp fn-bpsr-encode fn-bpsr-decode
                    fn-bpsr-adu-octets))

(verify-guards fn-bpsr-signedp)
(verify-guards fn-bpsr-encode)
(verify-guards fn-bpsr-decode
  :hints (("Goal" :in-theory (e/d (fn-record-guard-vocabulary)
                                  (fn-record-read-bytes fn-record-read-uint
                                   fn-record-parse-rest fn-cbor-octet-listp
                                   fn-record-parse-okp fn-bpa-read-fields
                                   fn-bpsr-signedp fn-bpsr-encode)))))
(verify-guards fn-bpsr-adu-octets)
