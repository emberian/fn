; Selected SBCL 2.6.8 x86-64 allocation layout, not a portable CL guarantee.
; Source/measurement coordinates: planning/evidence/paged-resource-pool/
; persistent-layout-hbox-sbcl-2.6.8.log and layout-source-2026-09-30.md.
; The native factory supplies :size N >= 8, :rehash-size 1, threshold 1.0,
; synchronized T, nonweak standard EQ/EQL/EQUAL maps and never exceeds N.
; Its constructor silently caps N at 2^24; supported-policy validation must
; reject that mismatch BEFORE allocation. This is a runtime resource bound,
; not a ceiling on stored records or frame extent lengths.
(in-package "ACL2")

(defun fn-crl-align16 (octets)
  (declare (xargs :guard t))
  (* 16 (ceiling (nfix octets) 16)))

(defun fn-crl-array-octets (count width)
  (declare (xargs :guard t))
  (fn-crl-align16 (+ 16 (* (nfix count) (nfix width)))))

(defun fn-crl-table-capacity (count)
  (declare (xargs :guard t))
  (max 8 (nfix count)))

(defun fn-crl-table-supportedp (count)
  (declare (xargs :guard t))
  (and (natp count) (<= (fn-crl-table-capacity count) (expt 2 24))))

(defun fn-crl-table-buckets (count)
  (declare (xargs :guard t))
  (expt 2 (integer-length (- (fn-crl-table-capacity count) 1))))

; Six backing objects for EQUAL, five for EQ/EQL, including the lock.
; N <= 2^24 makes conversion to single-float in SBCL exact.
(defun fn-crl-table-octets (count equalp)
  (declare (xargs :guard t))
  (let ((n (fn-crl-table-capacity count)))
    (+ 176 32
       (fn-crl-array-octets (+ (* 2 n) 3) 8)
       (fn-crl-array-octets (fn-crl-table-buckets count) 4)
       (fn-crl-array-octets (+ 1 n) 4)
       (if equalp (fn-crl-array-octets (+ 1 n) 4) 0))))

; An immutable token can contain offsets/cids wider than u64. Do not hide
; those heap digits in a fixed per-job constant. Positive fixnums use62bits;
; bignums need a sign bit, a header word and whole64bit digits, aligned16.
(defun fn-crl-natural-octets (value)
  (declare (xargs :guard t))
  (let ((bits (integer-length (nfix value))))
    (if (<= bits 62) 0
      (fn-crl-align16 (+ 8 (* 8 (ceiling (+ bits 1) 64)))))))

(defun fn-crl-token-integer-octets (id cid file eoff elen trailer)
  (declare (xargs :guard t))
  (+ (fn-crl-natural-octets id) (fn-crl-natural-octets cid)
     (fn-crl-natural-octets file) (fn-crl-natural-octets eoff)
     (fn-crl-natural-octets elen) (fn-crl-natural-octets trailer)))

(in-theory (disable fn-crl-align16 fn-crl-array-octets fn-crl-table-capacity
                    fn-crl-table-supportedp fn-crl-table-buckets
                    fn-crl-table-octets fn-crl-natural-octets
                    fn-crl-token-integer-octets))
