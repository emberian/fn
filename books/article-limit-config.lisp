; Startup text projection only. The upload profile and execution admission
; remain the authority for the manifest domain and resource reservation.
(in-package "ACL2")
(include-book "upload-kind")
(fn2-book-layer :d)

(defun fn2-article-limit-decimal-aux (text index value)
 (declare (xargs :measure (nfix (- (length text) (nfix index)))
  :guard (and (stringp text) (natp index) (<= index (length text)) (natp value))))
 (if (>= (nfix index) (length text))
     (if (unsigned-byte-p 32 value) value nil)
   (let ((digit (- (char-code (char text (nfix index))) 48)))
    (if (and (<= 0 digit) (<= digit 9))
        (fn2-article-limit-decimal-aux text (+ 1 (nfix index)) (+ (* 10 value) digit))
      nil))))
(defun fn2-article-limit-decimal (text)
 (declare (xargs :guard t))
 (if (and (stringp text) (< 0 (length text)) (<= (length text) 10))
     (fn2-article-limit-decimal-aux text 0 0) nil))

(defun fn2-article-limit-profile-from-text (profile text)
 (declare (xargs :guard t))
 (if (null text) profile
  (let* ((value (fn2-article-limit-decimal text))
         (base (if (alistp profile) profile nil))
         (projected (put-assoc-equal :article-max (if value value -1) base)))
   ; Invalid present input must not become NIL, the default-selection value.
   ; Use the actual producer's domain predicate, not a copied manifest limit.
   (if (fn2-input-config-profilep projected) projected
     (put-assoc-equal :article-max -1 base)))))
