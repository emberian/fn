; Startup text projection only. The upload profile and execution admission
; remain the authority for the manifest domain and resource reservation.
(in-package "ACL2")
(include-book "upload-kind")
(include-book "article-limit-text")
(fn2-book-layer :d)

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
