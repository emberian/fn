; Bounded codec boundary. The composed mounted provider supplies the retained
; cursor. This entry is not a mount/QID issuer or a permission to allocate.
(in-package "ACL2")
(include-book "../books/ninep-stat-stream")
(include-book "../books/definterface")
(defun fn-ninep-stat-reply-step (cursor fn-octets state)
 (declare (xargs :stobjs (fn-octets state) :guard t))
 (mv-let (word next fn-octets) (fn-9pst-reply-step cursor fn-octets)
  (mv word next fn-octets state)))
(defthm fn-ninep-stat-reply-step-complete-correspondence
 (equal (fn-ninep-stat-reply-step cursor fn-octets state)
        (list (mv-nth 0 (fn-9pst-reply-step cursor fn-octets))
              (mv-nth 1 (fn-9pst-reply-step cursor fn-octets))
              (mv-nth 2 (fn-9pst-reply-step cursor fn-octets)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-stat-reply-step) (fn-9pst-reply-step)))))
(definterface fn-ninep-stat-reply-step :class :common-lisp-compliant)
