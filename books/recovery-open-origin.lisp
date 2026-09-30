; Accepted full-open origin is distinct from a verified checkpoint.
; Runtime callers never construct this origin or supply final Store counts.
(in-package "ACL2")
(include-book "recovery-source-authority")

(defun fn-rsoa-originp (origin)
 (declare (xargs :guard t))
 (and (fn-omk-widthp origin 5)
      (eq (fn-omk-at 0 origin) :completed-store-open)
      (natp (fn-omk-at 1 origin)) (natp (fn-omk-at 2 origin))
      (member-eq (fn-omk-at 3 origin) '(:empty-initialized :full-log-replay))))

(defun fn-rsoa-begin (ticket epoch origin ctx count frontier)
 (declare (xargs :guard t))
 (if (not (and (natp ticket) (natp epoch) (fn-rsoa-originp origin)
               (equal epoch (fn-omk-at 2 origin))
               (natp count) (natp frontier)
               (equal (fn-rsa-context-count ctx) count)
               (if (eq (fn-omk-at 3 origin) :empty-initialized)
                   (equal count 0) (< 0 count))))
     (mv :refused nil)
   (mv :issued (list :recovering ticket epoch origin count frontier ctx 0
                      (fn-omk-at 1 origin)))))

(in-theory (disable fn-rsoa-originp fn-rsoa-begin))
