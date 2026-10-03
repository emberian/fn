(in-package "ACL2")
(include-book "../../books/catalog-root-incarnation")

(assert-event
 (mv-let (first next) (fn-cri-reserve 0)
   (mv-let (second next2) (fn-cri-reserve next)
     (and (equal first '(:catalog-root 0))
          (equal second '(:catalog-root 1))
          (fn-cri-tokenp first) (fn-cri-tokenp second)
          (< next next2) (not (equal first second))))))
; Spending a reservation does not depend on installation succeeding.
(assert-event
 (mv-let (unused next) (fn-cri-reserve 17)
   (mv-let (installed next2) (fn-cri-reserve next)
     (and (equal unused '(:catalog-root 17))
          (equal installed '(:catalog-root 18))
          (equal next2 19) (not (equal unused installed))))))
(assert-event
 (mv-let (token next) (fn-cri-reserve :corrupted)
   (and (null token) (equal next :corrupted))))
(assert-event
 (let ((n (expt 2 128)))
   (mv-let (token next) (fn-cri-reserve n)
     (and (equal token (list :catalog-root n)) (< n next)))))
