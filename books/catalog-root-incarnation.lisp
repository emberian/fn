; Allocation identity is independent of the retained history version.
; Reserve before binding a replacement catalog; a failed binding spends the
; reservation. Tokens are private to one owner/image lifetime, never persisted
; or compared across processes. No bounded integer codec or wrap is imposed.
(in-package "ACL2")

(defun fn-cri-tokenp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)
       (eq (car x) :catalog-root) (natp (cadr x))))

(defun fn-cri-reserve (next)
  (declare (xargs :guard t))
  (if (natp next)
      (mv (list :catalog-root next) (+ 1 next))
    (mv nil next)))

(defthm fn-cri-reserve-is-fresh-and-advances
  (implies (natp next)
           (and (fn-cri-tokenp (mv-nth 0 (fn-cri-reserve next)))
                (equal (cadr (mv-nth 0 (fn-cri-reserve next))) next)
                (< next (mv-nth 1 (fn-cri-reserve next)))
                (natp (mv-nth 1 (fn-cri-reserve next))))))

(defthm fn-cri-reserve-never-reuses-an-earlier-token
  (implies (and (natp next) (natp earlier) (< earlier next))
           (not (equal (mv-nth 0 (fn-cri-reserve next))
                       (mv-nth 0 (fn-cri-reserve earlier))))))

(defthm fn-cri-corrupt-counter-refuses-without-reset
  (implies (not (natp next))
           (and (null (mv-nth 0 (fn-cri-reserve next)))
                (equal (mv-nth 1 (fn-cri-reserve next)) next))))
