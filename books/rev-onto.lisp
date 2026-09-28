; fn-ag-rev-onto: XS reversed onto ACC, by a tail call.
;
; The loop twins' shared step (PKT-876, PKT-877): a right fold executes by
; folding (fn-ag-rev-onto xs nil) from the left, and a collecting loop reverses
; each piece onto its accumulator.  Moved here from books/acceptance-alloc.lisp
; (lane serve-depth, 2026-09-28) so that books which do not include the
; acceptance helpers -- books/wire, the carriers, the web renderer -- can run
; their walks by loops too.  Guard t: any XS, a non-list tail dropped as
; `append' drops it.

(in-package "ACL2")

(defun fn-ag-rev-onto (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-ag-rev-onto (cdr xs) (cons (car xs) acc))
    acc))

(defthm fn-ag-rev-onto-true-listp
  (implies (true-listp acc)
           (true-listp (fn-ag-rev-onto xs acc))))
