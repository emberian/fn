; Exact modern served producer; body and guard unchanged.
(in-package "ACL2")
(include-book "catalog")
(include-book "catalog-prepared-record")

(defun fn-cat-prepare-sealed (w row plan reservation pending fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)))
  (cond (pending (list :pending))
        ((and (natp (fn-record-payload row))
              (equal (fn-record-payload row) (1- (fn-arena-count fn-arena))))
         (let ((expected (fn-cat-count fn-cat)))
           (fn-pc-make (cons (nfix (fn-record-txid w)) expected)
                       expected row plan reservation)))
        (t (list :not-sealed))))
