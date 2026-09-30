(in-package "ACL2")
(include-book "../../books/msgid-query-page")

(defun fn-mpt-repeat (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons x (fn-mpt-repeat (1- n) x))))

; A complete occupied page yields to directory traversal without losing the
; residual quantum. The next occupied page consumes the rest and yields;
; neither observation is completed absence.
(assert-event
 (let* ((page (append (fn-mpt-repeat 1024 2) (fn-mpt-repeat 1024 1)))
        (a (mv-list 4 (fn-mpl-page-next 1 '(0 3 0) 2048 3 0 page)))
        (b (mv-list 4 (fn-mpl-page-next 1 (nth 1 a) (nth 3 a) 3 1 page))))
   (and (equal a '(:next-page (1 2 0) nil 1024))
        (equal b '(:yield (2 1 0) nil 0)))))

; Nonempty literal instance of the entire page-span refinement antecedent
; and conclusion, including candidate ordinal zero and residual fuel.
(assert-event
 (let* ((page (append '(2 2 1) (fn-mpt-repeat 1021 0)
                      '(1 1 1) (fn-mpt-repeat 1021 0)))
        (words (append (fn-mpt-repeat 4096 0) page))
        (cursor '(2 1 0))
        (a (mv-list 4 (fn-mpl-page-next 1 cursor 2048 3 2 page)))
        (b (mv-list 4 (fn-mpl-next 1 cursor 2048 3 words))))
   (and (fn-mpr-cursorp cursor 3)
        (fn-mpl-page-match-from 0 2 page words)
        (not (equal (nth 0 a) :next-page))
        (equal a '(:candidate (2 1 3) 0 2045))
        (equal a b))))
