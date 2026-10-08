(in-package "ACL2")
(include-book "../../books/checkpoint-frame-fit")
(include-book "must-fail-checked")

(defun pckff-held-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena)
      (mv-let (row fn-arena)
        (fn-cat-intern-list
         (fn-record-make 0 1 0 "<a@x>" '(1 2) '("fn.test") "o" "s" "e" 1 5)
         nil 0 fn-arena)
        (mv (and (fn-arena-p fn-arena) (fn-held-p row)
                 (member-equal row (list row))
                 (equal (fn-pck-x-frame-length row fn-arena) 2)
                 (natp (fn-pck-x-frame-length row fn-arena))
                 (< (+ 1 (fn-pck-x-frame-length row fn-arena)) 18446744073709551616)
                 (equal (fn-pck-x-frame-length row fn-arena)
                        (fn-pck-frame-length (fn-row-wire-of row fn-arena)))
                 (eq (fn-pck-x-frame-preflight (list row) fn-arena) :ok)
                 (equal (fn-pck-x-frame-preflight (list row) fn-arena)
                        (fn-pck-frame-verdict
                         (fn-pck-frame-lengths (fn-rows-wire-of (list row) fn-arena)))))
            fn-arena))
      ok)))
(assert-event (pckff-held-witness))

; The boundary decision is the same entry the host and model plans call.
; The descriptor's length is an integer; this tooth allocates no huge payload.
(assert-event
 (and (eq (fn-pck-frame-verdict '(0 2 18446744073709551614)) :ok)
      (equal (fn-pck-frame-verdict '(0 2 18446744073709551615))
             '(:refused :payload-over-frame))))
; Mutation: checking LEN < 2^64 instead of 1+LEN < 2^64 wrongly admits it.
(assert-event
 (let ((n 18446744073709551615))
   (and (natp n) (< n 18446744073709551616)
        (not (< (+ 1 n) 18446744073709551616))
        (equal (fn-pck-frame-verdict (list n)) '(:refused :payload-over-frame)))))
(must-fail-checked
 (assert-event (eq (fn-pck-frame-verdict '(18446744073709551615)) :ok)))
