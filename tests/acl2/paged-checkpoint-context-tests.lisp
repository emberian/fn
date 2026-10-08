(in-package "ACL2")
(include-book "../../books/paged-checkpoint-context")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)
(defun pck-context-test-record (s)
  (fn-record-make s (+ 1 (nfix s)) 0 "<a@x>" '(7)
                  '("fn.test") "o" "s" "e" 1 5))
(defun pck-context-test-records (s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons (pck-context-test-record s)
          (pck-context-test-records (+ 1 (nfix s)) (1- n)))))
(defconst *pck-context-prefix* (pck-context-test-records 0 1))
(defconst *pck-context-delta* (pck-context-test-records 1 80))
(defconst *pck-context-full* (fn-pck-st-of (fn-pck-seed) *pck-context-prefix*))
(defconst *pck-context-thin* (fn-pck-context-state (fn-pck-context *pck-context-full*)))
(assert-event
 (and (fn-ssr-statep *pck-context-full*)
      (fn-ssr-statep *pck-context-thin*)
      (consp (fn-ssr-at 0 *pck-context-full*))
      (equal (fn-ssr-at 0 *pck-context-thin*) nil)
      (fn-pck-context-agreep *pck-context-full* *pck-context-thin*)
      (equal (fn-pck-rows-from *pck-context-delta* 70 *pck-context-full*)
             (fn-pck-rows-from *pck-context-delta* 70 *pck-context-thin*))
      (fn-pck-context-agreep
       (fn-pck-st-of *pck-context-full* *pck-context-delta*)
       (fn-pck-st-of *pck-context-thin* *pck-context-delta*))
      (< (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows *pck-context-prefix*))) 2048)
      (< 2048 (len (adt-tp-seq-words *fn-pck-row-schema*
                                    (fn-pck-rows (append *pck-context-prefix* *pck-context-delta*)))))))
(defconst *pck-context-wrong*
 (fn-ssr-state nil (fn-ssr-at 1 *pck-context-full*) 1 (fn-ssr-at 3 *pck-context-full*)))
(assert-event
 (and (fn-ssr-statep *pck-context-wrong*)
      (not (fn-pck-context-agreep *pck-context-full* *pck-context-wrong*))
      (not (equal (fn-pck-meta (car *pck-context-delta*) *pck-context-full*)
                  (fn-pck-meta (car *pck-context-delta*) *pck-context-wrong*)))))
(must-fail-checked
 (assert-event
  (equal (fn-pck-rows-from *pck-context-delta* 70 *pck-context-full*)
         (fn-pck-rows-from *pck-context-delta* 70 *pck-context-wrong*))))
