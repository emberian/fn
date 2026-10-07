(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-nntp-group-high-loop (group rev acc)
  (declare (xargs :guard (natp acc) :verify-guards nil))
  (if (consp rev)
      (fn-nntp-group-high-loop
       group (cdr rev)
       (let ((number (fn-nntp-article-number group (car rev))))
         (if (and (posp number) (< acc number)) number acc)))
    acc))

(defun fn-nntp-group-high (group articles)
  (mbe :logic
       (if (consp articles)
           (let ((number (fn-nntp-article-number group (car articles)))
                 (rest (fn-nntp-group-high group (cdr articles))))
             (if (and (posp number) (< rest number)) number rest))
         0)
       :exec (fn-nntp-group-high-loop group (fn-ag-rev-onto articles nil) 0)))

(local
 (defthm fn-nntp-group-high-loop-of-rev-onto
   (equal (fn-nntp-group-high-loop group (fn-ag-rev-onto xs zs) 0)
          (fn-nntp-group-high-loop group zs (fn-nntp-group-high group xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                   :in-theory (disable fn-nntp-article-number)))))

(verify-guards fn-nntp-group-high-loop)

(verify-guards fn-nntp-group-high
  :hints (("Goal" :in-theory (disable fn-nntp-article-number fn-ag-rev-onto)
                  :use ((:instance fn-nntp-group-high-loop-of-rev-onto (xs articles) (zs nil))))))
