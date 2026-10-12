(in-package "ACL2")
(include-book "../../books/newnews-stream-cost")
(include-book "served-plan-newnews-tests")

; The factory's configured cursor of the served-plan witness: two candidates,
; eleven configured groups. It finishes within the stated count at one octet
; per call and at a wide quantum (the keystone's instances, by evaluation),
; and teeth: it is NOT finished after one call nor after 200, and it finishes
; at 300, well inside the pessimistic bound.
(defthm nnsc-witness-finishes-within-the-linear-count
  (let* ((progress (fn-cur-progress (cadr (car (cdr (spn-result))))))
         (sum1 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress)
                                           (fn-nnw-tail progress) 1))
         (sum256 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress)
                                             (fn-nnw-tail progress) 256)))
    (and (fn-nnw-configured-cursorp progress)
         (equal (len (fn-nnw-tail progress)) 2)
         (equal sum1 3686)
         (equal sum256 3672)
         (null (fn-nnw-stream-run progress 1 (+ 2 sum1) nil nil))
         (null (fn-nnw-stream-run progress 256 (+ 2 sum256) nil nil))
         (null (fn-nnw-stream-run progress 1 300 nil nil))
         (null (fn-nnw-stream-run progress 256 300 nil nil)))))

(defthm nnsc-witness-teeth-not-finished-early
  (let ((progress (fn-cur-progress (cadr (car (cdr (spn-result)))))))
    (and (fn-nnw-stream-run progress 1 1 nil nil)
         (fn-nnw-stream-run progress 1 200 nil nil)
         (fn-nnw-stream-run progress 256 1 nil nil)
         (fn-nnw-stream-run progress 256 60 nil nil))))

; The uniform bound at the witness: each candidate is under its closed form.
(defthm nnsc-witness-candidate-under-uniform-bound
  (let ((a (car (fn-nnw-tail (fn-cur-progress (cadr (car (cdr (spn-result)))))))))
    (<= (fn-nnw-candidate-calls *spn-configured-groups*
                                (fn-wildmat-result-value
                                 (fn-wildmat-parse (fn-nntp-string-octets "fn.test")))
                                a 1)
        (+ 5 (length (fn-article-msgid a))
           (* (len *spn-configured-groups*)
              (+ 3 (len (fn-article-memberships a))
                 (fn-nnw-match-bound
                  (fn-wildmat-result-value
                   (fn-wildmat-parse (fn-nntp-string-octets "fn.test")))))))))
  :rule-classes nil)
