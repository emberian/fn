; Guard domains survive the actual withdrawal update without revalidation.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-escape")

(local (defthm fn-lbcwdg-alist-of-remove
 (implies (alistp cell) (alistp (remove-assoc-equal key cell)))
 :hints (("Goal" :induct (remove-assoc-equal key cell)
  :in-theory (union-theories (theory 'ground-zero) '(remove-assoc-equal alistp))))))
(local (defthm fn-lbcwdg-alist-of-append
 (implies (and (alistp a) (alistp b)) (alistp (append a b)))
 :hints (("Goal" :induct (append a b)
  :in-theory (union-theories (theory 'ground-zero) '(binary-append alistp))))))
(defthm fn-lbc-withdrawal-escape-cell-is-alist
 (implies (alistp cell) (alistp (fn-lbc-withdrawal-escape-cell version by cell)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-withdrawal-escape-cell fn-lbc-sparse-u64 fn-lbcwdg-alist-of-remove
    fn-lbcwdg-alist-of-append alistp)))))

(defthm fn-lbc-escape-cellsp-of-set-withdrawal
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)) (fn-lbc-escape-cellsp start fn-lbc-v))
  (fn-lbc-escape-cellsp start (fn-lbc-set-withdrawal i version by fn-lbc-v)))
 :hints (("Goal" :induct (fn-lbc-escape-cellsp start fn-lbc-v)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-escape-cellsp fn-lbc-count-of-set-withdrawal-by-definition
     fn-lbc-escape-store-get-of-set-withdrawal-by-definition fn-lbc-withdrawal-escape-cell-is-alist)))))

(defthm fn-lbc-number-escape-cellsp-of-set-withdrawal
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)) (fn-lbc-number-escape-cellsp start fn-lbc-v))
  (fn-lbc-number-escape-cellsp start (fn-lbc-set-withdrawal i version by fn-lbc-v)))
 :hints (("Goal" :induct (fn-lbc-number-escape-cellsp start fn-lbc-v)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-number-escape-cellsp fn-lbc-count-of-set-withdrawal-by-definition
     fn-lbc-escape-store-get-of-set-withdrawal-by-definition
     fn-lbc-withdrawal-escape-cell-other-by-definition)))))

(defthm fn-lbc-stamp-escape-cellsp-of-set-withdrawal
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)) (fn-lbc-stamp-escape-cellsp start fn-lbc-v))
  (fn-lbc-stamp-escape-cellsp start (fn-lbc-set-withdrawal i version by fn-lbc-v)))
 :hints (("Goal" :induct (fn-lbc-stamp-escape-cellsp start fn-lbc-v)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-stamp-escape-cellsp fn-lbc-count-of-set-withdrawal-by-definition
     fn-lbc-escape-store-get-of-set-withdrawal-by-definition
     fn-lbc-withdrawal-escape-cell-other-by-definition)))))

(defthm fn-lbc-lc-guardp-of-set-withdrawal
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)) (fn-lbc-lc-guardp log fn-lbc-v))
  (fn-lbc-lc-guardp log (fn-lbc-set-withdrawal i version by fn-lbc-v)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-lc-guardp fn-lbc-escape-cellsp-of-set-withdrawal)))))
