; Exact withdrawal projection, including unlimited escape values.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-escape")
(include-book "catalog-columns-withdraw-row-bit-properties")

(defthm fn-lbc-value-withdrawal-at-of-set-by-definition
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)))
  (equal (fn-lbc-value i :withdrawal-at (fn-lbc-set-withdrawal i version by fn-lbc-v)) version))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-value fn-lbc-escape fn-lbc-escape-store-get-of-set-withdrawal-by-definition
    fn-lbc-withdrawal-escape-cell-withdrawal-at-by-definition
    fn-lbc-word-withdrawal-at-of-set-withdrawal-by-definition fn-lbc-u64)))))
(defthm fn-lbc-value-withdrawal-by-of-set-by-definition
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc-v)))
  (equal (fn-lbc-value i :withdrawal-by (fn-lbc-set-withdrawal i version by fn-lbc-v)) by))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-value fn-lbc-escape fn-lbc-escape-store-get-of-set-withdrawal-by-definition
    fn-lbc-withdrawal-escape-cell-withdrawal-by-by-definition
    fn-lbc-word-withdrawal-by-of-set-withdrawal-by-definition fn-lbc-u64)))))

(defthm fn-lbc-withdrawn-of-set-withdrawal-by-definition
 (implies (and (fn-lbc-p fn-lbc-v) (natp i) (< i (fn-lbc-count fn-lbc-v)))
  (equal (fn-lbc-withdrawn i (fn-lbc-set-withdrawal i version by fn-lbc-v)) (cons version by)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-flags-word-has-native-type (fn-lbc fn-lbc-v))
        (:instance fn-lbc-withdrawal-flags-bit-2-by-definition
         (flags (fn-lbc-word :flags i fn-lbc-v))
         (escaped (not (and (unsigned-byte-p 64 version) (unsigned-byte-p 64 by))))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-withdrawn fn-lbc-flag fn-lbc-word-flags-of-set-withdrawal-by-definition
     fn-lbc-value-withdrawal-at-of-set-by-definition fn-lbc-value-withdrawal-by-of-set-by-definition)))))
