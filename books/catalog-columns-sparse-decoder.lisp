; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-store-effects")

(local (defun-nx fn-lbesp-index-induct (k fields values)
 (declare (xargs :measure (nfix k)
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nfix))))))
 (if (and (not (zp k)) (consp fields))
  (fn-lbesp-index-induct (- k 1) (cdr fields) (cdr values))
  (list fields values))))

(defthm fn-lbc-sparse-u64-absent-key
 (implies (not (member-equal key fields))
  (not (assoc-eq key (fn-lbc-sparse-u64 fields values))))
 :hints (("Goal" :induct (fn-lbc-sparse-u64 fields values)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-sparse-u64 assoc-eq member-equal)) '((:definition unsigned-byte-p) (tau-system))))))

(local (defthm fn-lbesp-nth-member
  (implies (and (natp k) (< k (len fields)))
   (member-equal (nth k fields) fields))
  :hints (("Goal" :induct (nth k fields)
   :in-theory (union-theories (theory 'ground-zero) '(nth member-equal len))))))

(defthm fn-lbc-sparse-u64-recovers-selected-value
 (implies (and (natp k) (< k (len fields)) (no-duplicatesp-equal fields))
  (equal (let ((escape (assoc-eq (nth k fields) (fn-lbc-sparse-u64 fields values))))
           (if escape (cdr escape) (fn-lbc-u64 (nth k values))))
         (nth k values)))
 :hints (("Goal" :induct (fn-lbesp-index-induct k fields values)
  :do-not '(preprocess)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbesp-index-induct fn-lbc-sparse-u64 fn-lbc-u64 fn-lbc-sparse-u64-absent-key
     no-duplicatesp-equal member-equal assoc-eq nth))
   '((:definition unsigned-byte-p) (tau-system)))) ("Subgoal *1/1" :use ((:instance fn-lbesp-nth-member (k (- k 1)) (fields (cdr fields)))))))

(defthm fn-lbc-sparse-u64-is-alist
  (alistp (fn-lbc-sparse-u64 fields values))
  :hints (("Goal" :induct (fn-lbc-sparse-u64 fields values)
   :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-sparse-u64 alistp)))))

(defthm fn-lbc-assoc-eq-of-append
 (implies (alistp a)
  (equal (assoc-eq key (append a b))
         (or (assoc-eq key a) (assoc-eq key b))))
 :hints (("Goal" :induct (len a)
  :in-theory (union-theories (theory 'ground-zero) '(assoc-eq binary-append alistp)))))

(defthm fn-lbc-assoc-eq-of-pair-cons
 (equal (assoc-eq key (cons (cons field value) rest))
        (if (equal key field) (cons field value) (assoc-eq key rest)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(assoc-eq)))))
