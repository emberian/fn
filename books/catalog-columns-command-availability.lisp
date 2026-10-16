; The command predicate observes decided/tomb columns without a full NOV fetch.
(in-package "ACL2")
(include-book "catalog-columns-command-reads")
(include-book "catalog-columns-constructor-helper-types")

(local (defthm fn-lbcc-nov-boolean-fields
 (implies (fn-lbc-p fn-lbc)
  (and (booleanp (fn-lbc-nov-field :tomb i fn-lbc))
       (booleanp (fn-lbc-nov-field :ok i fn-lbc))))
 :hints (("Goal"
 :use ((:instance fn-lbc-nov-store-has-native-type) (:instance adt-tp-rec-p-nth (s *fn-lbc-nov-schema*) (a (fn-lbc-nov-store fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-nov-field fn-lbc-nov-store-has-native-type fn-lbc-novp fn-lbc-nov$ap
   fn-lbc-nov-count fn-lbc-nov$a-count fn-lbc-nov-get-tomb-is-nth
   fn-lbc-nov-get-ok-is-nth adt-rec-p adt-val-okp nth natp nfix booleanp))))))

(local (defthm fn-lbcc-nov-at-is-decided
 (implies (fn-lbc-p fn-lbc) (fn-hnov-p (fn-lbc-nov-at i fn-lbc)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'ground-zero)
   (union-theories (theory 'fn-hnov-internals)
    '(fn-hnov-p fn-hnov-flagp fn-lbc-nov-at fn-lbc-nov-text
      fn-lbcc-nov-boolean-fields fn-record-octets-string)))))))

(local (defthm fn-lbcc-nov-at-tomb-column
 (equal (fn-hnov-tomb (fn-lbc-nov-at i fn-lbc)) (fn-lbc-nov-field :tomb i fn-lbc))
 :hints (("Goal" :in-theory '(fn-lbc-nov-at fn-hnov-tomb-of-fn-hnov-make)))))

(defthm fn-lbcc-original-nov-availability-columns
 (implies (fn-lbc-p fn-lbc)
  (equal
   (and (fn-hnov-p (fn-lbc-original-nov i fn-lbc))
        (not (fn-hnov-tomb (fn-lbc-original-nov i fn-lbc))))
   (let ((e (fn-lbc-escape i :nov fn-lbc)))
    (if e (and (fn-hnov-p (fn-ag-cdr e)) (not (fn-hnov-tomb (fn-ag-cdr e))))
     (and (not (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0))
          (not (fn-lbc-nov-field :tomb (fn-lbc-directory-value i :nov-start fn-lbc) fn-lbc)))))))

 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-original-nov fn-lbcc-nov-at-is-decided fn-lbcc-nov-at-tomb-column
   fn-ag-cdr (:executable-counterpart fn-hnov-p) (:executable-counterpart fn-hnov-tomb))))))

(defthm fn-lbc-command-row-observes-original-nov
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-command-row group number v fn-lbc)
   (let ((i (fn-lbc-number-get group number fn-lbc)))
    (and (posp number) (<= number *fn-nntp-max-article-number*)
         (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-visiblep i v fn-lbc)
         (and (fn-hnov-p (fn-lbc-original-nov i fn-lbc))
              (not (fn-hnov-tomb (fn-lbc-original-nov i fn-lbc))))
         (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc)) i))))
 :hints (("Goal"
  :use ((:instance fn-lbcc-original-nov-availability-columns
         (i (fn-lbc-number-get group number fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-command-row)))))
