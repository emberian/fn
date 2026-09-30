; Literal string boundary to the report renderer's existing record primitive.
(in-package "ACL2")
(include-book "operator-report-fields")
(include-book "records-shape")

(local (include-book "arithmetic/top" :dir :system))
(local (defthm fn-orf-shift-less
  (implies (and (integerp i) (integerp n))
           (equal (< (+ -1 i) n) (< i (+ 1 n))))
  :hints (("Goal" :cases ((< i (+ 1 n)))))))
(local (defthm fn-orf-consp-nthcdr
  (implies (natp i) (equal (consp (nthcdr i xs)) (< i (len xs))))
  :hints (("Goal" :induct (nthcdr i xs)))))
(local (defthm fn-orf-nthcdr-past-end
  (implies (and (true-listp xs) (natp i) (<= (len xs) i))
           (equal (nthcdr i xs) nil))
  :hints (("Goal" :induct (nthcdr i xs)))))
(local (defthm fn-orf-car-nthcdr
  (equal (car (nthcdr i xs)) (nth i xs))
  :hints (("Goal" :induct (nthcdr i xs)))))
(local (defthm fn-orf-cdr-nthcdr-successor
  (implies (natp i) (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))
  :hints (("Goal" :induct (nthcdr i xs)))))

(defthm fn-orf-text-tail-is-record-string-tail
  (implies (and (stringp text) (natp index))
           (equal (fn-orf-text-tail text index)
                  (fn-record-string-octets-aux (nthcdr index (coerce text 'list)))))
  :hints (("Goal" :induct (fn-orf-text-tail text index)
           :in-theory (disable nth)
           :expand ((fn-record-string-octets-aux
                     (nthcdr index (coerce text 'list)))))))

(defthm fn-orf-text-reference-is-record-string-octets
  (implies (stringp text)
           (equal (fn-orf-text-tail text 0) (fn-record-string-octets text)))
  :hints (("Goal" :in-theory (disable fn-orf-text-tail))))
