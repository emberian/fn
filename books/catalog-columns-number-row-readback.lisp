; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-table-frames")

(local (defthm fn-lbnrr-member-cons
 (iff (member-equal query (cons key rest)) (or (equal query key) (member-equal query rest)))
 :hints (("Goal" :in-theory (enable member-equal)))))

(defthm fn-lbc-number-get-of-number-put-row-seen
 (implies (fn-held-numbersp numbers)
 (equal (fn-lbc-number-get read-group read-number (fn-lbc-number-put-row-seen numbers seen i fn-lbc))
  (let ((old (fn-lbc-number-get read-group read-number fn-lbc))
        (pair (fn-cat-assoc read-group numbers)))
   (if (or (natp old) (member-equal read-group seen)) old
     (if (and (consp pair) (equal read-number (cdr pair))) i old)))))
 :hints (("Goal" :induct (fn-lbc-number-put-row-seen numbers seen i fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-put-row-seen fn-lbc-number-get-of-number-put-first fn-held-numbersp
 fn-cat-assoc fn-lbnrr-member-cons)))))
