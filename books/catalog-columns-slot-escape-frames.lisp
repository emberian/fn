; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-count-frames")

(local (defthm fn-lbse-assoc-of-put-other
 (implies (not (equal field key))
  (equal (assoc-eq field (put-assoc-eq key value cell)) (assoc-eq field cell)))
 :hints (("Goal" :induct (put-assoc-eq key value cell)
  :in-theory (union-theories (theory 'ground-zero) '(put-assoc-eq assoc-eq))))))

(local (defthm fn-lbse-assoc-of-remove-other
 (implies (not (equal field key))
  (equal (assoc-eq field (remove-assoc-eq key cell)) (assoc-eq field cell)))
 :hints (("Goal" :induct (remove-assoc-eq key cell)
  :in-theory (union-theories (theory 'ground-zero) '(remove-assoc-equal assoc-eq))))))

(defthm fn-lbc-escape-of-slot-drop-owner-other-key
 (implies (not (equal field :msgid-slot))
  (equal (fn-lbc-escape i field (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
         (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-slot-drop-owner fn-lbc-escape fn-lbc-escape-store-get-of-put
     fn-lbse-assoc-of-put-other fn-lbse-assoc-of-remove-other mv-nth)) '((tau-system))))))
