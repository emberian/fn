; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-summary-value-layout")

(local (defthm fn-lbscc-hons-assoc-cons-key
 (equal (cdr (hons-assoc-equal (cons group number) table))
        (cdr (assoc-equal (cons group number) table)))
 :hints (("Goal" :induct (len table) :in-theory (union-theories (theory 'ground-zero)
 '(len hons-assoc-equal assoc-equal))))))

(defthm fn-lbc-summary-word-by-table
 (equal (fn-lbc-summary-word group field fn-lbc)
 (let ((v (cdr (assoc-equal (cons (list :summary group) field) (fn-lb-summary-table fn-lbc)))))
 (if v v (if (equal field 4) 1 0))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-word fn-lbc-number-store fn-dmap-get fn-dmap$a-get fn-lb-summary-table fn-lbscc-hons-assoc-cons-key)))))

(local (defthm fn-lbscc-member-value-nat
 (implies (and (fn-lb-summary-valuesp table) (member-equal pair table))
 (natp (cdr (assoc-equal (car pair) table))))
 :hints (("Goal" :induct (len table) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-summary-valuesp member-equal assoc-equal))))))

(defthm fn-lbc-summary-field-of-open-rebuild
 (implies (member-equal field '(1 2 3 4))
 (equal (fn-lbc-summary-word group field (fn-lbc-open-rebuild rows log fn-lbc))
 (case field (1 (fn-cat$a-group-live-count group rows)) (2 (fn-cat$a-group-live-low group rows))
 (3 (fn-cat$a-group-live-high group rows)) (4 (fn-cat$a-group-next group rows)))))
 :hints (("Goal" :do-not-induct t :cases ((equal field 1) (equal field 2) (equal field 3))
 :in-theory (union-theories (theory 'ground-zero)
 '(member-equal fn-lbc-summary-field-1-of-open-rebuild fn-lbc-summary-field-2-of-open-rebuild
 fn-lbc-summary-field-3-of-open-rebuild fn-lbc-summary-field-4-of-open-rebuild)))))

(defthm fn-lbc-summary-cell-of-open-rebuild
 (implies (and (member-equal field '(1 2 3 4))
 (natp (cdr (assoc-equal (cons (list :summary group) field)
 (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc))))))
 (equal (cdr (assoc-equal (cons (list :summary group) field)
 (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc))))
 (case field (1 (fn-cat$a-group-live-count group rows)) (2 (fn-cat$a-group-live-low group rows))
 (3 (fn-cat$a-group-live-high group rows)) (4 (fn-cat$a-group-next group rows)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-summary-field-of-open-rebuild)
 (:instance fn-lbc-summary-word-by-table (fn-lbc (fn-lbc-open-rebuild rows log fn-lbc))))
 :in-theory (theory 'ground-zero))))

(local (defthm fn-lbscc-two-list-shape
 (implies (and (true-listp tag) (equal (len tag) 2))
 (equal tag (list (car tag) (cadr tag))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(true-listp len))))))

(local (defthm fn-lbscc-summary-key-shape
 (implies (and (true-listp (car key)) (equal (len (car key)) 2) (equal (caar key) :summary))
 (equal key (cons (list :summary (cadar key)) (cdr key))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbscc-two-list-shape (tag (car key))))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbscc-arbitrary-summary-cell
 (implies (and (true-listp (car key)) (equal (len (car key)) 2) (equal (caar key) :summary)
 (member-equal (cdr key) '(1 2 3 4))
 (natp (cdr (assoc-equal key (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc))))))
 (equal (cdr (assoc-equal key (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc))))
 (case (cdr key) (1 (fn-cat$a-group-live-count (cadar key) rows))
 (2 (fn-cat$a-group-live-low (cadar key) rows)) (3 (fn-cat$a-group-live-high (cadar key) rows))
 (4 (fn-cat$a-group-next (cadar key) rows)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbscc-summary-key-shape)
 (:instance fn-lbc-summary-cell-of-open-rebuild (group (cadar key)) (field (cdr key))))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lbc-summary-cells-corr-for-open-rebuild
 (implies (subsetp-equal keys (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc)))
 (fn-lbc-summary-cells-corr keys (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc)) rows))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbc-summary-cells-corr fn-lbscc-member-value-nat
 fn-lb-summary-valuesp-of-open-rebuild fn-lbscc-arbitrary-summary-cell)))))

(local (defthm fn-lbscc-member-cons
 (iff (member-equal query (cons key rest)) (or (equal query key) (member-equal query rest)))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbscc-subset-cons
 (implies (subsetp-equal xs ys) (subsetp-equal xs (cons item ys)))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbscc-member-cons))))))

(local (defthm fn-lbscc-member-head
 (implies (consp xs) (member-equal (car xs) xs))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbscc-subset-self
 (subsetp-equal xs xs)
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbscc-subset-cons fn-lbscc-member-head))))))

(defthm fn-lbc-summary-cells-corr-of-open-rebuild
 (fn-lbc-summary-cells-corr (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc))
 (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc)) rows)
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-summary-cells-corr-for-open-rebuild
 (keys (fn-lb-summary-table (fn-lbc-open-rebuild rows log fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbscc-subset-self)))))
