; Compare a query with the first keys of consecutive children of a sorted run.
(in-package "ACL2")
(include-book "range-seek-scan-proof")

(defun-nx fn2-range-indexes-children-p (index children)
  (if (atom index)
      (and (null index) (null children))
    (and (consp children) (consp (car children)) (true-listp (car children))
         (equal (caar index) (caaar children))
         (equal (cadar index) (cadr (caar children)))
         (fn2-range-indexes-children-p (cdr index) (cdr children)))))

(local
 (defthm fn2-range-partition-first-key-order
   (implies (and (equal (car index-row) (car first-row))
                 (equal (cadr index-row) (cadr first-row)))
            (equal (fn2-run-key-order-spec *fn2-overview-range-key* index-row query)
                   (fn2-run-key-order-spec *fn2-overview-range-key* first-row query)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn2-range-index-compares-first-child-key
   (implies (and (fn2-range-indexes-children-p index children) (consp index))
            (equal (fn2-run-key-order-spec *fn2-overview-range-key* (car index) query)
                   (fn2-run-key-order-spec *fn2-overview-range-key* (caar children) query)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-range-indexes-children-p index children))
            :use ((:instance fn2-range-partition-first-key-order (index-row (car index)) (first-row (caar children))))
            :in-theory (disable fn2-run-key-order-spec)))))

(defthm fn2-range-sorted-after-child
   (implies (fn2-run-sorted-spec key (append child rest)) (fn2-run-sorted-spec key rest))
   :rule-classes nil
   :hints (("Goal" :induct (len child) :expand ((fn2-run-sorted-spec key (cons (car child) (append (cdr child) rest))))
            :in-theory (disable fn2-run-key-order-spec))))

(local (defthm fn2-range-first-key-of-appended-rows
         (equal (car (append a b)) (if (consp a) (car a) (car b)))))

(local
 (defthm fn2-range-child-precedes-following-child
   (implies (and (consp child) (consp rest)
                 (fn2-run-sorted-spec *fn2-overview-range-key* (append child rest)))
            (equal (fn2-run-key-order-spec *fn2-overview-range-key* (car child) (car rest)) :lt))
   :hints (("Goal" :induct (len child) :do-not '(preprocess)
            :expand ((fn2-run-sorted-spec *fn2-overview-range-key* (append child rest)))
            :in-theory (disable nfix)))))

(local
 (defthm fn2-range-child-key-below-query
   (implies (and (consp child) (consp rest)
                 (fn2-run-sorted-spec *fn2-overview-range-key* (append child rest))
                 (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rest) query) '(:lt :eq)))
            (equal (fn2-run-key-order-spec *fn2-overview-range-key* (car child) query) :lt))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess) :use fn2-range-child-precedes-following-child
            :in-theory (disable fn2-range-child-precedes-following-child fn2-run-sorted-spec binary-append nfix)))))

(local
 (defthm fn2-range-skip-child-before-query
   (implies (and (consp rest) (fn2-run-sorted-spec *fn2-overview-range-key* (append child rest))
                 (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rest) query) '(:lt :eq)))
            (equal (fn2-run-from-spec *fn2-overview-range-key* (append child rest) query)
                   (fn2-run-from-spec *fn2-overview-range-key* rest query)))
   :hints (("Goal" :do-not '(preprocess) :induct (len child)
            :expand ((:free (a b) (fn2-run-from-spec *fn2-overview-range-key* (cons a b) query))
                     (:free (a b) (fn2-run-sorted-spec *fn2-overview-range-key* (cons a b))))
            :in-theory (disable fn2-run-key-order-spec fn2-run-sorted-spec fn2-run-from-spec))
           ("Subgoal *1/1" :use fn2-range-child-key-below-query))))

(local
 (defthm fn2-range-from-spec-with-right-siblings
   (implies (and (true-listp rest) (or (atom rest)
                (not (eq (fn2-run-key-order-spec key (car rest) query) :lt))))
            (equal (fn2-run-from-spec key (append child rest) query)
                   (append (fn2-run-from-spec key child query) rest)))
   :hints (("Goal" :induct (len child) :do-not '(preprocess)
            :expand ((:free (a b) (fn2-run-from-spec key (cons a b) query))
                     (fn2-run-from-spec key child query) (fn2-run-from-spec key rest query))
            :in-theory (e/d (binary-append) (fn2-run-key-order-spec fn2-run-from-spec
                             true-listp fn2-range-first-key-of-appended-rows))))))

(local
 (defthm fn2-range-child-at-or-after-query
   (implies (and (consp child) (not (eq (fn2-run-key-order-spec key (car child) query) :lt)))
            (equal (fn2-run-from-spec key (append child rest) query)
                   (append (fn2-run-from-spec key child query) rest)))
   :hints (("Goal" :expand ((fn2-run-from-spec key child query)
                             (:free (a b) (fn2-run-from-spec key (cons a b) query)))
            :in-theory (disable fn2-run-from-spec fn2-run-key-order-spec)))))

(local
 (defthm fn2-range-first-row-of-children
   (implies (consp (car children))
            (equal (car (append-lst children)) (caar children)))
   :hints (("Goal" :expand ((append-lst children))))))

(defthm fn2-range-partition-shape
   (implies (fn2-range-indexes-children-p index children)
            (and (iff (consp children) (consp index))
                 (implies (consp index)
                          (and (consp (car children)) (fn2-range-indexes-children-p (cdr index) (cdr children))))))
   :hints (("Goal" :expand ((fn2-range-indexes-children-p index children))
            :in-theory (disable fn2-range-indexes-children-p))))

(local
 (defthm fn2-range-nonempty-index-has-rows
   (implies (fn2-range-indexes-children-p index children)
            (iff (consp (append-lst children)) (consp index)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-range-indexes-children-p index children) (append-lst children))
            :in-theory (disable fn2-range-indexes-children-p fn2-range-partition-shape)))))

(defthmd fn2-range-select-first-or-later-child
   (let* ((key *fn2-overview-range-key*) (rest (append-lst (cdr children)))
          (later (and (consp (cdr index)) (eq (fn2-run-key-order-spec key (car index) query) :lt)
                      (member-eq (fn2-run-key-order-spec key (cadr index) query) '(:lt :eq)))))
     (implies (and (consp index) (fn2-range-indexes-children-p index children)
                   (fn2-run-sorted-spec key (append-lst children)))
              (equal (fn2-run-from-spec key (append-lst children) query)
                     (if later (fn2-run-from-spec key rest query)
                       (append (fn2-run-from-spec key (car children) query) rest)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-range-partition-shape
                  (:instance fn2-range-partition-shape (index (cdr index)) (children (cdr children)))
                  (:instance fn2-range-nonempty-index-has-rows (index (cdr index)) (children (cdr children)))
                  fn2-range-index-compares-first-child-key
                  (:instance fn2-range-index-compares-first-child-key (index (cdr index)) (children (cdr children)))
                  (:instance fn2-range-skip-child-before-query (child (car children)) (rest (append-lst (cdr children))))
                  (:instance fn2-range-child-at-or-after-query (key *fn2-overview-range-key*) (child (car children)) (rest (append-lst (cdr children))))
                  (:instance fn2-range-from-spec-with-right-siblings (key *fn2-overview-range-key*) (child (car children)) (rest (append-lst (cdr children)))))
            :expand ((append-lst children))
            :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-range-first-row-of-children (:t append-lst) eq endp not member-equal
                    (:e equal) (:e member-equal) (:e consp) (:e car) (:e cdr) (:e append-lst))))))
