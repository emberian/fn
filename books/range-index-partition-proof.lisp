; An index entry holds its child's first key. Seeking in the selected
; child and then visiting its right siblings gives the whole run suffix.
(in-package "ACL2")
(include-book "range-index-child-choice-proof")
(include-book "range-child-row-order-proof")

(defmacro fn2-range-index-child-at (rows query)
  `(fn2-range-index-child-number (fn2-run-lower-bound-spec *fn2-overview-range-key* ,rows ,query 0)))

(local
 (defthm fn2-run-lower-bound-shifts-with-start
   (let ((a (fn2-run-lower-bound-spec key rows query i))
         (b (fn2-run-lower-bound-spec key rows query (1+ i))))
     (implies (natp i)
              (and (equal (car b) (car a)) (equal (cadr b) (1+ (cadr a))))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query i)
            :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthmd fn2-range-index-child-recursion
   (equal (fn2-range-index-child-at rows query)
          (if (and (consp (cdr rows))
                   (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rows) query) :lt)
                   (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* (cadr rows) query) '(:lt :eq)))
              (1+ (fn2-range-index-child-at (cdr rows) query)) 0))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-run-lower-bound-shifts-with-start (key *fn2-overview-range-key*) (rows (cdr rows)) (i 0))
                  (:instance fn2-range-lower-bound-result-limits (key *fn2-overview-range-key*) (rows (cddr rows)) (idx 1)))
            :expand ((fn2-run-lower-bound-spec *fn2-overview-range-key* rows query 0)
                     (fn2-run-lower-bound-spec *fn2-overview-range-key* (cdr rows) query 0))
            :in-theory (e/d (fn2-range-index-child-number)
                            (fn2-run-lower-bound-spec fn2-run-key-order-spec len))))))

(local
 (defthm fn2-range-index-child-is-natural
   (natp (fn2-range-index-child-number lower))
   :rule-classes :type-prescription))

(local
 (defun-nx fn2-range-walk-index-children (index children)
   (if (atom index) children (fn2-range-walk-index-children (cdr index) (cdr children)))))

(local
 (defthm fn2-range-siblings-at-child-offset
   (implies (and (natp k) (equal i (if later (1+ k) 0)))
            (equal (nthcdr i children) (if later (nthcdr k (cdr children)) children)))
   :rule-classes nil :hints (("Goal" :cases (later) :expand ((nthcdr (1+ k) children))))))

(local
 (defthmd fn2-range-selected-child-siblings
   (equal (nthcdr (fn2-range-index-child-at index query) children)
          (if (and (consp (cdr index))
                   (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car index) query) :lt)
                   (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* (cadr index) query) '(:lt :eq)))
              (nthcdr (fn2-range-index-child-at (cdr index) query) (cdr children))
            children))
   :hints (("Goal" :use ((:instance fn2-range-index-child-recursion (rows index))
                  (:instance fn2-range-siblings-at-child-offset (i (fn2-range-index-child-at index query))
                     (k (fn2-range-index-child-at (cdr index) query))
                     (later (and (consp (cdr index))
                       (eq (fn2-run-key-order-spec *fn2-overview-range-key* (car index) query) :lt)
                       (member-eq (fn2-run-key-order-spec *fn2-overview-range-key* (cadr index) query) '(:lt :eq))))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-index-child-is-natural natp (:e equal) not))))))

(defthm fn2-range-index-partitions-run-suffix
  (let* ((key *fn2-overview-range-key*) (k (fn2-range-index-child-at index query))
         (remaining (nthcdr k children)))
    (implies (and (consp index) (fn2-range-indexes-children-p index children)
                  (fn2-run-sorted-spec key (append-lst children)))
             (equal (fn2-run-from-spec key (append-lst children) query)
                    (append (fn2-run-from-spec key (car remaining) query) (append-lst (cdr remaining))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-range-walk-index-children index children) :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                        '((:induction fn2-range-walk-index-children) eq atom not endp (:e equal))))
          ("Subgoal *1/2" :use
           (fn2-range-select-first-or-later-child fn2-range-partition-shape
            fn2-range-selected-child-siblings
            (:instance fn2-range-sorted-after-child (key *fn2-overview-range-key*) (child (car children)) (rest (append-lst (cdr children)))))
           :expand ((append-lst children) (:free (k) (nthcdr (+ 1 k) children)) (nthcdr 0 children)))))

(defthm fn2-range-stored-index-preserves-run-suffix
  (let* ((n (fn2-run-page-restart-count rb f)) (query (fn2-overview-range-key-at qbase f))
         (step (fn2-run-step-seek c 3 nil level fuel 0 n 0 0 qbase slot gen unit counter
                                  rb pk ps pg qk qs qg curs f pool))
         (after (mv-nth 1 step))
         (remaining (nthcdr (fn2-run-cursors-idx c after) children)))
    (implies (and (fn2-range-indexes-children-p rows children)
                  (fn2-run-sorted-spec *fn2-overview-range-key* (append-lst children))
                  (natp c) (< c (fn2-run-cursors-rows curs)) (posp level) (unsigned-byte-p 8 level)
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (consp rows) (unsigned-byte-p 32 (len rows)) (fn2-run-sorted-spec *fn2-overview-range-key* rows)
                  (natp fuel) (< (+ (integer-length n) *fn2-run-restart-interval* 1) fuel)
                  (natp rb) (natp qbase) (< (1+ qbase) (+ rb *fn2-run-reader-restart*))
                  (fn2-fieldsp f) (fn2-run-readerp rb f)
                  (fn2-run-stored-overview-page-p rows level rb slot gen pk ps pg f pool))
             (and (equal (car step) :more)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-child*)
                  (equal (fn2-run-from-spec *fn2-overview-range-key* (append-lst children) query)
                         (append (fn2-run-from-spec *fn2-overview-range-key* (car remaining) query)
                                 (append-lst (cdr remaining)))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-stored-index-selects-lower-bound-child
                 (:instance fn2-range-index-partitions-run-suffix (index rows) (query (fn2-overview-range-key-at qbase f))))
           :in-theory (theory 'minimal-theory))))
