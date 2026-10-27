; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-log-readback")
(include-book "lb-log-layout")

(defthm fn-lb-log-row-entry-in-is-member
 (implies (fn-lb-log-model-row-entry-in sequence handle entries)
  (member-equal (fn-lb-log-model-row-entry-in sequence handle entries) entries))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry-in member-equal)))))

(defthm fn-lb-log-row-entry-in-binds-identity
 (implies (fn-lb-log-model-row-entry-in sequence handle entries)
  (and (equal (nth 8 (fn-lb-log-model-row-entry-in sequence handle entries)) sequence)
       (equal (nth 5 (fn-lb-log-model-row-entry-in sequence handle entries)) handle)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry-in)) '(nth)))))

(local (defthm fn-lblup-row-segment-member
 (implies (fn-lb-log-model-row-entry row log)
  (member-equal (fn-lb-log-model-row-segment row log) (fn-lb-log-layout-ids log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-layout-ids member-equal))))))

(defthm fn-lb-log-row-entry-is-in-selected-segment
 (implies (and (fn-lb-log-layoutp log) (fn-lb-log-model-row-entry row log))
  (equal (fn-lb-log-model-row-entry-in (fn-record-sequence row) (fn-record-payload row)
           (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log)))
         (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-model-segment
     fn-lb-log-layoutp fn-lb-log-layout-ids fn-lblup-row-segment-member member-equal))
   '(nth true-listp)))))

(defthm fn-lb-log-selected-segment-has-layout
 (implies (and (fn-lb-log-layoutp log) (member-equal seg (fn-lb-log-layout-ids log)))
  (fn-lb-log-segment-layoutp (fn-lb-log-model-segment seg log)))
 :hints (("Goal" :induct (fn-lb-log-model-segment seg log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-segment fn-lb-log-layoutp fn-lb-log-layout-ids member-equal)))))

(local (defthm fn-lblup-home-position-lower-bound
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper)
               (member-equal e entries))
  (and (natp (nth 3 e)) (natp (nth 4 e))
       (<= lower (+ (nfix (nth 3 e)) (nfix (nth 4 e))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-entries-layoutp member-equal nfix)) '(nth true-listp))))))

(defthm fn-lb-log-home-entry-of-layout-member
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper)
               (member-equal e entries))
  (equal (fn-lb-log-model-home-entry (+ (nfix (nth 3 e)) (nfix (nth 4 e))) entries) e))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-entries-layoutp fn-lb-log-model-home-entry member-equal nfix)) '(nth true-listp)))
  ("Subgoal *1/1" :use ((:instance fn-lblup-home-position-lower-bound
    (entries (cdr entries)) (lower (+ (nth 1 (car entries)) (nth 2 (car entries)) 32)))))))

(defthm fn-lb-log-home-entry-of-row-locator
 (implies (and (fn-lb-log-layoutp log) (fn-lb-log-model-row-entry row log))
  (equal (fn-lb-log-model-home-entry (+ (nfix (nth 3 (fn-lb-log-model-row-entry row log))) (nfix (nth 4 (fn-lb-log-model-row-entry row log)))) (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))) (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lblup-row-segment-member)
        (:instance fn-lb-log-selected-segment-has-layout (seg (fn-lb-log-model-row-segment row log)))
        (:instance fn-lb-log-row-entry-is-in-selected-segment)
        (:instance fn-lb-log-row-entry-in-is-member
          (sequence (fn-record-sequence row)) (handle (fn-record-payload row)) (entries (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))))
        (:instance fn-lb-log-home-entry-of-layout-member
          (entries (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))) (e (fn-lb-log-model-row-entry row log)) (lower 0) (upper (len (cadr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-segment-layoutp)))))
