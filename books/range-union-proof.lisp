; Order and field types of the overview union used by reads and seeks.
(in-package "ACL2")
(include-book "range-seek-probe-proof")
(include-book "runs-layout-id-proof")

(local
 (defthm fn2-overview-order-reverse
   (implies (and (not (eq (fn2-run-key-order-spec *fn2-overview-range-key* a b) :lt))
                 (not (eq (fn2-run-key-order-spec *fn2-overview-range-key* a b) :eq)))
            (eq (fn2-run-key-order-spec *fn2-overview-range-key* b a) :lt))
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn2-overview-order-substitute
   (implies (eq (fn2-run-key-order-spec *fn2-overview-range-key* a b) :eq)
            (equal (fn2-run-key-order-spec *fn2-overview-range-key* b c)
                   (fn2-run-key-order-spec *fn2-overview-range-key* a c)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn2-overview-put-sorted
   (implies (fn2-run-sorted-spec *fn2-overview-range-key* acc)
            (fn2-run-sorted-spec *fn2-overview-range-key*
                                 (fn2-range-put-spec *fn2-overview-range-key* e acc)))
   :hints (("Goal" :induct (fn2-range-put-spec *fn2-overview-range-key* e acc)
            :in-theory (disable fn2-run-key-order-spec))
           ("Subgoal *1/3" :use ((:instance fn2-overview-order-substitute
                                  (a (car acc)) (b e) (c (cadr acc))))))))
(local
 (defthm fn2-overview-puts-sorted
   (implies (fn2-run-sorted-spec *fn2-overview-range-key* acc)
            (fn2-run-sorted-spec *fn2-overview-range-key*
                                 (fn2-range-puts-spec *fn2-overview-range-key* es acc)))
   :hints (("Goal" :induct (fn2-range-puts-spec *fn2-overview-range-key* es acc)
            :in-theory (disable fn2-range-put-spec fn2-run-sorted-spec)))))

(defthm fn2-overview-union-sorted
 (implies (fn2-run-sorted-spec *fn2-overview-range-key* acc)
          (fn2-run-sorted-spec *fn2-overview-range-key*
                               (fn2-range-union-spec *fn2-overview-range-key* sources acc)))
 :hints (("Goal" :induct (fn2-range-union-spec *fn2-overview-range-key* sources acc)
          :in-theory (disable fn2-range-puts-spec fn2-run-sorted-spec))))

(local
 (defthm fn2-range-entry-id-keys
   (implies (and (fn2-run-values-layoutp layout row)
                 (equal (cadar layout) '(:id group))
                 (equal (cadr (cadr layout)) '(:id group-number)))
            (and (natp (car row)) (natp (cadr row))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-layout-id-natural (i 0) (id 'group) (values row))
                         (:instance fn2-run-layout-id-natural (i 1) (id 'group-number) (values row)))
            :in-theory (disable fn2-run-values-layoutp)))))

(local
 (defthm fn2-range-put-natural-keys
   (implies (and (natp (car e)) (natp (cadr e)) (fn2-range-natural-keysp acc))
            (fn2-range-natural-keysp (fn2-range-put-spec key e acc)))
   :hints (("Goal" :induct (fn2-range-put-spec key e acc)
            :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthm fn2-range-puts-natural-keys
   (implies (and (fn2-run-entries-layoutp layout es)
                 (equal (cadar layout) '(:id group))
                 (equal (cadr (cadr layout)) '(:id group-number))
                 (fn2-range-natural-keysp acc))
            (fn2-range-natural-keysp (fn2-range-puts-spec key es acc)))
   :hints (("Goal" :induct (fn2-range-puts-spec key es acc)
            :in-theory (disable fn2-range-put-spec fn2-run-values-layoutp fn2-range-natural-keysp))
           ("Subgoal *1/2" :use ((:instance fn2-range-entry-id-keys (row (car es))))))))

(defthm fn2-overview-union-natural-keys
 (implies (and (fn2-range-listsp layout key sources)
               (equal (cadar layout) '(:id group))
               (equal (cadr (cadr layout)) '(:id group-number))
               (fn2-range-natural-keysp acc))
          (fn2-range-natural-keysp (fn2-range-union-spec key sources acc)))
 :hints (("Goal" :induct (fn2-range-union-spec key sources acc)
          :in-theory (disable fn2-range-puts-spec fn2-run-entries-layoutp
                              fn2-run-sorted-spec fn2-range-natural-keysp))))
