; Actual source selection order and prepared-suffix restart lineage.
; All additional relations are ghost-only, never served graph validators.
(in-package "ACL2")
(include-book "snapshot-source-resident-lineage")
(local (defthm fn-rcco-car-nthcdr-is-nth
 (implies (natp n) (equal (car (nthcdr n x)) (nth n x)))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr nth)))))
(defthm fn-rcco-actual-resident-row-is-the-captured-suffix-ordinal
 (implies
  (and (fn-rccos-cursor-invariantp c)
       (eq (car (fn-osrc-tick c observation)) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick c observation))) :resident))
  (and (equal (fn-osrc-at 1 (fn-osrc-tick c observation)) (fn-osrc-at 2 c))
       (equal (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick c observation)))
              (nth (- (fn-osrc-at 2 c) (fn-osrc-at 4 c))
                   (fn-rccos-suffix (fn-osrc-at 1 c))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-rccos-cursor-invariantp fn-osrc-tick fn-osrc-at fn-osrc-guardp)
                 (fn-rccos-base fn-rccos-suffix fn-osrc-token fn-osrc-with
                  fn-sl-rev-take nthcdr nth)))))
(defun-nx fn-rcco-prepared-invariantp (c)
 (and (fn-rccos-cursor-invariantp c)
      (or (eq (fn-osrc-at 0 c) :reverse)
          (equal (fn-osrc-at 11 c) (fn-rccos-suffix (fn-osrc-at 1 c))))))
(defthm fn-rcco-actual-begin-retains-the-prepared-source
 (implies (and (natp count)
               (equal count (+ (fn-rccos-base field) (len (fn-rccos-suffix field)))))
  (fn-rcco-prepared-invariantp (fn-osrc-begin field count epoch lease)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-actual-begin-establishes-resident-suffix-lineage)
  :in-theory (e/d (fn-rcco-prepared-invariantp fn-osrc-begin fn-osrc-at
                   fn-rccos-suffix fn-sl-list)
                 (fn-rccos-cursor-invariantp fn-rccos-base fn-sl-rev-take)))))
(defthm fn-rcco-actual-tick-preserves-the-prepared-source
 (implies (and (fn-rcco-prepared-invariantp c)
               (member-eq (car (fn-osrc-tick c observation)) '(:yield :row)))
  (fn-rcco-prepared-invariantp
   (if (eq (car (fn-osrc-tick c observation)) :row)
       (fn-osrc-at 4 (fn-osrc-tick c observation))
     (fn-osrc-at 1 (fn-osrc-tick c observation)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-actual-tick-preserves-resident-suffix-lineage)
  :in-theory (e/d (fn-rcco-prepared-invariantp fn-rccos-cursor-invariantp
                   fn-osrc-tick fn-osrc-with fn-osrc-at fn-osrc-guardp fn-sl-rev-take)
                 (fn-rccos-base fn-rccos-suffix fn-osrc-token nthcdr)))))
(defthm fn-rcco-actual-restart-retains-source-order-and-capture
 (implies (and (fn-rcco-prepared-invariantp c)
               (eq (car (fn-osrc-restart c)) :restarted))
  (let ((next (fn-osrc-at 1 (fn-osrc-restart c))))
   (and (fn-rcco-prepared-invariantp next)
        (equal (fn-osrc-at 1 next) (fn-osrc-at 1 c))
        (equal (fn-osrc-at 2 next) 0)
        (equal (fn-osrc-at 9 next) (fn-osrc-at 9 c))
        (equal (fn-osrc-at 10 next) (fn-osrc-at 10 c))
        (equal (fn-osrc-at 12 next) (+ 1 (fn-osrc-at 12 c))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-rcco-prepared-invariantp fn-rccos-cursor-invariantp
                   fn-osrc-restart fn-osrc-with fn-osrc-at fn-osrc-guardp)
                 (fn-rccos-base fn-rccos-suffix nthcdr)))))

(local (defthm fn-rcco-source-field-is-nth
 (implies (natp n) (equal (fn-osrc-at n x) (nth n x)))
 :hints (("Goal" :induct (fn-osrc-at n x) :in-theory (enable fn-osrc-at nth)))))
(local (defthm fn-rcco-nth-of-true-list-fix
 (implies (natp n) (equal (nth n (true-list-fix x)) (nth n x)))
 :hints (("Goal" :induct (nth n x) :in-theory (enable nth true-list-fix)))))
(local (defthm fn-rcco-canonical-based-tag-is-actual-based-field
 (implies (and (fn-sfr-canonp field) (consp field) (eq (car field) :hrs-based))
          (fn-sfr-basedp field))
 :hints (("Goal" :do-not-induct t :cases ((fn-sfr-basedp field))
  :in-theory (e/d (fn-sfr-canonp fn-sl-canonp fn-sl-of)
                 (fn-sfr-basedp fn-sl-list fn-sl-rev-take fn-hrs-disk-history))))))
(local (defthm fn-rcco-nth-one-is-cadr
 (equal (nth 1 x) (cadr x)) :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-rcco-resident-row-requires-suffix-phase
 (implies (and (eq (car (fn-osrc-tick c observation)) :row)
               (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick c observation))) :resident))
          (eq (fn-osrc-at 0 c) :suffix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-osrc-tick fn-osrc-at)
                 (fn-osrc-with fn-osrc-token fn-sl-rev-take))))))
(defthm fn-rcco-actual-resident-row-is-the-captured-logical-record-ordinal
 (implies
  (and (fn-rccos-cursor-invariantp c) (fn-sfr-canonp (fn-osrc-at 1 c))
       (eq (car (fn-osrc-tick c observation)) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick c observation))) :resident))
  (and (equal (fn-osrc-at 1 (fn-osrc-tick c observation)) (fn-osrc-at 2 c))
       (equal (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick c observation)))
              (nth (fn-osrc-at 2 c) (fn-sfr-list (fn-osrc-at 1 c))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rcco-actual-resident-row-is-the-captured-suffix-ordinal
        fn-rcco-resident-row-requires-suffix-phase
        (:instance fn-rcco-canonical-based-tag-is-actual-based-field
         (field (fn-osrc-at 1 c)))
        (:instance fn-sfr-nth-is-nth (i (fn-osrc-at 2 c)) (f (fn-osrc-at 1 c))))
  :in-theory (e/d (fn-rccos-cursor-invariantp fn-osrc-guardp fn-rccos-base
                   fn-rccos-suffix fn-sfr-nth fn-sfr-handle fn-sfr-suffix
                   fn-sfr-basedp fn-hrs-h-n)
                 (fn-osrc-tick fn-osrc-at fn-sfr-canonp fn-sfr-list
                  fn-sl-list fn-sl-nth nth fn-hrs-handlep fn-hrs-disk-history)))))
