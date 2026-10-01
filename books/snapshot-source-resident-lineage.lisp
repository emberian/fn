; Ghost lineage for the actual resident suffix source cursor.
; No served FnSLList/FnSFRList/member validator.
(in-package "ACL2")
(include-book "snapshot-source-cursor")
(include-book "store-records-field")

(defun-nx fn-rccos-suffix (field)
 (fn-sl-list (if (and (consp field) (eq (car field) :hrs-based))
                 (if (consp (cdr field)) (cddr field) nil) field)))
(defun-nx fn-rccos-base (field)
 (if (and (consp field) (eq (car field) :hrs-based))
     (nfix (fn-osrc-at 4 (fn-osrc-at 1 field))) 0))
(defun-nx fn-rccos-cursor-invariantp (c)
 (let* ((field (fn-osrc-at 1 c)) (suffix (fn-rccos-suffix field))
        (base (fn-rccos-base field)) (seq (fn-osrc-at 2 c))
        (phase (fn-osrc-at 0 c)))
  (and (fn-osrc-guardp c) (equal (fn-osrc-at 4 c) base)
       (equal (fn-osrc-at 3 c) (+ base (len suffix)))
       (cond
        ((eq phase :reverse)
         (and (equal seq 0)
              (equal (fn-sl-rev-take (fn-osrc-at 6 c) (fn-osrc-at 7 c) (fn-osrc-at 8 c)) suffix)))
        ((eq phase :prefix)
         (and (<= seq base) (equal (fn-osrc-at 8 c) suffix)))
        ((eq phase :waiting)
         (and (< seq base) (equal (fn-osrc-at 8 c) suffix)))
        ((eq phase :suffix)
         (and (<= base seq) (<= seq (fn-osrc-at 3 c))
              (equal (fn-osrc-at 8 c) (nthcdr (- seq base) suffix))))
        (t nil)))))

(local (defthm fn-rccos-len-of-rev-take
 (equal (len (fn-sl-rev-take n rev acc)) (+ (nfix n) (len acc)))
 :hints (("Goal" :induct (fn-sl-rev-take n rev acc)
  :in-theory (enable fn-sl-rev-take len)))))
; Actual begin must be supplied the maintained exact field count. This is
; a logical hypothesis, never a served suffix-length census.
(defthm fn-rccos-actual-begin-establishes-resident-suffix-lineage
 (implies (and (natp count)
               (equal count (+ (fn-rccos-base field) (len (fn-rccos-suffix field)))))
  (fn-rccos-cursor-invariantp (fn-osrc-begin field count epoch lease)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-rccos-cursor-invariantp fn-rccos-base fn-rccos-suffix
   fn-osrc-begin fn-osrc-at fn-osrc-guardp fn-sl-list fn-sl-snoc-formp fn-sl-rev-take))))

(local (defthm fn-rccos-cdr-of-nthcdr
 (implies (natp n) (equal (cdr (nthcdr n x)) (nthcdr (+ 1 n) x)))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local (defthm fn-rccos-zero-nthcdr
 (equal (nthcdr 0 x) x) :hints (("Goal" :in-theory (enable nthcdr)))))
(defthm fn-rccos-actual-tick-preserves-resident-suffix-lineage
 (implies (and (fn-rccos-cursor-invariantp c)
               (member-eq (car (fn-osrc-tick c observation)) '(:yield :row)))
  (fn-rccos-cursor-invariantp
   (if (eq (car (fn-osrc-tick c observation)) :row)
       (fn-osrc-at 4 (fn-osrc-tick c observation))
     (fn-osrc-at 1 (fn-osrc-tick c observation)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-rccos-cursor-invariantp fn-osrc-tick fn-osrc-with fn-osrc-at
                   fn-osrc-guardp fn-sl-rev-take)
                 (fn-rccos-base fn-rccos-suffix fn-osrc-token nthcdr)))))

(local (defthm fn-rccos-member-of-nthcdr
 (implies (and (natp n) (member-equal row (nthcdr n x)))
          (member-equal row x))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr member-equal)))))
(defthm fn-rccos-actual-resident-row-belongs-to-captured-suffix
 (implies
  (and (fn-rccos-cursor-invariantp c)
       (eq (car (fn-osrc-tick c observation)) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick c observation))) :resident))
  (member-equal (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick c observation)))
                (fn-rccos-suffix (fn-osrc-at 1 c))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccos-member-of-nthcdr
         (n (- (fn-osrc-at 2 c) (fn-osrc-at 4 c)))
         (row (car (fn-osrc-at 8 c))) (x (fn-rccos-suffix (fn-osrc-at 1 c)))))
  :in-theory (e/d (fn-rccos-cursor-invariantp fn-osrc-tick fn-osrc-at fn-osrc-guardp
                   member-equal)
                 (fn-rccos-base fn-rccos-suffix fn-osrc-token fn-osrc-with
                  fn-sl-rev-take nthcdr)))))

(local (defthm fn-rccos-canonical-based-tag-is-actual-based-field
 (implies (and (fn-sfr-canonp field) (consp field) (eq (car field) :hrs-based))
          (fn-sfr-basedp field))
 :hints (("Goal" :do-not-induct t :cases ((fn-sfr-basedp field))
  :in-theory (e/d (fn-sfr-canonp fn-sl-canonp fn-sl-of)
                 (fn-sfr-basedp fn-sl-list fn-sl-rev-take fn-hrs-disk-history))))))
(local (defthm fn-rccos-member-of-appended-suffix
 (implies (member-equal row suffix) (member-equal row (append prefix suffix)))
 :hints (("Goal" :induct (append prefix suffix)
  :in-theory (enable binary-append member-equal)))))
(defthm fn-rccos-canonical-captured-suffix-member-is-logical-record-member
 (implies (and (fn-sfr-canonp field) (member-equal row (fn-rccos-suffix field)))
          (member-equal row (fn-sfr-list field)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-canonical-based-tag-is-actual-based-field
        (:instance fn-rccos-member-of-appended-suffix
         (prefix (fn-hrs-disk-history (fn-sfr-handle field)))
         (suffix (fn-sl-list (fn-sfr-suffix field)))))
  :in-theory (e/d (fn-rccos-suffix fn-sfr-list fn-sfr-suffix fn-sfr-handle fn-sfr-basedp)
                 (fn-sl-list fn-hrs-disk-history fn-hrs-handlep fn-sfr-canonp member-equal)))))
(defthm fn-rccos-actual-resident-row-belongs-to-captured-logical-records
 (implies
  (and (fn-rccos-cursor-invariantp c) (fn-sfr-canonp (fn-osrc-at 1 c))
       (eq (car (fn-osrc-tick c observation)) :row)
       (eq (fn-osrc-at 0 (fn-osrc-at 2 (fn-osrc-tick c observation))) :resident))
  (member-equal (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick c observation)))
                (fn-sfr-list (fn-osrc-at 1 c))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-actual-resident-row-belongs-to-captured-suffix
        (:instance fn-rccos-canonical-captured-suffix-member-is-logical-record-member
         (field (fn-osrc-at 1 c))
         (row (fn-osrc-at 1 (fn-osrc-at 2 (fn-osrc-tick c observation))))))
  :in-theory (theory 'minimal-theory))))

(local (defthm fn-rccos-source-field-is-nth
 (implies (natp n) (equal (fn-osrc-at n x) (nth n x)))
 :hints (("Goal" :induct (fn-osrc-at n x) :in-theory (enable fn-osrc-at nth)))))
(local (defthm fn-rccos-fix-of-true-list
 (implies (true-listp x) (equal (true-list-fix x) x))
 :hints (("Goal" :induct (true-list-fix x) :in-theory (enable true-list-fix)))))
(local (defthm fn-rccos-canonical-based-tag-is-actual-based-field-count
 (implies (and (fn-sfr-canonp field) (consp field) (eq (car field) :hrs-based))
          (fn-sfr-basedp field))
 :hints (("Goal" :do-not-induct t :cases ((fn-sfr-basedp field))
  :in-theory (e/d (fn-sfr-canonp fn-sl-canonp fn-sl-of)
                 (fn-sfr-basedp fn-sl-list fn-sl-rev-take fn-hrs-disk-history))))))
(defthm fn-rccos-captured-count-is-the-actual-field-count
 (implies (fn-sfr-canonp field)
  (equal (fn-sfr-count field) (+ (fn-rccos-base field) (len (fn-rccos-suffix field)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-canonical-based-tag-is-actual-based-field-count)
  :in-theory (e/d (fn-sfr-count fn-rccos-base fn-rccos-suffix fn-sfr-basedp
                   fn-sfr-handle fn-sfr-suffix fn-hrs-h-n fn-hrs-handlep)
                 (fn-sl-list fn-sl-count fn-sfr-canonp fn-osrc-at nth fn-sfr-count-is-len)))))
(defthm fn-rccos-actual-field-count-begins-carried-resident-lineage
 (implies (fn-sfr-canonp field)
  (fn-rccos-cursor-invariantp (fn-osrc-begin field (fn-sfr-count field) epoch lease)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-rccos-captured-count-is-the-actual-field-count
        (:instance fn-rccos-actual-begin-establishes-resident-suffix-lineage
         (count (fn-sfr-count field))))
  :in-theory (e/d (fn-sfr-count)
                 (fn-rccos-cursor-invariantp fn-rccos-base fn-rccos-suffix
                  fn-osrc-begin fn-sl-count fn-hrs-h-n fn-sfr-basedp fn-sfr-handle
                  fn-sfr-suffix len)))))
