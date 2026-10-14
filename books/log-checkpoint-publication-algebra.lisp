; Request order and accepted disk effects, with columns kept as a value.
(in-package "ACL2")
(include-book "log-checkpoint-publication")
(include-book "log-checkpoint-delta")
(include-book "pagestore-keystones")
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(defthm fn-lc-len-page-write-program
 (equal (len (fn-lc-page-write-program writes)) (len writes)))
(defthm fn-lc-len-publication-program
 (equal (len (fn-lc-publication-program plan)) (+ 3 (len (nth 1 plan)))))
(defthm fn-lc-outcome-count-bounded
 (<= (fn-lc-outcome-ok-count outcome n) (nfix n)) :rule-classes :linear)
(defthm fn-lc-page-write-program-has-no-fences
 (equal (fn-lc-fence-sequence (fn-lc-page-write-program writes)) nil))
(defthm fn-lc-fences-of-append
 (equal (fn-lc-fence-sequence (append a b))
        (append (fn-lc-fence-sequence a) (fn-lc-fence-sequence b))))
(defthm fn-lc-program-complete-fences
 (equal (fn-lc-fence-sequence (fn-lc-publication-program plan))
        '(:data-fsync :root-write :root-fsync)))
(defun fn-lc-write-prefix-induction (writes n)
 (declare (xargs :measure (nfix n) :guard t :verify-guards nil))
 (if (mbe :logic (zp n) :exec (not (posp n))) writes (fn-lc-write-prefix-induction (mbe :logic (cdr writes) :exec (fn-lc-rest writes)) (1- n))))
(defthm fn-lc-fences-of-take-nil
 (equal (fn-lc-fence-sequence (take n nil)) nil)
 :hints (("Goal" :induct (take n nil))))
(defthm fn-lc-write-prefix-fences
 (fn-lc-list-prefixp
  (fn-lc-fence-sequence
   (take n (append (fn-lc-page-write-program writes)
                   (list '(:data-fsync)
                         (list :root-write slot record (fn-lc-root-slot-octets))
                         '(:root-fsync)))))
  '(:data-fsync :root-write :root-fsync))
 :hints (("Goal" :induct (fn-lc-write-prefix-induction writes n)
  :in-theory (enable fn-lc-page-write-program fn-lc-list-prefixp))))
(defthm fn-lc-program-prefix-fences
 (fn-lc-list-prefixp
  (fn-lc-fence-sequence (take (min (nfix n) (len (fn-lc-publication-program plan)))
                             (fn-lc-publication-program plan)))
  '(:data-fsync :root-write :root-fsync))
 :hints (("Goal" :use
   ((:instance fn-lc-write-prefix-fences (writes (nth 1 plan))
     (slot (nth 2 plan)) (record (nth 3 plan))
     (n (min (nfix n) (len (fn-lc-publication-program plan))))))
   :in-theory (e/d (fn-lc-publication-program)
     (fn-lc-page-write-program fn-lc-fence-sequence fn-lc-list-prefixp
      fn-lc-write-prefix-fences take)))))
(defthm fn-lc-completed-stage-value-fences
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
  (equal (fn-lc-fence-sequence
          (nth 2 (fn-lc-stage-value old old-header columns header disk r mode outcome)))
         '(:data-fsync :root-write :root-fsync)))
 :hints (("Goal" :in-theory (e/d (fn-lc-stage-value)
  (fn-lc-publication-valuep fn-lc-dirty pgs-plan-commit fn-lc-publication-program
   fn-lc-fence-sequence fn-lc-outcome-ok-count)))))
(defthm fn-lc-nth-1-alias (equal (nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable nth))))
(defthm fn-lc-nth-2-alias (equal (nth 2 x) (caddr x))
 :hints (("Goal" :in-theory (enable nth))))
(defthm fn-lc-nth-3-alias (equal (nth 3 x) (cadddr x))
 :hints (("Goal" :in-theory (enable nth))))
(defthm fn-lc-accepted-stage-value-is-commit
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
  (equal (nth 1 (fn-lc-stage-value old old-header columns header disk r mode outcome))
         (pgs-commit disk r mode (fn-lc-dirty old old-header columns header)
                     (fn-lc-publication-alloc disk))))
 :hints (("Goal" :in-theory (e/d (fn-lc-stage-value pgs-commit nth)
  (fn-lc-publication-valuep fn-lc-dirty pgs-plan-commit fn-lc-publication-program
   pgs-crash fn-lc-outcome-ok-count)))))

(defthm fn-lc-accepted-stage-value-has-publication
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
          (fn-lc-publication-valuep old old-header columns header disk r mode))
 :hints (("Goal" :in-theory (e/d (fn-lc-stage-value)
  (fn-lc-publication-valuep fn-lc-dirty pgs-plan-commit fn-lc-publication-program
   pgs-crash fn-lc-outcome-ok-count)))))
(defthm fn-lc-view-gives-contents
 (implies (equal (pgs-view opened) (list txid contents))
          (and (equal (car opened) :ok) (equal (nth 3 opened) contents)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable pgs-view))))
(defthm fn-lc-stage-value-is-the-dirty
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
  (equal (fn-lc-durable-image
          (nth 1 (fn-lc-stage-value old old-header columns header disk r mode outcome)) r mode)
         (pgs-apply-dirty (fn-lc-pages old old-header)
                         (fn-lc-dirty old old-header columns header))))
 :hints (("Goal"
  :use (fn-lc-accepted-stage-value-has-publication
   fn-lc-accepted-stage-value-is-commit
   (:instance pgs-open-after-commit
    (dirty (fn-lc-dirty old old-header columns header))
    (alloc (fn-lc-publication-alloc disk)))
   (:instance fn-lc-view-gives-contents
    (opened (pgs-open (pgs-commit disk r mode
                      (fn-lc-dirty old old-header columns header)
                      (fn-lc-publication-alloc disk)) r mode))
    (txid (pgs-next-txid (pgs-root-slots r disk)))
    (contents (pgs-apply-dirty (nth 3 (pgs-open disk r mode))
                             (fn-lc-dirty old old-header columns header)))))
  :in-theory (e/d (fn-lc-publication-valuep fn-lc-durable-image)
   (fn-lc-stage-value fn-lc-dirty fn-lc-pages fn-lc-publication-alloc
    fn-lc-accepted-stage-value-has-publication fn-lc-accepted-stage-value-is-commit
    pgs-commit pgs-open pgs-root-slots pgs-next-txid pgs-view pgs-apply-dirty
    fn-lc-column-pages fn-lc-directory-pages)))))
(defthm fn-lc-stage-value-image
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
  (equal (fn-lc-durable-image
          (nth 1 (fn-lc-stage-value old old-header columns header disk r mode outcome)) r mode)
         (fn-lc-pages columns header)))
 :hints (("Goal" :use
   (fn-lc-accepted-stage-value-has-publication fn-lc-stage-value-is-the-dirty
    (:instance fn-lc-exact-delta-nonshrinking
    (old (fn-lc-pages old old-header)) (new (fn-lc-pages columns header))))
  :in-theory (e/d (fn-lc-publication-valuep fn-lc-dirty)
   (fn-lc-stage-value fn-lc-pages fn-lc-value-dirty-from
    fn-lc-durable-image fn-lc-publication-alloc pgs-apply-dirty
    fn-lc-accepted-stage-value-has-publication fn-lc-stage-value-is-the-dirty
    fn-lc-exact-delta-nonshrinking)))))

(defthm fn-lc-root-requests-allowed-when-fenced
 (implies fenced (fn-lc-root-write-after-data-fsync-aux trace fenced)))
(defthm fn-lc-root-requests-of-take-nil
 (fn-lc-root-write-after-data-fsync-aux (take n nil) fenced)
 :hints (("Goal" :induct (take n nil))))
(defthm fn-lc-write-prefix-root-after-data
 (fn-lc-root-write-after-data-fsyncp
  (take n (append (fn-lc-page-write-program writes)
                   (list '(:data-fsync)
                         (list :root-write slot record (fn-lc-root-slot-octets))
                         '(:root-fsync)))))
 :hints (("Goal" :induct (fn-lc-write-prefix-induction writes n)
  :in-theory (enable fn-lc-root-write-after-data-fsyncp fn-lc-page-write-program))))
(defthm fn-lc-program-prefix-root-after-data
 (fn-lc-root-write-after-data-fsyncp (take n (fn-lc-publication-program plan)))
 :hints (("Goal" :use
  ((:instance fn-lc-write-prefix-root-after-data
    (writes (nth 1 plan)) (slot (nth 2 plan)) (record (nth 3 plan))))
  :in-theory (e/d (fn-lc-publication-program)
   (take fn-lc-root-write-after-data-fsyncp fn-lc-root-write-after-data-fsync-aux
    fn-lc-page-write-program fn-lc-write-prefix-root-after-data)))))
(defthm fn-lc-program-fences-of-take
 (fn-lc-list-prefixp
  (fn-lc-fence-sequence (take n (fn-lc-publication-program plan)))
  '(:data-fsync :root-write :root-fsync))
 :hints (("Goal" :use
   ((:instance fn-lc-write-prefix-fences (writes (nth 1 plan))
     (slot (nth 2 plan)) (record (nth 3 plan))))
   :in-theory (e/d (fn-lc-publication-program)
    (fn-lc-page-write-program fn-lc-fence-sequence fn-lc-list-prefixp
     fn-lc-write-prefix-fences take)))))
(defthm fn-lc-program-root-after-data
 (fn-lc-root-write-after-data-fsyncp (fn-lc-publication-program plan))
 :hints (("Goal" :use
  ((:instance fn-lc-program-prefix-root-after-data
     (n (len (fn-lc-publication-program plan)))))
  :in-theory (disable fn-lc-root-write-after-data-fsyncp
     fn-lc-root-write-after-data-fsync-aux fn-lc-publication-program
     fn-lc-program-prefix-root-after-data))))
(defthm fn-lc-stage-value-fences-prefix
 (and (fn-lc-list-prefixp
       (fn-lc-fence-sequence
        (nth 2 (fn-lc-stage-value old old-header columns header disk r mode outcome)))
       '(:data-fsync :root-write :root-fsync))
      (fn-lc-root-write-after-data-fsyncp
       (nth 2 (fn-lc-stage-value old old-header columns header disk r mode outcome))))
 :hints (("Goal" :in-theory (e/d (fn-lc-stage-value)
  (fn-lc-publication-valuep fn-lc-dirty pgs-plan-commit fn-lc-publication-program
   fn-lc-fence-sequence fn-lc-outcome-ok-count
   take fn-lc-root-write-after-data-fsyncp fn-lc-list-prefixp)))))

(defthm fn-lc-image-gives-header
 (implies (and (fn-lc-headerp header)
               (equal (fn-lc-durable-image disk r mode) (fn-lc-pages columns header)))
          (equal (fn-lc-adopted-header disk r mode) header))
 :hints (("Goal" :in-theory
  (e/d (fn-lc-adopted-header fn-lc-header-of-open fn-lc-durable-image fn-lc-pages)
       (pgs-open fn-lc-headerp fn-lc-column-pages fn-lc-directory-pages)))))

(defthm fn-lc-accepted-stage-value-headerp
 (implies (equal (car (fn-lc-stage-value old old-header columns header disk r mode outcome)) :ok)
          (fn-lc-headerp header))
 :hints (("Goal" :use fn-lc-accepted-stage-value-has-publication
  :in-theory (e/d (fn-lc-publication-valuep fn-lc-snapshotp)
   (fn-lc-stage-value fn-lc-accepted-stage-value-has-publication fn-lc-headerp
    fn-lc-pages pgs-open fn-lc-publication-alloc pgs-alloc-inv)))))
