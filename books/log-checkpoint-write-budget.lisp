; Charge actual requested PGS writes, including failed requests and the directory run.
(in-package "ACL2")
(include-book "log-checkpoint-publication-algebra")
(include-book "log-checkpoint-budget")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-lc-write-octets-of-append
 (equal (fn-lc-write-octets (append x y))
        (+ (fn-lc-write-octets x) (fn-lc-write-octets y))))
(defthm fn-lc-write-octets-nonnegative
 (<= 0 (fn-lc-write-octets trace)) :rule-classes :linear)
(defthm fn-lc-write-octets-of-take
 (implies (natp n)
          (<= (fn-lc-write-octets (take n trace)) (fn-lc-write-octets trace)))
 :rule-classes nil
 :hints (("Goal" :induct (take n trace)
  :in-theory (enable take fn-lc-write-octets))))
(defthm fn-lc-page-program-with-directory-cost
 (equal (fn-lc-write-octets
         (fn-lc-page-write-program (append writes (list (cons addr directory)))))
        (* (+ (len writes) (pgs-ptab-run-pages (len directory))) (fn-lc-page-octets)))
 :hints (("Goal" :induct (len writes)
  :in-theory (e/d (fn-lc-page-write-program fn-lc-write-octets)
                 (pgs-ptab-run-pages)))))
(defthm fn-lc-program-cost-by-definition
 (equal (fn-lc-write-octets (fn-lc-publication-program plan))
        (+ (fn-lc-write-octets (fn-lc-page-write-program (nth 1 plan)))
           (fn-lc-root-slot-octets)))
 :hints (("Goal" :in-theory (e/d (fn-lc-publication-program fn-lc-write-octets)
                  (fn-lc-page-write-program)))))
(defthm fn-lc-pgs-page-writes-length
 (equal (len (pgs-page-writes dirty fresh)) (len dirty))
 :hints (("Goal" :induct (pgs-page-writes dirty fresh)
  :in-theory (enable pgs-page-writes))))
(defthm fn-lc-grown-delta-has-new-extent
 (implies (<= (len (fn-lc-pages old old-header)) (len (fn-lc-pages new header)))
  (equal (pgs-grown-len (pgs-dirty-lpages (fn-lc-dirty old old-header new header))
                        (len (fn-lc-pages old old-header)))
         (len (fn-lc-pages new header))))
 :hints (("Goal" :use
  ((:instance fn-lc-exact-delta-nonshrinking
    (old (fn-lc-pages old old-header)) (new (fn-lc-pages new header)))
   (:instance pgs-len-of-apply-dirty
    (c (fn-lc-pages old old-header)) (d (fn-lc-dirty old old-header new header))))
  :in-theory (e/d (fn-lc-dirty)
   (fn-lc-value-dirty-from fn-lc-pages pgs-apply-dirty pgs-grown-len
    pgs-dirty-lpages fn-lc-exact-delta-nonshrinking pgs-len-of-apply-dirty)))))

(defthm fn-lc-pgs-step-program-cost
 (equal (fn-lc-write-octets
         (fn-lc-page-write-program (pgs-step-writes dirty fresh tdirty tfresh rs dir2)))
        (* (+ (len dirty) (len tdirty) (pgs-ptab-run-pages (len dir2)))
           (fn-lc-page-octets)))
  :hints (("Goal" :use
  ((:instance fn-lc-page-program-with-directory-cost
    (writes (append (pgs-page-writes dirty fresh) (pgs-page-writes tdirty tfresh)))
    (addr rs) (directory dir2)))
  :in-theory (e/d (pgs-step-writes)
   (fn-lc-page-write-program fn-lc-write-octets pgs-page-writes pgs-ptab-run-pages
    fn-lc-page-program-with-directory-cost)))))
(defthm fn-lc-pgs-step-program-physical-cost
 (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
  (equal (fn-lc-write-octets
          (fn-lc-page-write-program (pgs-swr cur pages dirty fresh tfresh rs txid)))
         (* (+ (len dirty)
               (len (pgs-touched (pgs-dirty-lpages dirty) nil))
               (pgs-dir-run-pages
                (pgs-grown-len (pgs-dirty-lpages dirty) (len (pgs-sp cur pages)))))
            (fn-lc-page-octets))))
 :hints (("Goal" :use
  (pgs-s-dir2-len pgs-sp2-is-plan
   (:instance pgs-len-of-plan-ptab (ptab (pgs-sp cur pages))
    (lpages (pgs-dirty-lpages dirty)) (digests (pgs-dirty-digests dirty)))
   pgs-len-of-std)
  :in-theory (e/d (pgs-swr pgs-step-tl pgs-dir-run-pages)
   (pgs-sp2 pgs-sd2 pgs-sp pgs-std pgs-step-writes pgs-touched pgs-dirty-lpages
    pgs-plan-ptab pgs-len-of-plan-ptab pgs-len-of-std
    fn-lc-page-write-program fn-lc-write-octets pgs-grown-len pgs-ptab-run-pages)))))

(defthm fn-lc-open-table-length
 (implies (equal (car (pgs-open disk r mode)) :ok)
  (equal (len (pgs-sp (pgs-c-cur disk r mode) (pgs-pages disk)))
         (len (nth 3 (pgs-open disk r mode)))))
 :hints (("Goal" :use
  (pgs-c-view-facts
   (:instance pgs-len-of-contents
    (ptab (pgs-sp (pgs-c-cur disk r mode) (pgs-pages disk))) (pages (pgs-pages disk))))
  :in-theory (disable pgs-open pgs-sp pgs-c-cur pgs-pages pgs-contents
                      pgs-c-view-facts pgs-len-of-contents))))
(defthm fn-lc-valid-plan-program-cost
 (implies (and (equal (car (pgs-open disk r mode)) :ok)
               (pgs-c-lpages-ok disk r mode dirty) (pgs-alloc-inv alloc disk))
  (equal (fn-lc-write-octets
          (fn-lc-publication-program (pgs-plan-commit disk r mode dirty alloc)))
         (+ (* (+ (len dirty)
                   (len (pgs-touched (pgs-dirty-lpages dirty) nil))
                   (pgs-dir-run-pages
                    (pgs-grown-len (pgs-dirty-lpages dirty)
                     (len (nth 3 (pgs-open disk r mode)))))) (fn-lc-page-octets))
            (fn-lc-root-slot-octets))))
 :hints (("Goal" :use
  (pgs-c-open-facts pgs-c-step-hyps pgs-plan-commit-unfold
   (:instance fn-lc-pgs-step-program-physical-cost
    (cur (pgs-c-cur disk r mode)) (pages (pgs-pages disk))
    (fresh (pgs-c-fresh disk r mode dirty alloc))
    (tfresh (pgs-c-tfresh disk r mode dirty alloc))
    (rs (pgs-c-rs disk r mode dirty alloc)) (txid (pgs-c-txid disk r))))
  :in-theory (e/d (pgs-c-writes)
   (pgs-open pgs-c-cur pgs-pages pgs-c-fresh pgs-c-tfresh pgs-c-rs pgs-c-txid
    pgs-swr pgs-sp pgs-plan-commit pgs-c-open-facts pgs-c-step-hyps
    pgs-plan-commit-unfold fn-lc-pgs-step-program-physical-cost
    fn-lc-write-octets fn-lc-publication-program fn-lc-page-write-program
    pgs-grown-len pgs-dirty-lpages pgs-touched pgs-dir-run-pages)))))
(defthm fn-lc-publication-value-has-valid-plan
 (implies (fn-lc-publication-valuep old old-header columns header disk r mode)
  (and (equal (car (pgs-open disk r mode)) :ok)
       (pgs-c-lpages-ok disk r mode (fn-lc-dirty old old-header columns header))
       (pgs-alloc-inv (fn-lc-publication-alloc disk) disk)))
 :hints (("Goal" :use
  ((:instance pgs-c-lpages-ok-is (dirty (fn-lc-dirty old old-header columns header)))
   (:instance fn-lc-dirty-lpages-ok (new columns)))
  :in-theory (e/d (fn-lc-publication-valuep)
    (pgs-open pgs-c-lpages-ok pgs-lpages-ok fn-lc-dirty fn-lc-pages
     fn-lc-publication-alloc pgs-alloc-inv pgs-c-lpages-ok-is
     fn-lc-dirty-lpages-ok fn-lc-snapshotp fn-lc-headerp)))))
(defthm fn-lc-publication-value-program-cost
 (implies (fn-lc-publication-valuep old old-header columns header disk r mode)
  (equal (fn-lc-write-octets
          (fn-lc-publication-program
           (pgs-plan-commit disk r mode (fn-lc-dirty old old-header columns header)
                            (fn-lc-publication-alloc disk))))
         (+ (* (+ (len (fn-lc-dirty old old-header columns header))
                   (len (pgs-touched (pgs-dirty-lpages
                         (fn-lc-dirty old old-header columns header)) nil))
                   (pgs-dir-run-pages (len (fn-lc-pages columns header))))
                (fn-lc-page-octets)) (fn-lc-root-slot-octets))))
 :hints (("Goal" :use
  (fn-lc-publication-value-has-valid-plan
   (:instance fn-lc-valid-plan-program-cost
    (dirty (fn-lc-dirty old old-header columns header))
    (alloc (fn-lc-publication-alloc disk)))
   (:instance fn-lc-grown-delta-has-new-extent (new columns)))
  :in-theory (e/d (fn-lc-publication-valuep)
   (fn-lc-dirty fn-lc-pages pgs-open pgs-c-lpages-ok pgs-alloc-inv
    fn-lc-publication-alloc pgs-plan-commit fn-lc-publication-program
    fn-lc-publication-value-has-valid-plan fn-lc-write-octets fn-lc-valid-plan-program-cost pgs-grown-len
    pgs-dirty-lpages pgs-touched pgs-dir-run-pages fn-lc-grown-delta-has-new-extent)))))

(defthm fn-lc-stage-value-write-bound
 (<= (fn-lc-write-octets (nth 2 (fn-lc-stage-value old old-header columns header disk r mode outcome)))
     (+ (* (+ (len (fn-lc-dirty-column-pages old columns))
              (len (fn-lc-dirty-directory-pages old old-header columns header)))
           (fn-lc-page-octets)) (fn-lc-root-slot-octets)))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-write-octets-of-take (trace (fn-lc-publication-program (pgs-plan-commit disk r mode (fn-lc-dirty old old-header columns header) (fn-lc-publication-alloc disk)))) (n (min (+ 1 (fn-lc-outcome-ok-count outcome (len (fn-lc-publication-program (pgs-plan-commit disk r mode (fn-lc-dirty old old-header columns header) (fn-lc-publication-alloc disk)))))) (len (fn-lc-publication-program (pgs-plan-commit disk r mode (fn-lc-dirty old old-header columns header) (fn-lc-publication-alloc disk)))))))
   fn-lc-publication-value-program-cost
   (:instance fn-lc-dirty-plus-physical-metadata-bound (new columns)))
  :in-theory (e/d (fn-lc-stage-value)
   (fn-lc-publication-valuep fn-lc-dirty fn-lc-pages fn-lc-dirty-column-pages
    fn-lc-dirty-directory-pages fn-lc-publication-program pgs-plan-commit
    fn-lc-outcome-ok-count fn-lc-write-octets pgs-crash pgs-apply-pages
    fn-lc-publication-value-program-cost take pgs-touched pgs-dirty-lpages pgs-dir-run-pages)))))
; Standing rule: invalid publications have no requested writes.
(defthm fn-lc-publication-writes-bound
 (let ((out (fn-lc-stage old old-header header disk r mode segs outcome fn-lbc)))
  (<= (fn-lc-write-octets (mv-nth 4 out))
      (+ (* (+ (len (fn-lc-dirty-column-pages old (fn-lc-columns fn-lbc)))
               (len (fn-lc-dirty-directory-pages old old-header (fn-lc-columns fn-lbc) header)))
            (fn-lc-page-octets)) (fn-lc-root-slot-octets))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-lc-stage-value-write-bound (columns (fn-lc-columns fn-lbc))))
  :in-theory (e/d (fn-lc-stage)
   (fn-lc-stage-value fn-lc-columns fn-lc-columns-value fn-lc-write-octets
    fn-lc-dirty-column-pages fn-lc-dirty-directory-pages)))))
