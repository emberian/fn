; LC steps append only into already allocated segments.
(in-package "ACL2")
(include-book "log-checkpoint-backpressure")
(defthm fn-lc-append-prepared-retains-segment-ids
 (equal (fn-lc-seg-ids (fn-lc-append-prepared record id unit segs)) (fn-lc-seg-ids segs))
 :hints (("Goal" :induct (fn-lc-append-prepared record id unit segs))))
(defthm fn-lc-prepare-tail-retains-segment-ids
 (equal (fn-lc-seg-ids (fn-lc-prepare-tail records id unit segs)) (fn-lc-seg-ids segs))
 :hints (("Goal" :induct (fn-lc-prepare-tail records id unit segs))))
(defthm fn-lc-commit-adds-no-segment-id
 (let ((out (fn-lc-commit records segs header k fn-lbc)))
  (subsetp-equal (fn-lc-seg-ids (mv-nth 2 out)) (fn-lc-seg-ids segs)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-lc-commit)
  (fn-lc-prepare-tail fn-lc-tail-history fn-lc-prepared-recordsp
   fn-lc-tail-scan fn-lc-segs-retain fn-lc-commit-prepared)))))
(defun fn-lc-id-preservation-tooth (mutant records segs header k fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (and (fn-lbc-p fn-lbc) (natp k)) :verify-guards nil))
 (mv-let (answer fn-lbc post-segs) (fn-lc-commit records segs header k fn-lbc)
  (declare (ignore answer))
  (mv (subsetp-equal (if mutant (cons 999 (fn-lc-seg-ids post-segs)) (fn-lc-seg-ids post-segs))
                    (fn-lc-seg-ids segs)) fn-lbc)))
(defteeth fn-lc-commit-adds-no-segment-id
 :claim (let ((out (fn-lc-commit records segs header k fn-lbc)))
          (() (subsetp-equal (fn-lc-seg-ids (mv-nth 2 out)) (fn-lc-seg-ids segs))))
 :subject fn-lc-commit
 :witness ((records nil) (segs '((0 nil nil)))
  (header (list :lc-header (list 0 0 0 0 *fn-lg-genesis*) 1 nil nil nil)) (k 0))
 :stobjs ((fn-lbc (fn-lc-teeth-empty-columns fn-lbc)))
 :stobj-checks
 (((let ((out (fn-lc-commit records segs header k fn-lbc))) (declare (ignorable out))
    (subsetp-equal (fn-lc-seg-ids (mv-nth 2 out)) (fn-lc-seg-ids segs)))
   (fn-lc-id-preservation-tooth nil records segs header k fn-lbc)
   :hints (("Goal" :in-theory (disable fn-lc-commit))))
  ((let ((out (fn-lc-commit records segs header k fn-lbc))) (declare (ignorable out))
    (subsetp-equal (cons 999 (fn-lc-seg-ids (mv-nth 2 out))) (fn-lc-seg-ids segs)))
   (fn-lc-id-preservation-tooth t records segs header k fn-lbc)
   :hints (("Goal" :in-theory (disable fn-lc-commit)))))
 :breaks nil
 :mutations ((rolls-in-commit (:conclusion
  (subsetp-equal (cons 999 (fn-lc-seg-ids (mv-nth 2 out))) (fn-lc-seg-ids segs)))
  ((records nil) (segs '((0 nil nil)))
   (header (list :lc-header (list 0 0 0 0 *fn-lg-genesis*) 1 nil nil nil)) (k 0))
  :fault "commit inserts a new segment instead of leaving allocation to rollover")))
(defteeth-check (fn-lc-commit-adds-no-segment-id))
