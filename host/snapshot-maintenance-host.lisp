; Actual funded-pool calls for the snapshot writer's core-derived backing
; request. Initial whole-operation adequacy is not inferred from this adapter.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/snapshot-maintenance-profile")

(defun fn-owner-snapshot-growth (maintenance source stage request fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv '(:refused :maintenance-resources-unavailable) fn-page-read-pool)
    (mv-let (grant next)
      (fn-osj-native-grow (fn-owner-page-read-ledger fn-page-read-pool)
                   maintenance source stage request)
      (if (not (equal (fn-omk-at 0 grant) :checkpoint-funded))
          (mv grant fn-page-read-pool)
        (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger next fn-page-read-pool)))
          (mv grant fn-page-read-pool))))))

(defun fn-owner-snapshot-grant-livep (grant fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (and (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
       (fn-osj-native-grant-livep grant (fn-owner-page-read-ledger fn-page-read-pool))))

(defthm fn-owner-snapshot-growth-refines-actual-ledger
  (implies (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
           (let* ((r (fn-owner-snapshot-growth maintenance source stage request fn-page-read-pool))
                  (model (fn-osj-native-grow (fn-owner-page-read-ledger fn-page-read-pool)
                                      maintenance source stage request)))
             (and (equal (mv-nth 0 r) (mv-nth 0 model))
                  (equal (fn-owner-page-read-ledger (mv-nth 1 r)) (mv-nth 1 model)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-owner-snapshot-growth fn-owner-page-read-ledger
                   fn-owner-page-read-keep-ledger fn-osj-native-grow fn-osj-native-backingp fn-osj-grow fn-osj-keep-grant
                   fn-prl-build fn-prl-nth fn-omk-at))))

(in-theory (disable fn-owner-snapshot-growth fn-owner-snapshot-grant-livep))
