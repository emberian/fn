; Core wrapper for the actual retained funded pool. Initial constructor
; adequacy remains the outer maintenance admission obligation.
(in-package "ACL2")
(include-book "snapshot-maintenance-host")
(include-book "../books/history-image-producer")
(include-book "../books/history-image-action-observation")

(defun fn-owner-history-image-offer (c ordinal source token key fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (if (not (and (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
                (fn-hpi-grant-matchesp c (fn-owner-page-read-ledger fn-page-read-pool))))
      (mv '(:refused :image-growth-receipt) c fn-page-read-pool)
    (mv-let (word next) (fn-hpi-offer c ordinal source token key)
      (mv word next fn-page-read-pool))))

(defun fn-owner-history-image-tick (c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
                                    pgs-digest-state fn-page-read-pool)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
                          pgs-digest-state fn-page-read-pool)))
  (if (not (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv '(:refused :maintenance-resources-unavailable) nil c
          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state fn-page-read-pool)
    (mv-let (word effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c observation (fn-owner-page-read-ledger fn-page-read-pool)
                   fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
            pgs-digest-state fn-page-read-pool)))))
