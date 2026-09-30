; Installed recovery input for the existing OSM/HCT canonical census.
; This descriptor is not a live capture, a grant, or canonical readiness.
(in-package "ACL2")
(include-book "recovery-source-sized-host")
(include-book "../books/store-node")

(defun fn-owner-recovery-census-source (token state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((c (fn-owner-recovery-global 'fn-owner-recovery-source state))
         (epoch (fn-owner-canonical-epoch state))
         (generation (fn-store-sco-recovery-source-generation-value state))
         (st (fn-owner-recovery-global 'fn-store-sn state))
         (files (fn-sn-files st))
         (field (fn-sf-records-field files)))
    (cond
     ((not (and (fn-rsa-metap (fn-store-sco-recovery-source-value state))
                 (fn-rsa-currentp c token epoch generation)))
      (value '(:unavailable :recovery-source)))
     ((not (eq (fn-sf-phase files) :ready))
      (value '(:unavailable :recovery-store)))
     ; Gate the concrete count representation before the actual accessor:
     ; its legacy raw-list branch otherwise traverses the whole history.
     ; This is a bounded representation test, not a canon/domain scan.
     ((not (if (fn-sfr-basedp field)
               (or (null (fn-sfr-suffix field))
                   (fn-sl-snoc-formp (fn-sfr-suffix field)))
             (or (null field) (fn-sl-snoc-formp field))))
      (value '(:unavailable :recovery-records-form)))
     (t
      (let ((count (fn-sf-records-count files))
            (frontier (fn-sf-frontier files)))
        (if (not (and (natp count) (natp frontier)
                      (equal count (fn-omk-at 4 c))
                      (<= (nfix (fn-omk-at 5 c)) frontier)))
            (value '(:unavailable :recovery-store-lineage))
          (mv-let (erp carries state)
                  (fn-owner-recovery-source-sized-readout token state)
            (if (or erp (not (eq (fn-omk-at 0 carries) :ready)))
                (mv erp carries state)
              ; Borrow the literal installed Store and records field. The
              ; collector's lifecycle retains this root and invalidates on
              ; mutation/reset; count coincidence never establishes that.
              (value (list :recovery-census token epoch generation st field
                           count frontier (fn-sn-consumer st)))))))))))
