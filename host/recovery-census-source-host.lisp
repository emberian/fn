; Installed recovery input for the existing OSM/HCT canonical census.
; This descriptor is not a live capture, a grant, or canonical readiness.
(in-package "ACL2")
(include-book "recovery-source-sized-host")
(include-book "../books/store-node")

(defun fn-owner-recovery-startup-source (token state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((c (fn-owner-recovery-global 'fn-owner-recovery-source state))
         (epoch (fn-owner-canonical-epoch state))
         (generation (fn-owner-recovery-source-generation-value c state))
         (st (fn-owner-recovery-global 'fn-store-sn state))
         (files (fn-sn-files st))
         (field (fn-sf-records-field files)))
    (cond
     ((not (fn-owner-recovery-source-currentp-value c token state))
      (value '(:unavailable :recovery-source)))
     ((not (eq (fn-sf-phase files) :ready))
      (value '(:unavailable :recovery-store)))
     ; Gate the concrete count representation before the actual accessor:
     ; its legacy raw-list branch otherwise traverses the whole history.
     ; This is a bounded representation test, not a canon/domain scan.
     ((not (fn-owner-recovery-records-formp field))
      (value '(:unavailable :recovery-records-form)))
     (t
      (let ((count (fn-sf-records-count files))
            (frontier (fn-sf-frontier files)))
        (if (not (and (natp count) (natp frontier)
                      (equal count (fn-omk-at 4 c))
                      (<= (nfix (fn-omk-at 5 c)) frontier)))
            (value '(:unavailable :recovery-store-lineage))
          ; Authority for INITIAL source custody does not assert size readiness.
          (value (list :recovery-census token epoch generation st field
                       count frontier (fn-sn-consumer st)))))))))

(defun fn-owner-recovery-census-source (token state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (erp descriptor state) (fn-owner-recovery-startup-source token state)
  (if (or erp (not (eq (fn-omk-at 0 descriptor) :recovery-census)))
      (mv erp descriptor state)
   (mv-let (erp carries state) (fn-owner-recovery-source-sized-readout token state)
    (if (or erp (not (eq (fn-omk-at 0 carries) :ready)))
        (mv erp carries state)
      (value descriptor))))))
