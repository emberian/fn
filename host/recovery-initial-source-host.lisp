; Exact readonly functions extracted from completed-open source39c904.
; These are the same actual public functions, not substitute source models.
(in-package "ACL2")
(include-book "../books/recovery-source-authority")
(include-book "../books/recovery-open-origin")
(include-book "../books/store-node")
(include-book "../books/owner-canonical-epoch")
(include-book "store-checkpoint-context-host")

(defun fn-owner-recovery-global (key state)
  (declare (xargs :stobjs state :mode :program))
  (and (boundp-global key state) (f-get-global key state)))

(defun fn-owner-recovery-records-formp (field)
 (declare (xargs :mode :program))
 (if (fn-sfr-basedp field)
     (or (null (fn-sfr-suffix field)) (fn-sl-snoc-formp (fn-sfr-suffix field)))
   (or (null field) (fn-sl-snoc-formp field))))

(defun fn-owner-recovery-source-generation-value (c state)
 (declare (xargs :stobjs state :mode :program))
 (if (fn-rsoa-originp (fn-omk-at 3 c))
     (fn-omk-at 1 (fn-owner-recovery-global 'fn-store-recovery-open-origin state))
   (fn-store-sco-recovery-source-generation-value state)))

(defun fn-owner-recovery-source-currentp-value (c token state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((origin (fn-omk-at 3 c))
        (current (fn-owner-recovery-global 'fn-store-recovery-open-origin state))
        (epoch (fn-owner-canonical-epoch state))
        (generation (fn-owner-recovery-source-generation-value c state)))
  (and (fn-rsa-currentp c token epoch generation)
       (if (fn-rsoa-originp origin)
           (and (fn-rsoa-originp current)
                (equal (fn-omk-at 1 current) (fn-omk-at 1 origin))
                (equal (fn-omk-at 2 current) epoch)
                (eq (fn-omk-at 3 current) (fn-omk-at 3 origin)))
         (fn-rsa-metap (fn-store-sco-recovery-source-value state))))))

(defun fn-owner-recovery-source-token (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((c (fn-owner-recovery-global 'fn-owner-recovery-source state))
         (token (fn-rsa-token c)))
    (value (if (fn-owner-recovery-source-currentp-value c token state)
               token '(:unavailable :recovery-source)))))

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
