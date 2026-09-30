; One coherent operational writer scheduling action. Constructor phases have
; no positive implementation here until actual installed admission exists.
; Ready is a carried guard; the body dispatches fixed scalar phase fields.
(in-package "ACL2")
(logic)
(include-book "index-backing-table-seal")

(defun fn-ipa-writer-step-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (phase (fn-omk-at 1 builder)) (control (fn-omk-at 18 builder)))
  (case phase
   (:assigning (fn-ibp-writer-assignment-ready-p fn-index-backing))
   (:numbers (fn-ibp-writer-number-ready-p fn-index-backing))
   (:row-source (fn-ibp-writer-row-source-ready-p fn-index-backing))
   (:row-share (fn-ipa-row-share-ready-p fn-index-backing))
   (:table-reinsert
    (or (equal control '(:table-reinsert 0 nil))
        (fn-ipa-reinsert-ready-p fn-index-backing)))
   (:table-seal (fn-ipa-table-seal-ready-p fn-index-backing))
   (otherwise t))))

(defun fn-ipa-writer-step (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                             (fn-ipa-writer-step-ready-p fn-index-backing))))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (phase (fn-omk-at 1 builder)) (control (fn-omk-at 18 builder))
        (pending (fn-ibp-page-pending fn-index-backing)))
  (if (zp fuel) (mv :yield fuel fn-index-backing)
   (case phase
    (:arena-held (fn-ibp-writer-assignment-begin fuel fn-index-backing))
    (:assigning (fn-ibp-writer-assignment-one fuel fn-index-backing))
    (:numbers (fn-ibp-writer-number-one fuel fn-index-backing))
    (:row-source (fn-ibp-writer-row-source-one fuel fn-index-backing))
    (:layout
     (cond
      ((null control) (fn-ibp-writer-row-source-begin fuel fn-index-backing))
      ((and (eq (fn-omk-at 6 pending) :rows) (eq (fn-omk-at 10 pending) :built))
       (fn-ipa-row-copy-one fuel fn-index-backing))
      ((and (eq (fn-omk-at 6 pending) :rows) (eq (fn-omk-at 10 pending) :copied))
       (fn-ipa-row-seal fuel fn-index-backing))
      ((and (eq (fn-omk-at 6 pending) :table) (eq (fn-omk-at 10 pending) :built))
       (fn-ipa-table-root-begin fuel fn-index-backing))
      (t (mv :constructor-required fuel fn-index-backing))))
    (:row-root (fn-ipa-row-root-one fuel fn-index-backing))
    (:table-layout
     (cond (pending (fn-ipa-row-debt-transfer fuel fn-index-backing))
           ((eq (fn-omk-at 17 builder) :rows-shared)
            (fn-ipa-table-layout-begin fuel fn-index-backing))
           (t (fn-ipa-row-share-begin fuel fn-index-backing))))
    (:row-share (fn-ipa-row-share-one fuel fn-index-backing))
    (:table-depth (fn-ipa-table-depth-one fuel fn-index-backing))
    (:table-root (fn-ipa-table-root-one fuel fn-index-backing))
    (:table-page-attached (fn-ipa-table-page-advance fuel fn-index-backing))
    (:table-reinsert
     (if (equal control '(:table-reinsert 0 nil))
         (fn-ipa-reinsert-begin fuel fn-index-backing)
       (case (fn-omk-at 2 control)
        ((:row-directory :table-directory) (fn-ipa-reinsert-directory-one fuel fn-index-backing))
        (:row-read (fn-ipa-reinsert-row-read fuel fn-index-backing))
        (:tag (fn-ipa-reinsert-tag fuel fn-index-backing))
        (:place (fn-ipa-reinsert-place-one fuel fn-index-backing))
        (otherwise (mv :recovery-required fuel fn-index-backing)))))
    (:table-seal (fn-ipa-table-seal-one fuel fn-index-backing))
    (:ready (mv :ready fuel fn-index-backing))
    (:recovery-required (mv :recovery-required fuel fn-index-backing))
    (otherwise (mv :unavailable fuel fn-index-backing))))))
(verify-guards fn-ipa-writer-step
 :hints (("Goal" :in-theory
  (e/d (fn-ipa-writer-step-ready-p)
       (fn-ibp-writer-assignment-ready-p fn-ibp-writer-number-ready-p
        fn-ibp-writer-row-source-ready-p fn-ipa-row-share-ready-p
        fn-ipa-reinsert-ready-p fn-ipa-table-seal-ready-p)))))

(defun fn-mio-writer-step-ready-p (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (ready) (fn-ipa-writer-step-ready-p fn-index-backing) ready))
(defun fn-mio-writer-step (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (and (natp fuel) (<= fuel *fn-mpr-slot-quantum*)
                                            (fn-mio-writer-step-ready-p fn-mio$c))))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing)
  (fn-ipa-writer-step fuel fn-index-backing)
  (mv word left fn-mio$c)))
