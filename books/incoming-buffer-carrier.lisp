; PRF-1143 operational incoming capacity carrier. The shared pool's existing
; third field stores (descriptor row). NIL is uninitialized, not zero capacity.
; Descriptor publication must join actual raw backing identity/observation,
; installed capacity and atomic C->U funding before host activation.
(in-package "ACL2")
(include-book "incoming-octet-holder")

(include-book "incoming-buffer-carrier-shape")

(include-book "index-query-resources")
(include-book "incoming-setup-ranges")
(defun fn-ibc-row-with-job (row job)
  (declare (xargs :guard t))
  (list (fn-prl-nth 0 row) (fn-prl-nth 1 row) (fn-prl-nth 2 row) job))
; Stage consumes only an already-reserved current row. RETAINED remains a
; source-level claim until the actual selected-runtime demand constructor is
; joined. This helper never admits an unfunded allocation itself.
(defun fn-ibc-stage-backing (ledger carrier token capacity retained)
  (declare (xargs :guard t))
  (let ((row (fn-ibc-carrier-row carrier)))
    (if (not (and (fn-ioh-matches row token)
                  (equal (fn-prl-nth 1 row) :setup)
                  (not (fn-prl-nth 3 row)) (natp capacity)
                  (fn-prs-vectorp retained) (equal (fn-prl-nth 4 retained) 0)
                  (fn-prs-vectorp (fn-prl-nth 2 row))
                  (fn-prs-below retained (fn-prl-nth 2 row))
                  (fn-prs-below retained (fn-prl-nth 1 ledger))))
        (mv :backing-refused carrier)
      (mv :backing-staged
          (fn-ibc-carrier-with-row
            carrier (fn-ibc-row-with-job row (list :backing-install capacity retained)))))))
(defun fn-ibc-publish-backing (ledger carrier token outcome)
  (declare (xargs :guard t))
  (let* ((row (fn-ibc-carrier-row carrier)) (job (fn-prl-nth 3 row))
         (capacity (fn-prl-nth 1 job)) (retained (fn-prl-nth 2 job)))
    (cond ((not (and (fn-ioh-matches row token)
                     (equal (fn-prl-nth 1 row) :setup)
                     (equal (fn-prl-nth 0 job) :backing-install)
                     (natp capacity) (fn-prs-vectorp retained)
                     (equal (fn-prl-nth 4 retained) 0)
                     (fn-prs-vectorp (fn-prl-nth 2 row))
                     (true-listp retained) (true-listp (fn-prl-nth 2 row))
                     (true-listp (fn-prl-nth 1 ledger))
                     (fn-prs-below retained (fn-prl-nth 2 row))
                     (fn-prs-below retained (fn-prl-nth 1 ledger))))
           (mv :backing-refused ledger carrier))
          ((equal outcome :installed)
           (mv :backing-installed
               (fn-iqr-promoted-ledger ledger retained)
               (fn-ibc-carrier
                 (fn-ibc-descriptor (fn-prl-nth 1 token) capacity)
                 (list token :setup
                       (fn-prs-release-reusable (fn-prl-nth 2 row) retained) nil))))
          ((member-eq outcome '(:uncertain :failed))
           (mv :backing-held ledger
               (fn-ibc-carrier-with-row
                 carrier (list token :cancelled (fn-prl-nth 2 row) job))))
          (t (mv :invalid-backing-outcome ledger carrier)))))

(defthm fn-ibc-publish-preserves-shared-next
  (equal (fn-prl-nth 2 (mv-nth 1 (fn-ibc-publish-backing ledger carrier token outcome)))
         (fn-prl-nth 2 ledger))
  :hints (("Goal" :in-theory (enable fn-ibc-publish-backing fn-iqr-promoted-ledger
                                    fn-prl-build fn-prl-nth))))
(defthm fn-ibc-noninstalled-publication-keeps-ledger
  (implies (not (equal outcome :installed))
           (equal (mv-nth 1 (fn-ibc-publish-backing ledger carrier token outcome)) ledger))
  :hints (("Goal" :in-theory (enable fn-ibc-publish-backing))))
(defthm fn-ibc-noninstalled-publication-keeps-backing-descriptor
  (implies (not (equal outcome :installed))
           (equal (fn-ibc-carrier-descriptor
                    (mv-nth 2 (fn-ibc-publish-backing ledger carrier token outcome)))
                  (fn-ibc-carrier-descriptor carrier)))
  :hints (("Goal" :in-theory (enable fn-ibc-publish-backing fn-ibc-carrier-descriptor
                                    fn-ibc-carrier-with-row fn-ibc-carrier fn-prl-nth))))
(defthm fn-ibc-publication-preserves-resident-total
  (implies (fn-iqr-resident-promotion-domainp
             ledger (fn-prl-nth 2 (fn-prl-nth 3 (fn-ibc-carrier-row carrier))))
           (equal (fn-iqr-resident-total
                    (mv-nth 1 (fn-ibc-publish-backing ledger carrier token outcome)))
                  (fn-iqr-resident-total ledger)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-iqr-promoted-ledger-preserves-resident-total
                         (retained (fn-prl-nth 2
                                     (fn-prl-nth 3 (fn-ibc-carrier-row carrier))))))
           :in-theory (e/d (fn-ibc-publish-backing)
                           (fn-iqr-resident-promotion-domainp fn-iqr-resident-total
                            fn-iqr-promoted-ledger)))))
