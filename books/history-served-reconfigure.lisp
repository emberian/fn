; Resident history refinement of the phased live-configuration completion.
(in-package "ACL2")
(include-book "config-owner-carried")
(include-book "owner-refresh-indexed")

(defun fn-hcr-owner-with-store (o st fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (fn-own-refresh-ix
   (fn-own-make st (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger-field o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)) fn-hist))

(defun fn-hcr-complete (oc fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (let* ((record (fn-ocfg-staged oc))
         (o (fn-ocfg-owner oc))
         (old-store (fn-own-store o)))
    (mv-let (new-store config1)
      (fn-oclc-configure old-store (fn-ocfg-config oc) record)
      (if (equal (fn-sn-config-history new-store)
                 (fn-sn-config-history old-store))
          oc
        (fn-ocfg-make (fn-hcr-owner-with-store o new-store fn-hist)
                      config1 (fn-ocfg-pins oc) nil)))))

(defun fn-hcr-publish (oc generation max-octets fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (let ((record (fn-ocfg-staged oc)))
    (if (or (not record)
            (not (equal (fn-cfg-record-generation record) generation)))
        (mv :refused oc)
      (let ((next (fn-hcr-complete oc fn-hist)))
        (if (fn-ocfg-staged next)
            (mv :recovery-required oc)
          (mv :durable
              (fn-ocfg-with-owner
               next
               (fn-own-configure
                (fn-ocfg-owner next)
                (fn-oag-post-config (fn-ocfg-config next) max-octets)))))))))

(defthm fn-hcr-owner-with-store-is-reference
  (implies (and (fn-sn-statep st) (fn-hist-of-storep hist st))
           (equal (fn-hcr-owner-with-store o st hist)
                  (fn-ocl-owner-with-store o st)))
  :hints (("Goal" :in-theory '(fn-hcr-owner-with-store fn-ocl-owner-with-store
                              fn-own-refresh-ix-is-own-refresh
                              fn-own-store-of-fn-own-make))))

(defthm fn-hcr-configure-keeps-records
  (equal (fn-sf-records (fn-sn-files (mv-nth 0 (fn-oclc-configure st config record))))
         (fn-sf-records (fn-sn-files st)))
  :hints (("Goal" :in-theory (e/d (fn-oclc-configure fn-cpo-install)
                                 (fn-sn-with-configuration)))))

(defthm fn-hcr-configure-preserves-state
  (implies (and (fn-cst-relation st)
                (equal config (fn-cnode-config (fn-oclc-replayed st))))
           (fn-sn-statep (mv-nth 0 (fn-oclc-configure st config record))))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files st)) :ready))
           :use (fn-oclc-configure-is-configure-durable
                 fn-oclc-ready-cst-relation-is-history-relation
                 fn-cpo-configure-durable-preserves-history-relation)
           :in-theory (e/d (fn-cpo-history-relation fn-cst-relation)
                           (fn-sn-statep fn-oclc-configure fn-cpo-configure-durable
                            fn-oclc-configure-is-configure-durable
                            fn-oclc-ready-cst-relation-is-history-relation
                            fn-cpo-configure-durable-preserves-history-relation
                            fn-cst-replay-node fn-cpr-replay)))))

(defthm fn-hcr-complete-is-reference
  (implies (and (fn-ocl-relation oc)
                (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-hcr-complete oc hist) (fn-oclc-complete oc)))
  :hints (("Goal"
           :use ((:instance fn-hcr-configure-preserves-state
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (config (fn-ocfg-config oc)) (record (fn-ocfg-staged oc))))
           :in-theory '(fn-hcr-complete fn-oclc-complete
                        fn-hcr-owner-with-store-is-reference fn-hcr-configure-keeps-records
                        fn-ocl-relation fn-ocl-config-historyp fn-oclc-replayed
                        fn-hist-of-storep))))

(defthm fn-hcr-publish-is-reference
  (implies (and (fn-ocl-relation oc)
                (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-hcr-publish oc generation max-octets hist)
                  (fn-oclc-publish oc generation max-octets)))
  :hints (("Goal" :in-theory '(fn-hcr-publish fn-oclc-publish
                              fn-hcr-complete-is-reference))))

(in-theory (disable fn-hcr-owner-with-store fn-hcr-complete fn-hcr-publish))

; The resident publication is also the original replay-based publication,
; including refusal and recovery-required results, under the carried relation.
(defthm fn-hcr-publish-is-publish
  (implies (and (fn-ocl-relation oc)
                (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-hcr-publish oc generation max-octets hist)
                  (fn-ocl-publish oc generation max-octets)))
  :hints (("Goal" :in-theory '(fn-hcr-publish-is-reference
                              fn-oclc-publish-is-publish))))
