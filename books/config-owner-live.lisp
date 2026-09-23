; Atomic logical publication of a durable configuration into the served owner.
; The physical record has already passed the host's immutable publication
; barrier.  This function is administrative, never a per-command served path.
(in-package "ACL2")
(include-book "owner-config")
(include-book "config-store-traces")

(defun fn-ocl-owner-with-store (o st)
  (declare (xargs :guard t))
  (fn-own-make st (fn-own-view o) (fn-own-conns o)
               (fn-own-next-id o) (fn-own-max-conns o)
               (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o)))

(defun fn-ocl-complete (oc)
  (declare (xargs :guard (fn-sn-statep
                          (fn-own-store (fn-ocfg-owner oc)))))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (let* ((o (fn-ocfg-owner oc))
               (old-store (fn-own-store o))
               (new-store (fn-cpo-configure-durable old-store record)))
          ; A durable physical record that cannot be applied to the carried
          ; history is a recovery event.  Keep the stage so the host fences
          ; instead of returning an accepted live configuration.
          (if (equal (fn-sn-config-history new-store)
                     (fn-sn-config-history old-store))
              oc
            (fn-ocfg-make
             (fn-ocl-owner-with-store o new-store)
             (fn-ocfg-published-config (fn-ocfg-config oc) record)
             (fn-ocfg-pins oc) nil)))
      (fn-ocfg-complete oc))))

(defthm fn-ocl-complete-keeps-existing-pins
  (equal (fn-ocfg-pins (fn-ocl-complete oc))
         (fn-ocfg-pins oc))
  :hints (("Goal" :in-theory (enable fn-ocl-complete fn-ocfg-complete))))

(defthm fn-ocl-complete-success-install-exact-store
  (implies (and (fn-ocfg-staged oc)
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (equal (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))
                  (fn-cpo-configure-durable
                   (fn-own-store (fn-ocfg-owner oc))
                   (fn-ocfg-staged oc))))
  :hints (("Goal" :in-theory (enable fn-ocl-complete fn-ocl-owner-with-store))))

(defthm fn-ocl-complete-success-preserves-historical-store-relation
  (implies (and (fn-ocfg-staged oc)
                (fn-cpo-history-relation
                 (fn-own-store (fn-ocfg-owner oc)))
                (true-listp (fn-sn-config-history
                             (fn-own-store (fn-ocfg-owner oc))))
                (fn-snt-idle-phasep
                 (fn-sf-phase
                  (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                (not (fn-ocfg-staged (fn-ocl-complete oc))))
           (fn-cst-relation
            (fn-own-store (fn-ocfg-owner (fn-ocl-complete oc)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cpo-configure-durable-preserves-history-relation
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-cst-idle-from-observed-history
                            (st (fn-cpo-configure-durable
                                 (fn-own-store (fn-ocfg-owner oc))
                                 (fn-ocfg-staged oc)))))
           :in-theory (e/d (fn-ocl-complete fn-ocl-owner-with-store)
                           (fn-cpo-configure-durable fn-cpo-history-relation
                            fn-cst-relation fn-cst-idle-from-observed-history)))))

(deftheory fn-ocl-vocabulary '(fn-ocl-owner-with-store fn-ocl-complete))
(in-theory (disable fn-ocl-vocabulary))
