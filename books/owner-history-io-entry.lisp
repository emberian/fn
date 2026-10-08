; Served observations synchronize the memory suffix after each file-model step.
(in-package "ACL2")
(include-book "owner-history-log-io")
(include-book "owner-history-carried")
(include-book "owner-retain-writer-frame")

(defun fn-owner-io-safep (st operation result)
  (declare (xargs :guard t) (ignore st result))
  (case operation
    (:log-reserve t)
    (:log-order t)
    (t (fn-psrv-io-safep operation))))

(defun fn-owner-io-served (operation result fn-hist state)
 (declare (xargs :stobjs (fn-hist state)
  :guard (and (boundp-global 'fn-owner state)
              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))
  :guard-hints (("Goal" :in-theory (e/d (fn-sbud-oc-store fn-host-hist-sync)
                                       (fn-sn-statep boundp-global))))))
 (let ((oc (fn-owner-ocfg state)))
  (if (not (fn-owner-io-safep (fn-sbud-oc-store oc) operation result))
      (mv nil :unsafe-observation fn-hist state)
    (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
      (mv-let (oc fn-hist)
          (case operation
            (:log-reserve (fn-hsv-log-reserve oc fn-hist))
            (:log-order (fn-hsv-log-order oc fn-hist))
            (t (fn-hsv-observe oc operation result fn-hist)))
        (let ((state (fn-owner-install-ocfg oc state)))
          (mv nil (fn-sf-phase (fn-sn-files (fn-owner-store state))) fn-hist state)))))))

(defthm fn-owner-io-served-preserves-carried-state
 (implies (fn-owner-retain-statep state)
          (fn-owner-retain-statep
           (mv-nth 3 (fn-owner-io-served operation result fn-hist state))))
 :hints (("Goal" :in-theory
 '(fn-owner-io-served fn-owner-io-safep fn-host-hist-sync-preserves-state
   fn-orh-retain-statep-of-install-ocfg
   fn-hsv-observe-preserves-invariant fn-hsv-observe-car-preserves-invariant
   fn-hsv-log-reserve-car-preserves-invariant fn-hsv-log-order-car-preserves-invariant
   (:type-prescription fn-host-hist-sync) (:type-prescription fn-hsv-observe)
   (:type-prescription fn-hsv-log-reserve) (:type-prescription fn-hsv-log-order)
   mv-nth nth zp car-cons cdr-cons (:executable-counterpart zp)
   (:executable-counterpart equal))
 :use ((:instance fn-owner-retain-statep-implies-lgoc (state state))))))

(in-theory (disable fn-owner-io-served))

; Startup retains the reference reader; serving uses the memory entry above.
(defun fn-owner-io (operation result state)
  (declare (xargs :stobjs state :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let ((oc (fn-owner-ocfg state)))
    (if (not (fn-owner-io-safep (fn-sbud-oc-store oc) operation result))
        (value :unsafe-observation)
      (let ((state (fn-owner-install-ocfg
                    (case operation
                      (:log-reserve (fn-olr-ocfg-reserve oc))
                      (:log-order (fn-olr-ocfg-order oc))
                      (t (fn-rcon-ocfg-io oc operation result)))
                    state)))
        (value (fn-sf-phase (fn-sn-files (fn-owner-store state))))))))

(defthm fn-hsv-current-sync-is-current
 (implies (and (fn-sn-statep s) (fn-hist-of-storep hist s))
  (equal (mv-nth 0 (fn-host-hist-sync s hist state)) hist))
 :hints (("Goal"
 :use ((:instance fn-hist-served-base-is-within-record-count (files (fn-sn-files s)))
       (:instance fn-hsv-state-has-history-list))
 :in-theory '(fn-host-hist-sync fn-hist-served-sync-is-sync
 fn-hist-sync-of-prefix-is-the-history fn-sf-prefixp-reflexive
 fn-hist-of-storep fn-hist-count-is-len fn-sf-records-count))))

(defthm fn-owner-io-served-is-owner-io
 (implies (and (fn-sn-statep (fn-owner-store state))
               (fn-hist-of-storep hist (fn-owner-store state)))
  (and (equal (mv-nth 1 (fn-owner-io-served operation result hist state))
              (mv-nth 1 (fn-owner-io operation result state)))
       (equal (mv-nth 3 (fn-owner-io-served operation result hist state))
              (mv-nth 2 (fn-owner-io operation result state)))))
 :hints (("Goal"
 :use ((:instance fn-hsv-log-reserve-is-reference (oc (fn-owner-ocfg state)))
       (:instance fn-hsv-log-order-is-reference (oc (fn-owner-ocfg state)))
       (:instance fn-hsv-observe-is-reference (oc (fn-owner-ocfg state))))
 :in-theory '(fn-owner-io-served fn-owner-io fn-host-hist-sync-preserves-state
 fn-hsv-current-sync-is-current fn-owner-store fn-sbud-oc-store fn-owner-core fn-owner-ocfg
 mv-nth nth zp car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal)
 (:type-prescription fn-host-hist-sync) (:type-prescription fn-hsv-observe)
 (:type-prescription fn-hsv-log-reserve) (:type-prescription fn-hsv-log-order)))))
