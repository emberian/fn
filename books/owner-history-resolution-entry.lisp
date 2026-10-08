; Reservation resolution refreshes the owner from resident history.
(in-package "ACL2")
(include-book "owner-history-identity-entry")
(include-book "owner-post-carried")

(defthm fn-hsv-refuse-keeps-histories
 (and (equal (fn-sn-config-history (fn-sn-refuse-reservation s txid)) (fn-sn-config-history s))
      (equal (fn-sf-records (fn-sn-files (fn-sn-refuse-reservation s txid)))
             (fn-sf-records (fn-sn-files s))))
 :hints (("Goal" :use (fn-cstp-refuse-reservation-cases) :in-theory nil)))

(defun fn-hsv-pout-refuse-reservation (oc fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist)
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil)
           (ignorable fn-arena))
  (let ((txid (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc))))))
    (mv (if (fn-sn-refuse-reservation-enabledp (fn-sbud-oc-store oc) txid) :refused :fault)
        (fn-ocfg-with-owner oc
                            (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                        (fn-sn-refuse-reservation (fn-own-store (fn-ocfg-owner oc))
                                                                                  txid)
                                                        fn-hist)))))

(verify-guards fn-hsv-pout-refuse-reservation :hints (("Goal" :use ((:guard-theorem fn-pout-refuse-reservation)) :in-theory (enable fn-sbud-oc-store))))

(defthm fn-hsv-pout-refuse-reservation-preserves-invariant
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (mv-nth 1 (fn-hsv-pout-refuse-reservation oc fn-arena fn-hist))))
 :hints (("Goal" :use ((:instance fn-cstp-refuse-reservation-preserves (s (fn-own-store (fn-ocfg-owner oc))) (txid (+ -1 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
 (:instance fn-hsp-owner-with-store-preserves-invariant (st (fn-sn-refuse-reservation (fn-own-store (fn-ocfg-owner oc)) (+ -1 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))) (fn-hist fn-hist))
 fn-lgoc-ocl-relation-cst)
 :in-theory '(fn-hsv-pout-refuse-reservation fn-lgoc-invariantp fn-sbud-oc-store fn-hsv-refuse-keeps-histories
 mv-nth nth zp car-cons cdr-cons (:executable-counterpart zp)))))
(defthm fn-hsv-pout-refuse-reservation-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsv-pout-refuse-reservation oc arena hist) (fn-pout-refuse-reservation oc arena)))
 :hints (("Goal" :use ((:instance fn-sn-refuse-reservation-preserves-state (s (fn-own-store (fn-ocfg-owner oc))) (txid (+ -1 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))))
 :in-theory '(fn-hsv-pout-refuse-reservation fn-pout-refuse-reservation fn-psrv-store-step-is-owner-with-store
 fn-snrt-step fn-sbud-oc-store fn-ocl-owner-with-store-ix-is-reference
 fn-hist-of-storep fn-hsv-refuse-keeps-histories car-cons cdr-cons (:executable-counterpart equal)))))
(in-theory (disable fn-hsv-pout-refuse-reservation))

(defun fn-owner-refuse-reservation-served (fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist)
                  :verify-guards nil
                  :guard (and (boundp-global (quote fn-owner) state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))))
  (mv-let (word next) (fn-hsv-pout-refuse-reservation (fn-owner-ocfg state) fn-arena fn-hist)
    (let* ((state (fn-owner-install-ocfg next state))
           (state (if (equal word :refused)
                      (f-put-global (quote fn-owner-cat-pending) nil state)
                    state)))
      (value word))))

(def-carried-writer fn-owner-refuse-reservation-served
 :profile fn-owner-post-retain
 :bridges ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard))
 :via (fn-hsv-pout-refuse-reservation-preserves-invariant))
(defthm fn-owner-refuse-reservation-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-refuse-reservation-served arena hist state) (fn-owner-refuse-reservation arena state)))
 :hints (("Goal" :use ((:instance fn-owner-retain-statep-implies-entry-guard))
 :in-theory '(fn-owner-refuse-reservation-served fn-owner-refuse-reservation fn-hsv-pout-refuse-reservation-is-reference
 fn-owner-store fn-owner-core fn-owner-ocfg fn-sbud-oc-store))))
(in-theory (disable fn-owner-refuse-reservation-served))

(defun fn-hsv-pout-known-abort (oc fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist)
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil)
           (ignorable fn-arena))
  (mv (if (fn-sn-known-abort-enabledp (fn-sbud-oc-store oc)) :aborted :fault)
      (fn-ocfg-with-owner oc
                          (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
                                                      (fn-sn-known-abort (fn-own-store (fn-ocfg-owner oc)))
                                                      fn-hist))))

(verify-guards fn-hsv-pout-known-abort :hints (("Goal" :use ((:guard-theorem fn-pout-known-abort)) :in-theory (enable fn-sbud-oc-store))))

(defthm fn-hsv-pout-known-abort-preserves-invariant
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (mv-nth 1 (fn-hsv-pout-known-abort oc fn-arena fn-hist))))
 :hints (("Goal" :use ((:instance fn-psrv-known-abort-preserves (s (fn-own-store (fn-ocfg-owner oc))) )
 (:instance fn-hsp-owner-with-store-preserves-invariant (st (fn-sn-known-abort (fn-own-store (fn-ocfg-owner oc)))) (fn-hist fn-hist))
 fn-lgoc-ocl-relation-cst)
 :in-theory '(fn-hsv-pout-known-abort fn-lgoc-invariantp fn-sbud-oc-store fn-psrv-known-abort-keeps-histories
 mv-nth nth zp car-cons cdr-cons (:executable-counterpart zp)))))
(defthm fn-hsv-pout-known-abort-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsv-pout-known-abort oc arena hist) (fn-pout-known-abort oc arena)))
 :hints (("Goal" :use ((:instance fn-sn-known-abort-preserves-state (s (fn-own-store (fn-ocfg-owner oc))) ))
 :in-theory '(fn-hsv-pout-known-abort fn-pout-known-abort fn-psrv-store-step-is-owner-with-store
 fn-snrt-step fn-sbud-oc-store fn-ocl-owner-with-store-ix-is-reference
 fn-hist-of-storep fn-psrv-known-abort-keeps-histories car-cons cdr-cons (:executable-counterpart equal)))))
(in-theory (disable fn-hsv-pout-known-abort))

(defun fn-owner-known-abort-served (fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist)
                  :verify-guards nil
                  :guard (and (boundp-global (quote fn-owner) state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))))
  (mv-let (word next) (fn-hsv-pout-known-abort (fn-owner-ocfg state) fn-arena fn-hist)
    (let* ((state (fn-owner-install-ocfg next state))
           (state (if (equal word :aborted)
                      (f-put-global (quote fn-owner-cat-pending) nil state)
                    state)))
      (value word))))

(def-carried-writer fn-owner-known-abort-served
 :profile fn-owner-post-retain
 :bridges ((fn-sn-statep fn-owner-retain-statep-implies-entry-guard))
 :via (fn-hsv-pout-known-abort-preserves-invariant))
(defthm fn-owner-known-abort-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-known-abort-served arena hist state) (fn-owner-known-abort arena state)))
 :hints (("Goal" :use ((:instance fn-owner-retain-statep-implies-entry-guard))
 :in-theory '(fn-owner-known-abort-served fn-owner-known-abort fn-hsv-pout-known-abort-is-reference
 fn-owner-store fn-owner-core fn-owner-ocfg fn-sbud-oc-store))))
(in-theory (disable fn-owner-known-abort-served))
