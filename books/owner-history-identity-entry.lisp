; Identity admission with a memory-only prepare and the same owner effects.
(in-package "ACL2")
(include-book "history-served-prepare-general")
(include-book "owner-retain-writer-frame")

(defun fn-owner-prepare-identity-served (event fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena state fn-hist)
                  :guard (and (and (boundp-global (quote fn-owner) state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                              (fn-prc-carryp (fn-owner-retain-carry state))) (fn-cst-relation (fn-owner-store state)))
                  :guard-hints (("Goal"
                                 :in-theory
                                 (enable fn-sn-statep fn-sbud-oc-store fn-arena-count-is-len)))))
  (let ((s (fn-owner-store state)))
    (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
        (value :invalid)
      (let ((carry (fn-prc-refresh (fn-owner-retain-carry state) (fn-node-retention (fn-sn-node s)))))
        (mv-let (word next) (fn-hsp-irc-pout-prepare-identity (fn-owner-ocfg state)
                                                              event
                                                              (fn-arena-count fn-arena)
                                                              carry
                                                              fn-hist)
          (let* ((row (fn-oii-identity-row event
                                           (fn-sn-keyring s)
                                           (fn-sn-keyring-generation s)
                                           (fn-arena-count fn-arena)))
                 (state (fn-owner-retain-carry-put carry state))
                 (state (fn-owner-install-ocfg next state)))
            (cond ((not (equal word :prepared)) (value word))
                  ((fn-oii-identity-sealsp event)
                   (let ((state (f-put-global (quote fn-owner-cat-candidate)
                                              (if (fn-hstxa-p row)
                                                  (cons (fn-replay-composite-record event)
                                                        (fn-hstxa-held row))
                                                (cons event row))
                                              state)))
                     (value (list :seal (fn-oii-identity-payload event)))))
                  (t (value :prepared)))))))))

(defthm fn-owner-prepare-identity-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-prepare-identity-served event arena hist state)
         (fn-owner-prepare-identity event arena state)))
 :hints (("Goal" :use ((:instance fn-owner-retain-statep-implies-entry-guard))
 :in-theory '(fn-owner-prepare-identity-served fn-owner-prepare-identity
 fn-owner-store fn-owner-core fn-owner-ocfg fn-sbud-oc-store
 fn-hsp-irc-pout-prepare-identity-is-reference))))

(defthm fn-owner-prepare-identity-served-preserves-carried-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep (mv-nth 2 (fn-owner-prepare-identity-served event fn-arena fn-hist state))))
 :hints (("Goal" :in-theory
 '(fn-owner-retain-statep fn-owner-prepare-identity-served
 fn-hsp-irc-pout-prepare-identity mv-nth nth endp zp car-cons cdr-cons
 fn-owner-bound-of-retain-carry-put fn-owner-bound-of-install-ocfg
 fn-owner-bound-of-other-global-put fn-owner-ocfg-of-retain-carry-put
 fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
 fn-owner-retain-carry-of-put fn-owner-retain-carry-of-other-global-put
 fn-owner-retain-carry-of-install-ocfg fn-prc-carryp-of-refresh
 fn-hsp-irc-oiis-prepare-preserves-invariant))))

(in-theory (disable fn-owner-prepare-identity-served))
