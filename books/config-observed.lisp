; Open a physical image under its ordered configuration and Store histories.
; This runs once at process recovery. It carries no host-derived group table or
; capacity and leaves the existing five recovery barriers to the file kernel.
(in-package "ACL2")
(include-book "config-physical-replay")
(include-book "store-observed")

(defun fn-cpo-open-observed (configs frontier events)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (null configs)
          (not (fn-sn-observed-historyp frontier events)))
      (fn-sn-open-error :history)
    (let ((replayed (fn-cpr-replay configs events)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (let* ((cn (fn-replay-result-node replayed))
               (node (fn-cnode-node cn)))
          (if (not (and (fn-cnode-statep cn)
                        (fn-replay-advance-okp node frontier)))
              (fn-sn-open-error :frontier)
            (let* ((advanced (fn-replay-advance-txid node frontier))
                   (config (fn-cnode-config cn))
                   (identity (fn-replay-identity events))
                   (files (fn-sf-make :recovering frontier nil events
                                      nil nil nil 0))
                   (seed (fn-sn-observed-seed
                          (fn-cnode-domain-of config)
                          (fn-cfg-capacity (fn-cfg-value config))
                          frontier events))
                   (opened (fn-sn-update-replayed
                            seed files advanced
                            (fn-stx-index-of-store (fn-stx-store advanced) nil)
                            identity)))
              (if (and (equal (fn-stxk-context-kind identity) :ok)
                       (fn-sn-statep opened))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :identity)))))))))

(verify-guards fn-cpo-open-observed)

; The caller sees the complete observed journal and the parameters from the
; final *ordered* configuration. No barrier has been reported at open.
(defthm fn-cpo-open-success-exact-image
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let* ((st (fn-sn-open-state
                       (fn-cpo-open-observed configs frontier events)))
                  (cn (fn-replay-result-node
                       (fn-cpr-replay configs events))))
             (and (equal (fn-sf-records (fn-sn-files st)) events)
                  (equal (fn-sf-frontier (fn-sn-files st)) frontier)
                  (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                  (equal (fn-sf-barriers (fn-sn-files st)) 0)
                  (equal (fn-sn-groups st) (fn-cnode-domain cn))
                  (equal (fn-sn-capacity st)
                         (fn-cfg-capacity
                          (fn-cfg-value (fn-cnode-config cn)))))))
  :hints (("Goal" :in-theory (enable fn-cpo-open-observed fn-sn-open-okp))))

(deftheory fn-cpo-vocabulary '(fn-cpo-open-observed))
(in-theory (disable fn-cpo-vocabulary))
