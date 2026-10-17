(in-package "ACL2")

(include-book "../../books/bp-node-receive-boundary")
; Seeded unfunded registered storage. Marker payloads are not a real writer.
(defun fn-bpcc-payload-directory-test-install (fn-bp-controller-registry fn-page-read-pool)
  (declare (xargs :stobjs (fn-bp-controller-registry fn-page-read-pool) :guard t))
  (let* ((initial (fn-bpnf-initial-state
                   (fn-bpn-config (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47))
                                  3600000 2 32 1048576) 8 1048576))
         (current (fn-bpnf-with-issued initial
                    (fn-bpnf-operation (fn-bpnf-epoch initial) 0 :checkpoint 5 :pending)))
         (ledger (fn-prl-build '(1000000 100000 10 10 100) '(0 0 0 0 0)
                              7 nil '(1000 0 0 0 0)))
         (fn-page-read-pool (update-fn-prp-data (list ledger nil nil nil nil) fn-page-read-pool))
         (fn-page-read-pool (update-fn-prp-mode :served fn-page-read-pool))
         (fn-bp-controller-registry (update-fn-bpcr-highwater 1 fn-bp-controller-registry)))
    (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
      (fn-bpc-node)
      (stobj-let ((fn-bpc-segment
                   (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
        (fn-bpc-segment)
        (mv-let (word fn-bpc-segment)
          (fn-bpc-segment-install 2 0 current :unfunded-storage-only fn-bpc-segment)
          (declare (ignore word)) fn-bpc-segment)
        fn-bpc-node)
      (mv fn-bp-controller-registry fn-page-read-pool))))

