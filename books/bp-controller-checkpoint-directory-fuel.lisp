; Proof support for the actual directory scheduling result, not a twin.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-directory")
(defthm fn-bpcc-node-job-fuel-natural
  (implies (and (natp physical-segment) (natp depth) (natp fuel))
           (natp (mv-nth 3 (fn-bpcc-node-job controller token operation slot
                            physical-segment depth demand ledger fuel fn-bpc-node))))
  :hints (("Goal"
           :induct (fn-bpcc-node-job controller token operation slot
                     physical-segment depth demand ledger fuel fn-bpc-node)
            :in-theory (e/d (fn-bpcc-node-job)
                          (floor mod fn-bpcn-children-get fn-bpcn-children-boundp
                           create-fn-bpc-left create-fn-bpc-right create-fn-bpc-segment
                           fn-bpcc-segment-issue-prepare fn-bpcc-segment-issued-publish
                           fn-bpcc-segment-fence-current fn-bpcc-segment-cancel)))))
(defthm fn-bpcc-directory-job-fuel-natural
  (implies (and (fn-bp-controller-registryp fn-bp-controller-registry)
                (natp fuel))
           (natp (mv-nth 3 (fn-bpcc-directory-job controller token operation
                            demand ledger fuel fn-bp-controller-registry))))
  :hints (("Goal" :in-theory (e/d (fn-bpcc-directory-job)
                                 (fn-bpcc-node-job)))))
