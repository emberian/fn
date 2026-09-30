; Structural proper CURRENT carry, never a served recognizer.
(in-package "ACL2")
(include-book "bp-node-job-offer-guards")
(local (defthm fn-bpcl-answer-state
 (equal (fn-bpnf-answer-state (fn-bpnf-answer st effects)) st)
 :hints (("Goal" :in-theory (enable fn-bpnf-answer fn-bpnf-answer-state fn-bpn-nth fn-cbor-ag-car)))))
(local (defthm fn-bpcl-state-constructor
 (true-listp (fn-bpnf-state-with-arrival b h o ho c i w e n a))
 :hints (("Goal" :in-theory (enable fn-bpnf-state-with-arrival)))))
(local (defthm fn-bpcl-update-list
 (implies (true-listp st) (true-listp (update-nth n v st)))
 :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-bpcl-writers
 (implies (true-listp st)
  (and (true-listp (fn-bpnf-with-issued st i))
       (true-listp (fn-bpnf-with-base st b))
       (true-listp (fn-bpnp-with-waits st w))
       (true-listp (fn-bpnp-with-credit st u d))
       (true-listp (fn-bpnp-with-runtime st s p))
       (true-listp (fn-bpnp-with-issued st i))
       (true-listp (fn-bpnp-with-next-issued st i))))
 :hints (("Goal" :in-theory (enable fn-bpnf-with-issued fn-bpnf-with-base
 fn-bpnp-with-waits fn-bpnp-with-credit fn-bpnp-with-runtime
 fn-bpnp-with-issued fn-bpnp-with-next-issued)))))

(local (defthm fn-bpcl-deliver-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpah-deliver-step st key node))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpah-deliver-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-deliver-result-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpah-deliver-result-step st epoch marker-id key
                                                status detail))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpah-deliver-result-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-persist-delivery-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpah-persist-delivery-step st epoch operation-id
                                                  result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpah-persist-delivery-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-recover-fnbs-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnf-recover-fnbs-step st new-epoch base-records
                                              sequence-ready replay-result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpnf-recover-fnbs-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-foundation-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnf-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpnf-step fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-family-propose-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnf-family-propose-step st anchor-arrival observation))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpnf-family-propose-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-family-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnf-family-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpnf-family-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-job-propose-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpfj-propose-step st anchor-arrival observation job limit))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpfj-propose-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-job-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpfj-persist-step st epoch op result job limit))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpfj-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-fragment-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnf-fragment-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpnf-fragment-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-delete-propose-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpn-report-delete-propose-step st observation enabled))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpn-report-delete-propose-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-delete-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpn-report-delete-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpn-report-delete-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-report-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpn-report-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpn-report-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-queue-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpn-report-queue-step st arrival sequence route
                                             observation))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpn-report-queue-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-report-author-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpn-report-author-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpn-report-author-step fn-bpcl-report-step fn-bpcl-queue-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-credit-refusal
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-credit-refusal st event kind))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpnp-credit-refusal fn-bpcl-report-author-step fn-cbor-ag-car car-cons) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-delegate-with-credit
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-delegate-with-credit st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpnp-delegate-with-credit fn-bpcl-report-author-step fn-bpcl-credit-refusal) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-transit-dispatch-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-transit-dispatch-step st h peer node))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpnp-transit-dispatch-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-progress-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-progress-step st node observation routes
                                          generation budget))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpnp-progress-step fn-bpcl-deliver-step fn-bpcl-transit-dispatch-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-dispatch-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-dispatch-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpnp-dispatch-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-clock-domain-fence
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-clock-domain-fence st plan))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpnp-clock-domain-fence) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-conflict-propose-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-conflict-propose-step st event h))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpnp-conflict-propose-step fn-bpnp-with-next-issued fn-bpnp-conflict-refusal) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-rotate-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-rotate-step st generation ck))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpnp-rotate-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-rotation-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-rotation-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpnp-rotation-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-busy-delivery-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-busy-delivery-step st epoch op key observation budgets))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpnp-busy-delivery-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-deferral-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-deferral-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpnp-deferral-persist-step fn-bpnp-deferral-apply car-cons) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-busy-resume-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-busy-resume-step st arrival budget))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpnp-busy-resume-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-conflict-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-conflict-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpnp-conflict-persist-step fn-bpnp-conflict-refusal) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-start-one
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-start-one st peer session mru observation budget ordered))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpnp-start-one) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-routed-start
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-routed-start st peer session mru observation via budget))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpnp-routed-start fn-bpcl-start-one) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-attempt-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-attempt-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpcl-routed-start fn-bpnp-attempt-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-forward-result-propose-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-forward-result-propose-step
                    st attempt-epoch attempt-op session outcome observation))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpcl-routed-start fn-bpcl-attempt-persist-step fn-bpnp-forward-result-propose-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-operator-resume-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-operator-resume-step st arrival budget))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpcl-routed-start fn-bpcl-attempt-persist-step fn-bpcl-forward-result-propose-step fn-bpnp-operator-resume-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-forward-result-persist-step
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-forward-result-persist-step st epoch op result))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpcl-routed-start fn-bpcl-attempt-persist-step fn-bpcl-forward-result-propose-step fn-bpcl-operator-resume-step fn-bpnp-forward-result-persist-step) (theory 'minimal-theory))))))

(local (defthm fn-bpcl-preserve-runtime-answer
 (implies (true-listp (fn-bpnf-answer-state answer))
 (true-listp (fn-bpnf-answer-state (fn-bpnp-preserve-runtime-answer answer st recovery))))
 :hints (("Goal" :in-theory (e/d (fn-bpnp-preserve-runtime-answer) (fn-bpnp-with-runtime))))))

(defthm fn-bpnp-step-preserves-current-list
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnp-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpcl-answer-state fn-bpcl-state-constructor fn-bpcl-writers fn-bpcl-update-list true-listp-update-nth (:e true-listp) (:e equal) car-cons cdr-cons fn-bpcl-deliver-step fn-bpcl-deliver-result-step fn-bpcl-persist-delivery-step fn-bpcl-recover-fnbs-step fn-bpcl-foundation-step fn-bpcl-family-propose-step fn-bpcl-family-persist-step fn-bpcl-job-propose-step fn-bpcl-job-persist-step fn-bpcl-fragment-step fn-bpcl-delete-propose-step fn-bpcl-delete-persist-step fn-bpcl-report-step fn-bpcl-queue-step fn-bpcl-report-author-step fn-bpcl-credit-refusal fn-bpcl-delegate-with-credit fn-bpcl-transit-dispatch-step fn-bpcl-progress-step fn-bpcl-dispatch-persist-step fn-bpcl-clock-domain-fence fn-bpcl-conflict-propose-step fn-bpcl-rotate-step fn-bpcl-rotation-persist-step fn-bpcl-busy-delivery-step fn-bpcl-deferral-persist-step fn-bpcl-busy-resume-step fn-bpcl-conflict-persist-step fn-bpcl-start-one fn-bpcl-routed-start fn-bpcl-attempt-persist-step fn-bpcl-forward-result-propose-step fn-bpcl-operator-resume-step fn-bpcl-forward-result-persist-step fn-bpnp-step fn-bpcl-preserve-runtime-answer) (theory 'minimal-theory)))))

(local (defthm fn-bpcl-job-with-base
 (implies (true-listp st) (true-listp (fn-bpnj-with-base st b)))
 :hints (("Goal" :in-theory (enable fn-bpnj-with-base)))))

(defthm fn-bpnj-step-preserves-current-list
 (implies (true-listp st) (true-listp (fn-bpnf-answer-state (fn-bpnj-step st event))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories
 '(fn-bpnj-step fn-bpnj-result-step fn-bpnj-contact-job-step
   fn-bpcl-job-with-base fn-bpcl-answer-state fn-bpnp-step-preserves-current-list
   (:e equal)) (theory 'minimal-theory)))) :rule-classes nil)
