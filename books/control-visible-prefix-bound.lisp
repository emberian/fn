; The captured ready Store's actual replay relation gives the strict-past
; premise of the existing later-configuration withdrawal law. Proof-only:
; neither a served history scan nor a replacement source predicate.
(in-package "ACL2")
(include-book "control-visible")
(include-book "store-node-traces-prepare")

(local
 (defthm fn-ctl-selected-record-is-in-history
   (implies (fn-ctl-row-event msgid records)
            (member-equal (fn-ctl-row-event msgid records) records))
   :hints (("Goal" :induct (fn-ctl-row-event msgid records)
            :in-theory (e/d (fn-ctl-row-event)
                            (fn-ctl-event-row fn-record-msgid))))))

(local
 (defthm fn-ctl-record-list-member-below-frontier
   (implies (and (fn-sf-record-listp records sequence lower frontier)
                 (member-equal event records))
            (< (nfix (fn-store-event-txid event)) frontier))
   :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
            :in-theory (e/d (fn-sf-record-listp)
                            (fn-store-event-p fn-store-event-txid
                             fn-store-event-sequence fn-store-event-generation))))))

(defthm fn-ctl-archive-entries-below-record-frontier
  (implies (and (natp frontier)
                (fn-sf-record-listp records sequence lower frontier))
           (fn-ctl-entries-below-p
            (fn-ctl-archive-entries articles verdicts records) frontier))
  :hints (("Goal" :induct (fn-ctl-archive-entries articles verdicts records)
           :in-theory (e/d (fn-ctl-archive-entries fn-ctl-entries-below-p
                            fn-ctl-control-target fn-ctl-at)
                           (nfix fn-sf-record-listp fn-ctl-row-event fn-ctl-event-row
                            fn-held-facts fn-hf-control fn-store-event-txid
                            fn-article-msgid fn-ctl-lookup-verdict
                            fn-ctl-control-keys fn-ctl-control-locks
                            fn-ctl-row-control)))))

(defthm fn-ctl-ready-store-control-entries-are-strictly-past
  (implies (and (fn-snt-relation store)
                (equal (fn-sf-phase (fn-sn-files store)) :ready))
           (fn-ctl-entries-below-p
            (fn-ctl-archive-entries
             articles verdicts (fn-sf-records (fn-sn-files store)))
            (fn-state-next-txid (fn-node-acceptance (fn-sn-node store)))))
  :hints (("Goal"
           :use ((:instance fn-ctl-archive-entries-below-record-frontier
                    (records (fn-sf-records (fn-sn-files store)))
                    (sequence 0) (lower 0)
                    (frontier (fn-sf-frontier (fn-sn-files store)))))
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep fn-sn-statep
                            fn-sf-statep fn-sf-history-recoverablep)
                           (fn-ctl-archive-entries-below-record-frontier
                            fn-ctl-archive-entries fn-ctl-entries-below-p
                            fn-sf-replay-node fn-sf-record-listp
                            fn-node-statep fn-node-acceptance fn-state-next-txid
                            fn-sn-node fn-sn-files fn-sf-records fn-sf-phase
                            fn-sf-frontier)))))

(defthm fn-ctl-ready-store-later-config-preserves-withdrawals
  (implies (and (fn-snt-relation store)
                (equal (fn-sf-phase (fn-sn-files store)) :ready)
                (equal (fn-cfg-record-txid record)
                       (fn-state-next-txid
                        (fn-node-acceptance (fn-sn-node store)))))
           (equal
            (fn-ctl-journal-withdrawals
             (fn-ctl-archive-entries articles verdicts
                                     (fn-sf-records (fn-sn-files store)))
             (append configs (list record)))
            (fn-ctl-journal-withdrawals
             (fn-ctl-archive-entries articles verdicts
                                     (fn-sf-records (fn-sn-files store)))
             configs)))
  :hints (("Goal"
           :use ((:instance fn-ctl-ready-store-control-entries-are-strictly-past)
                 (:instance fn-ctl-revoke-changes-decisions-not-records
                    (entries (fn-ctl-archive-entries articles verdicts
                               (fn-sf-records (fn-sn-files store))))
                    (more (list record))))
           :in-theory (disable fn-ctl-ready-store-control-entries-are-strictly-past
                                fn-ctl-revoke-changes-decisions-not-records
                                fn-ctl-journal-withdrawals fn-ctl-archive-entries
                                fn-ctl-entries-below-p fn-snt-relation
                                fn-sn-files fn-sf-phase fn-sf-records
                                fn-cfg-record-txid fn-state-next-txid
                                fn-node-acceptance fn-sn-node))))
