; The K4 node correspondence at the host's reopen (PKT-087).
;
; host/store-node-host.lisp:180 (fn-store-sn-recover) and
; host/owner-host.lisp:178 (fn-owner-recover) open every process through
; fn-cpo-open-observed, whose node is the configured replay's: fn-cpr-replay
; interleaves the configuration journal with the Store journal.  The K4
; statements about the node (the node conjunct of
; fn-sn-open-observed-success-exact-history, fn-snt-relation in
; fn-sn-open-observed-success-has-live-history-relation, and the BP
; receipt-regeneration theorem that runs fn-snrt-run from the opened node)
; are stated over fn-sn-open-observed, whose node is the fixed-table replay
; fn-replay under one group table and capacity.  books/store-open-bridge
; carried the kernel conjuncts and left these three.
;
; THE CORRESPONDENCE.  When every configuration record names transaction 0
; (fn-sonb-configured-before-eventsp: the store was configured before its
; first Store event and never reconfigured after one; a fresh store's
; initial record is at txid 0, host/config-host.lisp fn-cfg-host-initial-octets),
; the configured replay is the fixed-table replay under the final
; configuration's allocation domain and capacity, node for node
; (fn-sonb-configured-replay-is-fixed-table-replay).  The configuration
; records then all precede the first event, each one rebuilds the initial
; node over its own domain and capacity (fn-sonb-config-step-keeps-initial-cnode),
; and every Store event step of fn-cpr-loop is the fn-replay-loop step on
; the same node (fn-sonb-cpr-events-loop-is-replay-loop; the served-group
; check only adds refusals).  Under that hypothesis the host's opened state
; satisfies fn-snt-relation, and the three statements hold at the host's call.
;
; Without the hypothesis, the node conjunct holds against the configured
; replay (fn-sn-open-observed-success-configured-node-of-host-open) and the
; host-side relation is fn-cst-relation (fn-cst-open-success-has-historical-relation,
; books/config-store-traces).  A history reconfigured after an event is not
; covered here; the test book shows one whose host open succeeds and whose
; fixed-table replay under the final configuration refuses.
(in-package "ACL2")
(include-book "store-open-bridge")
(include-book "config-store-traces")

; Every configuration record names transaction 0, and the journal is a true
; list.  A configuration at the same txid precedes the event
; (fn-cpr-config-firstp), so these records are all replayed before any event.
(defun fn-sonb-configured-before-eventsp (configs)
  (declare (xargs :guard t))
  (if (consp configs)
      (and (equal (fn-cfg-record-txid (car configs)) 0)
           (fn-sonb-configured-before-eventsp (cdr configs)))
    (null configs)))

; The configured node is the fixed-table initial node of its own configuration.
(defun fn-sonb-initial-cnodep (cn)
  (declare (xargs :guard t))
  (equal (fn-cnode-node cn)
         (fn-node-initial-state (fn-cnode-domain-of (fn-cnode-config cn))
                                (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))))

(local (defun fn-sonb-events-induct (cn events es)
  (declare (xargs :measure (len events)))
  (if (consp events)
      (fn-sonb-events-induct (fn-cpr-apply-event cn (car events)) (cdr events)
                             (+ 1 (nfix es)))
    (list cn es))))

; With no configuration left, each step of the configured fold is the
; fixed-table fold's step on the same node, and the configuration is kept.
(defthm fn-sonb-cpr-events-loop-is-replay-loop
  (implies (and (natp es)
                (equal (fn-replay-result-kind (fn-cpr-loop cn nil events cs es)) :ok))
           (let ((final (fn-replay-result-node (fn-cpr-loop cn nil events cs es))))
             (and (fn-replay-okp (fn-replay-loop (fn-cnode-node cn) events es))
                  (equal (fn-replay-result-node
                          (fn-replay-loop (fn-cnode-node cn) events es))
                         (fn-cnode-node final))
                  (equal (fn-cnode-config final) (fn-cnode-config cn)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sonb-events-induct cn events es)
           :in-theory (e/d (fn-cpr-loop fn-replay-loop fn-cpr-apply-event
                            fn-cpr-config-firstp fn-replay-okp fn-cnode-statep)
                           (fn-replay-apply-record fn-cpr-event-servedp
                            fn-store-event-p fn-node-statep)))))

(local (defthm fn-sonb-next-number-of-initial-nexts
  (or (equal (fn-next-number n (fn-initial-nexts d)) 1)
      (equal (fn-next-number n (fn-initial-nexts d)) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-next-number fn-initial-nexts)))))

(local (defthm fn-sonb-extend-nexts-of-initial-nexts
  (equal (fn-cnode-extend-nexts names (fn-initial-nexts d))
         (fn-initial-nexts names))
  :hints (("Goal" :induct (len names)
           :in-theory (enable fn-initial-nexts fn-cnode-extend-nexts))
          ("Subgoal *1/1" :use ((:instance fn-sonb-next-number-of-initial-nexts
                                           (n (car names))))))))

; A configuration record applied at txid 0 to an initial configured node
; leaves the initial node of the new configuration.
(defthm fn-sonb-config-step-keeps-initial-cnode
  (implies (fn-sonb-initial-cnodep cn)
           (fn-sonb-initial-cnodep
            (fn-cnode-apply-config
             (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) 0)
                            (fn-cnode-config cn))
             record ceiling)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config fn-replay-advance-txid
                                   fn-node-initial-state fn-initial-state
                                   fn-retain-initial-state)
                                  (fn-cnode-statep fn-node-statep
                                   fn-cnode-record-acceptablep
                                   fn-cnode-domain-of fn-cfg-apply-record)))))

(local (defthm fn-sonb-cpr-loop-improper-configs-fault
  (implies (and (not (consp configs)) configs)
           (not (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)))
  :hints (("Goal" :induct (fn-sonb-events-induct cn events es)
           :in-theory (e/d (fn-cpr-loop fn-cpr-config-firstp)
                           (fn-cpr-apply-event fn-cnode-statep fn-store-event-p))))))

(local (defun fn-sonb-configs-induct (cn configs cs)
  (if (consp configs)
      (fn-sonb-configs-induct
       (fn-cnode-apply-config
        (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) 0) (fn-cnode-config cn))
        (car configs) (fn-cnode-line-ceiling))
       (cdr configs) (+ 1 (nfix cs)))
    (list cn cs))))

(local (defthm fn-sonb-cpr-loop-config-step
  (implies (and (consp configs)
                (equal (fn-cfg-record-txid (car configs)) 0)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (equal (fn-cpr-loop cn configs events cs es)
                  (fn-cpr-loop
                   (fn-cnode-apply-config
                    (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) 0)
                                   (fn-cnode-config cn))
                    (car configs) (fn-cnode-line-ceiling))
                   (cdr configs) events (+ 1 (nfix cs)) es)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es))
           :in-theory (e/d (fn-cpr-config-firstp)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-txid fn-replay-advance-okp))))))

(local (defthm fn-sonb-cpr-loop-no-configs
  (implies (and (not (consp configs))
                (fn-sonb-initial-cnodep cn)
                (natp es)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (let* ((final (fn-replay-result-node (fn-cpr-loop cn configs events cs es)))
                  (init (fn-node-initial-state
                         (fn-cnode-domain-of (fn-cnode-config final))
                         (fn-cfg-capacity (fn-cfg-value (fn-cnode-config final))))))
             (and (fn-replay-okp (fn-replay-loop init events es))
                  (equal (fn-replay-result-node (fn-replay-loop init events es))
                         (fn-cnode-node final)))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal configs nil))
           :in-theory (e/d (fn-sonb-initial-cnodep)
                           (fn-cnode-statep fn-cpr-loop fn-replay-loop fn-replay-okp
                            fn-node-initial-state fn-cnode-domain-of))
           :use ((:instance fn-sonb-cpr-events-loop-is-replay-loop)
                 (:instance fn-sonb-cpr-loop-improper-configs-fault))))))

(defthm fn-sonb-cpr-loop-is-fixed-table-replay-loop
  (implies (and (fn-sonb-configured-before-eventsp configs)
                (fn-sonb-initial-cnodep cn)
                (natp es)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (let* ((final (fn-replay-result-node (fn-cpr-loop cn configs events cs es)))
                  (init (fn-node-initial-state
                         (fn-cnode-domain-of (fn-cnode-config final))
                         (fn-cfg-capacity (fn-cfg-value (fn-cnode-config final))))))
             (and (fn-replay-okp (fn-replay-loop init events es))
                  (equal (fn-replay-result-node (fn-replay-loop init events es))
                         (fn-cnode-node final)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sonb-configs-induct cn configs cs)
           :in-theory (e/d ()
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-replay-loop fn-replay-okp fn-node-initial-state
                            fn-sonb-initial-cnodep fn-replay-advance-txid fn-cpr-loop
                            fn-replay-advance-okp fn-cnode-domain-of)))
          ("Subgoal *1/1" :use ((:instance fn-sonb-config-step-keeps-initial-cnode
                                 (record (car configs)) (ceiling (fn-cnode-line-ceiling)))
                                (:instance fn-sonb-cpr-loop-config-step)))
          ("Subgoal *1/2" :use ((:instance fn-sonb-cpr-loop-no-configs)))))

; =============================================================================
; The configured replay against the fixed-table replay.

(local (defthm fn-sonb-replay-loop-ok-has-node-state
  (implies (fn-replay-okp (fn-replay-loop node events es))
           (fn-node-statep node))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-replay-loop node events es))
           :in-theory (disable fn-node-statep fn-replay-apply-record fn-replay-okp)))))
(defthm fn-sonb-configured-replay-is-fixed-table-replay
  (implies (and (fn-sonb-configured-before-eventsp configs)
                (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
           (let* ((cn (fn-replay-result-node (fn-cpr-replay configs events)))
                  (answer (fn-replay (fn-cnode-domain-of (fn-cnode-config cn))
                                     (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))
                                     events)))
             (and (fn-replay-okp answer)
                  (equal (fn-replay-result-node answer) (fn-cnode-node cn)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sonb-cpr-loop-is-fixed-table-replay-loop
                            (cn (fn-cnode-initial (fn-cfg-initial))) (cs 0) (es 0))
                 (:instance fn-sonb-replay-loop-ok-has-node-state
                            (es 0)
                            (node (fn-node-initial-state
                                   (fn-cnode-domain-of
                                    (fn-cnode-config
                                     (fn-replay-result-node (fn-cpr-replay configs events))))
                                   (fn-cfg-capacity
                                    (fn-cfg-value
                                     (fn-cnode-config
                                      (fn-replay-result-node (fn-cpr-replay configs events)))))))))
           :in-theory (e/d (fn-cpr-replay fn-replay fn-sonb-initial-cnodep fn-cnode-initial)
                           (fn-cpr-loop fn-replay-loop fn-replay-okp fn-node-statep
                            fn-node-initial-state fn-cnode-domain-of fn-cfg-initial)))))
(defthm fn-sonb-configured-node-is-fixed-table-node
  (implies (and (fn-sonb-configured-before-eventsp configs)
                (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
           (let ((cn (fn-replay-result-node (fn-cpr-replay configs events))))
             (equal (fn-cst-replay-node configs events frontier)
                    (fn-sf-replay-node (fn-cnode-domain-of (fn-cnode-config cn))
                                       (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))
                                       events frontier))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sonb-configured-replay-is-fixed-table-replay
                 fn-cpr-replay-ok-is-configured)
           :in-theory (e/d (fn-cst-replay-node fn-sf-replay-node)
                           (fn-cpr-replay fn-replay fn-replay-okp fn-cnode-statep
                            fn-cnode-domain-of fn-replay-advance-okp fn-replay-advance-txid
                            fn-cpr-replay-ok-is-configured)))))

; =============================================================================
; The node at the host's call.
;
; Unconditionally: the host's node is the configured replay's node advanced to
; the frontier (the conjunct fn-sn-open-observed-success-exact-history states
; against fn-sf-replay-node, restated against the replay the host runs).
(defthm fn-sn-open-observed-success-configured-node-of-host-open
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sn-node (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                  (fn-cst-replay-node configs events frontier)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-cpo-open-success-exact-image fn-cpo-open-success-has-historical-relation)
           :in-theory (e/d (fn-cst-replay-node fn-cpo-history-relation)
                           (fn-cpo-open-observed fn-cpr-replay fn-sn-statep fn-cnode-statep
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cpo-open-success-has-historical-relation
                            fn-cpo-open-observed-success-has-history-relation)))))

(local (defthm fn-sonb-host-open-configured-facts
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (let ((st (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                 (cn (fn-replay-result-node (fn-cpr-replay configs events))))
             (and (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
                  (equal (fn-sn-groups st) (fn-cnode-domain-of (fn-cnode-config cn)))
                  (equal (fn-sn-capacity st)
                         (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))
                  (equal (fn-sf-records (fn-sn-files st)) events)
                  (equal (fn-sf-frontier (fn-sn-files st)) frontier)
                  (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                  (fn-sn-statep st))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-cpo-open-success-exact-image fn-cpo-open-success-has-historical-relation
                 fn-sob-cpo-open-ok-facts)
           :in-theory (e/d (fn-cpo-history-relation fn-cnode-domain)
                           (fn-cpo-open-observed fn-cpr-replay fn-sn-statep fn-cnode-statep
                            fn-cnode-domain-of
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cpo-open-success-has-historical-relation
                            fn-cpo-open-observed-success-has-history-relation))))))

; Before any reconfiguration: the node conjunct of
; fn-sn-open-observed-success-exact-history at the host's call, against the
; fixed-table replay under the opened state's own groups and capacity.
(defthm fn-sn-open-observed-success-exact-history-node-of-host-open
  (implies (and (fn-sonb-configured-before-eventsp configs)
                (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
           (let ((st (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
             (equal (fn-sn-node st)
                    (fn-sf-replay-node (fn-sn-groups st) (fn-sn-capacity st)
                                       events frontier))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sonb-host-open-configured-facts
                 fn-sn-open-observed-success-configured-node-of-host-open
                 fn-sonb-configured-node-is-fixed-table-node)
           :in-theory (disable fn-cpo-open-observed fn-cpr-replay fn-sn-statep
                               fn-cst-replay-node fn-sf-replay-node fn-cnode-domain-of))))

; fn-sn-open-observed-success-has-live-history-relation at the host's call:
; the host's opened state satisfies fn-snt-relation, so
; fn-snrt-mixed-trace-preserves-live-history-relation and its consequences
; hold from the state the host actually starts in.
(local (defthm fn-sonb-configured-before-events-is-true-list
  (implies (fn-sonb-configured-before-eventsp configs) (true-listp configs))
  :rule-classes nil))
(local (defthm fn-sonb-cst-relation-recoverable
  (implies (fn-cst-relation st)
           (fn-cst-recoverablep (fn-sn-config-history st)
                                (fn-sf-records (fn-sn-files st))
                                (fn-sf-frontier (fn-sn-files st))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cst-relation)))))
(defthm fn-sn-open-observed-success-has-live-history-relation-of-host-open
  (implies (and (fn-sonb-configured-before-eventsp configs)
                (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
           (fn-snt-relation (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
  :hints (("Goal"
           :use (fn-sonb-host-open-configured-facts
                 fn-sn-open-observed-success-configured-node-of-host-open
                 fn-sn-open-observed-success-exact-history-node-of-host-open
                 fn-sonb-configured-before-events-is-true-list
                 fn-cst-open-success-has-historical-relation
                 fn-cpo-open-success-exact-image
                 (:instance fn-sonb-cst-relation-recoverable
                            (st (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))))
           :in-theory (union-theories '(fn-snt-relation fn-sf-history-recoverablep
                                        fn-snt-idle-phasep fn-cst-recoverablep
                                        (:e member-equal))
                                      (theory 'minimal-theory)))))

; =============================================================================
; fn-bpr-live-receipt-regenerated-after-restart at the host's call.  The
; restart reopens through fn-cpo-open-observed on the configuration journal
; the host reads; the added hypotheses are fn-sob-configured-openp (the
; configuration journal replays and accepts the frontier) and
; fn-sonb-configured-before-eventsp.  The proof is the keystone's, with the
; reopen facts below in place of fn-bprv-observed-reopen-facts.

; The BP book's own local theory for these proofs.
(local (in-theory (disable fn-snt-relation fn-snt-step fn-snt-run fn-snrt-step fn-snrt-run
                           fn-sf-prefixp fn-sf-crash-imagep fn-sn-open-observed
                           fn-sn-open-okp fn-sn-open-state fn-sf-replay-node
                           fn-sf-history-recoverablep fn-node-statep fn-statep
                           fn-bprv-history fn-bprv-phase fn-bprv-history-relationalp
                           fn-bprv-evolving-invariantp fn-bprv-entries-decidedp
                           fn-bprv-contexts-groundedp fn-bprv-context-groundedp
                           fn-bpi-node-record-committedp
                           fn-sn-observed-configurationp fn-sn-observed-historyp
                           fn-cpo-open-observed fn-sob-configured-openp
                           fn-sonb-configured-before-eventsp)))
(local (defthm fn-sonb-full-relation-has-store-relation
  (implies (fn-csi-full-relationp s) (fn-snt-relation s))
  :hints (("Goal" :in-theory (enable fn-csi-full-relationp)))))
(local (in-theory (disable fn-sn-observed-topic-okp fn-sn-observed-identity-okp
                           fn-csi-full-relationp)))

(defthm fn-bprv-observed-reopen-facts-of-host-open
  (implies (and (fn-csi-full-relationp s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                (fn-sn-observed-identity-okp records)
                (fn-sn-observed-topic-okp records)
                (fn-sob-configured-openp configs frontier records)
                (fn-sonb-configured-before-eventsp configs))
           (let ((opened (fn-cpo-open-observed configs frontier records)))
             (and (fn-sn-open-okp opened)
                  (fn-snt-relation (fn-sn-open-state opened))
                  (equal (fn-bprv-history (fn-sn-open-state opened)) records)
                  (fn-bprv-extendsp s (fn-sn-open-state opened)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bprv-observed-reopen-facts)
                 (:instance fn-cpo-open-observed-is-sn-open-observed-on-the-kernel
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (events records))
                 (:instance fn-sn-open-observed-success-has-live-history-relation-of-host-open
                            (events records)))
           :in-theory (e/d (fn-bprv-extendsp fn-bprv-history)
                           (fn-bprv-observed-reopen-facts fn-cpo-open-observed
                            fn-sn-open-observed fn-snt-relation fn-sn-open-okp
                            fn-sob-configured-openp fn-csi-full-relationp
                            fn-sf-crash-imagep fn-sf-prefixp
                            fn-sn-open-observed-success-has-live-history-relation-of-host-open)))))

; The keystone's argument over any opened Store the relation holds of and
; whose history extends the crashed one: the restart's recovery trace keeps
; the relation, the receiver journal replays to the live state against the
; ready probe, and the ADU is a query of that state.
(defthm fn-sonb-live-receipt-regenerated-from-related-open
  (let* ((final (fn-bpr-live-run live events))
         (probe (fn-snrt-run o recovery-events))
         (installed (fn-bpr-live-install probe (caddr final))))
    (implies (and (fn-csi-full-relationp (car live))
                  (equal (fn-bprr-replay (car live) (caddr live)) (list t (cadr live)))
                  (fn-snt-relation o)
                  (fn-bprv-extendsp (car final) o)
                  (equal (fn-bprv-phase probe) :ready))
             (and (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpr-live-run-preserves-store-relation)
                 (:instance fn-bpr-live-run-extends-history)
                 (:instance fn-bpr-live-state-is-replay-of-journal
                            (probe (fn-snrt-run o recovery-events)))
                 (:instance fn-bprv-replay-agrees-at-ready-extension
                            (s1 (car live)) (s2 (fn-snrt-run o recovery-events))
                            (records (caddr live)))
                 (:instance fn-bprv-snrt-run-extends-history (s o) (events recovery-events))
                 (:instance fn-snrt-mixed-trace-preserves-live-history-relation
                            (s o) (events recovery-events))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car (fn-bpr-live-run live events))) (b o)
                            (c (fn-snrt-run o recovery-events)))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car live)) (b (car (fn-bpr-live-run live events)))
                            (c (fn-snrt-run o recovery-events))))
           :in-theory (union-theories '(fn-bpr-live-install fn-sonb-full-relation-has-store-relation fn-bprv-extendsp
                                        car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

(defthm fn-bpr-live-receipt-regenerated-after-restart-of-host-open
  (let* ((final (fn-bpr-live-run live events))
         (opened (fn-cpo-open-observed configs frontier records))
         (probe (fn-snrt-run (fn-sn-open-state opened) recovery-events))
         (installed (fn-bpr-live-install probe (caddr final))))
    (implies (and (fn-csi-full-relationp (car live))
                  (equal (fn-bprr-replay (car live) (caddr live)) (list t (cadr live)))
                  (fn-sf-crash-imagep (fn-sn-files (car final)) frontier records)
                  (fn-sn-observed-identity-okp records)
                  (fn-sn-observed-topic-okp records)
                  (fn-sob-configured-openp configs frontier records)
                  (fn-sonb-configured-before-eventsp configs)
                  (equal (fn-bprv-phase probe) :ready))
             (and (fn-sn-open-okp opened)
                  (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bprv-observed-reopen-facts-of-host-open
                            (s (car (fn-bpr-live-run live events))))
                 (:instance fn-bpr-live-run-preserves-consumer-full-relation)
                 (:instance fn-sonb-live-receipt-regenerated-from-related-open
                            (o (fn-sn-open-state (fn-cpo-open-observed configs frontier records)))))
           :in-theory (theory 'minimal-theory))))
