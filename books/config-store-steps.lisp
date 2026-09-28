; fn: the configured Store relation across the commit's store steps
; (lane control-quanta-2, 2026-09-27; PKT-827 (c)).
;
; This book shares the prefix `fn-cstp-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config-store-traces")
(include-book "store-prepare-correspondence")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-cpr-config-firstp-has-config))))

; Two rules that backchain into the consumer-id recognizer on every
; `true-listp' and `len' (the note in books/store-node-traces-prepare.lisp).
(local (in-theory (disable fn-cp-idp-true-listp fn-cp-id-length-bound)))
(defun fn-cstp-idlep (node)
  (declare (xargs :guard t))
  (and (null (fn-node-stage node))
       (null (fn-state-pending (fn-node-acceptance node)))
       (equal (fn-state-fenced (fn-node-acceptance node)) nil)))

(defthm fn-cstp-apply-config-keeps-idle-and-txid
  (implies (fn-cstp-idlep (fn-cnode-node cn))
           (and (fn-cstp-idlep (fn-cnode-node (fn-cnode-apply-config cn record ceiling)))
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-cnode-node (fn-cnode-apply-config cn record ceiling))))
                       (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn))))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config)
                                  (fn-cnode-statep fn-cnode-record-acceptablep
                                   fn-cnode-carried-acceptablep)))))
(defthm fn-cstp-advance-idle-at
  (implies (fn-replay-advance-okp node txid)
           (and (fn-cstp-idlep (fn-replay-advance-txid node txid))
                (equal (fn-state-next-txid
                        (fn-node-acceptance (fn-replay-advance-txid node txid)))
                       txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid fn-replay-advance-okp))))

(in-theory (disable fn-cstp-idlep))

(defthm fn-cstp-apply-event-idle
  (implies (and (fn-cstp-idlep (fn-cnode-node cn))
                (consp (fn-cpr-apply-event cn event)))
           (fn-cstp-idlep (fn-cnode-node (fn-cpr-apply-event cn event))))
  :hints (("Goal" :use ((:instance fn-snt-apply-event-from-idle-is-idle-and-monotone
                                   (node (fn-cnode-node cn)) (record event)))
           :in-theory (e/d (fn-cpr-apply-event fn-cnode-statep fn-cstp-idlep)
                           (fn-snt-apply-event-from-idle-is-idle-and-monotone
                            fn-replay-apply-record fn-node-statep fn-store-event-p
                            fn-cpr-event-servedp)))))

(defthm fn-cstp-apply-event-monotone
  (implies (and (fn-cstp-idlep (fn-cnode-node cn))
                (consp (fn-cpr-apply-event cn event)))
           (<= (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn)))
               (fn-state-next-txid
                (fn-node-acceptance (fn-cnode-node (fn-cpr-apply-event cn event))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-snt-apply-event-from-idle-is-idle-and-monotone
                                   (node (fn-cnode-node cn)) (record event)))
           :in-theory (e/d (fn-cpr-apply-event fn-cnode-statep fn-cstp-idlep)
                           (fn-snt-apply-event-from-idle-is-idle-and-monotone
                            fn-replay-apply-record fn-node-statep fn-store-event-p
                            fn-cpr-event-servedp)))))
(defthm fn-cstp-advance-okp-bound
  (implies (fn-replay-advance-okp node txid)
           (<= (fn-state-next-txid (fn-node-acceptance node)) txid))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))
(defthm fn-cstp-loop-idle-monotone
  (implies (and (fn-cstp-idlep (fn-cnode-node cn))
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (and (fn-cstp-idlep (fn-cnode-node (fn-replay-result-node
                                                (fn-cpr-loop cn configs events cs es))))
                (<= (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn)))
                    (fn-state-next-txid
                     (fn-node-acceptance
                      (fn-cnode-node (fn-replay-result-node
                                      (fn-cpr-loop cn configs events cs es))))))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cs es)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cnode-carried-acceptablep fn-cpr-config-firstp)))))
(defun fn-cstp-configs-at-most (configs bound)
  ; Every configuration record's transaction id is at most BOUND.
  (declare (xargs :guard t))
  (if (consp configs)
      (and (<= (nfix (fn-cfg-record-txid (car configs))) (nfix bound))
           (fn-cstp-configs-at-most (cdr configs) bound))
    t))

(defthm fn-cstp-configs-at-most-weaken
  (implies (and (fn-cstp-configs-at-most configs a)
                (<= (nfix a) (nfix b)))
           (fn-cstp-configs-at-most configs b)))
(defthm fn-cstp-loop-txid-monotone
  (implies (and (fn-cstp-idlep (fn-cnode-node cn))
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (<= (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn)))
               (fn-state-next-txid
                (fn-node-acceptance
                 (fn-cnode-node (fn-replay-result-node
                                 (fn-cpr-loop cn configs events cs es)))))))
  :rule-classes :linear
  :hints (("Goal" :use fn-cstp-loop-idle-monotone
           :in-theory (disable fn-cstp-loop-idle-monotone fn-cpr-loop))))
(defthm fn-cstp-cnode-next-txid-natp
  (implies (fn-cnode-statep cn)
           (natp (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn)))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-cnode-statep fn-node-statep fn-statep))))

(defthm fn-cstp-advance-okp-natp
  (implies (fn-replay-advance-okp node txid) (natp txid))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))

(defthm fn-cstp-loop-ok-next-txid-natp
  (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
           (natp (fn-state-next-txid
                  (fn-node-acceptance
                   (fn-cnode-node (fn-replay-result-node
                                   (fn-cpr-loop cn configs events cs es)))))))
  :rule-classes
  ((:rewrite :corollary
    (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
             (integerp (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-cnode-node (fn-replay-result-node
                                         (fn-cpr-loop cn configs events cs es))))))))
   (:linear :corollary
    (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
             (<= 0 (fn-state-next-txid
                    (fn-node-acceptance
                     (fn-cnode-node (fn-replay-result-node
                                     (fn-cpr-loop cn configs events cs es)))))))))
  :hints (("Goal" :use ((:instance fn-cpr-loop-ok-is-configured (config-sequence cs) (event-sequence es)) (:instance fn-cstp-cnode-next-txid-natp (cn (fn-replay-result-node (fn-cpr-loop cn configs events cs es)))))
           :in-theory (disable fn-cpr-loop fn-cpr-loop-ok-is-configured fn-cstp-cnode-next-txid-natp fn-cnode-statep))))
(defthm fn-cstp-loop-configs-at-most-final
  (implies (and (fn-cstp-idlep (fn-cnode-node cn))
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (fn-cstp-configs-at-most
            configs
            (fn-state-next-txid
             (fn-node-acceptance
              (fn-cnode-node (fn-replay-result-node
                              (fn-cpr-loop cn configs events cs es)))))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cs es)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cnode-carried-acceptablep fn-cpr-config-firstp)))))
(defthm fn-cstp-cpr-loop-append-event
  (implies (and (true-listp configs) (true-listp events)
                (natp cs) (natp es)
                (fn-cstp-configs-at-most configs (fn-store-event-txid event)))
           (equal (fn-cpr-loop cn configs (append events (list event)) cs es)
                  (let ((mid (fn-cpr-loop cn configs events cs es)))
                    (if (equal (fn-replay-result-kind mid) :ok)
                        (fn-cpr-loop (fn-replay-result-node mid) nil (list event)
                                     (+ cs (len configs)) (+ es (len events)))
                      mid))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cs es)
           :in-theory (e/d (fn-cpr-loop fn-cpr-config-firstp)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cnode-carried-acceptablep fn-cp-idp fn-cp-idp-true-listp fn-cp-id-length-bound
                            (:type-prescription fn-replay-record-counters-are-natural . 2))))))
(defthm fn-cstp-initial-idle
  (fn-cstp-idlep (fn-cnode-node (fn-cnode-initial config)))
  :hints (("Goal" :in-theory (enable fn-cstp-idlep fn-cnode-initial fn-node-initial-state
                                     fn-initial-state))))

; The fold's configured node, and what recoverability at a frontier says of it.
(defun fn-cstp-fold (configs events)
  ; Proof vocabulary: the configured node the fold computes.
  (declare (xargs :guard t :verify-guards nil))
  (fn-replay-result-node (fn-cpr-replay configs events)))

(defthm fn-cstp-recoverable-facts
  (implies (fn-cst-recoverablep configs events frontier)
           (and (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
                (fn-cnode-statep (fn-cstp-fold configs events))
                (fn-cstp-idlep (fn-cnode-node (fn-cstp-fold configs events)))
                (fn-replay-advance-okp (fn-cnode-node (fn-cstp-fold configs events))
                                       frontier)
                (equal (fn-cst-replay-node configs events frontier)
                       (fn-replay-advance-txid (fn-cnode-node (fn-cstp-fold configs events))
                                               frontier))
                (fn-cstp-configs-at-most configs frontier)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-loop-idle-monotone
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (cs 0) (es 0))
                 (:instance fn-cstp-loop-configs-at-most-final
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (cs 0) (es 0))
                 (:instance fn-cstp-configs-at-most-weaken
                            (a (fn-state-next-txid
                                (fn-node-acceptance
                                 (fn-cnode-node (fn-cstp-fold configs events)))))
                            (b frontier)))
           :in-theory (e/d (fn-cst-recoverablep fn-cst-replay-node fn-cstp-fold
                            fn-cpr-replay)
                           (fn-cpr-loop fn-cnode-statep fn-replay-advance-okp
                            fn-replay-advance-txid fn-node-statep
                            fn-cstp-loop-idle-monotone fn-cstp-loop-configs-at-most-final
                            fn-cstp-configs-at-most-weaken fn-cnode-initial)))))

(defthm fn-cstp-okp-later
  (implies (and (fn-replay-advance-okp node f) (natp g) (<= f g))
           (fn-replay-advance-okp node g))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))
(defthm fn-cstp-okp-node-statep
  (implies (fn-replay-advance-okp node txid) (fn-node-statep node))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))
(defthm fn-cstp-recoverable-later
  (implies (and (fn-cst-recoverablep configs events f) (natp g) (<= f g))
           (and (fn-cst-recoverablep configs events g)
                (equal (fn-cst-replay-node configs events g)
                       (fn-replay-advance-txid (fn-cst-replay-node configs events f) g))))
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-facts (frontier f))
                 (:instance fn-snt-advance-twice
                            (node (fn-cnode-node (fn-cstp-fold configs events)))
                            (first f) (second g))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-cnode-node (fn-cstp-fold configs events)))
                            (recorded-txid g))
                 (:instance fn-cstp-advance-idle-at
                            (node (fn-cnode-node (fn-cstp-fold configs events)))
                            (txid g))
                 (:instance fn-cstp-okp-later
                            (node (fn-cnode-node (fn-cstp-fold configs events)))))
           :in-theory '(fn-cst-recoverablep fn-cst-replay-node fn-cstp-fold
                        fn-snt-advanced-node-is-consp fn-cstp-okp-node-statep))))
(defthm fn-cstp-cpr-loop-one-event
  (implies (and (fn-cnode-statep cn) (natp es))
           (equal (fn-cpr-loop cn nil (list event) cs es)
                  (cond ((not (fn-store-event-p event))
                         (fn-replay-fault cn (+ (nfix cs) es) :invalid-event))
                        ((not (equal (fn-store-event-sequence event) es))
                         (fn-replay-fault cn (+ (nfix cs) es) :event-sequence))
                        ((not (fn-cnode-statep (fn-cpr-apply-event cn event)))
                         (fn-replay-fault cn (+ (nfix cs) es) :event-refusal))
                        (t (fn-replay-ok (fn-cpr-apply-event cn event)
                                         (+ (nfix cs) (+ 1 es)))))))
  :hints (("Goal" :expand ((fn-cpr-loop cn nil (list event) cs es)
                           (:free (x a b) (fn-cpr-loop x nil nil a b)))
           :use ((:instance fn-cpr-apply-event-statep-iff-consp (cn cn) (event event)))
           :in-theory (e/d (fn-cpr-config-firstp)
                           (fn-cnode-statep fn-cpr-apply-event fn-store-event-p)))))

(defthm fn-cstp-apply-after-advance-to-its-txid
  (implies (fn-replay-advance-okp node (fn-store-event-txid event))
           (equal (fn-replay-apply-record
                   (fn-replay-advance-txid node (fn-store-event-txid event))
                   event)
                  (fn-replay-apply-record node event)))
  :hints (("Goal"
           :use ((:instance fn-snt-advance-twice
                            (first (fn-store-event-txid event))
                            (second (fn-store-event-txid event))))
           :in-theory (e/d (fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-replay-apply-identity-neutral
                            fn-replay-advance-okp)
                           (fn-replay-advance-txid fn-node-prepare
                            fn-node-complete fn-node-statep
                            fn-node-pending-matchesp
                            fn-replay-complete-retention
                            fn-replay-composite-record
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                            fn-retain-admissiblep fn-retain-admit
                            fn-retain-release fn-retain-matching-releasep
                            fn-snt-advance-twice)))))
(in-theory (disable fn-cstp-fold))

(defthm fn-cstp-replay-append-event-fold
  (implies (and (true-listp configs) (true-listp events)
                (fn-cst-recoverablep configs events txid)
                (equal (fn-store-event-txid event) txid))
           (equal (fn-cpr-replay configs (append events (list event)))
                  (fn-cpr-loop (fn-cstp-fold configs events) nil (list event)
                               (len configs) (len events))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-facts (frontier txid))
                 (:instance fn-cstp-cpr-loop-append-event
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (cs 0) (es 0)))
           :in-theory '(fn-cpr-replay fn-cstp-fold natp fix
                        (:executable-counterpart natp) (:executable-counterpart binary-+)
                        commutativity-of-+ unicity-of-0 (:type-prescription len)))))

(defthm fn-cstp-apply-event-of-fold
  (let ((base (fn-cst-replay-node configs events txid)))
    (implies (and (fn-cst-recoverablep configs events txid)
                  (fn-store-event-p event)
                  (equal (fn-store-event-txid event) txid)
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) event)
                  (fn-node-statep (fn-replay-apply-record base event)))
             (equal (fn-cpr-apply-event (fn-cstp-fold configs events) event)
                    (fn-cnode-make (fn-replay-apply-record base event)
                                   (fn-cnode-config (fn-cstp-fold configs events))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-facts (frontier txid))
                 (:instance fn-cstp-apply-after-advance-to-its-txid
                            (node (fn-cnode-node (fn-cstp-fold configs events)))))
           :in-theory '(fn-cpr-apply-event fn-snt-valid-node-is-consp))))
(defthm fn-cstp-cnode-make-consp
  (consp (fn-cnode-make node config))
  :rule-classes :type-prescription)

(defthm fn-cstp-replay-append-event-ok
  (let* ((base (fn-cst-replay-node configs events txid))
         (applied (fn-replay-apply-record base event)))
    (implies (and (true-listp configs) (true-listp events)
                  (fn-cst-recoverablep configs events txid)
                  (fn-store-event-p event)
                  (equal (fn-store-event-sequence event) (len events))
                  (equal (fn-store-event-txid event) txid)
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) event)
                  (fn-node-statep applied))
             (equal (fn-cpr-replay configs (append events (list event)))
                    (fn-replay-ok (fn-cnode-make applied
                                                 (fn-cnode-config (fn-cstp-fold configs events)))
                                  (+ (len configs) (+ 1 (len events)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-facts (frontier txid))
                 fn-cstp-replay-append-event-fold
                 fn-cstp-apply-event-of-fold
                 (:instance fn-cstp-cpr-loop-one-event
                            (cn (fn-cstp-fold configs events))
                            (cs (len configs)) (es (len events)))
                 (:instance fn-cpr-apply-event-preserves-cnode-statep
                            (cn (fn-cstp-fold configs events))))
           :in-theory '(fn-cstp-cnode-make-consp (:type-prescription len) natp nfix))))

(defthm fn-cstp-recoverable-node-idle
  (implies (fn-cst-recoverablep configs events frontier)
           (and (fn-cstp-idlep (fn-cst-replay-node configs events frontier))
                (fn-replay-advance-okp (fn-cst-replay-node configs events frontier)
                                       frontier)))
  :hints (("Goal" :use (fn-cstp-recoverable-facts
                        (:instance fn-cstp-advance-idle-at
                                   (node (fn-cnode-node (fn-cstp-fold configs events)))
                                   (txid frontier))
                        (:instance fn-replay-advance-preserves-node-statep
                                   (node (fn-cnode-node (fn-cstp-fold configs events)))
                                   (recorded-txid frontier))
                        (:instance fn-cstp-advance-okp-natp
                                   (node (fn-cnode-node (fn-cstp-fold configs events)))
                                   (txid frontier)))
           :in-theory '(fn-replay-advance-okp fn-cstp-idlep natp))))

(defthm fn-cstp-applied-at-successor
  (let* ((base (fn-cst-replay-node configs events txid))
         (applied (fn-replay-apply-record base event)))
    (implies (and (fn-cst-recoverablep configs events txid)
                  (fn-store-event-p event)
                  (fn-node-statep applied))
             (and (fn-replay-advance-okp applied (+ 1 (fn-store-event-txid event)))
                  (equal (fn-state-next-txid (fn-node-acceptance applied))
                         (+ 1 (fn-store-event-txid event)))
                  (equal (fn-replay-advance-txid applied (+ 1 (fn-store-event-txid event)))
                         applied))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-node-idle (frontier txid))
                 (:instance fn-snt-apply-event-from-idle-is-idle-and-monotone
                            (node (fn-cst-replay-node configs events txid))
                            (record event))
                 (:instance fn-snt-apply-event-from-idle-is-at-the-successor
                            (node (fn-cst-replay-node configs events txid))
                            (record event))
                 (:instance fn-snt-advance-at-current-is-identity
                            (node (fn-replay-apply-record
                                   (fn-cst-replay-node configs events txid) event))
                            (frontier (+ 1 (fn-store-event-txid event)))))
           :in-theory (e/d (fn-cst-recoverablep fn-replay-advance-okp fn-cstp-idlep)
                           (fn-cst-replay-node fn-replay-apply-record fn-node-statep
                            fn-store-event-p fn-replay-advance-txid
                            fn-snt-apply-event-from-idle-is-idle-and-monotone
                            fn-snt-apply-event-from-idle-is-at-the-successor
                            fn-snt-advance-at-current-is-identity fn-cstp-recoverable-node-idle)))))

(defthm fn-cstp-replay-append-event
  (let* ((base (fn-cst-replay-node configs events txid))
         (applied (fn-replay-apply-record base event)))
    (implies (and (true-listp configs) (true-listp events)
                  (fn-cst-recoverablep configs events txid)
                  (fn-store-event-p event)
                  (equal (fn-store-event-sequence event) (len events))
                  (equal (fn-store-event-txid event) txid)
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) event)
                  (fn-node-statep applied))
             (and (equal (fn-replay-result-kind
                          (fn-cpr-replay configs (append events (list event))))
                         :ok)
                  (equal (fn-cstp-fold configs (append events (list event)))
                         (fn-cnode-make applied
                                        (fn-cnode-config (fn-cstp-fold configs events))))
                  (equal (fn-cst-replay-node configs (append events (list event))
                                             (+ 1 txid))
                         applied)
                  (fn-cst-recoverablep configs (append events (list event))
                                       (+ 1 txid)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-cstp-replay-append-event-ok fn-cstp-applied-at-successor
                 (:instance fn-cstp-recoverable-facts (frontier txid))
                 (:instance fn-cpr-apply-event-preserves-cnode-statep
                            (cn (fn-cstp-fold configs events)))
                 fn-cstp-apply-event-of-fold)
           :in-theory '(fn-cst-recoverablep fn-cst-replay-node fn-cstp-fold
                        fn-snt-valid-node-is-consp
                        fn-replay-result-kind-of-fn-replay-ok
                        fn-replay-result-node-of-fn-replay-ok
                        fn-cnode-node-of-fn-cnode-make fn-cnode-config-of-fn-cnode-make
                        fn-cstp-cnode-make-consp))))
(defthm fn-cstp-io-fields
  (let ((s2 (fn-sn-io s operation result)))
    (and (equal (fn-sn-groups s2) (fn-sn-groups s))
         (equal (fn-sn-capacity s2) (fn-sn-capacity s))
         (equal (fn-sn-node s2) (fn-sn-node s))
         (equal (fn-sn-config-history s2) (fn-sn-config-history s))
         (equal (fn-sn-keyring-generation s2) (fn-sn-keyring-generation s))
         (equal (fn-sn-keyring-snapshots s2) (fn-sn-keyring-snapshots s))
         (equal (fn-sn-identity-next s2) (fn-sn-identity-next s))
         (equal (fn-sn-consumer s2) (fn-sn-consumer s))
         (equal (fn-sn-topic s2) (fn-sn-topic s))
         (equal (fn-sn-files s2)
                (if (fn-sn-statep s)
                    (fn-sn-file-step (fn-sn-files s) operation result)
                  (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-sn-update)
                                  (fn-sn-statep fn-sn-file-step fn-cei-put
                                   fn-store-event-sequence)))))
(defthm fn-cstp-final-configurationp-congruence
  (implies (and (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sn-groups b) (fn-sn-groups a))
                (equal (fn-sn-capacity b) (fn-sn-capacity a)))
           (equal (fn-cst-final-configurationp b) (fn-cst-final-configurationp a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cst-final-configurationp))))

; The relation across a step between two idle phases that keeps the node, the
; frontier, the durable history and the configuration.
(defthm fn-cstp-relation-idle-congruence
  (implies (and (fn-cst-relation a)
                (fn-sn-statep b)
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files a)))
                (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files b)))
                (equal (fn-sn-node b) (fn-sn-node a))
                (equal (fn-sf-frontier (fn-sn-files b)) (fn-sf-frontier (fn-sn-files a)))
                (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sn-groups b) (fn-sn-groups a))
                (equal (fn-sn-capacity b) (fn-sn-capacity a)))
           (fn-cst-relation b))
  :rule-classes nil
  :hints (("Goal" :use fn-cstp-final-configurationp-congruence
           :in-theory '(fn-cst-relation))))
(defthm fn-cstp-sn-io-no-file-change
  (implies (and (fn-sn-statep s)
                (equal (fn-sn-file-step (fn-sn-files s) operation result)
                       (fn-sn-files s))
                (not (and (eq operation :record-directory) (eq result :ok)
                          (eq (fn-sf-phase (fn-sn-files s)) :record-attempted))))
           (equal (fn-sn-io s operation result) s))
  :hints (("Goal" :use fn-snt-state-reconstruction
           :in-theory (e/d (fn-sn-io fn-sn-update)
                           (fn-sn-statep fn-sn-file-step fn-snt-state-reconstruction)))))

(defun fn-cstp-reserve-opp (operation)
  (declare (xargs :guard t))
  (member-equal operation '(:start-frontier :frontier-file :frontier-replace
                            :frontier-directory :recovery-barrier)))

; The file steps of the reservation and of the recovery barriers: each either
; changes nothing, or moves between idle phases keeping the frontier and the
; history, or (the directory's success) enters :reserved one past the frontier.
(defthm fn-cstp-reserve-file-step-cases
  (implies (and (fn-sf-statep files)
                (fn-cstp-reserve-opp operation))
           (let ((next (fn-sn-file-step files operation result)))
             (or (equal next files)
                 (and (fn-snt-idle-phasep (fn-sf-phase files))
                      (fn-snt-idle-phasep (fn-sf-phase next))
                      (equal (fn-sf-frontier next) (fn-sf-frontier files))
                      (equal (fn-sf-records next) (fn-sf-records files)))
                 (and (equal operation :frontier-directory)
                      (equal (fn-sf-phase files) :frontier-attempted)
                      (equal (fn-sf-phase next) :reserved)
                      (equal (fn-sf-frontier next) (+ 1 (fn-sf-frontier files)))
                      (equal (fn-sf-records next) (fn-sf-records files))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-snt-typed-frontier-phase))
           :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                            fn-sf-recovery-barrier fn-snt-idle-phasep fn-sf-frontier-phasep)
                           (fn-sf-statep fn-snt-typed-frontier-phase)))))
(defthm fn-cstp-statep-observed
  (implies (fn-sn-statep st)
           (fn-sn-observed-historyp (fn-sf-frontier (fn-sn-files st))
                                    (fn-sf-records (fn-sn-files st))))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sf-statep fn-sn-observed-historyp)
                                  (fn-node-statep fn-sf-record-listp fn-sf-phase-shapep
                                   fn-sf-success-listp)))))

(defthm fn-cstp-minus-one-of-successor
  (implies (acl2-numberp x) (equal (+ -1 (+ 1 x)) x)))
(defthm fn-cstp-relation-reserved-from-attempted
  (implies (and (fn-cst-relation a)
                (fn-sn-statep b)
                (equal (fn-sf-phase (fn-sn-files a)) :frontier-attempted)
                (equal (fn-sf-phase (fn-sn-files b)) :reserved)
                (equal (fn-sn-node b) (fn-sn-node a))
                (equal (fn-sf-frontier (fn-sn-files b)) (+ 1 (fn-sf-frontier (fn-sn-files a))))
                (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sn-groups b) (fn-sn-groups a))
                (equal (fn-sn-capacity b) (fn-sn-capacity a)))
           (fn-cst-relation b))
  :rule-classes nil
  :hints (("Goal" :use (fn-cstp-final-configurationp-congruence
                        (:instance fn-cstp-statep-observed (st a))
                        (:instance fn-cstp-statep-observed (st b))
                        (:instance fn-cstp-recoverable-later
                                   (configs (fn-sn-config-history a))
                                   (events (fn-sf-records (fn-sn-files a)))
                                   (f (fn-sf-frontier (fn-sn-files a)))
                                   (g (+ 1 (fn-sf-frontier (fn-sn-files a))))))
           :in-theory '(fn-cst-relation fn-snt-idle-phasep member-equal fn-cstp-minus-one-of-successor
                        fn-sn-observed-historyp fn-record-uint32p natp posp
                        (:executable-counterpart member-equal)
                        (:executable-counterpart equal)))))
(defthm fn-cstp-relation-is-statep
  (implies (fn-cst-relation st) (fn-sn-statep st))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-cst-relation))))

(defthm fn-cstp-sn-statep-files
  (implies (fn-sn-statep st) (fn-sf-statep (fn-sn-files st)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; KEYSTONE (store).  The reservation's file steps and the recovery barriers
; keep the configured relation, for every result.
(defthm fn-cstp-reserve-io-preserves-relation
  (implies (and (fn-cst-relation s)
                (fn-cstp-reserve-opp operation))
           (fn-cst-relation (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-cstp-reserve-file-step-cases (files (fn-sn-files s)))
                 fn-cstp-io-fields fn-cstp-sn-io-no-file-change
                 (:instance fn-sn-io-preserves-state)
                 (:instance fn-cstp-relation-idle-congruence
                            (a s) (b (fn-sn-io s operation result)))
                 (:instance fn-cstp-relation-reserved-from-attempted
                            (a s) (b (fn-sn-io s operation result))))
           :in-theory '(fn-cstp-relation-is-statep fn-cstp-sn-statep-files
                        fn-cstp-reserve-opp member-equal
                        (:executable-counterpart equal)))))
(defthm fn-cstp-links-congruence
  (implies (and (equal (fn-sn-node b) (fn-sn-node a))
                (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sf-frontier (fn-sn-files b)) (fn-sf-frontier (fn-sn-files a)))
                (equal (fn-sf-record-candidate (fn-sn-files b))
                       (fn-sf-record-candidate (fn-sn-files a)))
                (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots a))
                (equal (fn-sn-identity-next b) (fn-sn-identity-next a)))
           (and (equal (fn-cst-pending-linkp b) (fn-cst-pending-linkp a))
                (equal (fn-cst-deferred-linkp b) (fn-cst-deferred-linkp a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cst-pending-linkp fn-cst-deferred-linkp
                               fn-sn-identity-context))))

(defthm fn-cstp-relation-record-congruence
  (implies (and (fn-cst-relation a)
                (fn-sn-statep b)
                (fn-sf-record-phasep (fn-sf-phase (fn-sn-files a)))
                (fn-sf-record-phasep (fn-sf-phase (fn-sn-files b)))
                (equal (fn-sn-node b) (fn-sn-node a))
                (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sf-frontier (fn-sn-files b)) (fn-sf-frontier (fn-sn-files a)))
                (equal (fn-sf-record-candidate (fn-sn-files b))
                       (fn-sf-record-candidate (fn-sn-files a)))
                (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots a))
                (equal (fn-sn-identity-next b) (fn-sn-identity-next a))
                (equal (fn-sn-groups b) (fn-sn-groups a))
                (equal (fn-sn-capacity b) (fn-sn-capacity a)))
           (fn-cst-relation b))
  :rule-classes nil
  :hints (("Goal" :use (fn-cstp-final-configurationp-congruence fn-cstp-links-congruence)
           :in-theory '(fn-cst-relation fn-snt-idle-phasep fn-sf-record-phasep
                        member-equal (:executable-counterpart equal)))))

(defthm fn-cstp-record-file-step-cases
  (implies (and (fn-sf-statep files)
                (member-equal operation '(:record-file :record-link :record-directory)))
           (let ((next (fn-sn-file-step files operation result)))
             (or (equal next files)
                 (and (fn-sf-record-phasep (fn-sf-phase files))
                      (fn-sf-record-phasep (fn-sf-phase next))
                      (equal (fn-sf-frontier next) (fn-sf-frontier files))
                      (equal (fn-sf-records next) (fn-sf-records files))
                      (equal (fn-sf-record-candidate next) (fn-sf-record-candidate files)))
                 (and (equal operation :record-directory)
                      (equal result :ok)
                      (equal (fn-sf-phase files) :record-attempted)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sf-record-file-result
                                   fn-sf-record-link-result fn-sf-record-dir-result
                                   fn-sf-record-phasep)
                                  (fn-sf-statep)))))

; KEYSTONE (store).  The record file steps before publication (and a failed
; directory observation) keep the configured relation.
(defthm fn-cstp-record-io-preserves-relation
  (implies (and (fn-cst-relation s)
                (member-equal operation '(:record-file :record-link :record-directory))
                (not (and (equal operation :record-directory) (equal result :ok)
                          (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))))
           (fn-cst-relation (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-cstp-record-file-step-cases (files (fn-sn-files s)))
                 fn-cstp-io-fields fn-cstp-sn-io-no-file-change
                 (:instance fn-sn-io-preserves-state)
                 (:instance fn-cstp-relation-record-congruence
                            (a s) (b (fn-sn-io s operation result))))
           :in-theory '(fn-cstp-relation-is-statep fn-cstp-sn-statep-files
                        member-equal (:executable-counterpart equal)))))
(defthm fn-cstp-sn-update-preserves-state
  (implies (and (fn-sn-statep s) (fn-sf-statep files)
                (fn-node-statep node))
           (fn-sn-statep (fn-sn-update s files node)))
  :hints (("Goal" :in-theory (e/d (fn-sn-update fn-sn-statep) (fn-sn-make-v6 fn-sf-statep fn-node-statep)))))

(defthm fn-cstp-stage-record-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-spc-stage-record files record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-stage-record fn-sf-statep fn-sf-phase-shapep fn-sf-phasep fn-sf-record-phasep)
                                  (fn-sf-candidatep fn-sf-record-listp
                                   fn-sf-success-listp)))))

(defthm fn-cstp-spc-prepare-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-spc-stage-record fn-sn-update
                                   fn-sn-prepare-node fn-sn-record-bindsp))
           :use ((:instance fn-cstp-sn-update-preserves-state
                            (files (fn-spc-stage-record (fn-sn-files s) record))
                            (node (fn-sn-prepare-node (fn-sn-node s) record)))
                 (:instance fn-cstp-sn-statep-files (st s))))))
(defthm fn-cstp-held-kind-facts
  (implies (fn-held-p x)
           (and (fn-store-event-p x)
                (not (fn-store-retention-event-p x))
                (not (fn-stxe-p x)) (not (fn-stxk-p x)) (not (fn-hstxa-p x))
                (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))
                (equal (fn-store-event-sequence x) (fn-record-sequence x))
                (equal (fn-store-event-txid x) (fn-record-txid x))
                (equal (fn-store-event-generation x) (fn-record-generation x))))
  :hints (("Goal" :in-theory (enable fn-store-event-p fn-held-p
                                     fn-held-shapep fn-store-retention-event-p
                                     fn-stxe-p fn-stxe-shapep fn-stxk-p
                                     fn-stxk-shapep fn-hstxa-p
                                     fn-cpe-eventp fn-th-topic-eventp
                                     fn-store-event-sequence fn-store-event-txid
                                     fn-store-event-generation))))

(defthm fn-cstp-apply-held-is-durable-completion
  (implies (and (fn-held-p record)
                (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp (fn-sn-prepare-node node record)
                                          (fn-record-txid record)
                                          (fn-record-generation record)))
           (equal (fn-replay-apply-record node record)
                  (fn-node-complete (fn-sn-prepare-node node record)
                                    (fn-record-txid record)
                                    (fn-record-generation record) :durable)))
  :hints (("Goal" :use ((:instance fn-cstp-advance-idle-at (txid (fn-record-txid record))))
           :in-theory (e/d (fn-replay-apply-record fn-sn-prepare-node fn-replay-advance-okp
                            fn-cstp-idlep)
                           (fn-replay-advance-txid fn-node-prepare fn-node-complete
                            fn-node-pending-matchesp fn-node-statep fn-held-p
                            fn-cstp-advance-idle-at
                            fn-record-record-vocabulary fn-record-shape-vocabulary)))))
(defthm fn-cstp-canonical-preparation-outcomes
  (let* ((txid (fn-record-txid record))
         (generation (fn-record-generation record))
         (base (fn-cst-replay-node configs events txid))
         (pending (fn-sn-prepare-node base record)))
    (implies (and (true-listp configs) (true-listp events)
                  (fn-cst-recoverablep configs events txid)
                  (fn-held-p record)
                  (equal (fn-record-sequence record) (len events))
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) record)
                  (fn-node-pending-matchesp pending txid generation))
             (and (equal (fn-node-complete pending txid generation :aborted)
                         (fn-cst-replay-node configs events (+ 1 txid)))
                  (equal (fn-node-complete pending txid generation :durable)
                         (fn-cst-replay-node configs (append events (list record))
                                             (+ 1 txid)))
                  (fn-cst-recoverablep configs (append events (list record)) (+ 1 txid))
                  (equal (fn-cnode-config (fn-cstp-fold configs (append events (list record))))
                         (fn-cnode-config (fn-cstp-fold configs events))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-node-idle (frontier (fn-record-txid record)))
                 (:instance fn-cstp-recoverable-later
                            (f (fn-record-txid record)) (g (+ 1 (fn-record-txid record))))
                 (:instance fn-snt-prepared-abort-is-frontier-advance
                            (node (fn-cst-replay-node configs events (fn-record-txid record))))
                 (:instance fn-snt-prepared-durable-is-idle-at-successor
                            (node (fn-cst-replay-node configs events (fn-record-txid record))))
                 (:instance fn-cstp-apply-held-is-durable-completion
                            (node (fn-cst-replay-node configs events (fn-record-txid record))))
                 (:instance fn-cstp-held-kind-facts (x record))
                 (:instance fn-cstp-advance-okp-natp (node (fn-cst-replay-node configs events (fn-record-txid record))) (txid (fn-record-txid record)))
                 (:instance fn-cstp-replay-append-event
                            (txid (fn-record-txid record)) (event record)))
           :in-theory '(fn-cstp-advance-okp-natp natp
                        fn-cnode-config-of-fn-cnode-make))))
(defthm fn-cstp-sn-update-fields
  (and (equal (fn-sn-node (fn-sn-update s files node)) node)
       (equal (fn-sn-config-history (fn-sn-update s files node)) (fn-sn-config-history s))
       (equal (fn-sn-groups (fn-sn-update s files node)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-update s files node)) (fn-sn-capacity s))
       (equal (fn-sn-keyring-generation (fn-sn-update s files node))
              (fn-sn-keyring-generation s))
       (equal (fn-sn-keyring-snapshots (fn-sn-update s files node))
              (fn-sn-keyring-snapshots s))
       (equal (fn-sn-topic (fn-sn-update s files node)) (fn-sn-topic s))
       (equal (fn-sn-consumer (fn-sn-update s files node)) (fn-sn-consumer s))
       (equal (fn-sn-identity-next (fn-sn-update s files node)) (fn-sn-identity-next s))
       (equal (fn-sn-files (fn-sn-update s files node)) files))
  :hints (("Goal" :in-theory (enable fn-sn-update))))

; What the carried article prepare does: nothing, or stage RECORD at the
; reservation with the prepared node, every other field kept.
(defthm fn-cstp-spc-prepare-cases
  (or (equal (fn-spc-prepare s record) s)
      (let ((b (fn-spc-prepare s record)))
        (and (fn-sn-statep s)
             (equal (fn-sf-phase (fn-sn-files s)) :reserved)
             (fn-held-p record)
             (fn-sf-candidatep record (fn-sf-records (fn-sn-files s))
                               (fn-sf-frontier (fn-sn-files s)))
             (equal (fn-hc-generation (fn-held-context record))
                    (fn-sn-keyring-generation s))
             (eq (car (fn-cpe-projection-step
                       (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok)
             (equal (fn-sn-node b) (fn-sn-prepare-node (fn-sn-node s) record))
             (fn-sn-record-bindsp (fn-sn-node b) record)
             (equal (fn-sf-phase (fn-sn-files b)) :record-staged)
             (equal (fn-sf-frontier (fn-sn-files b)) (fn-sf-frontier (fn-sn-files s)))
             (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files s)))
             (equal (fn-sf-record-candidate (fn-sn-files b)) record)
             (equal (fn-sn-config-history b) (fn-sn-config-history s))
             (equal (fn-sn-groups b) (fn-sn-groups s))
             (equal (fn-sn-capacity b) (fn-sn-capacity s))
             (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))
             (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots s))
             (equal (fn-sn-identity-next b) (fn-sn-identity-next s))
             (equal (fn-sn-consumer b) (fn-sn-consumer s))
             (equal (fn-sn-topic b) (fn-sn-topic s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-spc-stage-record)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-sn-prepare-node fn-sn-record-bindsp fn-sf-candidatep
                                   fn-held-p fn-cpe-projection-step fn-hc-generation
                                   fn-held-context fn-record-stamp fn-sn-update)))))
(defthm fn-cstp-canonical-at-frontier
  (let* ((txid (fn-record-txid record))
         (generation (fn-record-generation record))
         (base (fn-cst-replay-node configs events (+ -1 frontier)))
         (pending (fn-sn-prepare-node base record)))
    (implies (and (true-listp configs) (true-listp events)
                  (equal (+ 1 txid) frontier)
                  (fn-cst-recoverablep configs events (+ -1 frontier))
                  (fn-held-p record)
                  (equal (fn-record-sequence record) (len events))
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) record)
                  (fn-node-pending-matchesp pending txid generation))
             (and (equal (fn-node-complete pending txid generation :aborted)
                         (fn-cst-replay-node configs events frontier))
                  (equal (fn-node-complete pending txid generation :durable)
                         (fn-cst-replay-node configs (append events (list record))
                                             frontier))
                  (fn-cst-recoverablep configs (append events (list record)) frontier)
                  (equal (fn-cnode-config (fn-cstp-fold configs (append events (list record))))
                         (fn-cnode-config (fn-cstp-fold configs events))))))
  :rule-classes nil
  :hints (("Goal" :use fn-cstp-canonical-preparation-outcomes
           :in-theory '(fn-cstp-held-kind-facts fn-cstp-minus-one-of-successor fn-snt-record-counters-natural))))
(defthm fn-cstp-spc-prepare-preserves-relation
  (implies (and (fn-cst-relation s)
                (fn-cpr-event-servedp
                 (fn-cstp-fold (fn-sn-config-history s) (fn-sf-records (fn-sn-files s)))
                 record))
           (fn-cst-relation (fn-spc-prepare s record)))
  :hints (("Goal" :cases ((equal (fn-spc-prepare s record) s)))
          ("Subgoal 2"
           :use (fn-cstp-spc-prepare-cases
                 (:instance fn-cstp-canonical-at-frontier (frontier (fn-sf-frontier (fn-sn-files s)))
                            (configs (fn-sn-config-history s))
                            (events (fn-sf-records (fn-sn-files s))))
                 (:instance fn-cstp-held-kind-facts (x record))
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 fn-cstp-spc-prepare-preserves-state
                 (:instance fn-cstp-final-configurationp-congruence
                            (a s) (b (fn-spc-prepare s record)))
                 (:instance fn-cstp-statep-observed (st (fn-spc-prepare s record))))
           :in-theory '(fn-cst-relation fn-cst-pending-linkp fn-sf-candidatep
                        fn-snt-idle-phasep fn-sf-record-phasep member-equal
                        fn-sn-record-bindsp fn-cstp-sn-statep-files
                        fn-cstp-minus-one-of-successor
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))
(defthm fn-cstp-held-is-no-local-admin-event
  (implies (fn-held-p x) (not (fn-th-local-admin-eventp x)))
  :hints (("Goal" :use ((:instance fn-held-p-forward-natural-head))
           :in-theory '(fn-th-local-admin-eventp fn-th-at (:e zp) natp))))

(defthm fn-cstp-topic-step-ok-facts
  (implies (eq (fn-th-at 0 (fn-th-prefix-step p e)) :ok)
           (and (equal (fn-th-at 0 p) :ok)
                (equal (fn-th-at 1 p) (fn-store-event-sequence e))
                (equal (fn-th-at 1 (fn-th-prefix-step p e))
                       (+ 1 (nfix (fn-th-at 1 p))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-th-prefix-step fn-th-prefix-state)
                                  (fn-th-local-admin-commit fn-stmt-okp fn-stmt-value
                                   fn-th-commit-anchor fn-th-commit-anchor-installed-v2
                                   fn-th-commit-report fn-th-prefix-find-ref fn-stxk-find
                                   fn-store-event-p fn-stxk-p fn-hstxa-p
                                   fn-th-local-admin-eventp fn-th-topic-eventp
                                   fn-th-topic-v1-anchorp fn-store-event-sequence)))))

(defthm fn-cstp-topic-step-of-held
  (implies (and (equal (fn-th-at 0 p) :ok)
                (fn-held-p r)
                (equal (fn-th-at 1 p) (fn-store-event-sequence r)))
           (equal (fn-th-at 0 (fn-th-prefix-step p r)) :ok))
  :hints (("Goal" :use ((:instance fn-cstp-held-kind-facts (x r))
                        (:instance fn-cstp-held-is-no-local-admin-event (x r)))
           :in-theory (e/d (fn-th-prefix-step fn-th-prefix-state)
                           (fn-th-local-admin-commit fn-stmt-okp fn-stmt-value
                            fn-held-p fn-cstp-held-kind-facts
                            fn-cstp-held-is-no-local-admin-event
                            fn-store-event-p fn-stxk-p fn-hstxa-p
                            fn-th-local-admin-eventp fn-th-topic-eventp
                            fn-store-event-sequence fn-record-sequence)))))
; -----------------------------------------------------------------------------
; What the relation's :completing arm needs and its record arms do not carry.
; fn-cst-relation at :completing asks fn-sn-completion-enabledp: the consumer
; projection and the topic prefix accept the completion record, and a held
; row's context generation is the keyring's.  The record arms carry only the
; node links, so the directory observation cannot re-establish those from the
; relation alone.  This carried companion states them: from the prepare to
; the directory observation the gate's facts about the candidate, at
; :completing the topic prefix one short of the history, elsewhere the topic
; prefix at the history's length with status :ok (proof vocabulary; no served
; transition evaluates it).
(defun fn-cstp-carriedp (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files st))
         (phase (fn-sf-phase files))
         (records (fn-sf-records files))
         (topic (fn-sn-topic st)))
    (cond ((fn-sf-record-phasep phase)
           (let ((r (fn-sf-record-candidate files)))
             (and (or (not (fn-held-p r))
                      (equal (fn-hc-generation (fn-held-context r))
                             (fn-sn-keyring-generation st)))
                  (eq (car (fn-cpe-projection-step (fn-sn-consumer st) r
                                                   (fn-sn-identity-next st)))
                      :ok)
                  (eq (fn-th-at 0 (fn-th-prefix-step topic r)) :ok))))
          ((equal phase :completing)
           (equal (len records) (+ 1 (nfix (fn-th-at 1 topic)))))
          ((member-equal phase '(:replaying :fault)) t)
          (t (and (eq (fn-th-at 0 topic) :ok)
                  (equal (fn-th-at 1 topic) (len records)))))))

(defthm fn-cstp-carriedp-congruence
  (implies (and (equal (fn-sf-phase (fn-sn-files b)) (fn-sf-phase (fn-sn-files a)))
                (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files a)))
                (equal (fn-sf-record-candidate (fn-sn-files b))
                       (fn-sf-record-candidate (fn-sn-files a)))
                (equal (fn-sn-topic b) (fn-sn-topic a))
                (equal (fn-sn-consumer b) (fn-sn-consumer a))
                (equal (fn-sn-identity-next b) (fn-sn-identity-next a))
                (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation a)))
           (equal (fn-cstp-carriedp b) (fn-cstp-carriedp a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cstp-carriedp))))

(defthm fn-cstp-reserve-io-preserves-carriedp
  (implies (and (fn-cstp-carriedp s)
                (fn-sn-statep s)
                (fn-cstp-reserve-opp operation))
           (fn-cstp-carriedp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-cstp-reserve-file-step-cases (files (fn-sn-files s)))
                 fn-cstp-io-fields fn-cstp-sn-io-no-file-change)
           :in-theory '(fn-cstp-carriedp fn-cstp-sn-statep-files fn-snt-idle-phasep
                        fn-sf-record-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

(defthm fn-cstp-record-io-preserves-carriedp
  (implies (and (fn-cstp-carriedp s)
                (fn-sn-statep s)
                (member-equal operation '(:record-file :record-link :record-directory))
                (not (and (equal operation :record-directory) (equal result :ok)
                          (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))))
           (fn-cstp-carriedp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-cstp-record-file-step-cases (files (fn-sn-files s)))
                 fn-cstp-io-fields fn-cstp-sn-io-no-file-change)
           :in-theory '(fn-cstp-carriedp fn-cstp-sn-statep-files
                        fn-sf-record-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

(defthm fn-cstp-spc-prepare-preserves-carriedp
  (implies (fn-cstp-carriedp s)
           (fn-cstp-carriedp (fn-spc-prepare s record)))
  :hints (("Goal"
           :use (fn-cstp-spc-prepare-cases
                 (:instance fn-cstp-held-kind-facts (x record))
                 (:instance fn-cstp-topic-step-of-held (p (fn-sn-topic s)) (r record)))
           :in-theory '(fn-cstp-carriedp fn-sf-candidatep fn-sf-record-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))
(defun fn-cstp-config-fold (config configs)
  ; Proof vocabulary: the configuration a successful fold arrives at depends
  ; on the configuration records alone.
  (declare (xargs :guard t :verify-guards nil))
  (if (consp configs)
      (fn-cstp-config-fold (fn-cfg-apply-record config (car configs)) (cdr configs))
    config))

(defthm fn-cstp-loop-config-is-config-fold
  (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
           (equal (fn-cnode-config (fn-replay-result-node
                                    (fn-cpr-loop cn configs events cs es)))
                  (fn-cstp-config-fold (fn-cnode-config cn) configs)))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cs es)
           :in-theory (e/d (fn-cpr-loop fn-cnode-apply-config)
                           (fn-cnode-statep fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cnode-carried-acceptablep fn-cpr-config-firstp
                            fn-cfg-apply-record fn-cnode-extend-nexts
                            fn-cnode-domain-of)))))

(defthm fn-cstp-fold-config-independent-of-events
  (implies (and (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
                (equal (fn-replay-result-kind (fn-cpr-replay configs events2)) :ok))
           (equal (fn-cnode-config (fn-cstp-fold configs events2))
                  (fn-cnode-config (fn-cstp-fold configs events))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cstp-fold fn-cpr-replay fn-cstp-loop-config-is-config-fold))))
(defthm fn-cstp-record-dir-ok-files
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
           (let ((files (fn-sn-files (fn-sn-io s :record-directory :ok)))
                 (r (fn-sf-record-candidate (fn-sn-files s))))
             (and (equal (fn-sf-phase files) :completing)
                  (equal (fn-sf-frontier files) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-records files)
                         (append (fn-sf-records (fn-sn-files s)) (list r)))
                  (equal (fn-sf-completion files) (fn-sf-record-pair r)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cstp-io-fields (operation :record-directory)
                                   (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-record-dir-result)
                           (fn-sn-statep fn-sf-statep fn-cstp-io-fields fn-sn-io
                            fn-sf-record-pair)))))

(defthm fn-cstp-completion-record-after-dir
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
           (equal (fn-sn-completion-record (fn-sn-io s :record-directory :ok))
                  (fn-sf-record-candidate (fn-sn-files s))))
  :hints (("Goal" :use (fn-cstp-record-dir-ok-files
                        (:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                        (:instance fn-snt-find-published-candidate
                                   (files (fn-sn-files s))
                                   (record (fn-sf-record-candidate (fn-sn-files s))))
                        (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory '(fn-sn-completion-record fn-sf-record-phasep member-equal
                        (:executable-counterpart member-equal)))))
(defthm fn-cstp-found-record-is-a-true-list
  (implies (fn-sf-record-listp records sequence lower frontier)
           (true-listp (fn-sn-find-record pair records)))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
           :in-theory (e/d (fn-sn-find-record fn-sf-record-listp)
                           (fn-store-event-p fn-sf-record-pair
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary)))))

(defthm fn-cstp-completion-record-is-a-true-list
  (implies (fn-sn-statep s)
           (true-listp (fn-sn-completion-record s)))
  :hints (("Goal"
           :use ((:instance fn-cstp-found-record-is-a-true-list
                            (pair (fn-sf-completion (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-statep fn-sf-statep fn-sn-completion-record)
                           (fn-sf-record-listp fn-sf-success-listp
                            fn-sf-phase-shapep fn-sn-find-record
                            fn-cstp-found-record-is-a-true-list
                            fn-node-statep)))))
(defthm fn-cstp-final-configuration-of-longer-history
  (implies (and (fn-cst-final-configurationp a)
                (equal (fn-sn-config-history b) (fn-sn-config-history a))
                (equal (fn-sn-groups b) (fn-sn-groups a))
                (equal (fn-sn-capacity b) (fn-sn-capacity a))
                (fn-cst-recoverablep (fn-sn-config-history a)
                                     (fn-sf-records (fn-sn-files b)) frontier))
           (fn-cst-final-configurationp b))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-recoverable-facts
                            (configs (fn-sn-config-history a))
                            (events (fn-sf-records (fn-sn-files b))))
                 (:instance fn-cstp-fold-config-independent-of-events
                            (configs (fn-sn-config-history a))
                            (events (fn-sf-records (fn-sn-files a)))
                            (events2 (fn-sf-records (fn-sn-files b)))))
           :in-theory '(fn-cst-final-configurationp fn-cstp-fold))))
(defthm fn-cstp-held-completion-enabled-after-dir
  (implies (and (fn-cst-relation s)
                (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                (fn-held-p (fn-sf-record-candidate (fn-sn-files s))))
           (fn-sn-completion-enabledp (fn-sn-io s :record-directory :ok)))
  :hints (("Goal"
           :use (fn-cstp-record-dir-ok-files fn-cstp-completion-record-after-dir
                 (:instance fn-cstp-io-fields (operation :record-directory) (result :ok))
                 (:instance fn-sn-io-preserves-state (operation :record-directory)
                            (result :ok))
                 (:instance fn-cstp-held-kind-facts
                            (x (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory '(fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                        fn-cst-relation fn-cst-pending-linkp fn-cstp-carriedp
                        fn-cstp-relation-is-statep fn-sn-record-bindsp
                        fn-sf-record-phasep fn-snt-idle-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))
; KEYSTONE (store).  The directory observation that publishes a staged article
; keeps the configured relation, given the carried companion.
(defthm fn-cstp-held-record-dir-preserves-relation
  (implies (and (fn-cst-relation s)
                (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                (fn-held-p (fn-sf-record-candidate (fn-sn-files s))))
           (fn-cst-relation (fn-sn-io s :record-directory :ok)))
  :hints (("Goal"
           :use (fn-cstp-record-dir-ok-files fn-cstp-completion-record-after-dir
                 fn-cstp-held-completion-enabled-after-dir
                 (:instance fn-cstp-io-fields (operation :record-directory) (result :ok))
                 (:instance fn-sn-io-preserves-state (operation :record-directory)
                            (result :ok))
                 (:instance fn-cstp-completion-record-is-a-true-list
                            (s (fn-sn-io s :record-directory :ok)))
                 (:instance fn-cstp-statep-observed (st (fn-sn-io s :record-directory :ok)))
                 (:instance fn-cstp-final-configuration-of-longer-history
                            (a s) (b (fn-sn-io s :record-directory :ok))
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory '(fn-cst-relation fn-cst-pending-linkp fn-cst-completion-linkp
                        fn-cstp-relation-is-statep
                        fn-sf-record-phasep fn-snt-idle-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-cstp-len-of-append-one
  (equal (len (append xs (list x))) (+ 1 (len xs))))

(defthm fn-cstp-record-dir-preserves-carriedp
  (implies (and (fn-cstp-carriedp s)
                (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
           (fn-cstp-carriedp (fn-sn-io s :record-directory :ok)))
  :hints (("Goal"
           :use (fn-cstp-record-dir-ok-files
                 (:instance fn-cstp-io-fields (operation :record-directory) (result :ok))
                 (:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-statep-files (st s))
                 (:instance fn-cstp-topic-step-ok-facts
                            (p (fn-sn-topic s))
                            (e (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory '(fn-cstp-carriedp fn-sf-candidatep fn-sf-record-phasep member-equal
                        fn-cstp-len-of-append-one nfix natp (:type-prescription len)
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))
(defthm fn-cstp-finish-topic
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-topic (fn-sn-finish s))
                  (fn-th-prefix-step (fn-sn-topic s) (fn-sn-completion-record s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish)
                                  (fn-sn-completion-enabledp fn-sn-completion-record
                                   fn-th-prefix-step fn-cpe-projection-step
                                   fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-node-complete fn-sf-core-completion fn-sf-emit-success
                                   fn-sn-advance-identity-next fn-sn-update-indexed
                                   fn-sn-finish-identity fn-sn-update-accepted
                                   fn-stx-index-add fn-sn-accepted-delta
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-hstxa-p fn-cpe-eventp
                                   fn-th-topic-eventp)))))

(defthm fn-cstp-finish-preserves-carriedp
  (implies (and (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (fn-cstp-carriedp (fn-sn-finish s)))
  :hints (("Goal"
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-snt-finish-image fn-cstp-finish-topic fn-sn-finish-disabled-is-no-op
                 (:instance fn-cstp-topic-step-ok-facts
                            (p (fn-sn-topic s)) (e (fn-sn-completion-record s))))
           :in-theory '(fn-cstp-carriedp fn-sn-completion-enabledp fn-sf-record-phasep
                        member-equal nfix natp
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))
(defthm fn-cstp-car-update-nth
  (equal (car (update-nth n v x)) (if (zp n) v (car x))))

(defthm fn-cstp-cdr-update-nth
  (equal (cdr (update-nth n v x))
         (if (zp n) (cdr x) (update-nth (+ -1 n) v (cdr x)))))

(defun fn-cstp-nth-induct (n m x)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (zp m))
      (list n m x)
    (fn-cstp-nth-induct (1- n) (1- m) (cdr x))))

(defthm fn-cstp-store-event-nth-of-update-nth
  (implies (and (natp n) (natp m) (not (equal n m)))
           (equal (fn-store-event-nth n (update-nth m v x))
                  (fn-store-event-nth n x)))
  :hints (("Goal" :induct (fn-cstp-nth-induct n m x)
           :in-theory (enable fn-store-event-nth update-nth))))

(defthm fn-cstp-with-configuration-fields
  (let ((b (fn-sn-with-configuration s groups capacity node configs)))
    (and (equal (fn-sn-files b) (fn-sn-files s))
         (equal (fn-sn-topic b) (fn-sn-topic s))
         (equal (fn-sn-consumer b) (fn-sn-consumer s))
         (equal (fn-sn-identity-next b) (fn-sn-identity-next s))
         (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-with-configuration fn-sn-files fn-sn-topic fn-store-event-nth
                                     fn-sn-consumer fn-sn-identity-next
                                     fn-sn-keyring-generation) (update-nth)))))

(defthm fn-cstp-configure-durable-preserves-carriedp
  (implies (fn-cstp-carriedp st)
           (fn-cstp-carriedp (fn-cpo-configure-durable st record)))
  :hints (("Goal"
           :use ((:instance fn-cstp-carriedp-congruence
                            (a st) (b (fn-cpo-configure-durable st record))))
           :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install)
                           (fn-cstp-carriedp fn-cpo-history-relation fn-cpr-replay
                            fn-sn-statep fn-sn-with-configuration fn-cnode-statep
                            fn-replay-advance-okp fn-replay-advance-txid)))))
(defthm fn-cstp-topic-step-not-ok-is-identity
  (implies (not (equal (fn-th-at 0 p) :ok))
           (equal (fn-th-prefix-step p e) p))
  :hints (("Goal" :in-theory '(fn-th-prefix-step))))

(defthm fn-cstp-prefix-loop-not-ok
  (implies (and (true-listp records)
                (not (equal (fn-th-at 0 p) :ok)))
           (equal (fn-th-prefix-loop p records) p))
  :hints (("Goal" :induct (fn-th-prefix-loop p records)
           :in-theory (e/d (fn-th-prefix-loop) (fn-th-prefix-step)))))

(defthm fn-cstp-topic-step-ok-next
  (implies (equal (fn-th-at 0 (fn-th-prefix-step p e)) :ok)
           (equal (fn-th-at 1 (fn-th-prefix-step p e))
                  (+ 1 (nfix (fn-th-at 1 p)))))
  :hints (("Goal" :use fn-cstp-topic-step-ok-facts :in-theory nil)))

(defthm fn-cstp-prefix-loop-next
  (implies (and (true-listp records)
                (natp (fn-th-at 1 p))
                (equal (fn-th-at 0 (fn-th-prefix-loop p records)) :ok))
           (equal (fn-th-at 1 (fn-th-prefix-loop p records))
                  (+ (fn-th-at 1 p) (len records))))
  :hints (("Goal" :induct (fn-th-prefix-loop p records)
           :in-theory (e/d (fn-th-prefix-loop) (fn-th-prefix-step)))
          ("Subgoal *1/1" :cases ((equal (fn-th-at 0 (fn-th-prefix-step p (car records))) :ok)))))

; The configured open establishes the carried companion (its phase is
; :recovering, an idle one).
(defthm fn-cstp-open-establishes-carriedp
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)
           (fn-cstp-carriedp
            (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-is-true-list
                            (records events) (sequence 0) (lower 0))
                 (:instance fn-cstp-prefix-loop-next
                            (p (fn-th-prefix-state :ok 0 nil nil nil nil nil))
                            (records events)))
           :in-theory (e/d (fn-cpo-open-observed fn-cstp-carriedp fn-sn-observed-historyp fn-sn-open-ok
                            fn-sn-open-kind fn-sn-open-state fn-sn-open-error
                            fn-th-prefix-project fn-cpo-install fn-sf-record-phasep)
                           (fn-cpr-replay fn-sn-statep fn-th-prefix-loop
                            fn-replay-identity fn-cpe-projection-replay
                            fn-sn-observed-seed fn-sn-update-replayed fn-sn-with-configuration
                            fn-sn-with-consumer fn-sn-with-topic fn-sn-with-event-index
                            fn-cnode-statep fn-replay-advance-okp fn-replay-advance-txid
                            fn-stx-index-of-store fn-cei-build)))))
(defthm fn-cstp-refuse-reservation-cases
  (or (equal (fn-sn-refuse-reservation s txid) s)
      (let ((b (fn-sn-refuse-reservation s txid)))
        (and (fn-sn-statep s)
             (fn-sn-statep b)
             (equal (fn-sf-phase (fn-sn-files s)) :reserved)
             (equal (fn-sf-phase (fn-sn-files b)) :ready)
             (equal (fn-sn-node b)
                    (fn-replay-advance-txid (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
             (equal (fn-sf-frontier (fn-sn-files b)) (fn-sf-frontier (fn-sn-files s)))
             (equal (fn-sf-records (fn-sn-files b)) (fn-sf-records (fn-sn-files s)))
             (equal (fn-sn-config-history b) (fn-sn-config-history s))
             (equal (fn-sn-groups b) (fn-sn-groups s))
             (equal (fn-sn-capacity b) (fn-sn-capacity s))
             (equal (fn-sn-topic b) (fn-sn-topic s)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cstp-sn-update-preserves-state
                            (files (fn-sf-refuse-reservation (fn-sn-files s) txid))
                            (node (fn-replay-advance-txid (fn-sn-node s)
                                                          (fn-sf-frontier (fn-sn-files s)))))
                 (:instance fn-sf-refuse-reservation-preserves-state (s (fn-sn-files s)))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-sn-node s))
                            (recorded-txid (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-refuse-reservation-enabledp
                            fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep fn-node-statep
                            fn-replay-advance-okp fn-replay-advance-txid fn-sn-update)))))

(defthm fn-cstp-refuse-reservation-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-sn-refuse-reservation s txid))
                (fn-cstp-carriedp (fn-sn-refuse-reservation s txid))))
  :hints (("Goal" :cases ((equal (fn-sn-refuse-reservation s txid) s)))
          ("Subgoal 2"
           :use (fn-cstp-refuse-reservation-cases
                 (:instance fn-cstp-recoverable-later
                            (configs (fn-sn-config-history s))
                            (events (fn-sf-records (fn-sn-files s)))
                            (f (+ -1 (fn-sf-frontier (fn-sn-files s))))
                            (g (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-cstp-final-configurationp-congruence
                            (a s) (b (fn-sn-refuse-reservation s txid)))
                 (:instance fn-cstp-statep-observed (st (fn-sn-refuse-reservation s txid))))
           :in-theory '(fn-cst-relation fn-cstp-carriedp fn-snt-idle-phasep fn-sf-record-phasep
                        member-equal natp posp
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

; Accessor equalities used above as rewrite rules; withdrawn at export.
(in-theory (disable fn-cstp-completion-record-after-dir))
