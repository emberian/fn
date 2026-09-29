; fn: the carried owner invariant fn-lgoc-invariantp (books/owner-log-ocl.lisp)
; across every owner prepare the host calls, the deferred publications'
; directory observation and log order, the known abort, and the
; configuration un-stage (lane prepare-served, 2026-09-27; PKT-827 (d)).
;
; This book shares the prefix `fn-psrv-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "owner-prepare-served")
(include-book "owner-log-ocl")

(defthm fn-psrv-event-servedp-is-cpr-event-servedp
  (equal (fn-cpr-event-servedp cn event)
         (fn-psrv-event-servedp (fn-cnode-config cn) event))
  :hints (("Goal" :in-theory '(fn-cpr-event-servedp fn-psrv-event-servedp))))

(defthm fn-psrv-successor-of-predecessor
  (implies (acl2-numberp x) (equal (+ 1 (+ -1 x)) x)))

(defthm fn-psrv-event-txid-natp
  (implies (fn-store-event-p e) (natp (fn-store-event-txid e)))
  :rule-classes nil)

(defthm fn-psrv-recoverable-node-statep
  (implies (fn-cst-recoverablep configs events frontier)
           (fn-node-statep (fn-cst-replay-node configs events frontier)))
  :hints (("Goal" :in-theory '(fn-cst-recoverablep))))

; The configured relation of a Store whose record phase holds a deferred
; (non-article) candidate staged at the reservation, over the node the
; reservation left: every fact is read off B.
(defthm fn-psrv-deferred-staged-relation
  (let* ((files (fn-sn-files b))
         (configs (fn-sn-config-history b))
         (events (fn-sf-records files))
         (frontier (fn-sf-frontier files))
         (e (fn-sf-record-candidate files)))
    (implies (and (fn-sn-statep b)
                  (fn-sf-record-phasep (fn-sf-phase files))
                  (true-listp configs)
                  (fn-cst-final-configurationp b)
                  (posp frontier)
                  (fn-cst-recoverablep configs events (+ -1 frontier))
                  (fn-cst-recoverablep configs events frontier)
                  (equal (fn-sn-node b) (fn-cst-replay-node configs events (+ -1 frontier)))
                  (fn-store-event-p e)
                  (not (fn-held-p e))
                  (equal (fn-store-event-sequence e) (len events))
                  (equal (+ 1 (fn-store-event-txid e)) frontier)
                  (fn-cpr-event-servedp (fn-cstp-fold configs events) e)
                  (consp (fn-replay-apply-record (fn-sn-node b) e))
                  (or (fn-store-retention-event-p e)
                      (equal (fn-stxk-context-kind
                              (fn-replay-identity-step (fn-sn-identity-context b) e))
                             :ok)))
             (fn-cst-relation b)))
  :hints (("Goal"
           :use ((:instance fn-cstp-replay-append-event
                            (configs (fn-sn-config-history b))
                            (events (fn-sf-records (fn-sn-files b)))
                            (txid (+ -1 (fn-sf-frontier (fn-sn-files b))))
                            (event (fn-sf-record-candidate (fn-sn-files b))))
                 (:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-sn-node b))
                            (record (fn-sf-record-candidate (fn-sn-files b))))
                 (:instance fn-psrv-recoverable-node-statep
                            (configs (fn-sn-config-history b))
                            (events (fn-sf-records (fn-sn-files b)))
                            (frontier (+ -1 (fn-sf-frontier (fn-sn-files b)))))
                 (:instance fn-psrv-event-txid-natp (e (fn-sf-record-candidate (fn-sn-files b))))
                 (:instance fn-cstp-statep-observed (st b))
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files b)))
                 (:instance fn-cstp-sn-statep-files (st b)))
           :in-theory '(fn-cst-relation fn-cst-deferred-linkp
                        fn-snt-idle-phasep fn-sf-record-phasep
                        member-equal fn-psrv-successor-of-predecessor posp natp
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-psrv-topic-step-of-untopical
  (implies (and (equal (fn-th-at 0 p) :ok)
                (fn-store-event-p e)
                (equal (fn-th-at 1 p) (fn-store-event-sequence e))
                (not (fn-th-topic-eventp e))
                (not (fn-th-local-admin-eventp e)))
           (equal (fn-th-at 0 (fn-th-prefix-step p e)) :ok))
  :hints (("Goal" :in-theory (e/d (fn-th-prefix-step fn-th-prefix-state)
                                  (fn-th-local-admin-commit fn-stmt-okp fn-stmt-value
                                   fn-store-event-p fn-stxk-p fn-hstxa-p
                                   fn-th-local-admin-eventp fn-th-topic-eventp
                                   fn-store-event-sequence)))))

(defthm fn-psrv-topic-event-head
  (implies (fn-th-topic-eventp e)
           (member-equal (car e) '(:topic-admin-install :topic-anchor :topic-admit)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-th-topic-eventp fn-th-local-admin-eventp fn-th-at
                               member-equal (:executable-counterpart zp)
                               (:executable-counterpart member-equal)))))

(defthm fn-psrv-retention-head
  (implies (fn-store-retention-event-p e) (equal (car e) :retention))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-store-retention-event-p fn-store-event-nth
                               (:executable-counterpart zp)))))

(defthm fn-psrv-retention-event-kinds
  (implies (fn-store-retention-event-p e)
           (and (not (fn-held-p e)) (not (fn-hstxa-p e))
                (not (fn-th-topic-eventp e)) (not (fn-th-local-admin-eventp e))))
  :hints (("Goal" :use (fn-psrv-retention-head fn-psrv-topic-event-head
                        (:instance fn-held-p-forward-natural-head (x e))
                        (:instance fn-hstxa-p-forward-shape (x e)))
           :in-theory '(fn-th-local-admin-eventp fn-th-at natp member-equal
                        (:executable-counterpart zp)
                        (:executable-counterpart member-equal)))))

(defthm fn-psrv-consumer-event-kinds
  (implies (fn-cpe-eventp e)
           (and (not (fn-held-p e)) (not (fn-hstxa-p e))
                (not (fn-th-topic-eventp e)) (not (fn-th-local-admin-eventp e))))
  :hints (("Goal" :use ((:instance fn-held-p-forward-natural-head (x e))
                        (:instance fn-hstxa-p-forward-shape (x e)))
           :in-theory (e/d (fn-cpe-eventp fn-cp-nth fn-th-topic-eventp
                            fn-th-local-admin-eventp fn-th-at)
                           (fn-th-source-id-p fn-th-auth-ref-p fn-th-exact-octets-p
                            fn-held-p fn-hstxa-p)))))

(defthm fn-psrv-identity-event-head
  (implies (or (fn-stxe-p e) (fn-stxk-p e) (fn-hstxa-p e))
           (not (member-equal (car e) '(:topic-admin-install :topic-anchor :topic-admit))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hstxa-p-forward-shape (x e)))
           :in-theory '(fn-stxe-p fn-stxk-p fn-stxe-sequence fn-stxk-sequence
                        fn-record-uint32p natp member-equal
                        (:executable-counterpart member-equal)
                        (:executable-counterpart equal)))))

(defthm fn-psrv-identity-event-kinds
  (implies (or (fn-stxe-p e) (fn-stxk-p e) (fn-hstxa-p e))
           (and (not (fn-held-p e))
                (not (fn-th-topic-eventp e)) (not (fn-th-local-admin-eventp e))))
  :hints (("Goal" :use ((:instance fn-snt-an-article-record-is-no-other-store-event (record e))
                        fn-psrv-identity-event-head fn-psrv-topic-event-head)
           :in-theory '(fn-th-local-admin-eventp fn-th-at member-equal
                        (:executable-counterpart zp)
                        (:executable-counterpart member-equal)))))

(defthm fn-psrv-topic-event-kinds
  (implies (fn-th-topic-eventp e)
           (and (not (fn-held-p e)) (not (fn-hstxa-p e))))
  :hints (("Goal" :use ((:instance fn-snt-an-article-record-is-no-other-store-event (record e))
                        (:instance fn-snt-topic-event-is-not-hstxa (event e)))
           :in-theory nil)))

(defthm fn-psrv-sf-prepare-record-staged
  (let ((f (fn-sf-prepare-record files e groups capacity)))
    (implies (and (equal (fn-sf-phase files) :reserved)
                  (equal (fn-sf-phase f) :record-staged))
             (and (equal (fn-sf-record-candidate f) e)
                  (equal (fn-sf-records f) (fn-sf-records files))
                  (equal (fn-sf-frontier f) (fn-sf-frontier files))
                  (fn-sf-candidatep e (fn-sf-records files) (fn-sf-frontier files)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sf-prepare-record)
                                  (fn-sf-candidatep fn-sf-statep
                                   fn-sf-history-recoverablep)))))

(defthm fn-psrv-reserved-relation-facts
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (let* ((files (fn-sn-files s))
                  (configs (fn-sn-config-history s))
                  (events (fn-sf-records files))
                  (frontier (fn-sf-frontier files)))
             (and (fn-sn-statep s)
                  (true-listp configs)
                  (fn-cst-final-configurationp s)
                  (posp frontier)
                  (fn-cst-recoverablep configs events (+ -1 frontier))
                  (fn-cst-recoverablep configs events frontier)
                  (equal (fn-sn-node s)
                         (fn-cst-replay-node configs events (+ -1 frontier))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cst-relation fn-snt-idle-phasep member-equal
                               fn-sf-record-phasep
                               (:executable-counterpart equal)
                               (:executable-counterpart member-equal)
                               (:executable-counterpart fn-snt-idle-phasep)
                               (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-psrv-reserved-carried-facts
  (implies (and (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (and (equal (fn-th-at 0 (fn-sn-topic s)) :ok)
                (equal (fn-th-at 1 (fn-sn-topic s))
                       (len (fn-sf-records (fn-sn-files s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cstp-carriedp fn-sf-record-phasep member-equal
                               (:executable-counterpart equal)
                               (:executable-counterpart member-equal)
                               (:executable-counterpart fn-sf-record-phasep)))))

; What a deferred prepare leaves when it stages E: the Store with the file
; state F (the reservation's staged candidate E) and the node unchanged.
(defthm fn-psrv-deferred-stage-preserves
  (let ((b (fn-sn-update s f (fn-sn-node s))))
    (implies (and (fn-cst-relation s)
                  (fn-cstp-carriedp s)
                  (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                  (fn-sn-statep b)
                  (equal (fn-sf-phase f) :record-staged)
                  (equal (fn-sf-record-candidate f) e)
                  (equal (fn-sf-records f) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-frontier f) (fn-sf-frontier (fn-sn-files s)))
                  (fn-sf-candidatep e (fn-sf-records (fn-sn-files s))
                                    (fn-sf-frontier (fn-sn-files s)))
                  (not (fn-held-p e))
                  (fn-cpr-event-servedp (fn-cstp-fold (fn-sn-config-history s)
                                                      (fn-sf-records (fn-sn-files s)))
                                        e)
                  (or (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) e)) :ok)
                      (and (not (fn-th-topic-eventp e))
                           (not (fn-th-local-admin-eventp e))))
                  (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e
                                                   (fn-sn-identity-next s)))
                      :ok)
                  (consp (fn-replay-apply-record (fn-sn-node s) e))
                  (or (fn-store-retention-event-p e)
                      (equal (fn-stxk-context-kind
                              (fn-replay-identity-step (fn-sn-identity-context s) e))
                             :ok)))
             (and (fn-cst-relation b) (fn-cstp-carriedp b))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-psrv-reserved-relation-facts fn-psrv-reserved-carried-facts
                 (:instance fn-psrv-deferred-staged-relation
                            (b (fn-sn-update s f (fn-sn-node s))))
                 (:instance fn-cstp-final-configurationp-congruence
                            (a s) (b (fn-sn-update s f (fn-sn-node s))))
                 (:instance fn-psrv-topic-step-of-untopical (p (fn-sn-topic s))))
           :in-theory '(fn-cstp-sn-update-fields fn-cstp-carriedp fn-sf-candidatep
                        fn-sn-identity-context fn-sf-record-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-psrv-sn-prepare-retention-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-sn-prepare-retention s e))
                (fn-cstp-carriedp (fn-sn-prepare-retention s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-sn-prepare-retention s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-sf-prepare-record (fn-sn-files s) e (fn-sn-groups s)
                                                     (fn-sn-capacity s))))
                 (:instance fn-psrv-sf-prepare-record-staged
                            (files (fn-sn-files s)) (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-prepare-retention-preserves-state (event e))
                 (:instance fn-psrv-retention-event-kinds))
           :in-theory '(fn-sn-prepare-retention fn-replay-apply-record
                        fn-cstp-relation-is-statep fn-cpr-event-servedp))))

(defthm fn-psrv-projection-ok-sequence
  (implies (eq (car (fn-cpe-projection-step c e expected)) :ok)
           (equal (fn-store-event-sequence e) expected))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-cpe-projection-step car-cons
                               (:executable-counterpart equal)))))

(defthm fn-psrv-identity-step-of-plain-event
  (implies (and (equal (fn-store-event-sequence e) (fn-sn-identity-next s))
                (not (fn-stxk-p e)) (not (fn-stxe-p e)) (not (fn-stxa-p e))
                (not (fn-hstxa-p e)))
           (equal (fn-stxk-context-kind
                   (fn-replay-identity-step (fn-sn-identity-context s) e))
                  :ok))
  :hints (("Goal" :in-theory (e/d (fn-replay-identity-step fn-replay-identity-wire
                                   fn-sn-identity-context fn-stxk-context fn-stxk-context-kind)
                                  (fn-stxk-p fn-stxe-p fn-stxa-p fn-hstxa-p)))))

(defthm fn-psrv-consumer-event-is-no-identity-event
  (implies (fn-cpe-eventp e)
           (and (not (fn-stxk-p e)) (not (fn-stxe-p e)) (not (fn-stxa-p e))))
  :hints (("Goal" :in-theory (e/d (fn-cpe-eventp fn-cp-nth fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep)
                                  ()))))

(defthm fn-psrv-topic-event-is-no-identity-event
  (implies (fn-th-topic-eventp e)
           (and (not (fn-stxk-p e)) (not (fn-stxe-p e)) (not (fn-stxa-p e))))
  :hints (("Goal" :use fn-psrv-topic-event-head
           :in-theory (e/d (fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep)
                           (fn-th-topic-eventp)))))

(defthm fn-psrv-sn-prepare-consumer-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-sn-prepare-consumer s e))
                (fn-cstp-carriedp (fn-sn-prepare-consumer s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-sn-prepare-consumer s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-sf-prepare-record (fn-sn-files s) e (fn-sn-groups s)
                                                     (fn-sn-capacity s))))
                 (:instance fn-psrv-sf-prepare-record-staged
                            (files (fn-sn-files s)) (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-prepare-consumer-preserves-state (event e))
                 (:instance fn-psrv-consumer-event-kinds)
                 (:instance fn-psrv-consumer-event-is-no-identity-event)
                 (:instance fn-psrv-projection-ok-sequence
                            (c (fn-sn-consumer s)) (expected (fn-sn-identity-next s)))
                 (:instance fn-psrv-identity-step-of-plain-event))
           :in-theory '(fn-sn-prepare-consumer fn-cstp-relation-is-statep fn-cpr-event-servedp))))

; The topic prepare stages E when the carried topic prefix accepts it; its
; completion also needs the consumer projection to accept it
; (fn-sn-completion-enabledp), which fn-sn-prepare-topic does not test.  The
; hypothesis names that test; fn-psrv-prepare-topic makes it.
(defthm fn-psrv-sn-prepare-topic-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s)
                (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e
                                                 (fn-sn-identity-next s)))
                    :ok))
           (and (fn-cst-relation (fn-sn-prepare-topic s e))
                (fn-cstp-carriedp (fn-sn-prepare-topic s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-sn-prepare-topic s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-sf-prepare-record (fn-sn-files s) e (fn-sn-groups s)
                                                     (fn-sn-capacity s))))
                 (:instance fn-psrv-sf-prepare-record-staged
                            (files (fn-sn-files s)) (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-prepare-topic-preserves-state (event e))
                 (:instance fn-psrv-topic-event-kinds)
                 (:instance fn-psrv-topic-event-is-no-identity-event)
                 (:instance fn-psrv-projection-ok-sequence
                            (c (fn-sn-consumer s)) (expected (fn-sn-identity-next s)))
                 (:instance fn-psrv-identity-step-of-plain-event))
           :in-theory '(fn-sn-prepare-topic fn-cstp-relation-is-statep fn-cpr-event-servedp))))

(defthm fn-psrv-sn-statep-node-statep
  (implies (fn-sn-statep s) (fn-node-statep (fn-sn-node s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defthm fn-psrv-pcar-stage-record-staged
  (let ((f (fn-pcar-stage-record files e)))
    (implies (and (equal (fn-sf-phase files) :reserved)
                  (equal (fn-sf-phase f) :record-staged))
             (and (equal (fn-sf-record-candidate f) e)
                  (equal (fn-sf-records f) (fn-sf-records files))
                  (equal (fn-sf-frontier f) (fn-sf-frontier files))
                  (fn-sf-candidatep e (fn-sf-records files) (fn-sf-frontier files)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pcar-stage-record-is-stage-record fn-spc-stage-record)
                                  (fn-sf-candidatep fn-sf-statep)))))

(defthm fn-psrv-ccar-sn-prepare-identity-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s)
                (fn-cpr-event-servedp (fn-cstp-fold (fn-sn-config-history s)
                                                    (fn-sf-records (fn-sn-files s)))
                                      e))
           (and (fn-cst-relation (fn-ccar-sn-prepare-identity s e))
                (fn-cstp-carriedp (fn-ccar-sn-prepare-identity s e))))
  :hints (("Goal"
           :cases ((not (equal (fn-ccar-sn-prepare-identity s e) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use ((:instance fn-psrv-deferred-stage-preserves
                            (f (fn-pcar-stage-record (fn-sn-files s) e)))
                 (:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-update-preserves-state
                            (files (fn-pcar-stage-record (fn-sn-files s) e))
                            (node (fn-sn-node s)))
                 (:instance fn-cstp-stage-record-preserves-state
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-pcar-stage-record-is-stage-record
                            (files (fn-sn-files s)) (record e))
                 (:instance fn-psrv-sn-statep-node-statep)
                 (:instance fn-psrv-identity-event-kinds)
                 (:instance fn-psrv-topic-step-of-untopical (p (fn-sn-topic s)))
                 (:instance fn-psrv-reserved-carried-facts))
           :in-theory '(fn-ccar-sn-prepare-identity fn-cstp-relation-is-statep fn-cstp-sn-statep-files fn-sf-candidatep
                        fn-ccar-cpe-projection-step-is-cpe-projection-step))))

(defthm fn-psrv-deferred-completion-enabled-after-dir
  (implies (and (fn-cst-relation s)
                (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                (not (fn-held-p (fn-sf-record-candidate (fn-sn-files s)))))
           (fn-sn-completion-enabledp (fn-sn-io s :record-directory :ok)))
  :hints (("Goal"
           :use (fn-cstp-record-dir-ok-files fn-cstp-completion-record-after-dir
                 (:instance fn-cstp-io-fields (operation :record-directory) (result :ok))
                 (:instance fn-sn-io-preserves-state (operation :record-directory)
                            (result :ok)))
           :in-theory '(fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                        fn-cst-relation fn-cst-deferred-linkp fn-cstp-carriedp
                        fn-cstp-relation-is-statep fn-sn-identity-context
                        fn-replay-apply-record
                        fn-sf-record-phasep fn-snt-idle-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

; KEYSTONE (store).  The directory observation that publishes a staged
; deferred record (retention, identity, consumer or topic) keeps the
; configured relation, given the carried companion.
(defthm fn-psrv-deferred-record-dir-preserves-relation
  (implies (and (fn-cst-relation s)
                (fn-cstp-carriedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                (not (fn-held-p (fn-sf-record-candidate (fn-sn-files s)))))
           (fn-cst-relation (fn-sn-io s :record-directory :ok)))
  :hints (("Goal"
           :use (fn-cstp-record-dir-ok-files fn-cstp-completion-record-after-dir
                 fn-psrv-deferred-completion-enabled-after-dir
                 (:instance fn-cstp-io-fields (operation :record-directory) (result :ok))
                 (:instance fn-sn-io-preserves-state (operation :record-directory)
                            (result :ok))
                 (:instance fn-cstp-completion-record-is-a-true-list
                            (s (fn-sn-io s :record-directory :ok)))
                 (:instance fn-cstp-statep-observed (st (fn-sn-io s :record-directory :ok)))
                 (:instance fn-cstp-final-configuration-of-longer-history
                            (a s) (b (fn-sn-io s :record-directory :ok))
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory '(fn-cst-relation fn-cst-deferred-linkp fn-cst-completion-linkp
                        fn-cstp-relation-is-statep
                        fn-sf-record-phasep fn-snt-idle-phasep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-psrv-known-abort-files-facts
  (implies (and (fn-sf-statep files)
                (member-equal (fn-sf-phase files) '(:record-staged :record-data-durable)))
           (let ((next (fn-sn-known-abort-files files)))
             (and (equal (fn-sf-phase next) :ready)
                  (equal (fn-sf-frontier next) (fn-sf-frontier files))
                  (equal (fn-sf-records next) (fn-sf-records files)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-snt-typed-record-phase) fn-sn-known-abort-file-start-preserves-state)
           :in-theory (e/d (fn-sn-known-abort-files fn-sn-known-abort-file-start
                            fn-sf-record-file-result fn-sf-prepublish-abort
                            fn-sf-abort-completion fn-sf-record-pair fn-sf-candidatep
                            fn-sf-record-phasep)
                           (fn-sf-statep fn-store-event-p fn-store-event-sequence
                            fn-store-event-txid)))))

(defthm fn-psrv-known-abort-cases
  (or (equal (fn-sn-known-abort s) s)
      (let ((b (fn-sn-known-abort s))
            (r (fn-sf-record-candidate (fn-sn-files s))))
        (and (fn-sn-statep s)
             (member-equal (fn-sf-phase (fn-sn-files s)) '(:record-staged :record-data-durable))
             (equal (fn-sn-node b)
                    (if (fn-held-p r)
                        (fn-node-complete (fn-sn-node s) (fn-record-txid r)
                                          (fn-record-generation r) :aborted)
                      (fn-replay-advance-txid (fn-sn-node s) (fn-sf-frontier (fn-sn-files s)))))
             (equal (fn-sn-files b) (fn-sn-known-abort-files (fn-sn-files s)))
             (equal (fn-sn-config-history b) (fn-sn-config-history s))
             (equal (fn-sn-groups b) (fn-sn-groups s))
             (equal (fn-sn-capacity b) (fn-sn-capacity s))
             (equal (fn-sn-topic b) (fn-sn-topic s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort fn-sn-known-abort-enabledp
                                   fn-sn-record-bindsp fn-cstp-sn-update-fields)
                                  (fn-sn-statep fn-sn-known-abort-files fn-held-p
                                   fn-store-retention-event-p fn-node-complete
                                   fn-replay-advance-txid fn-node-pending-matchesp
                                   fn-replay-apply-retention-event fn-held-wire
                                   fn-sn-pending-record)))))

; KEYSTONE (store).  The known abort (host/owner-host.lisp
; fn-owner-known-abort: (:store (:known-abort)), fn-sn-known-abort) keeps the
; configured relation and the carried companion, every candidate.
(defthm fn-psrv-known-abort-preserves
  (implies (and (fn-cst-relation s) (fn-cstp-carriedp s))
           (and (fn-cst-relation (fn-sn-known-abort s))
                (fn-cstp-carriedp (fn-sn-known-abort s))))
  :hints (("Goal"
           :cases ((not (equal (fn-sn-known-abort s) s)))
           :in-theory nil)
          ("Subgoal 1"
           :use (fn-psrv-known-abort-cases
                 fn-sn-known-abort-preserves-state
                 (:instance fn-psrv-known-abort-files-facts (files (fn-sn-files s)))
                 (:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                 (:instance fn-cstp-final-configurationp-congruence
                            (a s) (b (fn-sn-known-abort s)))
                 (:instance fn-cstp-statep-observed (st (fn-sn-known-abort s)))
                 (:instance fn-cstp-recoverable-later
                            (configs (fn-sn-config-history s))
                            (events (fn-sf-records (fn-sn-files s)))
                            (f (+ -1 (fn-sf-frontier (fn-sn-files s))))
                            (g (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-cstp-topic-step-ok-facts
                            (p (fn-sn-topic s))
                            (e (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-cstp-held-kind-facts
                            (x (fn-sf-record-candidate (fn-sn-files s))))
                 (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory '(fn-cst-relation fn-cst-pending-linkp fn-cst-deferred-linkp
                        fn-cstp-carriedp fn-sf-candidatep
                        fn-cstp-relation-is-statep
                        fn-snt-idle-phasep fn-sf-record-phasep member-equal
                        natp posp nfix fn-psrv-successor-of-predecessor
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-snt-idle-phasep)
                        (:executable-counterpart fn-sf-record-phasep)))))

(defthm fn-psrv-store-step-is-owner-with-store
  (equal (fn-ocfg-step oc (list :store ev) fn-arena)
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                 (fn-ocfg-owner oc)
                                 (fn-snrt-step (fn-own-store (fn-ocfg-owner oc)) ev))))
  :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-own-store-step
                               fn-ocl-owner-with-store car-cons cdr-cons
                               (:executable-counterpart equal)))))

; The owner over a Store step that keeps the configuration history and the
; durable history, and carries the Store's relation and companion, keeps the
; carried invariant.
(defthm fn-psrv-owner-with-store-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-cst-relation st)
                (fn-cstp-carriedp st)
                (equal (fn-sn-config-history st)
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                (equal (fn-sf-records (fn-sn-files st))
                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           (fn-lgoc-invariantp
            (fn-ocfg-with-owner oc (fn-ocl-owner-with-store (fn-ocfg-owner oc) st))))
  :hints (("Goal"
           :use (fn-lgoc-ocl-relation-of-owner-with-store
                 fn-lgoc-invariant-statep
                 (:instance fn-sf-prefixp-reflexive
                            (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                 (:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-cstp-sn-statep-files (st (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-lgoc-invariantp fn-lgoc-store-of-owner-with-store))))

(defthm fn-psrv-deferred-prepare-keeps-histories
  (and (equal (fn-sn-config-history (fn-sn-prepare-retention s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-retention s e)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-config-history (fn-sn-prepare-consumer s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-consumer s e)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-config-history (fn-sn-prepare-topic s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-topic s e)))
              (fn-sf-records (fn-sn-files s)))
       (equal (fn-sn-config-history (fn-ccar-sn-prepare-identity s e)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-ccar-sn-prepare-identity s e)))
              (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use ((:instance fn-psrv-sf-prepare-record-staged
                            (files (fn-sn-files s)) (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s)))
                 (:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files s))))
           :in-theory '(fn-sn-prepare-retention fn-sn-prepare-consumer fn-sn-prepare-topic
                        fn-ccar-sn-prepare-identity fn-cstp-sn-update-fields))))

(defthm fn-psrv-known-abort-keeps-histories
  (and (equal (fn-sn-config-history (fn-sn-known-abort s)) (fn-sn-config-history s))
       (equal (fn-sf-records (fn-sn-files (fn-sn-known-abort s)))
              (fn-sf-records (fn-sn-files s))))
  :hints (("Goal"
           :use (fn-psrv-known-abort-cases
                 (:instance fn-psrv-known-abort-files-facts (files (fn-sn-files s)))
                 (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory nil)))

; -----------------------------------------------------------------------------
; The owner transitions the host calls.

; KEYSTONE (owner).  The article prepare the host calls
; (host/owner-host.lisp fn-owner-prepare-buffer: fn-psrv-prepare over the
; carry fn-prc-refresh builds, which satisfies fn-prc-carryp by
; fn-prc-carryp-of-refresh) keeps the carried invariant for EVERY record:
; the served test is the transition's own, so the hypothesis control-quanta-2
; had to take (fn-lgoc-pidx-sbud-prepare-preserves-invariant) is gone.  The
; two index premises are carried by every owner transition the host installs
; (PRF-191, PRF-242).
(defthm fn-psrv-prepare-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-prc-carryp carry)
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (fn-lgoc-invariantp (fn-psrv-prepare oc record budget carry)))
  :hints (("Goal"
           :cases ((and (fn-psrv-event-servedp (fn-ocfg-config oc) record)
                        (fn-psrv-event-numberedp oc record))
                   (not (fn-psrv-event-servedp (fn-ocfg-config oc) record)))
           :use (fn-lgoc-pidx-sbud-prepare-preserves-invariant
                 fn-prc-sbud-prepare-is-pidx-sbud-prepare
                 fn-psrv-prepare-refuses-unserved fn-psrv-prepare-refuses-exhausted
                 fn-psrv-prepare-when-served)
           :in-theory '(fn-psrv-event-servedp))))

(defthm fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store
  (equal (fn-ccar-ocfg-prepare-identity oc e)
         (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                 (fn-ocfg-owner oc)
                                 (fn-ccar-sn-prepare-identity
                                  (fn-own-store (fn-ocfg-owner oc)) e))))
  :hints (("Goal" :in-theory '(fn-ccar-ocfg-prepare-identity fn-ocl-owner-with-store))))

(defthm fn-psrv-invariant-served-is-fold-served
  (implies (fn-lgoc-invariantp oc)
           (equal (fn-cpr-event-servedp
                   (fn-cstp-fold (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                                 (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                   e)
                  (fn-psrv-event-servedp (fn-ocfg-config oc) e)))
  :hints (("Goal" :use (fn-lgoc-ocl-relation-config-fold)
           :in-theory '(fn-lgoc-invariantp fn-psrv-event-servedp-is-cpr-event-servedp))))

; KEYSTONE (owner).  The identity prepare the host calls
; (host/owner-host.lisp fn-owner-prepare-identity: fn-psrv-prepare-identity)
; keeps the carried invariant for every event: a keyring snapshot, a verdict,
; or a signed composite, whose article's groups the transition tests.
(defthm fn-psrv-prepare-identity-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-psrv-prepare-identity oc e)))
  :hints (("Goal"
           :cases ((and (fn-psrv-event-servedp (fn-ocfg-config oc) e)
                        (fn-psrv-event-numberedp oc e))
                   (not (fn-psrv-event-servedp (fn-ocfg-config oc) e)))
           :use ((:instance fn-psrv-prepare-refuses-unserved (record e))
                 (:instance fn-psrv-prepare-refuses-exhausted (record e))
                 (:instance fn-psrv-prepare-when-served (record e))
                 fn-psrv-invariant-served-is-fold-served
                 (:instance fn-psrv-ccar-sn-prepare-identity-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-ccar-sn-prepare-identity
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store
                        fn-psrv-deferred-prepare-keeps-histories
                        fn-lgoc-invariantp))))

; KEYSTONE (owner).  The retention prepare the host calls
; (host/owner-host.lisp fn-owner-prepare-retention: (:store
; (:prepare-retention E)) through fn-owner-step) keeps the carried invariant.
(defthm fn-psrv-prepare-retention-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (fn-ocfg-step oc (list :store (list :prepare-retention e)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-psrv-sn-prepare-retention-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-sn-prepare-retention
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-psrv-store-step-is-owner-with-store fn-snrt-step
                        fn-psrv-deferred-prepare-keeps-histories fn-lgoc-invariantp
                        car-cons cdr-cons (:executable-counterpart equal)))))

; KEYSTONE (owner).  The consumer prepare the host calls
; (host/owner-host.lisp fn-owner-prepare-consumer: (:store (:prepare-consumer
; E)) through fn-owner-step) keeps the carried invariant.
(defthm fn-psrv-prepare-consumer-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (fn-ocfg-step oc (list :store (list :prepare-consumer e)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-psrv-sn-prepare-consumer-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-sn-prepare-consumer
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-psrv-store-step-is-owner-with-store fn-snrt-step
                        fn-psrv-deferred-prepare-keeps-histories fn-lgoc-invariantp
                        car-cons cdr-cons (:executable-counterpart equal)))))

(defthm fn-psrv-prepare-topic-cases
  (equal (fn-psrv-prepare-topic oc e)
         (if (and (fn-store-event-p e)
                  (eq (car (fn-cpe-projection-step
                            (fn-sn-consumer (fn-own-store (fn-ocfg-owner oc))) e
                            (fn-sn-identity-next (fn-own-store (fn-ocfg-owner oc)))))
                      :ok))
             (fn-ocfg-with-owner oc (fn-ocl-owner-with-store
                                     (fn-ocfg-owner oc)
                                     (fn-sn-prepare-topic
                                      (fn-own-store (fn-ocfg-owner oc)) e)))
           oc))
  :hints (("Goal" :in-theory '(fn-psrv-prepare-topic fn-ocl-owner-with-store
                               fn-ccar-cpe-projection-step-is-cpe-projection-step))))

; KEYSTONE (owner).  The topic prepare the host calls (host/owner-host.lisp
; fn-owner-prepare-topic: fn-psrv-prepare-topic) keeps the carried invariant
; for every event: its consumer test is what the relation's completion needs.
(defthm fn-psrv-prepare-topic-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-psrv-prepare-topic oc e)))
  :hints (("Goal"
           :use ((:instance fn-psrv-sn-prepare-topic-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-sn-prepare-topic
                                 (fn-own-store (fn-ocfg-owner oc)) e)))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-psrv-prepare-topic-cases
                        fn-psrv-deferred-prepare-keeps-histories fn-lgoc-invariantp))))

; The topic prepare is the configured owner's (:store (:prepare-topic E))
; whenever its consumer test admits E.
(defthm fn-psrv-prepare-topic-is-ocfg-step-when-admitted
  (implies (and (fn-store-event-p e)
                (eq (car (fn-cpe-projection-step
                          (fn-sn-consumer (fn-own-store (fn-ocfg-owner oc))) e
                          (fn-sn-identity-next (fn-own-store (fn-ocfg-owner oc)))))
                    :ok))
           (equal (fn-psrv-prepare-topic oc e)
                  (fn-ocfg-step oc (list :store (list :prepare-topic e)) fn-arena)))
  :hints (("Goal" :in-theory '(fn-psrv-prepare-topic-cases
                               fn-psrv-store-step-is-owner-with-store fn-snrt-step
                               car-cons cdr-cons (:executable-counterpart equal)))))

; KEYSTONE (owner).  The known abort the host calls (host/owner-host.lisp
; fn-owner-known-abort: (:store (:known-abort)) through fn-owner-step) keeps
; the carried invariant, whatever is staged.
(defthm fn-psrv-known-abort-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp
            (fn-ocfg-step oc (list :store (list :known-abort)) fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-psrv-known-abort-preserves
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-psrv-owner-with-store-preserves-invariant
                            (st (fn-sn-known-abort (fn-own-store (fn-ocfg-owner oc)))))
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-psrv-store-step-is-owner-with-store fn-snrt-step
                        fn-psrv-known-abort-keeps-histories fn-lgoc-invariantp
                        car-cons (:executable-counterpart equal)))))
; -----------------------------------------------------------------------------
; The deferred publications' order: the file observations of any staged
; record, and the log route's order step whatever is staged.

(defun fn-psrv-io-safep (operation)
  ; The file steps fn-owner-io feeds on the reservation, the recovery
  ; barriers and the publication of ANY staged record.
  (declare (xargs :guard t))
  (or (fn-cstp-reserve-opp operation)
      (if (member-equal operation '(:record-file :record-link :record-directory)) t nil)))

(defthm fn-psrv-deferred-dir-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                       :record-attempted)
                (not (fn-held-p (fn-sf-record-candidate
                                 (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
           (fn-lgoc-invariantp (fn-rcon-ocfg-io oc :record-directory :ok)))
  :hints (("Goal"
           :use ((:instance fn-psrv-deferred-record-dir-preserves-relation
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-cstp-record-dir-preserves-carriedp
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-lgoc-ocl-relation-of-owner-with-store
                            (st (fn-sn-io (fn-own-store (fn-ocfg-owner oc))
                                          :record-directory :ok)))
                 (:instance fn-cstp-io-fields (s (fn-own-store (fn-ocfg-owner oc)))
                            (operation :record-directory) (result :ok))
                 (:instance fn-snt-io-records-prefix (s (fn-own-store (fn-ocfg-owner oc)))
                            (operation :record-directory) (result :ok))
                 fn-lgoc-invariant-statep
                 fn-lgoc-ocl-relation-cst)
           :in-theory '(fn-lgoc-invariantp fn-lgoc-rcon-io-is-owner-with-store
                        fn-lgoc-store-of-owner-with-store))))

; KEYSTONE (owner).  Every file observation fn-owner-io feeds the owner
; (host/owner-host.lisp: fn-rcon-ocfg-io) on the reservation, the recovery
; barriers and the publication of any staged record -- an article or a
; retention, identity, consumer or topic record -- keeps the carried
; invariant.  (control-quanta-2's fn-lgoc-rcon-io-preserves-invariant named
; the article's publication only.)
(defthm fn-psrv-rcon-io-preserves-invariant
  (implies (and (fn-lgoc-invariantp oc)
                (fn-psrv-io-safep operation))
           (fn-lgoc-invariantp (fn-rcon-ocfg-io oc operation result)))
  :hints (("Goal"
           :cases ((and (equal operation :record-directory) (equal result :ok)
                        (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                               :record-attempted)
                        (not (fn-held-p (fn-sf-record-candidate
                                         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))))
           :use (fn-lgoc-rcon-io-preserves-invariant fn-psrv-deferred-dir-preserves-invariant)
           :in-theory '(fn-psrv-io-safep fn-lgoc-io-safep member-equal
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

; KEYSTONE (owner).  The log route's ORDER step (host/owner-host.lisp
; fn-owner-io :log-order: fn-olr-ocfg-order) keeps the carried invariant
; whatever record is staged (fn-lgoc-log-order-preserves-invariant asked
; that the staged record be an article).
(defthm fn-psrv-log-order-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-olr-ocfg-order oc)))
  :hints (("Goal"
           :use ((:instance fn-psrv-rcon-io-preserves-invariant
                            (operation :record-file) (result :ok))
                 (:instance fn-psrv-rcon-io-preserves-invariant
                            (oc (fn-rcon-ocfg-io oc :record-file :ok))
                            (operation :record-link) (result :ok))
                 (:instance fn-psrv-rcon-io-preserves-invariant
                            (oc (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :record-file :ok)
                                                 :record-link :ok))
                            (operation :record-directory) (result :ok)))
           :in-theory '(fn-olr-ocfg-order fn-psrv-io-safep member-equal
                        (:executable-counterpart fn-cstp-reserve-opp)
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)))))

; -----------------------------------------------------------------------------
; The configuration un-stage.

; KEYSTONE (owner).  The un-stage the host calls after a refused publication
; (host/owner-host.lisp fn-owner-reconfigure-unstage: fn-psrv-unstage) keeps
; the carried invariant; the owner, its Store and so every durable fact are
; unchanged (a process death on either side of it recovers the same state:
; the staged record was never written), and the configuration lock is
; released.
(defthm fn-psrv-unstage-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (and (fn-lgoc-invariantp (fn-psrv-unstage oc))
                (equal (fn-ocfg-owner (fn-psrv-unstage oc)) (fn-ocfg-owner oc))
                (equal (fn-ocfg-config (fn-psrv-unstage oc)) (fn-ocfg-config oc))
                (equal (fn-ocfg-pins (fn-psrv-unstage oc)) (fn-ocfg-pins oc))
                (not (fn-ocfg-staged (fn-psrv-unstage oc)))))
  :hints (("Goal"
           :in-theory (e/d (fn-lgoc-invariantp fn-psrv-unstage fn-ocl-relation)
                           (fn-cstp-carriedp fn-cst-relation fn-ocl-config-historyp
                            fn-ocl-view-configp fn-ocl-view-historyp fn-ocl-conns-historyp
                            fn-ocl-unique-conn-idsp fn-ocfg-pins-okp fn-ocfg-conns-pinnedp
                            fn-ocfg-pins-pin-conns-only fn-own-ids-below-next-p
                            fn-own-ledger-durablep fn-clock-observationp fn-own-facts-okp
                            fn-cfgp fn-own-shapep fn-cfg-recordp)))))

; Accessor equalities used above as rewrite rules; withdrawn at export.
(in-theory (disable fn-psrv-store-step-is-owner-with-store
                    fn-psrv-ccar-ocfg-prepare-identity-is-owner-with-store
                    fn-psrv-prepare-topic-cases))
