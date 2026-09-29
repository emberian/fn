; fn: the open's transaction frontier admits every history the replay accepts
; (row B10, lane limits-live-2, 2026-09-29).
;
; A store's durable history is two journals: Store events, each consuming
; its transaction id, and configuration records, each naming the next
; unconsumed id when it was accepted (books/config-physical-replay.lisp).
; Every other thing the owner does leaves its txids either in one of those
; journals or nowhere: a refused POST (the transaction budget full, a
; duplicate, a refused group) and an aborted transaction consume ids and
; leave no record -- a gap, which the replay admits by raising an idle
; node's next id (fn-replay-advance-txid); a checkpoint, a compaction or a
; rotation drops log segments and leaves their frontier as the floor the
; open starts from.
;
; The open derives its frontier from what is durable -- the fold of every
; Store event's id, the fold of every configuration record's id, the
; checkpoint's floor -- and refuses :frontier when the replayed node stands
; above it (books/replay-identity-index.lisp fn-rii-sco-finalize-configured,
; through fn-rii-advance-idlep).  The walk F3 of the operability review
; (2026-09-29) was that refusal: refused POSTs on a full budget consumed
; txids 12 and 13, a group create was accepted naming 14, and the open's
; frontier came from the events alone (12).
;
; KEYSTONE fn-ofr-replay-ok-frontier-admits: over ANY interleaving of the two
; journals -- every event kind the replay applies (articles, composites,
; retention undertakings and releases, identity, consumer and topic events)
; and every configuration record (groups, limits, every :set-* row), with
; ANY gaps between ids -- a replay that succeeds from a node idle at or
; below the floor ends idle at or below the open's frontier.  The gaps are
; universally quantified: whatever a refusal consumes, the open accounts
; for it.  So the open's frontier check never refuses a history the replay
; accepts; the premise the replay accepts the durable history is the
; configuration crash theorems' (books/config-crash-replay.lisp).

(in-package "ACL2")
(include-book "config-physical-replay")

(local (in-theory (disable (tau-system))))

; The frontier folds.  Each is the one the host calls
; (host/store-host.lisp, host/store-node-host.lisp).

(defun fn-ofr-events-next (events acc)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-ofr-events-next
       (cdr events)
       (let ((txid (fn-store-event-txid (car events))))
         (if (natp txid) (max (nfix acc) (+ 1 txid)) (nfix acc))))
    (nfix acc)))

(defun fn-ofr-configs-next (configs acc)
  (declare (xargs :guard t))
  (if (consp configs)
      (fn-ofr-configs-next
       (cdr configs)
       (let ((txid (fn-cfg-record-txid (car configs))))
         (if (natp txid) (max (nfix acc) txid) (nfix acc))))
    (nfix acc)))

(defun fn-ofr-frontier (configs events floor)
  (declare (xargs :guard t))
  (max (fn-ofr-events-next events floor)
       (fn-ofr-configs-next configs floor)))

; -----------------------------------------------------------------------------
; One step of the replay leaves an idle node at a known next id.

(defun fn-ofr-idlep (node)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-node-statep node)
       (null (fn-node-stage node))
       (null (fn-state-pending (fn-node-acceptance node)))
       (equal (fn-state-fenced (fn-node-acceptance node)) nil)))

(defthm fn-ofr-node-statep-acceptance
  (implies (fn-node-statep s) (fn-statep (fn-node-acceptance s)))
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(defthm fn-ofr-prepare-matching-consumes-next
  (implies (and (fn-node-statep s)
                (null (fn-node-stage s))
                (fn-node-pending-matchesp
                 (fn-node-prepare s generation msgid payload groups id subject evidence charge stamp)
                 txid gen))
           (and (equal (fn-state-next-txid (fn-node-acceptance s)) txid)
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-node-prepare s generation msgid payload groups id subject evidence
                                          charge stamp)))
                       (+ 1 txid))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-node-prepare fn-accept-prepare fn-node-pending-matchesp
                                     fn-pending-matchesp fn-make-state fn-state-pending
                                     fn-state-next-txid fn-state-fenced fn-make-pending
                                     fn-pending-txid fn-pending-generation))))

(defthm fn-ofr-complete-matching-is-idle
  (implies (and (fn-node-statep s)
                (fn-node-pending-matchesp s txid gen))
           (and (not (fn-node-stage (fn-node-complete s txid gen :durable)))
                (not (fn-state-pending (fn-node-acceptance (fn-node-complete s txid gen :durable))))
                (not (fn-state-fenced (fn-node-acceptance (fn-node-complete s txid gen :durable))))
                (equal (fn-state-next-txid (fn-node-acceptance (fn-node-complete s txid gen :durable)))
                       (fn-state-next-txid (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (enable fn-node-complete fn-accept-complete fn-install-pending
                                     fn-node-pending-matchesp fn-pending-matchesp fn-make-state
                                     fn-state-pending fn-state-next-txid fn-state-fenced
                                     fn-state-groups fn-state-nexts fn-state-articles))))

(defthm fn-ofr-advance-of-idle
  (implies (and (fn-ofr-idlep node)
                (natp txid)
                (<= (fn-state-next-txid (fn-node-acceptance node)) txid))
           (and (fn-ofr-idlep (fn-replay-advance-txid node txid))
                (equal (fn-state-next-txid (fn-node-acceptance (fn-replay-advance-txid node txid)))
                       txid)))
  :hints (("Goal" :use ((:instance fn-replay-advance-preserves-node-statep (recorded-txid txid)))
           :in-theory (e/d (fn-ofr-idlep fn-replay-advance-txid fn-make-state fn-state-next-txid
                            fn-state-pending fn-state-fenced fn-node-make-state fn-node-stage
                            fn-node-acceptance)
                           (fn-replay-advance-preserves-node-statep)))))

(defthm fn-ofr-idlep-parts
  (implies (fn-ofr-idlep node)
           (and (fn-node-statep node) (not (fn-node-stage node))
                (not (fn-state-pending (fn-node-acceptance node)))
                (not (fn-state-fenced (fn-node-acceptance node)))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-ofr-idlep-of-make-state
  (implies (and (fn-node-statep (fn-node-make-state a r nil b))
                (not (fn-state-pending a))
                (not (fn-state-fenced a)))
           (fn-ofr-idlep (fn-node-make-state a r nil b)))
  :hints (("Goal" :in-theory (enable fn-node-make-state fn-node-stage fn-node-acceptance))))

(in-theory (disable fn-ofr-idlep))

(defthm fn-ofr-advance-below-is-identity
  (implies (< txid (fn-state-next-txid (fn-node-acceptance node)))
           (equal (fn-replay-advance-txid node txid) node))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ofr-statep-before-advance
  (implies (fn-node-statep (fn-replay-advance-txid node txid))
           (fn-node-statep node))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ofr-make-state-accessors
  (and (equal (fn-node-acceptance (fn-node-make-state a r s b)) a)
       (equal (fn-node-stage (fn-node-make-state a r s b)) s))
  :hints (("Goal" :in-theory (enable fn-node-make-state fn-node-stage fn-node-acceptance))))

; Every event kind the replay applies: an article or a composite completes
; at its id, a retention undertaking or release and an identity, consumer
; or topic event advance past it.  Whatever gap precedes the event is
; admitted by the advance.
(defthm fn-ofr-apply-record-idle-past-txid
  (implies (and (fn-ofr-idlep node)
                (natp (fn-store-event-txid record))
                (fn-node-statep (fn-replay-apply-record node record)))
           (fn-replay-advance-okp (fn-replay-apply-record node record)
                                  (+ 1 (fn-store-event-txid record))))
  :hints (("Goal" :cases ((<= (fn-state-next-txid (fn-node-acceptance node))
                              (fn-store-event-txid record)))
           :use ((:instance fn-ofr-prepare-matching-consumes-next
                            (s (fn-replay-advance-txid node (fn-store-event-txid record)))
                            (generation (fn-record-generation record))
                            (msgid (fn-record-msgid record))
                            (payload (fn-record-payload record))
                            (groups (fn-record-groups record))
                            (id (fn-record-obligation-id record))
                            (subject (fn-record-content-subject record))
                            (evidence (fn-record-release-evidence record))
                            (charge (fn-record-charge record))
                            (stamp (fn-record-stamp record))
                            (txid (fn-record-txid record))
                            (gen (fn-record-generation record)))
                 (:instance fn-ofr-prepare-matching-consumes-next
                            (s (fn-replay-advance-txid node (fn-store-event-txid record)))
                            (generation (fn-record-generation (fn-replay-composite-held record)))
                            (msgid (fn-record-msgid (fn-replay-composite-held record)))
                            (payload (fn-record-payload (fn-replay-composite-held record)))
                            (groups (fn-record-groups (fn-replay-composite-held record)))
                            (id (fn-record-obligation-id (fn-replay-composite-held record)))
                            (subject (fn-record-content-subject (fn-replay-composite-held record)))
                            (evidence (fn-record-release-evidence (fn-replay-composite-held record)))
                            (charge (fn-record-charge (fn-replay-composite-held record)))
                            (stamp (fn-record-stamp (fn-replay-composite-held record)))
                            (txid (fn-record-txid (fn-replay-composite-held record)))
                            (gen (fn-record-generation (fn-replay-composite-held record)))))
           :in-theory (e/d (fn-replay-apply-record fn-replay-apply-retention-event
                            fn-replay-apply-identity-neutral fn-replay-complete-retention
                            fn-replay-advance-okp fn-replay-node-with-retention)
                           (fn-replay-advance-txid fn-node-prepare fn-node-complete
                            fn-node-pending-matchesp fn-store-event-p fn-record-p fn-stxe-p
                            fn-stxk-p fn-stxa-p fn-store-retention-event-p fn-cpe-eventp
                            fn-th-topic-eventp fn-hstxa-p fn-held-p fn-replay-composite-held
                            fn-node-statep)))))

(defthm fn-ofr-next-txid-natp
  (implies (fn-node-statep n) (natp (fn-state-next-txid (fn-node-acceptance n))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-ofr-apply-record-txid-natp
  (implies (and (fn-ofr-idlep node)
                (fn-node-statep (fn-replay-apply-record node record)))
           (natp (fn-store-event-txid record)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-apply-identity-neutral fn-replay-complete-retention
                                   fn-replay-node-with-retention fn-replay-advance-txid)
                                  (fn-node-prepare fn-node-complete
                                   fn-node-pending-matchesp fn-store-event-p fn-record-p fn-stxe-p
                                   fn-stxk-p fn-stxa-p fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-hstxa-p fn-held-p fn-replay-composite-held
                                   fn-node-statep)))))

(defthmd fn-ofr-okp-is-idle-within
  (equal (fn-replay-advance-okp node bound)
         (and (fn-ofr-idlep node) (natp bound)
              (<= (fn-state-next-txid (fn-node-acceptance node)) bound)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp fn-ofr-idlep))))

; -----------------------------------------------------------------------------
; The two replay steps, at the configured node.

(defthm fn-ofr-cpr-apply-event-step
  (implies (and (fn-ofr-idlep (fn-cnode-node cn))
                (fn-cnode-statep (fn-cpr-apply-event cn event)))
           (and (natp (fn-store-event-txid event))
                (fn-ofr-idlep (fn-cnode-node (fn-cpr-apply-event cn event)))
                (<= (fn-state-next-txid (fn-node-acceptance (fn-cnode-node (fn-cpr-apply-event cn event))))
                    (+ 1 (fn-store-event-txid event)))))
  :hints (("Goal" :use ((:instance fn-ofr-apply-record-txid-natp
                                   (node (fn-cnode-node cn)) (record event))
                        (:instance fn-ofr-apply-record-idle-past-txid
                                   (node (fn-cnode-node cn)) (record event))
                        (:instance fn-ofr-okp-is-idle-within
                                   (node (fn-replay-apply-record (fn-cnode-node cn) event))
                                   (bound (+ 1 (fn-store-event-txid event)))))
           :in-theory (e/d (fn-cpr-apply-event)
                           (fn-replay-apply-record fn-ofr-apply-record-idle-past-txid
                            fn-cpr-event-servedp fn-store-event-p fn-cnode-statep
                            fn-node-statep fn-replay-advance-okp)))))

(defthm fn-ofr-apply-config-step
  (implies (and (fn-cnode-statep cn)
                (fn-ofr-idlep (fn-cnode-node cn))
                (fn-node-statep (fn-cnode-node (fn-cnode-apply-config cn record ceiling))))
           (and (fn-ofr-idlep (fn-cnode-node (fn-cnode-apply-config cn record ceiling)))
                (equal (fn-state-next-txid
                        (fn-node-acceptance (fn-cnode-node (fn-cnode-apply-config cn record ceiling))))
                       (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn))))))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config fn-make-state fn-state-next-txid
                                   fn-state-pending fn-state-fenced)
                                  (fn-cnode-statep fn-node-statep fn-cnode-record-acceptablep)))))

; -----------------------------------------------------------------------------
; The folds.

(defthm fn-ofr-events-next-at-least
  (<= (nfix acc) (fn-ofr-events-next events acc))
  :rule-classes :linear)

(defthm fn-ofr-configs-next-at-least
  (<= (nfix acc) (fn-ofr-configs-next configs acc))
  :rule-classes :linear)

(defthm fn-ofr-events-next-natp
  (natp (fn-ofr-events-next events acc))
  :rule-classes :type-prescription)

(defthm fn-ofr-configs-next-natp
  (natp (fn-ofr-configs-next configs acc))
  :rule-classes :type-prescription)

(defthm fn-ofr-events-next-of-max
  (implies (natp tx)
           (equal (fn-ofr-events-next events (max (nfix acc) tx))
                  (max (fn-ofr-events-next events acc) tx))))

(defthm fn-ofr-configs-next-of-max
  (implies (natp tx)
           (equal (fn-ofr-configs-next configs (max (nfix acc) tx))
                  (max (fn-ofr-configs-next configs acc) tx))))

(defthm fn-ofr-configs-next-of-cons
  (implies (and (consp configs) (natp (fn-cfg-record-txid (car configs))))
           (equal (fn-ofr-configs-next configs acc)
                  (fn-ofr-configs-next (cdr configs)
                                       (max (nfix acc) (fn-cfg-record-txid (car configs)))))))

(defthm fn-ofr-events-next-of-cons
  (implies (and (consp events) (natp (fn-store-event-txid (car events))))
           (equal (fn-ofr-events-next events acc)
                  (fn-ofr-events-next (cdr events)
                                      (max (nfix acc) (+ 1 (fn-store-event-txid (car events))))))))

(defthm fn-ofr-frontier-config-step
  (implies (and (consp configs) (natp (fn-cfg-record-txid (car configs))))
           (and (equal (fn-ofr-frontier (cdr configs) events
                                        (max (nfix acc) (fn-cfg-record-txid (car configs))))
                       (fn-ofr-frontier configs events acc))
                (<= (fn-cfg-record-txid (car configs)) (fn-ofr-frontier configs events acc))))
  :hints (("Goal" :use ((:instance fn-ofr-events-next-of-max (tx (fn-cfg-record-txid (car configs))))
                        (:instance fn-ofr-configs-next-at-least (configs (cdr configs))
                                   (acc (max (nfix acc) (fn-cfg-record-txid (car configs))))))
           :in-theory (e/d (fn-ofr-frontier)
                           (fn-ofr-events-next fn-ofr-configs-next fn-ofr-events-next-of-max
                            fn-ofr-configs-next-at-least)))))

(defthm fn-ofr-frontier-event-step
  (implies (and (consp events) (natp (fn-store-event-txid (car events))))
           (and (equal (fn-ofr-frontier configs (cdr events)
                                        (max (nfix acc) (+ 1 (fn-store-event-txid (car events)))))
                       (fn-ofr-frontier configs events acc))
                (<= (+ 1 (fn-store-event-txid (car events))) (fn-ofr-frontier configs events acc))))
  :hints (("Goal" :use ((:instance fn-ofr-configs-next-of-max (tx (+ 1 (fn-store-event-txid (car events)))))
                        (:instance fn-ofr-events-next-at-least (events (cdr events))
                                   (acc (max (nfix acc) (+ 1 (fn-store-event-txid (car events)))))))
           :in-theory (e/d (fn-ofr-frontier)
                           (fn-ofr-events-next fn-ofr-configs-next fn-ofr-configs-next-of-max
                            fn-ofr-events-next-at-least)))))

(defthm fn-ofr-frontier-at-least
  (<= (nfix acc) (fn-ofr-frontier configs events acc))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The fold over the two journals.

(defthm fn-ofr-cnode-statep-node
  (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))
(defthm fn-ofr-loop-ok-has-cnode-state
  (implies (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok)
           (fn-cnode-statep cn))
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es)))))
(defthm fn-ofr-loop-base
  (implies (and (not (fn-cpr-config-firstp configs events))
                (not (consp events))
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (equal (fn-replay-result-node (fn-cpr-loop cn configs events cs es)) cn))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es))
           :in-theory (disable fn-cpr-config-firstp fn-cnode-statep))))
(defthm fn-ofr-loop-config
  (implies (and (fn-cpr-config-firstp configs events)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (let ((at (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn)
                                                            (fn-cfg-record-txid (car configs)))
                                    (fn-cnode-config cn))))
             (and (fn-replay-advance-okp (fn-cnode-node cn) (fn-cfg-record-txid (car configs)))
                  (fn-cnode-statep at)
                  (equal (fn-cpr-loop cn configs events cs es)
                         (fn-cpr-loop (fn-cnode-apply-config at (car configs) (fn-cnode-line-ceiling))
                                      (cdr configs) events (+ 1 (nfix cs)) es)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es))
           :in-theory (disable fn-cpr-config-firstp fn-cnode-statep fn-replay-advance-okp
                               fn-replay-advance-txid fn-cnode-apply-config fn-cfg-recordp
                               fn-cnode-record-acceptablep fn-cnode-carried-acceptablep))))
(defthm fn-ofr-loop-event
  (implies (and (not (fn-cpr-config-firstp configs events))
                (consp events)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
           (and (fn-cnode-statep (fn-cpr-apply-event cn (car events)))
                (equal (fn-cpr-loop cn configs events cs es)
                       (fn-cpr-loop (fn-cpr-apply-event cn (car events)) configs (cdr events)
                                    cs (+ 1 (nfix es))))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es))
           :in-theory (disable fn-cpr-config-firstp fn-cnode-statep fn-cpr-apply-event
                               fn-store-event-p))))

(defun fn-ofr-loop-induct (cn configs events config-sequence event-sequence acc)
  (declare (xargs :measure (+ (len configs) (len events)) :verify-guards nil
                  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))
           (irrelevant config-sequence event-sequence))
  (if (not (fn-cnode-statep cn))
      acc
    (if (fn-cpr-config-firstp configs events)
        (let* ((record (car configs))
               (txid (fn-cfg-record-txid record))
               (node (fn-cnode-node cn))
               (at (fn-cnode-make (fn-replay-advance-txid node txid) (fn-cnode-config cn))))
          (fn-ofr-loop-induct (fn-cnode-apply-config at record (fn-cnode-line-ceiling))
                              (cdr configs) events (+ 1 (nfix config-sequence)) event-sequence
                              (if (natp txid) (max (nfix acc) txid) (nfix acc))))
      (if (consp events)
          (fn-ofr-loop-induct (fn-cpr-apply-event cn (car events)) configs (cdr events)
                              config-sequence (+ 1 (nfix event-sequence))
                              (let ((txid (fn-store-event-txid (car events))))
                                (if (natp txid) (max (nfix acc) (+ 1 txid)) (nfix acc))))
        acc))))

; From any idle node at or below ACC, a replay that succeeds ends idle at or
; below the frontier folded from ACC: the checkpoint open (ACC its floor,
; CN its node) and the full replay alike.
(defthm fn-ofr-loop-ok-within-frontier
  (implies (and (equal (fn-replay-result-kind
                        (fn-cpr-loop cn configs events config-sequence event-sequence))
                       :ok)
                (fn-ofr-idlep (fn-cnode-node cn))
                (natp acc)
                (<= (fn-state-next-txid (fn-node-acceptance (fn-cnode-node cn))) acc))
           (and (fn-ofr-idlep
                 (fn-cnode-node (fn-replay-result-node
                                 (fn-cpr-loop cn configs events config-sequence event-sequence))))
                (<= (fn-state-next-txid
                     (fn-node-acceptance
                      (fn-cnode-node (fn-replay-result-node
                                      (fn-cpr-loop cn configs events config-sequence
                                                   event-sequence)))))
                    (fn-ofr-frontier configs events acc))))
  :hints (("Goal" :induct (fn-ofr-loop-induct cn configs events config-sequence event-sequence acc)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (fn-ofr-okp-is-idle-within)
                           (fn-cpr-loop fn-cpr-apply-event fn-cnode-apply-config fn-cnode-statep
                            fn-node-statep fn-replay-advance-txid fn-cfg-recordp
                            fn-store-event-p fn-cnode-record-acceptablep fn-ofr-frontier
                            fn-ofr-events-next fn-ofr-configs-next fn-cpr-config-firstp
                            fn-ofr-cpr-apply-event-step fn-ofr-apply-config-step fn-ofr-advance-of-idle
                            fn-ofr-frontier-event-step fn-ofr-frontier-config-step)))
          ("Subgoal *1/4"
           :use ((:instance fn-ofr-loop-base (cs config-sequence) (es event-sequence))))
          ("Subgoal *1/3"
           :use ((:instance fn-ofr-loop-event (cs config-sequence) (es event-sequence))
                 (:instance fn-ofr-cpr-apply-event-step (event (car events)))
                 fn-ofr-frontier-event-step))
          ("Subgoal *1/2"
           :use ((:instance fn-ofr-loop-config (cs config-sequence) (es event-sequence))
                 (:instance fn-ofr-advance-of-idle (node (fn-cnode-node cn))
                            (txid (fn-cfg-record-txid (car configs))))
                 (:instance fn-ofr-apply-config-step
                            (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn)
                                                                       (fn-cfg-record-txid (car configs)))
                                               (fn-cnode-config cn)))
                            (record (car configs)) (ceiling (fn-cnode-line-ceiling)))
                 fn-ofr-frontier-config-step))))

(defthm fn-ofr-initial-idle
  (and (fn-ofr-idlep (fn-cnode-node (fn-cnode-initial (fn-cfg-initial))))
       (equal (fn-state-next-txid (fn-node-acceptance (fn-cnode-node (fn-cnode-initial (fn-cfg-initial)))))
              0))
  :hints (("Goal" :in-theory (enable fn-ofr-idlep))))

; KEYSTONE.  The open's frontier admits every history the replay accepts:
; the configured open's :frontier refusal (fn-rii-sco-finalize-configured,
; through fn-rii-advance-idlep-is-advance-okp) never fires on it.
(defthm fn-ofr-replay-ok-frontier-admits
  (implies (and (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
                (natp floor))
           (fn-replay-advance-okp (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events)))
                                  (fn-ofr-frontier configs events floor)))
  :hints (("Goal" :use ((:instance fn-ofr-loop-ok-within-frontier
                                   (cn (fn-cnode-initial (fn-cfg-initial)))
                                   (config-sequence 0) (event-sequence 0) (acc floor))
                        (:instance fn-ofr-okp-is-idle-within
                                   (node (fn-cnode-node (fn-replay-result-node
                                                         (fn-cpr-replay configs events))))
                                   (bound (fn-ofr-frontier configs events floor))))
           :in-theory (e/d (fn-cpr-replay)
                           (fn-cpr-loop fn-ofr-loop-ok-within-frontier fn-ofr-frontier
                            fn-cnode-initial fn-cfg-initial)))))
