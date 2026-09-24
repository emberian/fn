; fn: the crash headline over the replay recovery calls.
;
; host/owner-host.lisp `fn-owner-recover' replays the two decoded journals
; with `(fn-cpr-replay config-records records)': CONFIG-RECORDS is the
; configuration directory decoded by `fn-store-cfg-decode-records', RECORDS
; the Store journal decoded by `fn-store-decode-records'; it installs the
; configuration of the replayed node only when the replay's kind is :ok and
; answers :fault otherwise.  The headline of specs/reconfiguration.md,
; `fn-ocfg-crash-at-any-instant-recovers-the-live-generation'
; (books/owner-config.lisp), is stated over `fn-cnode-config-replay', the
; configuration-only replay, which no host line calls.  This book relates the
; two replays and restates the headline over `fn-cpr-replay' and the
; publication the host calls, `fn-ocl-publish'.
;
; The two replays are not equivalent on arbitrary bytes.  `fn-cpr-replay'
; admits a configuration record only at its Store transaction id
; (`fn-replay-advance-okp': the ids never go down), at the reservation total
; the Store events before it produced, and in a properly terminated list,
; and it also replays every Store event.  `fn-cnode-config-replay' checks
; none of these.  So the equation is a refinement: every :ok of the called
; replay is an :ok of the configuration replay with the same configuration
; (`fn-ocl-cpr-replay-ok-is-config-replay-ok'), and the converse fails, for
; instance on a configuration journal whose second record names a smaller
; transaction id than its first (tests/acl2/config-crash-replay-tests.lisp).
; Such a journal is not one the called path writes: `fn-cpo-configure-durable'
; appends a record only when `fn-cpr-replay' of the extended journals is :ok.
;
; This book shares the prefix `fn-ocl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "config-owner-publish")

; -----------------------------------------------------------------------------
; What the configuration-only replay checks, as a predicate on the list: each
; record carries the next sequence and is acceptable, at reservation zero, to
; the configuration the records before it fold to.

(defun fn-ocl-config-chainp (cfg seq configs)
  (declare (xargs :verify-guards nil :measure (len configs)
                  :hints (("Goal" :in-theory (disable fn-cfg-record-acceptablep
                                                      fn-cfg-apply-record)))))
  (if (consp configs)
      (and (equal (fn-cfg-record-sequence (car configs)) seq)
           (fn-cfg-record-acceptablep cfg (car configs) 0 (fn-cnode-line-ceiling))
           (fn-ocl-config-chainp (fn-cfg-apply-record cfg (car configs))
                                 (+ 1 seq) (cdr configs)))
    t))

(local
 (defthm fn-ocl-crr-config-of-applied-config
   (implies (and (fn-cnode-statep cn)
                 (fn-cnode-record-acceptablep cn record ceiling))
            (equal (fn-cnode-config (fn-cnode-apply-config cn record ceiling))
                   (fn-cfg-apply-record (fn-cnode-config cn) record)))
   :hints (("Goal" :in-theory (enable fn-cnode-apply-config)))))

(local
 (defthm fn-ocl-crr-statep-is-consp
   (implies (fn-cnode-statep cn) (consp cn))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))

(local
 (defthm fn-ocl-crr-uint32-is-natp
   (implies (fn-record-uint32p x) (natp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))

(local
 (defthm fn-ocl-crr-record-sequence-is-natp
   (implies (fn-cfg-recordp r) (natp (fn-cfg-record-sequence r)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cfg-recordp fn-record-uint32p)))))

; The called replay's side: an :ok fold is a chain.  Each configuration
; record was acceptable at the reservation the Store events before it
; produced, hence at zero; Store events leave the configuration where it was.
(defthm fn-ocl-cpr-loop-ok-is-a-config-chain
  (implies (equal (fn-replay-result-kind
                   (fn-cpr-loop cn configs events config-sequence event-sequence))
                  :ok)
           (fn-ocl-config-chainp (fn-cnode-config cn) config-sequence configs))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                       event-sequence)
           :in-theory (e/d (fn-cpr-loop fn-ocl-config-chainp
                            fn-cnode-record-acceptablep)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cfg-record-acceptablep
                            fn-cfg-apply-record fn-replay-advance-txid
                            fn-replay-advance-okp fn-store-event-p
                            fn-cfg-recordp)))
          ("Subgoal *1/" :use ((:instance fn-ocfg-acceptable-record-is-acceptable-at-zero-reservation
                                (cfg (fn-cnode-config cn))
                                (r (car configs))
                                (reserved (fn-retain-reserved
                                           (fn-node-retention
                                            (fn-replay-advance-txid
                                             (fn-cnode-node cn)
                                             (fn-cfg-record-txid (car configs))))))
                                (ceiling (fn-cnode-line-ceiling)))))))

(local
 (defthm fn-ocl-crr-config-jrec-is-a-jrec
   (implies (fn-cfg-recordp r)
            (fn-jrec-p (fn-jrec-make :config (fn-cfg-record-sequence r) r)))
   :hints (("Goal" :in-theory (enable fn-jrec-p fn-cfg-recordp)))))

(local
 (defthm fn-ocl-crr-acceptable-record-is-a-record
   (implies (fn-cfg-record-acceptablep cfg r reserved ceiling)
            (fn-cfg-recordp r))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cfg-record-acceptablep)))))

; The configuration replay's side: a chain from a configuration-only node
; replays :ok to the fold.
(defthm fn-ocl-config-chain-replays-ok
  (implies (and (fn-ocfg-replay-cnode-okp cn seq)
                (fn-ocl-config-chainp (fn-cnode-config cn) seq configs))
           (let ((result (fn-cnode-replay-loop cn (fn-cnode-line-ceiling)
                                               (fn-cnode-config-jrecs configs)
                                               seq)))
             (and (equal (fn-replay-result-kind result) :ok)
                  (equal (fn-cnode-config (fn-replay-result-node result))
                         (fn-ocl-config-fold (fn-cnode-config cn) configs)))))
  :hints (("Goal" :induct (fn-ocfg-cr-induct cn (fn-cnode-line-ceiling) configs seq)
           :in-theory (e/d (fn-cnode-replay-loop fn-cnode-config-jrecs
                            fn-ocl-config-chainp fn-ocl-config-fold
                            fn-cnode-record-acceptablep)
                           (fn-ocfg-replay-cnode-okp fn-cnode-apply-config
                            fn-cnode-statep fn-cfg-record-acceptablep fn-jrec-p
                            fn-cfg-apply-record fn-cnode-apply-record
                            (:e fn-cnode-line-ceiling) fn-cnode-line-ceiling)))
          ("Subgoal *1/2" :expand ((fn-ocfg-replay-cnode-okp cn seq)))
          ("Subgoal *1/1"
           :expand ((fn-ocfg-replay-cnode-okp cn seq))
           :use ((:instance fn-ocfg-replay-cnode-okp-of-apply-config
                            (r (car configs)) (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-ocl-crr-config-jrec-is-a-jrec (r (car configs)))))))

; KEYSTONE (the equation, a refinement).  WHAT RECOVERY'S REPLAY ACCEPTS, THE
; CONFIGURATION REPLAY ACCEPTS, TO THE SAME CONFIGURATION.  If
; `fn-cpr-replay' of the configuration and Store journals is :ok, then
; `fn-cnode-config-replay' of the configuration journal alone is :ok and the
; two replayed nodes carry the same configuration.  One hypothesis, the :ok
; `fn-owner-recover' dispatches on.  The converse is false (see the head of
; this book and the separating journal in the test book).
(defthm fn-ocl-cpr-replay-ok-is-config-replay-ok
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (and (equal (fn-replay-result-kind (fn-cnode-config-replay configs)) :ok)
                (equal (fn-cnode-config
                        (fn-replay-result-node (fn-cnode-config-replay configs)))
                       (fn-cnode-config
                        (fn-replay-result-node (fn-cpr-replay configs events))))))
  :hints (("Goal"
           :use ((:instance fn-ocl-cpr-loop-ok-is-a-config-chain
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-ocl-cpr-loop-configuration-is-the-record-fold
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-ocl-config-chain-replays-ok
                            (cn (fn-cnode-initial (fn-cfg-initial))) (seq 0)))
           :in-theory (e/d (fn-cpr-replay fn-cnode-config-replay fn-cnode-replay)
                           (fn-cpr-loop fn-cnode-replay-loop fn-cnode-initial
                            fn-cfg-initial fn-cnode-statep fn-cnode-config-jrecs
                            fn-ocfg-replay-cnode-okp fn-ocl-config-chainp
                            fn-ocl-config-fold
                            fn-ocl-cpr-loop-ok-is-a-config-chain
                            fn-ocl-cpr-loop-configuration-is-the-record-fold
                            fn-ocl-config-chain-replays-ok)))))

; -----------------------------------------------------------------------------
; The appended record.

(defthm fn-ocl-config-chainp-of-one-more-record
  (implies (fn-ocl-config-chainp cfg seq (append configs (list r)))
           (fn-cfg-record-acceptablep (fn-ocl-config-fold cfg configs) r 0
                                      (fn-cnode-line-ceiling)))
  :hints (("Goal" :induct (fn-ocl-config-chainp cfg seq configs)
           :in-theory (e/d (fn-ocl-config-chainp fn-ocl-config-fold)
                           (fn-cfg-record-acceptablep fn-cfg-apply-record)))))

; An :ok replay of a journal with one record appended recovers that record
; applied, whole, to what the journal before it recovered.
(defthm fn-ocl-cpr-replay-of-one-more-record
  (implies (and (equal (fn-replay-result-kind
                        (fn-cpr-replay (append h (list r)) events))
                       :ok)
                (equal (fn-replay-result-kind (fn-cpr-replay h events)) :ok))
           (and (fn-cfg-record-acceptablep
                 (fn-cnode-config (fn-replay-result-node (fn-cpr-replay h events)))
                 r 0 (fn-cnode-line-ceiling))
                (equal (fn-cnode-config
                        (fn-replay-result-node
                         (fn-cpr-replay (append h (list r)) events)))
                       (fn-cfg-apply-record
                        (fn-cnode-config (fn-replay-result-node (fn-cpr-replay h events)))
                        r))))
  :hints (("Goal"
           :use ((:instance fn-ocl-cpr-loop-ok-is-a-config-chain
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (configs (append h (list r)))
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-ocl-cpr-loop-configuration-is-the-record-fold
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (configs (append h (list r)))
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-ocl-cpr-loop-configuration-is-the-record-fold
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (configs h)
                            (config-sequence 0) (event-sequence 0))
                 (:instance fn-ocl-config-chainp-of-one-more-record
                            (cfg (fn-cnode-config (fn-cnode-initial (fn-cfg-initial))))
                            (seq 0) (configs h)))
           :in-theory (e/d (fn-cpr-replay)
                           (fn-cpr-loop fn-cnode-initial fn-cfg-initial
                            fn-ocl-config-chainp fn-ocl-config-fold
                            fn-cfg-record-acceptablep fn-cfg-apply-record
                            fn-ocl-cpr-loop-ok-is-a-config-chain
                            fn-ocl-cpr-loop-configuration-is-the-record-fold
                            fn-ocl-config-chainp-of-one-more-record)))))

(local
 (defthm fn-ocl-crr-durable-history-change-replays-ok
   (implies (not (equal (fn-sn-config-history (fn-cpo-configure-durable st record))
                        (fn-sn-config-history st)))
            (equal (fn-replay-result-kind
                    (fn-cpr-replay (append (fn-sn-config-history st) (list record))
                                   (fn-sf-records (fn-sn-files st))))
                   :ok))
   :hints (("Goal" :in-theory (e/d (fn-cpo-configure-durable fn-cpo-install)
                                   (fn-cpo-history-relation fn-cpr-replay))))))

(local
 (defthm fn-ocl-crr-append-one-is-longer
   (not (equal (append x (list y)) x))))

; Staging and the close of the requesting connection move neither the store
; (so neither journal) nor the live configuration.
(local
 (defthm fn-ocl-crr-staging-and-close-keep-store-and-config
   (let ((staged (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                               (list :close id))))
     (and (equal (fn-own-store (fn-ocfg-owner staged))
                 (fn-own-store (fn-ocfg-owner oc)))
          (equal (fn-ocfg-config staged) (fn-ocfg-config oc))))
   :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-reconfigure fn-ocfg-close
                                    fn-own-close)
                                   (fn-ocfg-reconfig-okp fn-ocfg-reconfig-record
                                    fn-ocfg-pin-remove))))))

; On :durable the published store's journals are the old configuration
; journal with the staged record appended and the old Store journal, and
; the called replay of them is :ok, to the published configuration.
(local
 (defthm fn-ocl-crr-durable-publication-replays
   (implies (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
            (let* ((st (fn-own-store (fn-ocfg-owner oc)))
                   (published (mv-nth 1 (fn-ocl-publish oc generation max-octets)))
                   (pst (fn-own-store (fn-ocfg-owner published)))
                   (durable (append (fn-sn-config-history st)
                                    (list (fn-ocfg-staged oc))))
                   (events (fn-sf-records (fn-sn-files st))))
              (and (fn-ocfg-staged oc)
                   (equal (fn-sn-config-history pst) durable)
                   (equal (fn-sf-records (fn-sn-files pst)) events)
                   (equal (fn-replay-result-kind (fn-cpr-replay durable events)) :ok)
                   (equal (fn-cnode-config
                           (fn-replay-result-node (fn-cpr-replay durable events)))
                          (fn-ocfg-config published))
                   (not (fn-ocfg-staged published)))))
   :hints (("Goal"
            :use ((:instance fn-ocl-complete-success-publishes-the-store-configuration)
                  (:instance fn-ocl-success-appends-exact-config-history)
                  (:instance fn-ocl-staged-complete-keeps-store-events)
                  (:instance fn-ocl-crr-durable-history-change-replays-ok
                             (st (fn-own-store (fn-ocfg-owner oc)))
                             (record (fn-ocfg-staged oc)))
                  (:instance fn-ocl-complete-success-install-exact-store))
            :in-theory (e/d (fn-ocl-publish fn-ocfg-with-owner fn-own-configure
                             fn-ocl-store-config)
                            (fn-ocl-complete fn-cpo-configure-durable fn-cpr-replay
                             fn-oag-post-config
                             fn-ocl-crr-durable-history-change-replays-ok
                             fn-ocl-complete-success-publishes-the-store-configuration
                             fn-ocl-success-appends-exact-config-history
                             fn-ocl-staged-complete-keeps-store-events
                             fn-ocl-complete-success-install-exact-store))))))

(local
 (defthm fn-ocl-crr-model-complete-config
   (implies (fn-ocfg-staged x)
            (equal (fn-ocfg-config (fn-ocfg-step x (list :complete)))
                   (fn-ocfg-published-config (fn-ocfg-config x) (fn-ocfg-staged x))))
   :hints (("Goal" :in-theory (enable fn-ocfg-step fn-ocfg-complete)))))

(local
 (defthm fn-ocl-crr-generation-of-applied-record
   (equal (fn-cfg-generation (fn-cfg-apply-record cfg r))
          (fn-cfg-record-generation r))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-record)))))

; KEYSTONE (headline 2, over the called replay and the called publication).
; A CRASH AT ANY INSTANT OF A LIVE RECONFIGURATION RECOVERS THE LIVE
; GENERATION OR THE WHOLE NEW ONE, NEVER A PARTIAL ONE.  The host's arm is
; staging `(:reconfigure id deltas)' and the requester's `(:close id)'
; through `fn-ocfg-step' (host/owner-host.lisp `fn-owner-reconfigure-deltas',
; `fn-owner-close'), the durable write of the staged record, then
; `fn-ocl-publish' (`fn-owner-reconfigure-complete').  Recovery replays the
; journals the directory then holds with `fn-cpr-replay' (`fn-owner-recover',
; its arguments the decoded configuration journal and the decoded Store
; journal, here the store's `fn-sn-config-history' and `fn-sf-records').
; One hypothesis, `fn-ocl-config-historyp': the live configuration is what the
; called replay of the store's own journals recovers (what `fn-owner-recover'
; installs, carried across every completion by
; `fn-ocl-complete-preserves-full-historical-relation').  Then:
;
;   before the record is durable, the journals are the old ones and replay
;   :ok to the live configuration, which staging did not move;
;
;   once the record is durable and before or without publication, a replay
;   of the old configuration journal with the record appended is either not
;   :ok (the host answers :fault and installs nothing) or recovers exactly
;   the configuration the model's `(:complete)' publishes, the WHOLE record
;   applied, whose generation is the record's;
;
;   on a :durable publication the installed store's journals are exactly
;   those, their replay is :ok, it recovers the configuration published,
;   nothing is staged, and the hypothesis holds again of the published
;   owner, so the statement chains across every later reconfiguration.
;
; A-DURABILITY enters where it always does: that a record the publisher
; reported :durable is in the directory the next open reads and a torn
; staging file is not.  `fn-ocfg-crash-at-any-instant-recovers-the-live-generation'
; is the model-level statement over `fn-cnode-config-replay';
; `fn-ocl-cpr-replay-ok-is-config-replay-ok' transfers every :ok of this
; statement's replays to it.  Its hypothesis that nothing is staged is not
; needed here: a record staged before the arm is refused a second stage and is
; what the durable journal carries.
(defthm fn-ocl-crash-at-any-instant-recovers-the-live-generation
  (implies (fn-ocl-config-historyp oc)
           (let* ((staged (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                                        (list :close id)))
                  (record (fn-ocfg-staged staged))
                  (st (fn-own-store (fn-ocfg-owner staged)))
                  (h (fn-sn-config-history st))
                  (e (fn-sf-records (fn-sn-files st)))
                  (model (fn-ocfg-step staged (list :complete)))
                  (result (fn-ocl-publish staged generation max-octets))
                  (published (mv-nth 1 result))
                  (pst (fn-own-store (fn-ocfg-owner published))))
             (and (equal st (fn-own-store (fn-ocfg-owner oc)))
                  (equal (fn-replay-result-kind (fn-cpr-replay h e)) :ok)
                  (equal (fn-cnode-config (fn-replay-result-node (fn-cpr-replay h e)))
                         (fn-ocfg-config staged))
                  (equal (fn-ocfg-config staged) (fn-ocfg-config oc))
                  (implies (and record
                                (equal (fn-replay-result-kind
                                        (fn-cpr-replay (append h (list record)) e))
                                       :ok))
                           (and (equal (fn-cnode-config
                                        (fn-replay-result-node
                                         (fn-cpr-replay (append h (list record)) e)))
                                       (fn-ocfg-config model))
                                (equal (fn-ocfg-config model)
                                       (fn-cfg-apply-record (fn-ocfg-config oc) record))
                                (equal (fn-cfg-generation (fn-ocfg-config model))
                                       (fn-cfg-record-generation record))))
                  (implies (equal (mv-nth 0 result) :durable)
                           (and record
                                (equal (fn-sn-config-history pst) (append h (list record)))
                                (equal (fn-sf-records (fn-sn-files pst)) e)
                                (equal (fn-replay-result-kind
                                        (fn-cpr-replay (append h (list record)) e))
                                       :ok)
                                (equal (fn-cnode-config
                                        (fn-replay-result-node
                                         (fn-cpr-replay (append h (list record)) e)))
                                       (fn-ocfg-config published))
                                (equal (fn-ocfg-config published) (fn-ocfg-config model))
                                (not (fn-ocfg-staged published))
                                (fn-ocl-config-historyp published))))))
  :hints (("Goal"
           :use ((:instance fn-ocl-crr-staging-and-close-keep-store-and-config)
                 (:instance fn-ocl-crr-durable-publication-replays
                            (oc (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                                              (list :close id))))
                 (:instance fn-ocl-cpr-replay-of-one-more-record
                            (h (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                            (r (fn-ocfg-staged
                                (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                                              (list :close id))))
                            (events (fn-sf-records
                                     (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
           :in-theory (e/d (fn-ocl-config-historyp fn-ocfg-published-config)
                           (fn-ocfg-step fn-ocl-publish fn-cpr-replay
                            fn-cfg-record-acceptablep fn-cfg-apply-record
                            fn-ocl-crr-staging-and-close-keep-store-and-config
                            fn-ocl-crr-durable-publication-replays
                            fn-ocl-cpr-replay-of-one-more-record)))))
