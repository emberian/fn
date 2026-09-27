; fn: the offline configuration request extends the fold it opened with, by
; the one record it publishes (PKT-510 (1), wave 5 config-consumer-catalog).
;
; An offline `operator' request opened the store (host/native/io.lisp
; fnn-recover: one configuration fold over the configuration and Store
; histories, fn-cpr-replay) and then, to authorize its one new record R,
; replayed both histories again: fn-native-admin-publication-authorize ran the
; configuration-only fold twice (over CONFIGS and over CONFIGS ++ (R)) and
; fn-native-admin-candidate-open-result ran fn-cpr-replay over CONFIGS ++ (R)
; beside the candidate open's own.  Both folds are folds: the result over a
; history ending in R is one step from the result over the history without it
; (for the physical fold, when R is filed after every Store event: its txid is
; at or past the frontier, and every event of an observed history is below the
; frontier).  This book states the two extensions and the authorization the
; host calls, which takes the open's carried fold and is EQUAL to the
; authorization it replaces whenever that carried fold is the replay the open
; computed.  The candidate open (fn-cpo-open-observed over the exact next
; image, the reopen check) is decided from the open's own result, and the
; authorization the host calls is stated, in books/config-carried-open.lisp
; (PKT-601 (1), (2)).

(in-package "ACL2")
(include-book "store-capacity-config")

; -----------------------------------------------------------------------------
; The configuration-only fold, extended by one record.

(defthm fn-cfgc-config-jrecs-of-append
  (equal (fn-cnode-config-jrecs (append a b))
         (append (fn-cnode-config-jrecs a) (fn-cnode-config-jrecs b)))
  :hints (("Goal" :in-theory (enable fn-cnode-config-jrecs))))

(defthm fn-cfgc-true-listp-config-jrecs
  (true-listp (fn-cnode-config-jrecs a))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-cnode-config-jrecs))))

(defun fn-cfgc-config-extend (replayed record)
  ; The configuration-only fold continued by RECORD: one step, never a replay.
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-replay-result-kind replayed) :ok)
      (let ((cn (fn-replay-result-node replayed)))
        (mbe :logic (fn-cnode-replay-loop
                     cn (fn-cnode-line-ceiling)
                     (fn-cnode-config-jrecs (list record))
                     (fn-replay-result-sequence replayed))
             :exec (if (fn-cnode-statep cn)
                       (fn-cnode-replay-loop
                        cn (fn-cnode-line-ceiling)
                        (fn-cnode-config-jrecs (list record))
                        (fn-replay-result-sequence replayed))
                     (fn-replay-fault cn (fn-replay-result-sequence replayed)
                                      :invalid-initial-node))))
    replayed))

(local
 (defthm fn-cfgc-cnode-loop-of-non-state
   (implies (not (fn-cnode-statep cn))
            (equal (fn-cnode-replay-loop cn ceiling js expected)
                   (fn-replay-fault cn expected :invalid-initial-node)))
   :hints (("Goal" :expand ((fn-cnode-replay-loop cn ceiling js expected))))))

(verify-guards fn-cfgc-config-extend
  :hints (("Goal" :in-theory (disable fn-cnode-statep fn-cnode-replay-loop
                                      fn-cnode-config-jrecs))))

; KEYSTONE.  The configuration-only fold over CONFIGS ++ (RECORD) is one step
; from the fold over CONFIGS.  From fn-cnode-replay-loop-splits-at-any-prefix
; (books/node-config.lisp), the fold's own split theorem.
(defthm fn-cfgc-config-replay-of-one-more
  (equal (fn-cnode-config-replay (append configs (list record)))
         (fn-cfgc-config-extend (fn-cnode-config-replay configs) record))
  :hints (("Goal"
           :in-theory (e/d (fn-cnode-config-replay fn-cnode-replay)
                           (fn-cnode-config-jrecs fn-cnode-statep
                            fn-cnode-replay-loop fn-cnode-initial
                            fn-cnode-line-ceiling))
           :use ((:instance fn-cnode-replay-loop-splits-at-any-prefix
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (ceiling (fn-cnode-line-ceiling))
                            (a (fn-cnode-config-jrecs configs))
                            (b (fn-cnode-config-jrecs (list record)))
                            (expected 0))))
          ("Subgoal *1/1" :expand ((fn-cnode-replay-loop
                                    (fn-cnode-initial (fn-cfg-initial))
                                    (fn-cnode-line-ceiling) nil 0)))))

; -----------------------------------------------------------------------------
; The physical fold, extended by one record filed after every Store event.

(defun fn-cfgc-events-below (events bound)
  ; Every event's transaction id is below BOUND (the order fn-cpr-loop files
  ; a configuration record after an event).
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (and (< (nfix (fn-store-event-txid (car events))) (nfix bound))
           (fn-cfgc-events-below (cdr events) bound))
    t))

(defun fn-cfgc-cpr-extend (replayed configs events record)
  ; The physical fold continued by RECORD after the last event.
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-replay-result-kind replayed) :ok)
      (let ((cn (fn-replay-result-node replayed)))
        (mbe :logic (fn-cpr-loop cn (list record) nil (len configs) (len events))
             :exec (if (fn-cnode-statep cn)
                       (fn-cpr-loop cn (list record) nil (len configs) (len events))
                     (fn-replay-fault cn (+ (len configs) (len events))
                                      :invalid-node))))
    replayed))

(local
 (defthm fn-cfgc-cpr-loop-of-non-state
   (implies (not (fn-cnode-statep cn))
            (equal (fn-cpr-loop cn configs events cs es)
                   (fn-replay-fault cn (+ (nfix cs) (nfix es)) :invalid-node)))
   :hints (("Goal" :expand ((fn-cpr-loop cn configs events cs es))))))

(verify-guards fn-cfgc-cpr-extend
  :hints (("Goal" :in-theory (disable fn-cnode-statep fn-cpr-loop))))

(local
 (defthm fn-cfgc-cpr-loop-append-one
   (implies (and (true-listp a) (true-listp events)
                 (natp cs) (natp es)
                 (fn-cfgc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-loop cn (append a (list record)) events cs es)
                   (let ((mid (fn-cpr-loop cn a events cs es)))
                     (if (equal (fn-replay-result-kind mid) :ok)
                         (fn-cpr-loop (fn-replay-result-node mid) (list record) nil
                                      (+ cs (len a)) (+ es (len events)))
                       mid))))
   :hints (("Goal" :induct (fn-cpr-loop cn a events cs es)
            :in-theory (e/d (fn-cpr-loop fn-cpr-config-firstp)
                            (fn-cnode-statep fn-cnode-apply-config
                             fn-cpr-apply-event fn-cnode-record-acceptablep
                             fn-store-event-p fn-cfg-recordp
                             fn-replay-advance-okp fn-replay-advance-txid
                             fn-cnode-carried-acceptablep))))))

; KEYSTONE.  The physical fold over CONFIGS ++ (RECORD) and EVENTS is one step
; from the fold over CONFIGS and EVENTS, when RECORD is filed after every event.
(defthm fn-cfgc-cpr-replay-of-one-more
  (implies (and (true-listp configs) (true-listp events)
                (fn-cfgc-events-below events (fn-cfg-record-txid record)))
           (equal (fn-cpr-replay (append configs (list record)) events)
                  (fn-cfgc-cpr-extend (fn-cpr-replay configs events)
                                     configs events record)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep)))))

; An observed history (the candidate open's first test) is below its frontier,
; so a record whose txid is at or past the frontier is filed after it.
(defthm fn-cfgc-record-list-is-below
  (implies (and (fn-sf-record-listp events sequence lower frontier)
                (natp frontier)
                (<= frontier (nfix bound)))
           (fn-cfgc-events-below events bound))
  :hints (("Goal" :in-theory (enable fn-sf-record-listp))))

(defthm fn-cfgc-record-list-is-true-list
  (implies (fn-sf-record-listp events sequence lower frontier)
           (true-listp events))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sf-record-listp))))

; -----------------------------------------------------------------------------
; The candidate open, from the open's carried fold.

(defthm fn-cfgc-append-record-is-append
  (implies (true-listp configs)
           (equal (fn-native-admin-append-record configs record)
                  (append configs (list record))))
  :hints (("Goal" :in-theory (enable fn-native-admin-append-record))))

(defthm fn-cfgc-open-okp-is-observed
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-sn-observed-historyp frontier events))
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed)
                                  (fn-cpr-replay fn-sn-statep fn-cnode-statep
                                   fn-sn-observed-historyp)))))

(defthm fn-cfgc-observed-is-below
  (implies (and (fn-sn-observed-historyp frontier events)
                (<= (nfix frontier) (nfix bound)))
           (and (fn-cfgc-events-below events bound)
                (true-listp events)))
  :hints (("Goal" :in-theory (enable fn-sn-observed-historyp fn-record-uint32p))))

; CONFIGURATION is the configuration-only fold of CONFIG-RECORDS (the
; authorization computes it once); REPLAYED is the open's physical fold of
; CONFIG-RECORDS and RECORDS.  A record at or past the frontier is filed after
; every event of an observed history, so its fold is one step; otherwise (a
; record below the frontier: never one the host builds, whose txid is the
; opened node's next) the fold is replayed.  The candidate open itself is the
; reopen check and is kept.
(defun fn-cfgc-candidate-open-result
    (records frontier config-records record configuration replayed)
  (declare (xargs :guard t :verify-guards nil))
  (let ((configuration1 (fn-cfgc-config-extend configuration record)))
    (if (not (equal (fn-replay-result-kind configuration1) :ok))
        (list :refused :configuration)
      (let* ((configs1 (fn-native-admin-append-record config-records record))
             (replayed1 (if (<= (nfix frontier) (nfix (fn-cfg-record-txid record)))
                            (fn-cfgc-cpr-extend replayed config-records records record)
                          (fn-cpr-replay configs1 records)))
             (opened (fn-cpo-open-observed configs1 frontier records)))
        (if (and (equal (fn-replay-result-kind replayed1) :ok)
                 (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (list :accepted (fn-replay-result-node replayed1))
          (list :refused :history))))))

(verify-guards fn-cfgc-candidate-open-result)

; KEYSTONE.  From the open's carried folds the candidate is the candidate the
; authorization replayed for.
(defthm fn-cfgc-candidate-open-result-is-the-replayed-candidate
  (implies (and (true-listp config-records)
                (equal configuration (fn-cnode-config-replay config-records))
                (equal replayed (fn-cpr-replay config-records records)))
           (equal (fn-cfgc-candidate-open-result
                   records frontier config-records record configuration replayed)
                  (fn-native-admin-candidate-open-result
                   records frontier
                   (fn-native-admin-append-record config-records record))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-cfgc-config-replay-of-one-more
                            (configs config-records))
                 (:instance fn-cfgc-open-okp-is-observed
                            (configs (append config-records (list record)))
                            (events records))
                 (:instance fn-cfgc-observed-is-below
                            (events records)
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cfgc-cpr-replay-of-one-more
                            (configs config-records) (events records)))
           :in-theory (e/d (fn-native-admin-candidate-open-result)
                           (fn-cpo-open-observed fn-cpr-replay fn-cfgc-cpr-extend
                            fn-cfgc-config-extend fn-cnode-config-replay
                            fn-sn-observed-historyp fn-cfgc-events-below
                            fn-native-admin-append-record
                            fn-cfgc-config-replay-of-one-more
                            fn-cfgc-cpr-replay-of-one-more
                            fn-cfgc-open-okp-is-observed
                            fn-cfgc-observed-is-below
                            fn-sn-open-okp)))))

