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
; image, the reopen check) is decided from the open's own result and the
; extended fold (PKT-601 (1), fn-cfgc-candidate-open-carried): the history,
; identity, consumer, topic and index conditions it shares with the open are
; not rebuilt.

(in-package "ACL2")
(include-book "store-capacity-config")
(include-book "store-open-bridge")

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

(local
 (defthm fn-cfgc-append-record-is-append
   (implies (true-listp configs)
            (equal (fn-native-admin-append-record configs record)
                   (append configs (list record))))
   :hints (("Goal" :in-theory (enable fn-native-admin-append-record)))))

(local
 (defthm fn-cfgc-open-okp-is-observed
   (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
            (fn-sn-observed-historyp frontier events))
   :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed)
                                   (fn-cpr-replay fn-sn-statep fn-cnode-statep
                                    fn-sn-observed-historyp))))))

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

;-----------------------------------------------------------------------------
; The candidate open, extended from the open's own success (PKT-601 (1)).
;
; The candidate open fn-cpo-open-observed of CONFIGS ++ (R) differs from the
; open's fn-cpo-open-observed of CONFIGS only in its configuration: the
; history shape, the identity, consumer and topic replays and the event index
; are functions of the Store history and the frontier alone, which the
; request does not change.  Its success is exactly the configured replay's
; (store-open-bridge fn-cpo-open-observed-succeeds-exactly), so given the
; open's success the candidate's is the extended fold's kind and the four
; scalar conditions under which a replayed node accepts the frontier; the
; node's whole-state recognizer is implied by the fold's success
; (fn-cpr-replay-ok-is-configured).  No record is revisited.

; fn-replay-advance-okp without its whole-state recognizer: the four scalar
; tests on the node the fold produced.
(defun fn-cfgc-advance-okp (node frontier)
  (declare (xargs :guard t))
  (let ((acceptance (fn-node-acceptance node)))
    (and (natp frontier)
         (null (fn-node-stage node))
         (null (fn-state-pending acceptance))
         (equal (fn-state-fenced acceptance) nil)
         (natp (fn-state-next-txid acceptance))
         (<= (fn-state-next-txid acceptance) frontier))))

(defthm fn-cfgc-advance-okp-is-replay-advance-okp
  (implies (fn-node-statep node)
           (equal (fn-cfgc-advance-okp node frontier)
                  (fn-replay-advance-okp node frontier)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp fn-node-statep fn-statep))))

; The open's result kind is its success (the whole-state recognizer ran
; inside the open, before it answered :ok).
(defthm fn-cfgc-cpo-open-kind-ok-is-okp
  (equal (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)
         (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-okp fn-sn-open-ok
                                   fn-sn-open-error fn-sn-open-kind fn-sn-open-state
                                   fn-sn-open-shapep)
                                  (fn-sn-statep fn-cpr-replay fn-cnode-statep
                                   fn-replay-advance-okp fn-sn-observed-historyp
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-of-store fn-replay-advance-txid
                                   fn-replay-identity fn-cpe-projection-replay
                                   fn-th-prefix-project fn-cei-build)))))

; Over the same Store history and frontier, a second configuration history
; opens exactly when its configured replay does.
(defthm fn-cfgc-cpo-open-of-other-configs
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (iff (fn-sn-open-okp (fn-cpo-open-observed configs2 frontier events))
                (fn-sob-configured-openp configs2 frontier events)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpo-open-observed-succeeds-exactly)
                        (:instance fn-cpo-open-observed-succeeds-exactly
                                   (configs configs2)))
           :in-theory nil)))

(defthm fn-cfgc-cpo-open-ok-is-recovering
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state
                                             (fn-cpo-open-observed configs frontier events))))
                  :recovering))
  :hints (("Goal" :use (fn-sob-cpo-open-ok-facts)
           :in-theory (e/d (fn-bs-recovered-kernel)
                           (fn-cpo-open-observed fn-sn-open-okp)))))

; The configured open's condition is the fold's kind and the four scalar tests.
(defthm fn-cfgc-configured-openp-by-kind
  (implies (consp configs2)
           (equal (fn-sob-configured-openp configs2 frontier events)
                  (let ((replayed (fn-cpr-replay configs2 events)))
                    (and (equal (fn-replay-result-kind replayed) :ok)
                         (fn-cfgc-advance-okp
                          (fn-cnode-node (fn-replay-result-node replayed))
                          frontier)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpr-replay-ok-is-configured
                                   (configs configs2)))
           :in-theory (e/d (fn-sob-configured-openp fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-replay-ok-is-configured
                            fn-cfgc-advance-okp fn-replay-advance-okp)))))

; OPENED is the open's result, carried (host/store-node-host.lisp
; fn-store-sn-open-extended keeps it beside E and REPLAYED).  When it
; succeeded and the record is filed after every event, the candidate is decided
; from the extended fold alone; otherwise the replaying candidate.
(defun fn-cfgc-candidate-open-carried
    (records frontier config-records record configuration replayed opened)
  (declare (xargs :guard t :verify-guards nil))
  (let ((configuration1 (fn-cfgc-config-extend configuration record)))
    (if (not (equal (fn-replay-result-kind configuration1) :ok))
        (list :refused :configuration)
      (if (and (<= (nfix frontier) (nfix (fn-cfg-record-txid record)))
               (equal (fn-sn-open-kind opened) :ok))
          (let ((replayed1 (fn-cfgc-cpr-extend replayed config-records records record)))
            (if (and (equal (fn-replay-result-kind replayed1) :ok)
                     (fn-cfgc-advance-okp
                      (fn-cnode-node (fn-replay-result-node replayed1)) frontier))
                (list :accepted (fn-replay-result-node replayed1))
              (list :refused :history)))
        (fn-cfgc-candidate-open-result records frontier config-records record
                                       configuration replayed)))))

(verify-guards fn-cfgc-candidate-open-carried)

; KEYSTONE (PKT-601 (1): the candidate open is not recomputed).  From the
; open's carried result, the candidate is the candidate the authorization
; replayed for.
(defthm fn-cfgc-candidate-open-carried-is-the-replayed-candidate
  (implies (and (true-listp config-records)
                (equal configuration (fn-cnode-config-replay config-records))
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-candidate-open-carried
                   records frontier config-records record configuration replayed
                   opened)
                  (fn-native-admin-candidate-open-result
                   records frontier
                   (fn-native-admin-append-record config-records record))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-cfgc-candidate-open-result-is-the-replayed-candidate)
                 (:instance fn-cfgc-config-replay-of-one-more
                            (configs config-records))
                 (:instance fn-cfgc-cpo-open-kind-ok-is-okp
                            (configs config-records) (events records))
                 (:instance fn-cfgc-cpo-open-of-other-configs
                            (configs config-records) (events records)
                            (configs2 (append config-records (list record))))
                 (:instance fn-cfgc-configured-openp-by-kind
                            (configs2 (append config-records (list record)))
                            (events records))
                 (:instance fn-cfgc-cpo-open-ok-is-recovering
                            (configs (append config-records (list record)))
                            (events records))
                 (:instance fn-sob-cpo-open-ok-facts
                            (configs config-records) (events records))
                 (:instance fn-cfgc-observed-is-below
                            (events records)
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cfgc-cpr-replay-of-one-more
                            (configs config-records) (events records)))
           :in-theory (e/d (fn-native-admin-candidate-open-result)
                           (fn-cpo-open-observed fn-cpr-replay fn-cfgc-cpr-extend
                            fn-cfgc-config-extend fn-cnode-config-replay
                            fn-sn-observed-historyp fn-cfgc-events-below
                            fn-cfgc-candidate-open-result
                            fn-cfgc-candidate-open-result-is-the-replayed-candidate
                            fn-native-admin-append-record fn-sob-configured-openp
                            fn-cfgc-config-replay-of-one-more
                            fn-cfgc-cpr-replay-of-one-more
                            fn-cfgc-cpo-open-kind-ok-is-okp
                            fn-cfgc-cpo-open-ok-is-recovering
                            fn-cfgc-observed-is-below
                            fn-cfgc-advance-okp
                            fn-sn-open-okp fn-sn-open-kind)))))

; -----------------------------------------------------------------------------
; The authorization the offline request calls.

; fn-native-admin-publication-authorize with the configuration-only fold run
; once (over CONFIG-RECORDS; the candidate's is one step from it), the
; candidate's physical fold one step from REPLAYED, the open's, and the
; candidate open decided from OPENED, the open's result (PKT-601 (1)).
(defun fn-cfgc-publication-authorize
    (records frontier config-records record lock-owned observed-names
             max-generations replayed opened)
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((configuration (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind configuration) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node configuration)))
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (equal (car (fn-cfgc-candidate-open-carried
                                       records frontier config-records record
                                       configuration replayed opened))
                                 :accepted)))
          (cond ((not (fn-cfg-recordp record))
                 (fn-native-admin-publication-result :refused :record nil nil nil))
                ((or (not (equal (fn-cfg-record-sequence record)
                                 (fn-cfg-generation current)))
                     (not (equal (fn-cfg-record-generation record) generation)))
                 (fn-native-admin-publication-result :refused :generation nil nil nil))
                ((< (nfix max-generations) generation)
                 (fn-native-admin-publication-result
                  :refused :max-config-generations nil nil nil))
                ((null name)
                 (fn-native-admin-publication-result :refused :generation-name nil nil nil))
                ((fn-native-admin-name-memberp name observed-names)
                 (fn-native-admin-publication-result :refused :occupied nil nil nil))
                ((not candidate)
                 (fn-native-admin-publication-result :refused :candidate nil nil nil))
                (t (fn-native-admin-publication-result
                    :accepted nil generation name (fn-jpub-initial t)))))))))

; KEYSTONE.  With the open's fold carried, the authorization is the one it
; replaces, on every arm (so every keystone of
; fn-native-admin-publication-authorize carries: the lock, the generation, the
; occupied name, the candidate).
(defthm fn-cfgc-publication-authorize-is-the-replayed-authorization
  (implies (and (true-listp config-records)
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-publication-authorize
                   records frontier config-records record lock-owned
                   observed-names max-generations replayed opened)
                  (fn-native-admin-publication-authorize
                   records frontier config-records record lock-owned
                   observed-names max-generations)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-cfgc-candidate-open-carried-is-the-replayed-candidate
                            (configuration (fn-cnode-config-replay config-records))))
           :in-theory (e/d (fn-native-admin-publication-authorize
                            fn-native-admin-candidate-openp)
                           (fn-cfgc-candidate-open-carried
                            fn-native-admin-candidate-open-result
                            fn-cfgc-candidate-open-carried-is-the-replayed-candidate
                            fn-cpo-open-observed
                            fn-cnode-config-replay fn-cpr-replay
                            fn-native-admin-config-name fn-cfg-recordp
                            fn-native-admin-append-record)))))

; The host-called subject: fn-cvec-native-admin-authorize (the profile's
; group-name bound, then the publication under the profile's generations)
; over the carried fold.
(defun fn-cfgc-cvec-native-admin-authorize
    (records frontier config-records record lock-owned observed-names profile
             replayed opened)
  (declare (xargs :guard t))
  (if (not (fn-cvec-group-names-within
            (fn-cfg-record-change record)
            (fn-bs-profile-max-group-name-octets profile)))
      (fn-native-admin-publication-result :refused :max-group-name-octets
                                          nil nil nil)
    (fn-cfgc-publication-authorize
     records frontier config-records record lock-owned observed-names
     (fn-cvec-config-generations profile record) replayed opened)))

; KEYSTONE (PKT-510 (1): one replay per offline request).  The authorization
; host/store-node-host.lisp fn-store-cfg-native-admin-authorize-carried calls
; (for host/native/admin.lisp fnn-admin-execute) equals the one
; fn-store-cfg-native-admin-authorize calls, whenever REPLAYED is the open's
; fold of the same histories and OPENED is the open's result:
; fn-store-sn-open-extended keeps both in the global fn-store-sco-open, and
; fn-sco-store-open-of-extended-capture (books/owner-checkpoint-open.lisp) is
; the theorem that they are (fn-cpr-replay configs events) and
; (fn-cpo-open-observed configs frontier events) of the open's configuration
; records, frontier and the extended capture's records, on the full and the
; checkpoint open alike.
(defthm fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization
  (implies (and (true-listp config-records)
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-cvec-native-admin-authorize
                   records frontier config-records record lock-owned
                   observed-names profile replayed opened)
                  (fn-cvec-native-admin-authorize
                   records frontier config-records record lock-owned
                   observed-names profile)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-cvec-native-admin-authorize)
                           (fn-cfgc-publication-authorize
                            fn-native-admin-publication-authorize
                            fn-cpr-replay fn-cpo-open-observed fn-cvec-group-names-within
                            fn-cvec-config-generations)))))
