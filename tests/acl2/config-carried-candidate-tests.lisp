; Teeth for books/config-carried-candidate.lisp (PKT-510 (1), PKT-601 (1)):
; the offline request's candidate and authorization from the open's carried
; fold and its carried open result.
(in-package "ACL2")
(include-book "../../books/config-carried-candidate")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; Two Store events (txids 0 and 1), the frontier at 2.
(defconst *fn-cfgct-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "admin-history" "subject" "evidence" 0)))

; A configuration history of 50 records: the default record, then 49
; records filed at txid 2 (after both events), each a capacity row.
(defun fn-cfgct-configs (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-cfg-record-make i 2 (+ 1 i)
                                (list (fn-cfg-set-capacity (+ 1048576 i)))
                                *fn-cfg-default-stamp*)
            (fn-cfgct-configs (+ 1 i) n))
    nil))

(defconst *fn-cfgct-history*
  (cons *fn-cfg-default-record* (fn-cfgct-configs 1 50)))

; The request's record: sequence 50, generation 51, txid 2 (the frontier:
; the opened node's next, which is what the host builds).
(defconst *fn-cfgct-record*
  (fn-cfg-record-make 50 2 51 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))

(defconst *fn-cfgct-open* (fn-cpr-replay *fn-cfgct-history* *fn-cfgct-events*))
(defconst *fn-cfgct-configuration* (fn-cnode-config-replay *fn-cfgct-history*))
(defconst *fn-cfgct-opened* (fn-cpo-open-observed *fn-cfgct-history* 2 *fn-cfgct-events*))

; The antecedents hold, and they are not degenerate: the history of 50
; records opens (the fold is :ok at generation 50), the record is filed after
; every event.
(assert-event (equal (len *fn-cfgct-history*) 50))
(assert-event (true-listp *fn-cfgct-history*))
(assert-event (true-listp *fn-cfgct-events*))
(assert-event (equal (fn-replay-result-kind *fn-cfgct-open*) :ok))
(assert-event (equal (fn-cfg-generation
                      (fn-cnode-config (fn-replay-result-node *fn-cfgct-open*)))
                     50))
(assert-event (equal (fn-replay-result-kind *fn-cfgct-configuration*) :ok))
(assert-event (fn-cfgc-events-below *fn-cfgct-events*
                                   (fn-cfg-record-txid *fn-cfgct-record*)))
(assert-event (fn-sn-observed-historyp 2 *fn-cfgct-events*))

; fn-cfgc-config-replay-of-one-more and fn-cfgc-cpr-replay-of-one-more: the
; conclusions, with the one-step extensions :ok at generation 51.
(assert-event
 (equal (fn-cnode-config-replay (append *fn-cfgct-history* (list *fn-cfgct-record*)))
        (fn-cfgc-config-extend *fn-cfgct-configuration* *fn-cfgct-record*)))
(assert-event
 (equal (fn-cpr-replay (append *fn-cfgct-history* (list *fn-cfgct-record*))
                       *fn-cfgct-events*)
        (fn-cfgc-cpr-extend *fn-cfgct-open* *fn-cfgct-history* *fn-cfgct-events*
                           *fn-cfgct-record*)))
(assert-event
 (equal (fn-cfg-generation
         (fn-cnode-config
          (fn-replay-result-node
           (fn-cfgc-cpr-extend *fn-cfgct-open* *fn-cfgct-history* *fn-cfgct-events*
                              *fn-cfgct-record*))))
        51))

; fn-cfgc-candidate-open-result-is-the-replayed-candidate: the conclusion, and
; the candidate is accepted (a non-degenerate witness).
(assert-event
 (equal (fn-cfgc-candidate-open-result *fn-cfgct-events* 2 *fn-cfgct-history*
                                      *fn-cfgct-record* *fn-cfgct-configuration*
                                      *fn-cfgct-open*)
        (fn-native-admin-candidate-open-result
         *fn-cfgct-events* 2
         (fn-native-admin-append-record *fn-cfgct-history* *fn-cfgct-record*))))
(assert-event
 (equal (car (fn-cfgc-candidate-open-result *fn-cfgct-events* 2 *fn-cfgct-history*
                                           *fn-cfgct-record* *fn-cfgct-configuration*
                                           *fn-cfgct-open*))
        :accepted))

; fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization: the
; conclusion over the default profile, accepted at generation 51.
(defconst *fn-cfgct-profile* *fn-bs-profile-defaults*)
(defconst *fn-cfgct-carried*
  (fn-cfgc-cvec-native-admin-authorize *fn-cfgct-events* 2 *fn-cfgct-history*
                                      *fn-cfgct-record* t nil *fn-cfgct-profile*
                                      *fn-cfgct-open* *fn-cfgct-opened*))
(assert-event
 (equal *fn-cfgct-carried*
        (fn-cvec-native-admin-authorize *fn-cfgct-events* 2 *fn-cfgct-history*
                                        *fn-cfgct-record* t nil *fn-cfgct-profile*)))
(assert-event (equal (fn-native-admin-publication-status *fn-cfgct-carried*) :accepted))
(assert-event (equal (fn-native-admin-publication-generation *fn-cfgct-carried*) 51))

; -----------------------------------------------------------------------------
; Hypothesis removal.  Each omitted hypothesis: the retained ones hold, the
; omitted one fails, and the conclusion fails; then the theorem without it
; does not prove (the keystone's hints kept).

; (1) fn-cfgc-events-below.  Over the default record alone, a capacity
; decrease at txid 1 is filed BEFORE the release event (txid 1) and refused
; there (:config-refusal), while the one-step extension files it after the
; release, where its txid is behind the node (:config-txid): the replay is
; not one step from the fold.
(defconst *fn-cfgct-one* (list *fn-cfg-default-record*))
(defconst *fn-cfgct-early*
  (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1))
                      *fn-cfg-default-stamp*))
(assert-event (and (true-listp *fn-cfgct-one*) (true-listp *fn-cfgct-events*)))
(assert-event (not (fn-cfgc-events-below *fn-cfgct-events*
                                        (fn-cfg-record-txid *fn-cfgct-early*))))
(assert-event
 (equal (fn-replay-result-kind
         (fn-cpr-replay (append *fn-cfgct-one* (list *fn-cfgct-early*))
                        *fn-cfgct-events*))
        :fault))
(assert-event
 (not (equal (fn-cpr-replay (append *fn-cfgct-one* (list *fn-cfgct-early*))
                            *fn-cfgct-events*)
             (fn-cfgc-cpr-extend (fn-cpr-replay *fn-cfgct-one* *fn-cfgct-events*)
                                *fn-cfgct-one* *fn-cfgct-events* *fn-cfgct-early*))))
(must-fail
 (defthm fn-cfgct-cpr-without-below
   (implies (and (true-listp configs) (true-listp events))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-cfgc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (2) true-listp of the events.  An improper event list whose atom tail makes
; the fold fault; the extension then answers the fault while the replay with
; the record first consumes it.
(defconst *fn-cfgct-improper-events* (cons (car *fn-cfgct-events*) 7))
(assert-event (true-listp *fn-cfgct-history*))
(assert-event (fn-cfgc-events-below *fn-cfgct-improper-events*
                                   (fn-cfg-record-txid *fn-cfgct-record*)))
(assert-event (not (true-listp *fn-cfgct-improper-events*)))
(assert-event
 (not (equal (fn-cpr-replay (append *fn-cfgct-history* (list *fn-cfgct-record*))
                            *fn-cfgct-improper-events*)
             (fn-cfgc-cpr-extend (fn-cpr-replay *fn-cfgct-history*
                                               *fn-cfgct-improper-events*)
                                *fn-cfgct-history* *fn-cfgct-improper-events*
                                *fn-cfgct-record*))))
(must-fail
 (defthm fn-cfgct-cpr-without-true-events
   (implies (and (true-listp configs)
                 (fn-cfgc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-cfgc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (3) true-listp of the configurations.  An improper configuration history
; faults the fold (its tail is not a history), so the extension is the fault,
; while APPEND drops the tail and the replay succeeds.
(defconst *fn-cfgct-improper-history* (cons *fn-cfg-default-record* 5))
(defconst *fn-cfgct-second*
  (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 1048576))
                      *fn-cfg-default-stamp*))
(assert-event (true-listp *fn-cfgct-events*))
(assert-event (fn-cfgc-events-below *fn-cfgct-events*
                                   (fn-cfg-record-txid *fn-cfgct-second*)))
(assert-event (not (true-listp *fn-cfgct-improper-history*)))
; APPEND drops the atom tail (its guard refuses to execute it; this is its
; logical value).
(defthm fn-cfgct-append-of-improper
  (equal (append (cons x 5) (list y)) (list x y))
  :rule-classes nil)
(assert-event
 (not (equal (fn-cpr-replay (list *fn-cfg-default-record* *fn-cfgct-second*)
                            *fn-cfgct-events*)
             (fn-cfgc-cpr-extend (fn-cpr-replay *fn-cfgct-improper-history*
                                               *fn-cfgct-events*)
                                *fn-cfgct-improper-history* *fn-cfgct-events*
                                *fn-cfgct-second*))))
(must-fail
 (defthm fn-cfgct-cpr-without-true-configs
   (implies (and (true-listp events)
                 (fn-cfgc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-cfgc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (4) the carried fold is the open's replay (the open's result retained).  A
; carried fold of another
; history (the fold of the first 49 records) and the authorization differs:
; the candidate is refused where the replayed one is accepted.
(defconst *fn-cfgct-stale* (fn-cpr-replay (fn-cfgct-configs 0 0) *fn-cfgct-events*))
(assert-event (true-listp *fn-cfgct-history*))
(assert-event (not (equal *fn-cfgct-stale* *fn-cfgct-open*)))
(assert-event
 (not (equal (fn-cfgc-cvec-native-admin-authorize
              *fn-cfgct-events* 2 *fn-cfgct-history* *fn-cfgct-record* t nil
              *fn-cfgct-profile* *fn-cfgct-stale* *fn-cfgct-opened*)
             (fn-cvec-native-admin-authorize
              *fn-cfgct-events* 2 *fn-cfgct-history* *fn-cfgct-record* t nil
              *fn-cfgct-profile*))))
(must-fail
 (defthm fn-cfgct-authorize-without-the-open
   (implies (and (true-listp config-records)
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
                             fn-cpr-replay fn-cpo-open-observed
                             fn-cvec-group-names-within
                             fn-cvec-config-generations))))))

; (5) true-listp of the configuration records, for the authorization: the
; improper history's carried fold is its (faulting) replay, and the
; authorization it gives differs from the one over the appended history.
(defconst *fn-cfgct-improper-open*
  (fn-cpr-replay *fn-cfgct-improper-history* *fn-cfgct-events*))
(assert-event (not (true-listp *fn-cfgct-improper-history*)))
(assert-event
 (not (equal (fn-cfgc-candidate-open-result
              *fn-cfgct-events* 2 *fn-cfgct-improper-history* *fn-cfgct-second*
              (fn-cnode-config-replay *fn-cfgct-improper-history*)
              *fn-cfgct-improper-open*)
             (fn-native-admin-candidate-open-result
              *fn-cfgct-events* 2
              (fn-native-admin-append-record *fn-cfgct-improper-history*
                                             *fn-cfgct-second*)))))
(must-fail
 (defthm fn-cfgct-candidate-without-true-configs
   (implies (and (equal configuration (fn-cnode-config-replay config-records))
                 (equal replayed (fn-cpr-replay config-records records)))
            (equal (fn-cfgc-candidate-open-result
                    records frontier config-records record configuration replayed)
                   (fn-native-admin-candidate-open-result
                    records frontier
                    (fn-native-admin-append-record config-records record))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (fn-native-admin-candidate-open-result)
                            (fn-cpo-open-observed fn-cpr-replay fn-cfgc-cpr-extend
                             fn-cfgc-config-extend fn-cnode-config-replay
                             fn-sn-observed-historyp fn-cfgc-events-below
                             fn-native-admin-append-record))))))

; -----------------------------------------------------------------------------
; PKT-601 (1): the candidate open decided from the open's carried result
; (fn-cfgc-candidate-open-carried-is-the-replayed-candidate).

; The antecedents, non-degenerate: the open of the 50-record history
; succeeded (the whole-state recognizer ran inside it), its kind is :ok, the
; record is at the frontier; the carried candidate is the replaying one and
; accepts, from the fast arm (no candidate open run).
(assert-event (fn-sn-open-okp *fn-cfgct-opened*))
(assert-event (equal (fn-sn-open-kind *fn-cfgct-opened*) :ok))
(assert-event (<= 2 (fn-cfg-record-txid *fn-cfgct-record*)))
(defconst *fn-cfgct-candidate*
  (fn-cfgc-candidate-open-carried *fn-cfgct-events* 2 *fn-cfgct-history*
                                  *fn-cfgct-record* *fn-cfgct-configuration*
                                  *fn-cfgct-open* *fn-cfgct-opened*))
(assert-event
 (equal *fn-cfgct-candidate*
        (fn-native-admin-candidate-open-result
         *fn-cfgct-events* 2
         (fn-native-admin-append-record *fn-cfgct-history* *fn-cfgct-record*))))
(assert-event (equal (car *fn-cfgct-candidate*) :accepted))
(assert-event
 (equal (fn-cfg-generation (fn-cnode-config (cadr *fn-cfgct-candidate*))) 51))
; A refusal is decided the same way: a record whose generation skips one is
; refused by the extended fold, carried and replayed alike.
(defconst *fn-cfgct-skip*
  (fn-cfg-record-make 50 2 53 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))
(assert-event
 (and (not (equal (car (fn-native-admin-candidate-open-result
                        *fn-cfgct-events* 2
                        (fn-native-admin-append-record *fn-cfgct-history*
                                                       *fn-cfgct-skip*)))
                  :accepted))
      (equal (fn-cfgc-candidate-open-carried *fn-cfgct-events* 2 *fn-cfgct-history*
                                             *fn-cfgct-skip* *fn-cfgct-configuration*
                                             *fn-cfgct-open* *fn-cfgct-opened*)
             (fn-native-admin-candidate-open-result
              *fn-cfgct-events* 2
              (fn-native-admin-append-record *fn-cfgct-history* *fn-cfgct-skip*)))))
; fn-cfgc-advance-okp-is-replay-advance-okp, on the extended fold's node.
(assert-event
 (let ((node (fn-cnode-node (fn-replay-result-node
                             (fn-cfgc-cpr-extend *fn-cfgct-open* *fn-cfgct-history*
                                                 *fn-cfgct-events* *fn-cfgct-record*)))))
   (and (fn-node-statep node)
        (fn-cfgc-advance-okp node 2)
        (equal (fn-cfgc-advance-okp node 2) (fn-replay-advance-okp node 2))
        (not (fn-cfgc-advance-okp node 1))
        (equal (fn-cfgc-advance-okp node 1) (fn-replay-advance-okp node 1)))))

; Each attempt below carries the keystone's hints verbatim.

; (6) OPENED is the open's result.  A Store event whose generation is not its
; transaction id is not an observed history, so the open refuses it; the
; configured fold does not read the generation and succeeds.  A result that
; claims :ok for that history makes the carried candidate accept what the
; replaying one refuses.
(defconst *fn-cfgct-unobserved-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 5
                                        "admin-history" "subject" "evidence" 0)))
(defconst *fn-cfgct-one-open*
  (fn-cpr-replay *fn-cfgct-one* *fn-cfgct-unobserved-events*))
(assert-event (true-listp *fn-cfgct-one*))
(assert-event (equal (fn-replay-result-kind *fn-cfgct-one-open*) :ok))
(assert-event (not (fn-sn-observed-historyp 2 *fn-cfgct-unobserved-events*)))
(assert-event
 (not (equal (fn-sn-open-ok nil)
             (fn-cpo-open-observed *fn-cfgct-one* 2 *fn-cfgct-unobserved-events*))))
(assert-event
 (and (equal (car (fn-cfgc-candidate-open-carried
                   *fn-cfgct-unobserved-events* 2 *fn-cfgct-one* *fn-cfgct-second*
                   (fn-cnode-config-replay *fn-cfgct-one*) *fn-cfgct-one-open*
                   (fn-sn-open-ok nil)))
             :accepted)
      (equal (fn-native-admin-candidate-open-result
              *fn-cfgct-unobserved-events* 2
              (fn-native-admin-append-record *fn-cfgct-one* *fn-cfgct-second*))
             '(:refused :history))))
(must-fail
 (defthm fn-cfgct-carried-without-the-open-result
   (implies (and (true-listp config-records)
                 (equal configuration (fn-cnode-config-replay config-records))
                 (equal replayed (fn-cpr-replay config-records records)))
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
                             fn-sn-open-okp fn-sn-open-kind))))))

; (7) REPLAYED is the open's fold.  The stale fold (no configuration) with the
; open's own result: the carried candidate refuses what the replaying one
; accepts.
(assert-event
 (and (not (equal *fn-cfgct-stale* *fn-cfgct-open*))
      (not (equal (fn-cfgc-candidate-open-carried
                   *fn-cfgct-events* 2 *fn-cfgct-history* *fn-cfgct-record*
                   *fn-cfgct-configuration* *fn-cfgct-stale* *fn-cfgct-opened*)
                  *fn-cfgct-candidate*))))
(must-fail
 (defthm fn-cfgct-carried-without-the-fold
   (implies (and (true-listp config-records)
                 (equal configuration (fn-cnode-config-replay config-records))
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
                             fn-sn-open-okp fn-sn-open-kind))))))

; (8) CONFIGURATION is the configuration-only fold.  The fold of no record
; (the initial node at generation 0) makes the record's sequence 50 wrong.
(defconst *fn-cfgct-stale-configuration* (fn-cnode-config-replay nil))
(assert-event
 (and (not (equal *fn-cfgct-stale-configuration* *fn-cfgct-configuration*))
      (equal (fn-cfgc-candidate-open-carried
              *fn-cfgct-events* 2 *fn-cfgct-history* *fn-cfgct-record*
              *fn-cfgct-stale-configuration* *fn-cfgct-open* *fn-cfgct-opened*)
             '(:refused :configuration))))
(must-fail
 (defthm fn-cfgct-carried-without-the-configuration
   (implies (and (true-listp config-records)
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
                             fn-sn-open-okp fn-sn-open-kind))))))

; (9) true-listp of the configuration records: the improper history's open
; fails, the carried candidate falls back to the replaying one over the
; improper history, which differs from the one over the appended history
; (as in (5)).
(assert-event
 (not (equal (fn-cfgc-candidate-open-carried
              *fn-cfgct-events* 2 *fn-cfgct-improper-history* *fn-cfgct-second*
              (fn-cnode-config-replay *fn-cfgct-improper-history*)
              *fn-cfgct-improper-open*
              (fn-cpo-open-observed *fn-cfgct-improper-history* 2 *fn-cfgct-events*))
             (fn-native-admin-candidate-open-result
              *fn-cfgct-events* 2
              (fn-native-admin-append-record *fn-cfgct-improper-history*
                                             *fn-cfgct-second*)))))
(must-fail
 (defthm fn-cfgct-carried-without-true-configs
   (implies (and (equal configuration (fn-cnode-config-replay config-records))
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
                             fn-sn-open-okp fn-sn-open-kind))))))
