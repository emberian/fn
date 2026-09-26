; Teeth for books/config-carried-candidate.lisp (PKT-510 (1)): the offline
; request's candidate and authorization from the open's carried fold.
(in-package "ACL2")
(include-book "../../books/config-carried-candidate")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; Two Store events (txids 0 and 1), the frontier at 2.
(defconst *fn-ccct-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "admin-history" "subject" "evidence" 0)))

; A configuration history of 50 records: the default record, then 49
; records filed at txid 2 (after both events), each a capacity row.
(defun fn-ccct-configs (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-cfg-record-make i 2 (+ 1 i)
                                (list (fn-cfg-set-capacity (+ 1048576 i)))
                                *fn-cfg-default-stamp*)
            (fn-ccct-configs (+ 1 i) n))
    nil))

(defconst *fn-ccct-history*
  (cons *fn-cfg-default-record* (fn-ccct-configs 1 50)))

; The request's record: sequence 50, generation 51, txid 2 (the frontier:
; the opened node's next, which is what the host builds).
(defconst *fn-ccct-record*
  (fn-cfg-record-make 50 2 51 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))

(defconst *fn-ccct-open* (fn-cpr-replay *fn-ccct-history* *fn-ccct-events*))
(defconst *fn-ccct-configuration* (fn-cnode-config-replay *fn-ccct-history*))

; The antecedents hold, and they are not degenerate: the history of 50
; records opens (the fold is :ok at generation 50), the record is filed after
; every event.
(assert-event (equal (len *fn-ccct-history*) 50))
(assert-event (true-listp *fn-ccct-history*))
(assert-event (true-listp *fn-ccct-events*))
(assert-event (equal (fn-replay-result-kind *fn-ccct-open*) :ok))
(assert-event (equal (fn-cfg-generation
                      (fn-cnode-config (fn-replay-result-node *fn-ccct-open*)))
                     50))
(assert-event (equal (fn-replay-result-kind *fn-ccct-configuration*) :ok))
(assert-event (fn-ccc-events-below *fn-ccct-events*
                                   (fn-cfg-record-txid *fn-ccct-record*)))
(assert-event (fn-sn-observed-historyp 2 *fn-ccct-events*))

; fn-ccc-config-replay-of-one-more and fn-ccc-cpr-replay-of-one-more: the
; conclusions, with the one-step extensions :ok at generation 51.
(assert-event
 (equal (fn-cnode-config-replay (append *fn-ccct-history* (list *fn-ccct-record*)))
        (fn-ccc-config-extend *fn-ccct-configuration* *fn-ccct-record*)))
(assert-event
 (equal (fn-cpr-replay (append *fn-ccct-history* (list *fn-ccct-record*))
                       *fn-ccct-events*)
        (fn-ccc-cpr-extend *fn-ccct-open* *fn-ccct-history* *fn-ccct-events*
                           *fn-ccct-record*)))
(assert-event
 (equal (fn-cfg-generation
         (fn-cnode-config
          (fn-replay-result-node
           (fn-ccc-cpr-extend *fn-ccct-open* *fn-ccct-history* *fn-ccct-events*
                              *fn-ccct-record*))))
        51))

; fn-ccc-candidate-open-result-is-the-replayed-candidate: the conclusion, and
; the candidate is accepted (a non-degenerate witness).
(assert-event
 (equal (fn-ccc-candidate-open-result *fn-ccct-events* 2 *fn-ccct-history*
                                      *fn-ccct-record* *fn-ccct-configuration*
                                      *fn-ccct-open*)
        (fn-native-admin-candidate-open-result
         *fn-ccct-events* 2
         (fn-native-admin-append-record *fn-ccct-history* *fn-ccct-record*))))
(assert-event
 (equal (car (fn-ccc-candidate-open-result *fn-ccct-events* 2 *fn-ccct-history*
                                           *fn-ccct-record* *fn-ccct-configuration*
                                           *fn-ccct-open*))
        :accepted))

; fn-ccc-cvec-native-admin-authorize-is-the-replayed-authorization: the
; conclusion over the default profile, accepted at generation 51.
(defconst *fn-ccct-profile* *fn-bs-profile-defaults*)
(defconst *fn-ccct-carried*
  (fn-ccc-cvec-native-admin-authorize *fn-ccct-events* 2 *fn-ccct-history*
                                      *fn-ccct-record* t nil *fn-ccct-profile*
                                      *fn-ccct-open*))
(assert-event
 (equal *fn-ccct-carried*
        (fn-cvec-native-admin-authorize *fn-ccct-events* 2 *fn-ccct-history*
                                        *fn-ccct-record* t nil *fn-ccct-profile*)))
(assert-event (equal (fn-native-admin-publication-status *fn-ccct-carried*) :accepted))
(assert-event (equal (fn-native-admin-publication-generation *fn-ccct-carried*) 51))

; -----------------------------------------------------------------------------
; Hypothesis removal.  Each omitted hypothesis: the retained ones hold, the
; omitted one fails, and the conclusion fails; then the theorem without it
; does not prove (the keystone's hints kept).

; (1) fn-ccc-events-below.  Over the default record alone, a capacity
; decrease at txid 1 is filed BEFORE the release event (txid 1) and refused
; there (:config-refusal), while the one-step extension files it after the
; release, where its txid is behind the node (:config-txid): the replay is
; not one step from the fold.
(defconst *fn-ccct-one* (list *fn-cfg-default-record*))
(defconst *fn-ccct-early*
  (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1))
                      *fn-cfg-default-stamp*))
(assert-event (and (true-listp *fn-ccct-one*) (true-listp *fn-ccct-events*)))
(assert-event (not (fn-ccc-events-below *fn-ccct-events*
                                        (fn-cfg-record-txid *fn-ccct-early*))))
(assert-event
 (equal (fn-replay-result-kind
         (fn-cpr-replay (append *fn-ccct-one* (list *fn-ccct-early*))
                        *fn-ccct-events*))
        :fault))
(assert-event
 (not (equal (fn-cpr-replay (append *fn-ccct-one* (list *fn-ccct-early*))
                            *fn-ccct-events*)
             (fn-ccc-cpr-extend (fn-cpr-replay *fn-ccct-one* *fn-ccct-events*)
                                *fn-ccct-one* *fn-ccct-events* *fn-ccct-early*))))
(must-fail
 (defthm fn-ccct-cpr-without-below
   (implies (and (true-listp configs) (true-listp events))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-ccc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (2) true-listp of the events.  An improper event list whose atom tail makes
; the fold fault; the extension then answers the fault while the replay with
; the record first consumes it.
(defconst *fn-ccct-improper-events* (cons (car *fn-ccct-events*) 7))
(assert-event (true-listp *fn-ccct-history*))
(assert-event (fn-ccc-events-below *fn-ccct-improper-events*
                                   (fn-cfg-record-txid *fn-ccct-record*)))
(assert-event (not (true-listp *fn-ccct-improper-events*)))
(assert-event
 (not (equal (fn-cpr-replay (append *fn-ccct-history* (list *fn-ccct-record*))
                            *fn-ccct-improper-events*)
             (fn-ccc-cpr-extend (fn-cpr-replay *fn-ccct-history*
                                               *fn-ccct-improper-events*)
                                *fn-ccct-history* *fn-ccct-improper-events*
                                *fn-ccct-record*))))
(must-fail
 (defthm fn-ccct-cpr-without-true-events
   (implies (and (true-listp configs)
                 (fn-ccc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-ccc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (3) true-listp of the configurations.  An improper configuration history
; faults the fold (its tail is not a history), so the extension is the fault,
; while APPEND drops the tail and the replay succeeds.
(defconst *fn-ccct-improper-history* (cons *fn-cfg-default-record* 5))
(defconst *fn-ccct-second*
  (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 1048576))
                      *fn-cfg-default-stamp*))
(assert-event (true-listp *fn-ccct-events*))
(assert-event (fn-ccc-events-below *fn-ccct-events*
                                   (fn-cfg-record-txid *fn-ccct-second*)))
(assert-event (not (true-listp *fn-ccct-improper-history*)))
; APPEND drops the atom tail (its guard refuses to execute it; this is its
; logical value).
(defthm fn-ccct-append-of-improper
  (equal (append (cons x 5) (list y)) (list x y))
  :rule-classes nil)
(assert-event
 (not (equal (fn-cpr-replay (list *fn-cfg-default-record* *fn-ccct-second*)
                            *fn-ccct-events*)
             (fn-ccc-cpr-extend (fn-cpr-replay *fn-ccct-improper-history*
                                               *fn-ccct-events*)
                                *fn-ccct-improper-history* *fn-ccct-events*
                                *fn-ccct-second*))))
(must-fail
 (defthm fn-ccct-cpr-without-true-configs
   (implies (and (true-listp events)
                 (fn-ccc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-ccc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

; (4) the carried fold is the open's replay.  A carried fold of another
; history (the fold of the first 49 records) and the authorization differs:
; the candidate is refused where the replayed one is accepted.
(defconst *fn-ccct-stale* (fn-cpr-replay (fn-ccct-configs 0 0) *fn-ccct-events*))
(assert-event (true-listp *fn-ccct-history*))
(assert-event (not (equal *fn-ccct-stale* *fn-ccct-open*)))
(assert-event
 (not (equal (fn-ccc-cvec-native-admin-authorize
              *fn-ccct-events* 2 *fn-ccct-history* *fn-ccct-record* t nil
              *fn-ccct-profile* *fn-ccct-stale*)
             (fn-cvec-native-admin-authorize
              *fn-ccct-events* 2 *fn-ccct-history* *fn-ccct-record* t nil
              *fn-ccct-profile*))))
(must-fail
 (defthm fn-ccct-authorize-without-the-open
   (implies (true-listp config-records)
            (equal (fn-ccc-cvec-native-admin-authorize
                    records frontier config-records record lock-owned
                    observed-names profile replayed)
                   (fn-cvec-native-admin-authorize
                    records frontier config-records record lock-owned
                    observed-names profile)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (fn-cvec-native-admin-authorize)
                            (fn-ccc-publication-authorize
                             fn-native-admin-publication-authorize
                             fn-cpr-replay fn-cvec-group-names-within
                             fn-cvec-config-generations))))))

; (5) true-listp of the configuration records, for the authorization: the
; improper history's carried fold is its (faulting) replay, and the
; authorization it gives differs from the one over the appended history.
(defconst *fn-ccct-improper-open*
  (fn-cpr-replay *fn-ccct-improper-history* *fn-ccct-events*))
(assert-event (not (true-listp *fn-ccct-improper-history*)))
(assert-event
 (not (equal (fn-ccc-candidate-open-result
              *fn-ccct-events* 2 *fn-ccct-improper-history* *fn-ccct-second*
              (fn-cnode-config-replay *fn-ccct-improper-history*)
              *fn-ccct-improper-open*)
             (fn-native-admin-candidate-open-result
              *fn-ccct-events* 2
              (fn-native-admin-append-record *fn-ccct-improper-history*
                                             *fn-ccct-second*)))))
(must-fail
 (defthm fn-ccct-candidate-without-true-configs
   (implies (and (equal configuration (fn-cnode-config-replay config-records))
                 (equal replayed (fn-cpr-replay config-records records)))
            (equal (fn-ccc-candidate-open-result
                    records frontier config-records record configuration replayed)
                   (fn-native-admin-candidate-open-result
                    records frontier
                    (fn-native-admin-append-record config-records record))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (fn-native-admin-candidate-open-result)
                            (fn-cpo-open-observed fn-cpr-replay fn-ccc-cpr-extend
                             fn-ccc-config-extend fn-cnode-config-replay
                             fn-sn-observed-historyp fn-ccc-events-below
                             fn-native-admin-append-record))))))
