; Teeth for books/config-carried-candidate.lisp (PKT-510 (1)): the folds'
; one-step extensions and the candidate from the open's carried folds.  The
; authorization, the carried open result and the readback are
; tests/acl2/config-carried-open-tests.lisp.
(in-package "ACL2")
(include-book "../../books/config-carried-candidate")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

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
(must-fail-checked
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
(must-fail-checked
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
(must-fail-checked
 (defthm fn-cfgct-cpr-without-true-configs
   (implies (and (true-listp events)
                 (fn-cfgc-events-below events (fn-cfg-record-txid record)))
            (equal (fn-cpr-replay (append configs (list record)) events)
                   (fn-cfgc-cpr-extend (fn-cpr-replay configs events)
                                      configs events record)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-cnode-statep))))))

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
(must-fail-checked
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
