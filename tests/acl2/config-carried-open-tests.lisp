;; Teeth for books/config-carried-open.lisp (PKT-510 (1), PKT-601 (1) and
;; (2)): the authorization from the open's carried fold and carried open
;; result and the candidate open decided from that result.  The readback is
;; tests/acl2/config-carried-readback-tests.lisp.
;; The fixtures are books/config-carried-candidate's test book's (restated:
;; a test book is not included by another).
(in-package "ACL2")
(include-book "../../books/config-carried-open")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *fn-cfgct-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "admin-history" "subject" "evidence" 0)))

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

(defconst *fn-cfgct-record*
  (fn-cfg-record-make 50 2 51 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))

(defconst *fn-cfgct-open* (fn-cpr-replay *fn-cfgct-history* *fn-cfgct-events*))

(defconst *fn-cfgct-configuration* (fn-cnode-config-replay *fn-cfgct-history*))

(defconst *fn-cfgct-opened* (fn-cpo-open-observed *fn-cfgct-history* 2 *fn-cfgct-events*))

(defconst *fn-cfgct-one* (list *fn-cfg-default-record*))

(defconst *fn-cfgct-early*
  (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1))
                      *fn-cfg-default-stamp*))

(defconst *fn-cfgct-improper-events* (cons (car *fn-cfgct-events*) 7))

(defconst *fn-cfgct-improper-history* (cons *fn-cfg-default-record* 5))

(defconst *fn-cfgct-second*
  (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 1048576))
                      *fn-cfg-default-stamp*))

(defconst *fn-cfgct-improper-open*
  (fn-cpr-replay *fn-cfgct-improper-history* *fn-cfgct-events*))

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
(must-fail-checked
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
(must-fail-checked
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
(must-fail-checked
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
(must-fail-checked
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
(must-fail-checked
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
