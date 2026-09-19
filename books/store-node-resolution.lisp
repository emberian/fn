; fn: synchronous refusal and known prepublication abort for the live store.
(in-package "ACL2")
(include-book "store-node-traces")

; A semantic refusal consumes the durable file reservation and advances the
; actual idle node over the same txid.  The host supplies only the reservation
; identity; it cannot supply either component's resolution result.
(defun fn-sn-refuse-reservation-enabledp (s txid)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :reserved)
       (natp txid)
       (equal (1+ txid) (fn-sf-frontier (fn-sn-files s)))
       (fn-replay-advance-okp
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s)))))

(verify-guards fn-sn-refuse-reservation-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defun fn-sn-refuse-reservation (s txid)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-refuse-reservation-enabledp s txid)
      (fn-sn-update
       s
       (fn-sf-refuse-reservation (fn-sn-files s) txid)
       (fn-replay-advance-txid
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
    s))

(verify-guards fn-sn-refuse-reservation
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-refuse-reservation-enabledp)
                                  (fn-sf-statep fn-node-statep)))))

; Only a proposal whose immutable publication has not been attempted has a
; known-absent resolution.  Exact sequence, txid, generation, and record data
; come from the bound candidate rather than from a host completion claim.
(defun fn-sn-known-abort-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let ((files (fn-sn-files s)))
    (and (mbe :logic (fn-sn-statep s) :exec t)
         (or (equal (fn-sf-phase files) :record-staged)
             (equal (fn-sf-phase files) :record-data-durable))
         (fn-sn-record-bindsp
          (fn-sn-node s) (fn-sf-record-candidate files)))))

(verify-guards fn-sn-known-abort-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defun fn-sn-known-abort-file-start (files)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (if (equal (fn-sf-phase files) :record-staged)
      (fn-sf-record-file-result files :known-fail)
    (fn-sf-prepublish-abort files)))

(verify-guards fn-sn-known-abort-file-start)

; The guard proof of fn-sn-known-abort-files: the abort start is a kernel state.
(defthm fn-sn-known-abort-file-start-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-file-start files)))
  :hints (("Goal"
           :in-theory (enable fn-sn-known-abort-file-start))))

; The public known-abort gate establishes a valid record candidate before
; calling this helper.
(defun fn-sn-known-abort-files (files)
  (declare (xargs :guard (and (fn-sf-statep files)
                              (true-listp (fn-sf-record-candidate files)))
                  :verify-guards nil))
  (let* ((record (fn-sf-record-candidate files))
         (aborting (fn-sn-known-abort-file-start files)))
    (fn-sf-abort-completion
     aborting (fn-record-sequence record) (fn-record-txid record))))

(verify-guards fn-sn-known-abort-files
  :hints (("Goal" :in-theory (disable fn-sn-known-abort-file-start))))

(local
 (defthm fn-snr-record-is-a-true-list
   (implies (fn-record-p record) (true-listp record))
   :hints (("Goal" :in-theory (enable fn-record-p)))))

(defun fn-sn-known-abort (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-known-abort-enabledp s)
      (let* ((files (fn-sn-files s))
             (record (fn-sf-record-candidate files))
             (node (fn-node-complete
                    (fn-sn-node s) (fn-record-txid record)
                    (fn-record-generation record) :aborted)))
        (fn-sn-update s (fn-sn-known-abort-files files) node))
    s))

(verify-guards fn-sn-known-abort
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep fn-sn-known-abort-enabledp fn-sn-record-bindsp)
                (fn-sf-statep fn-node-statep fn-record-p
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-known-abort-files fn-sn-known-abort-file-start)))))

(local (in-theory
        (e/d (fn-sn-update fn-sn-completion-enabledp fn-sn-completion-record
              fn-sn-io fn-sn-file-step fn-sn-prepare fn-sn-finish fn-sn-crash
              fn-sn-recover fn-sn-committed-recordp
              fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary
              fn-store-files-traces-vocabulary
              fn-store-node-invariants-vocabulary
              fn-store-node-traces-vocabulary)
             (fn-sn-statep fn-sf-statep fn-node-statep fn-record-p
              fn-sn-record-bindsp fn-snt-relation fn-snt-pending-linkp
              fn-sf-history-recoverablep fn-sf-replay-node
              fn-sn-refuse-reservation-enabledp fn-sn-refuse-reservation
              fn-sn-known-abort-enabledp fn-sn-known-abort-file-start
              fn-sn-known-abort-files fn-sn-known-abort
              fn-sf-refuse-reservation
              fn-sf-record-file-result fn-sf-prepublish-abort
              fn-sf-abort-completion fn-replay-advance-txid
              fn-node-complete fn-node-prepare fn-replay fn-replay-loop))))

; -by-definition: the else branches with their tests negated.
(defthm fn-sn-refuse-reservation-disabled-is-no-op
  (implies (not (fn-sn-refuse-reservation-enabledp s txid))
           (equal (fn-sn-refuse-reservation s txid) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation))))

(defthm fn-sn-known-abort-disabled-is-no-op
  (implies (not (fn-sn-known-abort-enabledp s))
           (equal (fn-sn-known-abort s) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-known-abort))))

(defthm fn-sn-refuse-reservation-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use ((:instance fn-sf-refuse-reservation-preserves-state
                            (s (fn-sn-files s)))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-sn-node s))
                            (recorded-txid
                             (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update fn-sn-statep)
                           (fn-sf-refuse-reservation
                            fn-replay-advance-txid)))))

(defthm fn-sn-known-abort-files-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-files files)))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state)
                 (:instance fn-sf-abort-completion-preserves-state
                            (s (fn-sn-known-abort-file-start files))
                            (sequence (fn-record-sequence
                                       (fn-sf-record-candidate files)))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate files)))))
           :in-theory (enable fn-sn-known-abort-files))))

(defthm fn-sn-known-abort-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use ((:instance fn-sn-known-abort-files-preserves-state
                            (files (fn-sn-files s)))
                 (:instance fn-node-complete-preserves-state
                            (s (fn-sn-node s))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))
                            (generation (fn-record-generation
                                         (fn-sf-record-candidate
                                          (fn-sn-files s))))
                            (completion-status :aborted)))
           :in-theory (e/d (fn-sn-known-abort fn-sn-update fn-sn-statep)
                           (fn-sn-record-bindsp
                            fn-sn-known-abort-files fn-node-complete)))))

(defthm fn-sn-refuse-reservation-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-refuse-reservation s txid))
              (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-refuse-reservation s txid))
              (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation
                                      fn-sn-update))))

(defthm fn-sn-known-abort-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-known-abort s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-known-abort s)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-known-abort fn-sn-update))))

(defthm fn-sn-refuse-reservation-cannot-acknowledge
  (equal (fn-sf-successes
          (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-refuse-reservation
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update)
                           (fn-sf-refuse-reservation )))))

(defthm fn-sn-known-abort-file-start-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-known-abort-file-start files))
         (fn-sf-successes files))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort-file-start)
                           (fn-sf-record-file-result fn-sf-prepublish-abort
                            )))))

(defthm fn-sn-known-abort-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-abort-completion
                            (s (fn-sn-known-abort-file-start (fn-sn-files s)))
                            (sequence (fn-record-sequence
                                       (fn-sf-record-candidate (fn-sn-files s))))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (e/d (fn-sn-known-abort fn-sn-known-abort-files
                             fn-sn-update)
                           (fn-sn-known-abort-file-start
                            fn-sf-abort-completion )))))

(defthm fn-sn-known-abort-files-reaches-ready
  (implies (and (fn-sf-statep files)
                (or (equal (fn-sf-phase files) :record-staged)
                    (equal (fn-sf-phase files) :record-data-durable)))
           (equal (fn-sf-phase (fn-sn-known-abort-files files)) :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state))
           :in-theory (enable fn-sn-known-abort-files
                              fn-sn-known-abort-file-start
                              fn-sf-record-file-result
                              fn-sf-prepublish-abort
                              fn-sf-abort-completion))))

(defthm fn-sn-refuse-reservation-is-exact-advance
  (implies (fn-sn-refuse-reservation-enabledp s txid)
           (and (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-refuse-reservation s txid)))
                       :ready)
                (equal (fn-sn-node (fn-sn-refuse-reservation s txid))
                       (fn-replay-advance-txid
                        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-sn-node (fn-sn-refuse-reservation s txid))))
                       (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory
           (enable fn-sn-refuse-reservation
                   fn-sn-refuse-reservation-enabledp fn-sn-update
                   fn-sf-refuse-reservation fn-replay-advance-txid))))

(defthm fn-sn-known-abort-is-exact-node-abort
  (implies (fn-sn-known-abort-enabledp s)
           (let ((record (fn-sf-record-candidate (fn-sn-files s))))
             (and (equal (fn-sf-phase
                          (fn-sn-files (fn-sn-known-abort s)))
                         :ready)
                  (equal (fn-sn-node (fn-sn-known-abort s))
                         (fn-node-complete
                          (fn-sn-node s) (fn-record-txid record)
                          (fn-record-generation record) :aborted)))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort
                             fn-sn-known-abort-enabledp fn-sn-update)
                           (fn-sn-known-abort-files 
                            fn-node-complete)))))

(defthm fn-sn-refuse-reservation-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use (fn-sn-refuse-reservation-preserves-state
                 (:instance fn-snt-advance-replayed-node
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (first (1- (fn-sf-frontier (fn-sn-files s))))
                            (second (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-sn-refuse-reservation
                             fn-sn-refuse-reservation-enabledp fn-sn-update
                             fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep
                            fn-sf-history-recoverablep fn-sf-replay-node
                            fn-snt-pending-linkp fn-sn-completion-enabledp
                            fn-replay-advance-txid)))))

(defthm fn-sn-known-abort-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use (fn-sn-known-abort-preserves-state
                 fn-sn-known-abort-is-exact-node-abort)
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-snt-pending-linkp
                             fn-sn-known-abort fn-sn-known-abort-enabledp
                             fn-sn-known-abort-files
                             fn-sn-known-abort-file-start fn-sn-update
                             fn-sf-record-file-result
                             fn-sf-prepublish-abort
                             fn-sf-abort-completion)
                            (fn-sn-statep fn-sf-statep
                             fn-sn-record-bindsp
                             fn-sf-history-recoverablep
                             fn-sf-replay-node fn-node-complete
                             fn-sn-completion-enabledp)))))

; =============================================================================
; Mixed live-store traces including refusal and known prepublication abort
; (folded from store-node-resolution-traces.lisp, 2026-09-19 realignment).
(local (in-theory (disable fn-snt-step   fn-sf-prefixp
                           fn-node-recover fn-node-initial-state
                            fn-state-next-txid
                             )))

; Like the base dispatcher, these are decoded logical events.  The two added
; branches call actual resolution operations without any invariant filter.
(defun fn-snrt-step (s event)
  (case (car event)
    (:refuse-reservation (fn-sn-refuse-reservation s (cadr event)))
    (:known-abort (fn-sn-known-abort s))
    (otherwise (fn-snt-step s event))))

(defun fn-snrt-run (s events)
  (if (consp events)
      (fn-snrt-run (fn-snrt-step s (car events)) (cdr events))
    s))

(defthm fn-snrt-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snrt-step s event)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-sn-prepare fn-sn-io
                      fn-sn-finish fn-sn-crash fn-sn-recover))))

(defthm fn-snrt-mixed-trace-preserves-live-history-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snrt-run s events)))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step))))

(defthm fn-snrt-initialized-mixed-trace-has-live-history-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-snrt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-initial))))

(defthm fn-snrt-mixed-trace-ready-node-is-exact-replay
  (let ((final (fn-snrt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                      (fn-sf-records (fn-sn-files final))
                      (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-node-is-exact-replay
                                   (s (fn-snrt-run s events))))
           :in-theory (disable fn-snt-relation fn-snrt-run))))

(defthm fn-snrt-step-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snrt-step s event)))))
  :hints (("Goal" :in-theory (enable fn-snrt-step))))

(defthm fn-snrt-mixed-trace-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snrt-run s events)))))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-successes (fn-sn-files s)))
                                 (ys (fn-sf-successes (fn-sn-files (fn-snrt-step s (car events)))))
                                 (zs (fn-sf-successes (fn-sn-files (fn-snrt-run
                                       (fn-snrt-step s (car events)) (cdr events))))))))))

; Prior acknowledged pairs survive arbitrary mixed wrapper traces.  Whenever
; the final live node is ready/recovered it equals replay of precisely this
; surviving history, rather than an independently trusted completion cache.
(defthm fn-snrt-acknowledged-history-retained-through-mixed-trace
  (let ((final (fn-snrt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (and (member-equal pair (fn-sf-successes (fn-sn-files final)))
                  (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final))))))
  :hints (("Goal"
    :use (fn-snrt-mixed-trace-success-history-monotone
          fn-snrt-mixed-trace-preserves-live-history-relation
          (:instance fn-snt-relation-implies-structural-state (s (fn-snrt-run s events)))
          (:instance fn-snt-typed-store-components (s (fn-snrt-run s events)))
          (:instance fn-sf-state-success-member-has-record
            (s (fn-sn-files (fn-snrt-run s events))))
          (:instance fn-sf-member-preserved-by-prefix
            (x pair) (xs (fn-sf-successes (fn-sn-files s)))
            (ys (fn-sf-successes (fn-sn-files (fn-snrt-run s events))))))
    :in-theory (disable fn-snrt-run fn-snt-relation 
                          fn-sf-record-has-pairp))))

; Refusal and abort add no acknowledgement-producing paths.  Any step that
; changes acknowledgement history executes the actual matching live durable
; completion, including its exact article and retention obligation.
(defthm fn-snrt-new-success-is-actual-matching-durable-completion
  (let ((next (fn-snrt-step s event)))
    (implies
     (not (equal (fn-sf-successes (fn-sn-files next))
                  (fn-sf-successes (fn-sn-files s))))
     (and (equal (car event) :finish)
          (fn-sn-completion-enabledp s)
          (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
          (equal (fn-sn-node next)
                 (fn-node-complete (fn-sn-node s)
                   (fn-record-txid (fn-sn-completion-record s))
                   (fn-record-generation (fn-sn-completion-record s)) :durable))
          (fn-sn-committed-recordp (fn-sn-node next) (fn-sn-completion-record s)))))
  :hints (("Goal"
           :use fn-sn-new-success-requires-actual-matching-durable-node-completion
           :in-theory (e/d (fn-snrt-step fn-snt-step)
                            (fn-sn-prepare fn-sn-io fn-sn-crash fn-sn-recover
                             fn-sn-finish fn-sn-completion-enabledp
                             fn-sn-record-bindsp fn-sn-completion-record
                             fn-sn-committed-recordp fn-node-complete
                              fn-record-txid fn-record-generation)))))

; -----------------------------------------------------------------------------
; Stable records only grow along resolution traces as well.

(defthm fn-snrt-refuse-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update 
                                   )
                                  (fn-sn-refuse-reservation-enabledp
                                   fn-sf-refuse-reservation )))))

(defthm fn-snrt-known-abort-files-keep-records
  (equal (fn-sf-records (fn-sn-known-abort-files files))
         (fn-sf-records files))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort-files
                                   fn-sn-known-abort-file-start)
                                  (fn-sf-abort-completion fn-sf-record-file-result
                                   fn-sf-prepublish-abort )))))

(defthm fn-snrt-known-abort-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort fn-sn-update 
                                   )
                                  (fn-sn-known-abort-enabledp
                                   fn-sn-known-abort-files 
                                   fn-node-complete)))))

(defthm fn-snrt-step-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-step s event)))))
  :hints (("Goal"
           :use (fn-snt-related-records-true-list
                 (:instance fn-snt-step-records-prefix))
           :in-theory (e/d (fn-snrt-step)
                           (fn-snt-relation fn-snt-step fn-sn-refuse-reservation
                            fn-sn-known-abort  
                            fn-sf-prefixp fn-snt-step-records-prefix)))))

(defthm fn-snrt-mixed-trace-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-run s events)))))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-records (fn-sn-files s)))
                                 (ys (fn-sf-records (fn-sn-files (fn-snrt-step s (car events)))))
                                 (zs (fn-sf-records (fn-sn-files (fn-snrt-run
                                       (fn-snrt-step s (car events)) (cdr events))))))))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the two resolution operations and their gates,
; the file helpers, the dispatcher, and under a name the file-helper and
; footprint lemmas.  Enabled on include: preservation of state, relation and
; configuration, the cannot-acknowledge family, the exact-advance and
; exact-abort keystones, fn-snrt-run and the snrt trace keystones.
(deftheory fn-store-node-resolution-vocabulary
  '(fn-sn-known-abort-file-start-preserves-state
    fn-sn-known-abort-files-preserves-state
    fn-sn-known-abort-file-start-cannot-acknowledge
    fn-sn-known-abort-files-reaches-ready
    fn-snrt-refuse-keeps-records fn-snrt-known-abort-files-keep-records
    fn-snrt-known-abort-keeps-records))
(in-theory (disable fn-store-node-resolution-vocabulary
                    fn-sn-refuse-reservation-enabledp fn-sn-refuse-reservation
                    fn-sn-known-abort-enabledp fn-sn-known-abort-file-start
                    fn-sn-known-abort-files fn-sn-known-abort fn-snrt-step))
