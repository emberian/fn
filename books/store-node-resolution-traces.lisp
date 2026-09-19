; fn: mixed live-store traces including refusal and known prepublication abort.
(in-package "ACL2")
(include-book "store-node-resolution")
(local (in-theory (disable fn-snt-relation fn-snt-step fn-sn-refuse-reservation
                           fn-sn-known-abort fn-sn-files fn-sf-successes
                           fn-sf-prefixp fn-node-statep fn-sf-statep fn-record-p
                           fn-node-prepare fn-node-complete fn-node-recover
                           fn-replay-advance-txid fn-replay fn-replay-loop
                           fn-sf-replay-node fn-sn-prepare-node
                           fn-retain-statep fn-node-initial-state
                           fn-node-acceptance fn-state-next-txid
                           fn-node-stage fn-state-pending fn-state-fenced)))

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
           :in-theory (disable fn-snt-relation fn-snrt-step fn-sn-files
                               fn-sf-successes fn-sf-prefixp))
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
    :in-theory (disable fn-snrt-run fn-snt-relation fn-sn-files
                        fn-sf-successes fn-sf-records fn-sf-record-has-pairp))))

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
                             fn-sn-node fn-record-txid fn-record-generation)))))

; -----------------------------------------------------------------------------
; Stable records only grow along resolution traces as well.

(defthm fn-snrt-refuse-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update fn-sn-make
                                   fn-sn-files)
                                  (fn-sn-refuse-reservation-enabledp
                                   fn-sf-refuse-reservation fn-sf-records)))))

(defthm fn-snrt-known-abort-files-keep-records
  (equal (fn-sf-records (fn-sn-known-abort-files files))
         (fn-sf-records files))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort-files
                                   fn-sn-known-abort-file-start)
                                  (fn-sf-abort-completion fn-sf-record-file-result
                                   fn-sf-prepublish-abort fn-sf-records)))))

(defthm fn-snrt-known-abort-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-known-abort fn-sn-update fn-sn-make
                                   fn-sn-files)
                                  (fn-sn-known-abort-enabledp
                                   fn-sn-known-abort-files fn-sf-records
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
                            fn-sn-known-abort fn-sn-files fn-sf-records
                            fn-sf-prefixp fn-snt-step-records-prefix)))))

(defthm fn-snrt-mixed-trace-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snrt-run s events)))))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (disable fn-snt-relation fn-snrt-step fn-sn-files
                               fn-sf-records fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-records (fn-sn-files s)))
                                 (ys (fn-sf-records (fn-sn-files (fn-snrt-step s (car events)))))
                                 (zs (fn-sf-records (fn-sn-files (fn-snrt-run
                                       (fn-snrt-step s (car events)) (cdr events))))))))))
