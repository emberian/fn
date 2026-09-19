; Finite traces for the immutable-file storage kernel.
;
; Events in this book dispatch to the transitions in store-files.lisp.  The
; event recognizer describes bounded input syntax only: it does not assume that
; an event is enabled, that its result preserves the state recognizer, or that
; the post-state is valid.  Disabled and mismatched events consequently retain
; the kernel's existing no-op behavior.
;
; A trace carries one groups/capacity configuration, used by every prepare and
; recovery event in that trace.  The trace theorem is about the logical kernel
; and its crash choices.  In particular, it does not establish that POSIX I/O
; implements an event, or that the ghost success list has an independent
; durable representation.
;
; The event vocabulary is the kernel's.  :lose-success is retained for the
; kernel trace but is unreachable-in-composition (see fn-sf-lose-success);
; the composed dispatchers in store-node-traces.lisp never issue it.

(in-package "ACL2")
(include-book "store-files-invariants")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))
(local (in-theory (enable fn-store-files-invariants-vocabulary)))

(defconst *fn-sf-max-trace-events* 4096)

; -----------------------------------------------------------------------------
; Bounded event syntax.  Each event is a proper fixed-width list.  Records and
; integer identifiers use the bounds already enforced by the storage kernel.

(defun fn-sf-eventp (event)
  (and
   (true-listp event)
   (cond
    ((equal event '(:start-frontier)) t)
    ((equal (car event) :frontier-file)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :known-fail))))
    ((equal (car event) :frontier-replace)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :error))))
    ((equal (car event) :frontier-dir)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :error))))
    ((equal (car event) :refuse-reservation)
     (and (equal (len event) 2)
          (fn-record-uint32p (car (cdr event)))))
    ((equal (car event) :prepare-record)
     (and (equal (len event) 2)
          (fn-record-p (car (cdr event)))))
    ((equal (car event) :record-file)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :known-fail))))
    ((equal event '(:prepublish-abort)) t)
    ((equal (car event) :abort-completion)
     (and (equal (len event) 3)
          (fn-record-uint32p (car (cdr event)))
          (fn-record-uint32p (car (cdr (cdr event))))))
    ((equal (car event) :record-link)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :error))))
    ((equal (car event) :record-dir)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :error))))
    ((equal (car event) :core-completion)
     (and (equal (len event) 3)
          (fn-record-uint32p (car (cdr event)))
          (fn-record-uint32p (car (cdr (cdr event))))))
    ((equal (car event) :emit-success)
     (and (equal (len event) 3)
          (fn-record-uint32p (car (cdr event)))
          (fn-record-uint32p (car (cdr (cdr event))))))
    ((equal (car event) :lose-success)
     (and (equal (len event) 3)
          (fn-record-uint32p (car (cdr event)))
          (fn-record-uint32p (car (cdr (cdr event))))))
    ((equal (car event) :crash)
     (and (equal (len event) 3)
          (fn-sf-crash-choicep (car (cdr event))
                               (car (cdr (cdr event))))))
    ((equal event '(:recover)) t)
    ((equal (car event) :recovery-barrier)
     (and (equal (len event) 2)
          (member-equal (car (cdr event)) '(:ok :uncertain))))
    (t nil))))

(defun fn-sf-event-listp (events)
  (if (consp events)
      (and (fn-sf-eventp (car events))
           (fn-sf-event-listp (cdr events)))
    (null events)))

; Trace layout: (:store-files-trace groups capacity events).
(defun fn-sf-trace-groups (trace) (car (cdr trace)))
(defun fn-sf-trace-capacity (trace) (car (cdr (cdr trace))))
(defun fn-sf-trace-events (trace) (car (cdr (cdr (cdr trace)))))

(defun fn-sf-trace-make (groups capacity events)
  (list :store-files-trace groups capacity events))

(defun fn-sf-tracep (trace)
  (and (true-listp trace)
       (equal (len trace) 4)
       (equal (car trace) :store-files-trace)
       (fn-string-listp (fn-sf-trace-groups trace))
       (fn-no-duplicatesp (fn-sf-trace-groups trace))
       (natp (fn-sf-trace-capacity trace))
       (fn-sf-event-listp (fn-sf-trace-events trace))
       (<= (len (fn-sf-trace-events trace)) *fn-sf-max-trace-events*)))

; -----------------------------------------------------------------------------
; Dispatcher and interpreter.  These calls are the actual storage-kernel
; functions; the trace layer does not reproduce their phase semantics.

(defun fn-sf-dispatch (s event groups capacity)
  (cond
   ((equal (car event) :start-frontier)
    (fn-sf-start-frontier s))
   ((equal (car event) :frontier-file)
    (fn-sf-frontier-file-result s (car (cdr event))))
   ((equal (car event) :frontier-replace)
    (fn-sf-frontier-replace-result s (car (cdr event))))
   ((equal (car event) :frontier-dir)
    (fn-sf-frontier-dir-result s (car (cdr event))))
   ((equal (car event) :refuse-reservation)
    (fn-sf-refuse-reservation s (car (cdr event))))
   ((equal (car event) :prepare-record)
    (fn-sf-prepare-record s (car (cdr event)) groups capacity))
   ((equal (car event) :record-file)
    (fn-sf-record-file-result s (car (cdr event))))
   ((equal (car event) :prepublish-abort)
    (fn-sf-prepublish-abort s))
   ((equal (car event) :abort-completion)
    (fn-sf-abort-completion s (car (cdr event))
                            (car (cdr (cdr event)))))
   ((equal (car event) :record-link)
    (fn-sf-record-link-result s (car (cdr event))))
   ((equal (car event) :record-dir)
    (fn-sf-record-dir-result s (car (cdr event))))
   ((equal (car event) :core-completion)
    (fn-sf-core-completion s (car (cdr event))
                           (car (cdr (cdr event)))))
   ((equal (car event) :emit-success)
    (fn-sf-emit-success s (car (cdr event))
                        (car (cdr (cdr event)))))
   ((equal (car event) :lose-success)
    (fn-sf-lose-success s (car (cdr event))
                        (car (cdr (cdr event)))))
   ((equal (car event) :crash)
    (fn-sf-crash s (car (cdr event)) (car (cdr (cdr event)))))
   ((equal (car event) :recover)
    (fn-sf-recover s groups capacity))
   ((equal (car event) :recovery-barrier)
    (fn-sf-recovery-barrier s (car (cdr event))))
   (t s)))

(defun fn-sf-run-events (s events groups capacity)
  (if (consp events)
      (fn-sf-run-events
       (fn-sf-dispatch s (car events) groups capacity)
       (cdr events) groups capacity)
    s))

(defun fn-sf-run-trace (s trace)
  (if (fn-sf-tracep trace)
      (fn-sf-run-events s (fn-sf-trace-events trace)
                        (fn-sf-trace-groups trace)
                        (fn-sf-trace-capacity trace))
    s))

; -----------------------------------------------------------------------------
; One-event facts, established from each underlying transition theorem.

; Keep recognizers and replay semantics opaque in footprint and induction
; proofs.  The dispatcher preservation theorem below is where the already
; certified transition theorems discharge those obligations.
(local
 (in-theory
  (disable fn-sf-statep fn-sf-phase-shapep fn-sf-record-listp
           fn-sf-success-listp fn-sf-candidatep
           fn-sf-history-recoverablep fn-sf-replay-node fn-record-p
              fn-sf-prefixp)))

; These footprint lemmas keep the trace proofs at the storage API boundary.
; Every listed transition carries stable records through unchanged; publication
; directory completion and crash are the only transitions that may append one.
(defthm fn-sf-records-of-start-frontier
  (equal (fn-sf-records (fn-sf-start-frontier s)) (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier))))

(defthm fn-sf-records-of-frontier-file-result
  (equal (fn-sf-records (fn-sf-frontier-file-result s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-file-result))))

(defthm fn-sf-records-of-frontier-replace-result
  (equal (fn-sf-records (fn-sf-frontier-replace-result s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-replace-result))))

(defthm fn-sf-records-of-frontier-dir-result
  (equal (fn-sf-records (fn-sf-frontier-dir-result s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-dir-result))))

(defthm fn-sf-records-of-refuse-reservation
  (equal (fn-sf-records (fn-sf-refuse-reservation s txid))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-refuse-reservation))))

(defthm fn-sf-records-of-prepare-record
  (equal (fn-sf-records (fn-sf-prepare-record s record groups capacity))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-prepare-record))))

(defthm fn-sf-records-of-record-file-result
  (equal (fn-sf-records (fn-sf-record-file-result s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-record-file-result))))

(defthm fn-sf-records-of-prepublish-abort
  (equal (fn-sf-records (fn-sf-prepublish-abort s)) (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-prepublish-abort))))

(defthm fn-sf-records-of-abort-completion
  (equal (fn-sf-records
          (fn-sf-abort-completion s sequence txid))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-abort-completion))))

(defthm fn-sf-records-of-record-link-result
  (equal (fn-sf-records (fn-sf-record-link-result s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-record-link-result))))

(defthm fn-sf-records-of-core-completion
  (equal (fn-sf-records
          (fn-sf-core-completion s sequence txid))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-core-completion))))

(defthm fn-sf-records-of-emit-success
  (equal (fn-sf-records (fn-sf-emit-success s sequence txid))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-emit-success))))

; unreachable-in-composition: see fn-sf-lose-success in store-files.lisp.
(defthm fn-sf-records-of-lose-success
  (equal (fn-sf-records (fn-sf-lose-success s sequence txid))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-lose-success))))

(defthm fn-sf-records-of-recover
  (equal (fn-sf-records (fn-sf-recover s groups capacity))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-recover))))

(defthm fn-sf-records-of-recovery-barrier
  (equal (fn-sf-records (fn-sf-recovery-barrier s result))
         (fn-sf-records s))
  :hints (("Goal" :in-theory (enable fn-sf-recovery-barrier))))

(defthm fn-sf-state-records-are-true-list
  (implies (fn-sf-statep s)
           (true-listp (fn-sf-records s)))
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-is-true-list
                            (records (fn-sf-records s))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier s))))
           :in-theory (enable fn-sf-statep))))

(defthm fn-sf-stable-records-prefix-of-record-dir-result
  (implies (fn-sf-statep s)
           (fn-sf-prefixp
            (fn-sf-records s)
            (fn-sf-records (fn-sf-record-dir-result s result))))
  :hints (("Goal"
           :use ((:instance fn-sf-prefixp-append
                            (xs (fn-sf-records s))
                            (ys (list (fn-sf-record-candidate s)))))
           :in-theory (enable fn-sf-record-dir-result))))

; Success history is unchanged by every transition except emit-success.
(defthm fn-sf-successes-of-start-frontier
  (equal (fn-sf-successes (fn-sf-start-frontier s)) (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier))))

(defthm fn-sf-successes-of-frontier-file-result
  (equal (fn-sf-successes (fn-sf-frontier-file-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-file-result))))

(defthm fn-sf-successes-of-frontier-replace-result
  (equal (fn-sf-successes (fn-sf-frontier-replace-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-replace-result))))

(defthm fn-sf-successes-of-frontier-dir-result
  (equal (fn-sf-successes (fn-sf-frontier-dir-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-frontier-dir-result))))

(defthm fn-sf-successes-of-refuse-reservation
  (equal (fn-sf-successes (fn-sf-refuse-reservation s txid))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-refuse-reservation))))

(defthm fn-sf-successes-of-prepare-record
  (equal (fn-sf-successes (fn-sf-prepare-record s record groups capacity))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-prepare-record))))

(defthm fn-sf-successes-of-record-file-result
  (equal (fn-sf-successes (fn-sf-record-file-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-record-file-result))))

(defthm fn-sf-successes-of-prepublish-abort
  (equal (fn-sf-successes (fn-sf-prepublish-abort s))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-prepublish-abort))))

(defthm fn-sf-successes-of-abort-completion
  (equal (fn-sf-successes
          (fn-sf-abort-completion s sequence txid))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-abort-completion))))

(defthm fn-sf-successes-of-record-link-result
  (equal (fn-sf-successes (fn-sf-record-link-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-record-link-result))))

(defthm fn-sf-successes-of-record-dir-result
  (equal (fn-sf-successes (fn-sf-record-dir-result s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-record-dir-result))))

(defthm fn-sf-successes-of-core-completion
  (equal (fn-sf-successes
          (fn-sf-core-completion s sequence txid))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-core-completion))))

; unreachable-in-composition: see fn-sf-lose-success in store-files.lisp.
(defthm fn-sf-successes-of-lose-success
  (equal (fn-sf-successes (fn-sf-lose-success s sequence txid))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-lose-success))))

(defthm fn-sf-successes-of-crash
  (equal (fn-sf-successes (fn-sf-crash s frontier-choice record-choice))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-crash))))

(defthm fn-sf-successes-of-recover
  (equal (fn-sf-successes (fn-sf-recover s groups capacity))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-recover))))

(defthm fn-sf-successes-of-recovery-barrier
  (equal (fn-sf-successes (fn-sf-recovery-barrier s result))
         (fn-sf-successes s))
  :hints (("Goal" :in-theory (enable fn-sf-recovery-barrier))))

(defthm fn-sf-success-listp-is-true-list
  (implies (fn-sf-success-listp successes records)
           (true-listp successes))
  :hints (("Goal" :induct (fn-sf-success-listp successes records)
           :in-theory (enable fn-sf-success-listp)))
  :rule-classes :forward-chaining)

(defthm fn-sf-state-successes-are-true-list
  (implies (fn-sf-statep s)
           (true-listp (fn-sf-successes s)))
  :hints (("Goal" :in-theory (enable fn-sf-statep))))

(defthm fn-sf-successes-prefix-of-emit-success
  (implies (fn-sf-statep s)
           (fn-sf-prefixp
            (fn-sf-successes s)
            (fn-sf-successes (fn-sf-emit-success s sequence txid))))
  :hints (("Goal"
           :use ((:instance fn-sf-prefixp-append
                            (xs (fn-sf-successes s))
                            (ys (list (cons sequence txid)))))
           :in-theory (enable fn-sf-emit-success))))

(defthm fn-sf-dispatch-preserves-state
  (implies (and (fn-sf-statep s)
                (fn-sf-eventp event))
           (fn-sf-statep (fn-sf-dispatch s event groups capacity)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sf-eventp fn-sf-dispatch)
                (fn-sf-statep  fn-sf-prefixp
                 fn-sf-start-frontier
                 fn-sf-frontier-file-result
                 fn-sf-frontier-replace-result
                 fn-sf-frontier-dir-result
                 fn-sf-refuse-reservation
                 fn-sf-prepare-record
                 fn-sf-record-file-result
                 fn-sf-prepublish-abort
                 fn-sf-abort-completion
                 fn-sf-record-link-result
                 fn-sf-record-dir-result
                 fn-sf-core-completion
                 fn-sf-emit-success
                 fn-sf-lose-success
                 fn-sf-crash
                 fn-sf-recover
                 fn-sf-recovery-barrier)))))

(defthm fn-sf-stable-records-prefix-of-dispatch
  (implies (and (fn-sf-statep s)
                (fn-sf-eventp event))
           (fn-sf-prefixp
            (fn-sf-records s)
            (fn-sf-records (fn-sf-dispatch s event groups capacity))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sf-eventp fn-sf-dispatch)
                (fn-sf-statep  fn-sf-prefixp
                 fn-sf-start-frontier
                 fn-sf-frontier-file-result
                 fn-sf-frontier-replace-result
                 fn-sf-frontier-dir-result
                 fn-sf-refuse-reservation
                 fn-sf-prepare-record
                 fn-sf-record-file-result
                 fn-sf-prepublish-abort
                 fn-sf-abort-completion
                 fn-sf-record-link-result
                 fn-sf-record-dir-result
                 fn-sf-core-completion
                 fn-sf-emit-success
                 fn-sf-lose-success
                 fn-sf-crash
                 fn-sf-recover
                 fn-sf-recovery-barrier)))))

(defthm fn-sf-successes-prefix-of-dispatch
  (implies (and (fn-sf-statep s)
                (fn-sf-eventp event))
           (fn-sf-prefixp
            (fn-sf-successes s)
            (fn-sf-successes (fn-sf-dispatch s event groups capacity))))
  :hints (("Goal"
           :in-theory
           (e/d (fn-sf-eventp fn-sf-dispatch)
                (fn-sf-statep  fn-sf-prefixp
                 fn-sf-start-frontier
                 fn-sf-frontier-file-result
                 fn-sf-frontier-replace-result
                 fn-sf-frontier-dir-result
                 fn-sf-refuse-reservation
                 fn-sf-prepare-record
                 fn-sf-record-file-result
                 fn-sf-prepublish-abort
                 fn-sf-abort-completion
                 fn-sf-record-link-result
                 fn-sf-record-dir-result
                 fn-sf-core-completion
                 fn-sf-emit-success
                 fn-sf-lose-success
                 fn-sf-crash
                 fn-sf-recover
                 fn-sf-recovery-barrier)))))

; Prefix composition and membership are independent of store state.
(local
 (defun fn-sf-prefixp-transitive-induction (xs ys zs)
   (if (consp xs)
       (fn-sf-prefixp-transitive-induction (cdr xs) (cdr ys) (cdr zs))
     (list ys zs))))

(defthm fn-sf-prefixp-transitive
  (implies (and (fn-sf-prefixp xs ys)
                (fn-sf-prefixp ys zs))
           (fn-sf-prefixp xs zs))
  :hints (("Goal" :induct
           (fn-sf-prefixp-transitive-induction xs ys zs)
           :in-theory (enable fn-sf-prefixp))))

(defthm fn-sf-record-pair-preserved-by-prefix
  (implies (and (fn-sf-prefixp records more-records)
                (fn-sf-record-has-pairp pair records))
           (fn-sf-record-has-pairp pair more-records))
  :hints (("Goal" :induct (fn-sf-prefixp records more-records)
           :in-theory (enable fn-sf-prefixp fn-sf-record-has-pairp))))

(defthm fn-sf-member-preserved-by-prefix
  (implies (and (fn-sf-prefixp xs ys)
                (member-equal x xs))
           (member-equal x ys))
  :hints (("Goal" :induct (fn-sf-prefixp xs ys)
           :in-theory (enable fn-sf-prefixp member-equal))))

; -----------------------------------------------------------------------------
; Arbitrary finite permitted traces.

(defthm fn-sf-run-events-preserves-state
  (implies (and (fn-sf-statep s)
                (fn-sf-event-listp events))
           (fn-sf-statep (fn-sf-run-events s events groups capacity)))
  :hints (("Goal" :induct (fn-sf-run-events s events groups capacity)
           :in-theory
           (e/d (fn-sf-run-events fn-sf-event-listp)
                (fn-sf-statep fn-sf-dispatch fn-sf-eventp)))))

(defthm fn-sf-stable-records-prefix-of-run-events
  (implies (and (fn-sf-statep s)
                (fn-sf-event-listp events))
           (fn-sf-prefixp
            (fn-sf-records s)
            (fn-sf-records
             (fn-sf-run-events s events groups capacity))))
  :hints (("Goal" :induct (fn-sf-run-events s events groups capacity)
           :in-theory
           (e/d (fn-sf-run-events fn-sf-event-listp)
                (fn-sf-statep fn-sf-dispatch fn-sf-eventp
                  fn-sf-prefixp)))
          ("Subgoal *1/1"
           :use ((:instance fn-sf-prefixp-transitive
                            (xs (fn-sf-records s))
                            (ys (fn-sf-records
                                 (fn-sf-dispatch s (car events)
                                                 groups capacity)))
                            (zs (fn-sf-records
                                 (fn-sf-run-events
                                  (fn-sf-dispatch s (car events)
                                                  groups capacity)
                                  (cdr events) groups capacity))))))))

(defthm fn-sf-successes-prefix-of-run-events
  (implies (and (fn-sf-statep s)
                (fn-sf-event-listp events))
           (fn-sf-prefixp
            (fn-sf-successes s)
            (fn-sf-successes
             (fn-sf-run-events s events groups capacity))))
  :hints (("Goal" :induct (fn-sf-run-events s events groups capacity)
           :in-theory
           (e/d (fn-sf-run-events fn-sf-event-listp)
                (fn-sf-statep fn-sf-dispatch fn-sf-eventp
                  fn-sf-prefixp)))
          ("Subgoal *1/1"
           :use ((:instance fn-sf-prefixp-transitive
                            (xs (fn-sf-successes s))
                            (ys (fn-sf-successes
                                 (fn-sf-dispatch s (car events)
                                                 groups capacity)))
                            (zs (fn-sf-successes
                                 (fn-sf-run-events
                                  (fn-sf-dispatch s (car events)
                                                  groups capacity)
                                  (cdr events) groups capacity))))))))

(defthm fn-sf-run-trace-preserves-state
  (implies (and (fn-sf-statep s)
                (fn-sf-tracep trace))
           (fn-sf-statep (fn-sf-run-trace s trace))))

(defthm fn-sf-stable-records-prefix-of-run-trace
  (implies (and (fn-sf-statep s)
                (fn-sf-tracep trace))
           (fn-sf-prefixp
            (fn-sf-records s)
            (fn-sf-records (fn-sf-run-trace s trace)))))

(defthm fn-sf-successes-prefix-of-run-trace
  (implies (and (fn-sf-statep s)
                (fn-sf-tracep trace))
           (fn-sf-prefixp
            (fn-sf-successes s)
            (fn-sf-successes (fn-sf-run-trace s trace)))))

; Internal ghost retention: every success already present in the starting
; state's ghost list still names a stable record after any permitted trace.
(defthm fn-sf-prior-ghost-success-retained-by-run-trace
  (implies (and (fn-sf-statep s)
                (fn-sf-tracep trace)
                (member-equal pair (fn-sf-successes s)))
           (and (member-equal pair
                              (fn-sf-successes (fn-sf-run-trace s trace)))
                (fn-sf-record-has-pairp
                 pair (fn-sf-records (fn-sf-run-trace s trace)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-success-member-has-record)
                 (:instance fn-sf-member-preserved-by-prefix
                            (x pair)
                            (xs (fn-sf-successes s))
                            (ys (fn-sf-successes
                                 (fn-sf-run-trace s trace))))
                 (:instance fn-sf-record-pair-preserved-by-prefix
                            (records (fn-sf-records s))
                            (more-records
                             (fn-sf-records (fn-sf-run-trace s trace))))))))

; Environmental scope for the ghost premise.  This predicate is supplied by
; the trace environment: it says that each externally emitted success being
; claimed was recorded in the starting ghost history.  The kernel cannot infer
; it from socket writes, and the predicate is not stored by the file adapter.
(defun fn-sf-ghost-covers-emittedp (externally-emitted ghost-successes)
  (if (consp externally-emitted)
      (and (member-equal (car externally-emitted) ghost-successes)
           (fn-sf-ghost-covers-emittedp (cdr externally-emitted)
                                        ghost-successes))
    (null externally-emitted)))

(defthm fn-sf-covered-emitted-member-is-ghost-member
  (implies (and (fn-sf-ghost-covers-emittedp externally-emitted
                                             ghost-successes)
                (member-equal pair externally-emitted))
           (member-equal pair ghost-successes))
  :hints (("Goal" :induct
           (fn-sf-ghost-covers-emittedp externally-emitted
                                        ghost-successes))))

; Conditional external claim: prior emitted successes retain their exact
; sequence/txid record across arbitrary allocator, publication, crash, recovery,
; and rebarrier events, provided the environment placed those emissions in the
; initial ghost history and the modeled durable crash choices apply.
(defthm fn-sf-prior-emitted-success-retained-by-run-trace
  (implies
   (and (fn-sf-statep s)
        (fn-sf-tracep trace)
        (fn-sf-ghost-covers-emittedp externally-emitted
                                     (fn-sf-successes s))
        (member-equal pair externally-emitted))
   (fn-sf-record-has-pairp
    pair (fn-sf-records (fn-sf-run-trace s trace))))
  :hints (("Goal"
           :use ((:instance fn-sf-covered-emitted-member-is-ghost-member
                            (ghost-successes (fn-sf-successes s)))
                 (:instance fn-sf-prior-ghost-success-retained-by-run-trace)))))

; -----------------------------------------------------------------------------
; Export theory.  The per-transition footprint equalities are proof
; vocabulary (a book above re-enables them by this name); the trace
; recognizers, dispatcher and interpreter are withdrawn.  Enabled on include:
; fn-sf-prefixp and its lemmas, the typed-list facts about a kernel state,
; and the trace keystones.
(deftheory fn-store-files-traces-vocabulary
  '(fn-sf-records-of-start-frontier fn-sf-records-of-frontier-file-result
    fn-sf-records-of-frontier-replace-result fn-sf-records-of-frontier-dir-result
    fn-sf-records-of-refuse-reservation fn-sf-records-of-prepare-record
    fn-sf-records-of-record-file-result fn-sf-records-of-prepublish-abort
    fn-sf-records-of-abort-completion fn-sf-records-of-record-link-result
    fn-sf-records-of-core-completion fn-sf-records-of-emit-success
    fn-sf-records-of-lose-success fn-sf-records-of-recover
    fn-sf-records-of-recovery-barrier
    fn-sf-stable-records-prefix-of-record-dir-result
    fn-sf-successes-of-start-frontier fn-sf-successes-of-frontier-file-result
    fn-sf-successes-of-frontier-replace-result fn-sf-successes-of-frontier-dir-result
    fn-sf-successes-of-refuse-reservation fn-sf-successes-of-prepare-record
    fn-sf-successes-of-record-file-result fn-sf-successes-of-prepublish-abort
    fn-sf-successes-of-abort-completion fn-sf-successes-of-record-link-result
    fn-sf-successes-of-record-dir-result fn-sf-successes-of-core-completion
    fn-sf-successes-of-lose-success fn-sf-successes-of-crash
    fn-sf-successes-of-recover fn-sf-successes-of-recovery-barrier
    fn-sf-success-listp-is-true-list fn-sf-successes-prefix-of-emit-success
    fn-sf-covered-emitted-member-is-ghost-member))
(in-theory (disable fn-store-files-traces-vocabulary
                    fn-sf-eventp fn-sf-event-listp fn-sf-tracep
                    fn-sf-dispatch fn-sf-run-events fn-sf-run-trace
                    fn-sf-ghost-covers-emittedp))
