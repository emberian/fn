; Theorems about the journal interpreters the host calls.
;
; host/workflow-host.lisp:9 and :35 call fn-bp-replay-journal; :27 and :40
; call fn-bp-apply-journal-record.  Every sender theorem before this book was
; about fn-bp-step and fn-bp-trace.  This book lifts state, binding-state and
; node preservation to the called functions, proves that malformed or
; out-of-place records are refused wherever they occur, defines the event
; list a journal denotes (including the crash-implied :indeterminate
; completion that disk replay fabricates before every recovery outcome, and
; the trailing :restart), and proves that a successful replay is exactly the
; trace of the initial state over that denotation.  The live entry point
; fn-bp-apply-journal-record is exactly one fn-bp-step.
(in-package "ACL2")
(include-book "bp-workflow-records")
(include-book "bp-workflow-binding-invariants")
(local (in-theory (enable fn-node-statep)))

; Every workflow definition and every unfolding rule is closed by default;
; each proof opens exactly what it needs.
(local (in-theory (disable
 fn-bp-nth
 fn-bp-config-schema
 fn-bp-config-local-eid
 fn-bp-config-peer-eid
 fn-bp-config-policy-id
 fn-bp-config-authority
 fn-bp-config-lifetime
 fn-bp-config-incarnation
 fn-bp-config-auth-context
 fn-bp-make-config
 fn-bp-configp
 fn-bp-attempt-id
 fn-bp-attempt-generation
 fn-bp-attempt-status
 fn-bp-attempt-lifetime
 fn-bp-transport-statusp
 fn-bp-retryable-statusp
 fn-bp-make-attempt
 fn-bp-attemptp
 fn-bp-receipt-id
 fn-bp-receipt-work-id
 fn-bp-receipt-subject
 fn-bp-receipt-issuer
 fn-bp-receipt-peer-eid
 fn-bp-receipt-policy-id
 fn-bp-receipt-incarnation
 fn-bp-receipt-auth-context
 fn-bp-receipt-terms-id
 fn-bp-make-receipt
 fn-bp-receiptp
 fn-bp-receipt-listp
 fn-bp-work-id
 fn-bp-work-msgid
 fn-bp-work-subject
 fn-bp-work-archive-id
 fn-bp-work-obligation-id
 fn-bp-work-peer-eid
 fn-bp-work-policy-id
 fn-bp-work-incarnation
 fn-bp-work-auth-context
 fn-bp-work-terms-id
 fn-bp-work-next-generation
 fn-bp-work-attempt
 fn-bp-work-receipt
 fn-bp-make-work
 fn-bp-workp
 fn-bp-work-listp
 fn-bp-find-work
 fn-bp-find-work-by-msgid
 fn-bp-replace-work
 fn-bp-work-outstandingp
 fn-bp-work-retryablep
 fn-bp-authorized-receiptp
 fn-bp-work-with-attempt
 fn-bp-work-with-receipt
 fn-bp-work-with-status
 fn-bp-pending-kind
 fn-bp-pending-txid
 fn-bp-pending-generation
 fn-bp-pending-work
 fn-bp-pending-receipt
 fn-bp-make-pending
 fn-bp-pendingp
 fn-bp-make-tx-key
 fn-bp-tx-keyp
 fn-bp-tx-key-listp
 fn-bp-state-node
 fn-bp-state-config
 fn-bp-state-works
 fn-bp-state-receipts
 fn-bp-state-pending
 fn-bp-state-fenced
 fn-bp-state-used-txs
 fn-bp-make-state
 fn-bp-statep
 fn-bp-initial-state
 fn-bp-pending-matchesp
 fn-bp-work-boundp
 fn-bp-works-boundp
 fn-bp-prepare-enqueue
 fn-bp-prepare-attempt
 fn-bp-prepare-receipt
 fn-bp-apply-pending
 fn-bp-effect-for-pending
 fn-bp-make-result
 fn-bp-result-state
 fn-bp-result-effects
 fn-bp-complete
 fn-bp-recovery-pending
 fn-bp-recover
 fn-bp-transport-transition-okp
 fn-bp-live-statusp
 fn-bp-status-rank
 fn-bp-observe-transport
 fn-bp-request-retry
 fn-bp-restart-work
 fn-bp-restart-works
 fn-bp-restart
 fn-bp-event-kind
 fn-bp-enqueue-prepare-event
 fn-bp-attempt-prepare-event
 fn-bp-receipt-prepare-event
 fn-bp-storage-complete-event
 fn-bp-storage-recover-event
 fn-bp-transport-event
 fn-bp-no-contact-event
 fn-bp-retry-request-event
 fn-bp-restart-event
 fn-bp-eventp
 fn-bp-step
 fn-bp-trace
 fn-bp-binding-statep
 fn-bp-pending-boundp
 fn-bp-journal-textp
 fn-bp-u64p
 fn-bp-journal-nth
 fn-bp-config-recordp
 fn-bp-config-from-record
 fn-bp-journal-recordp
 fn-bp-record-event
 fn-bp-record-contextp
 fn-bp-apply-journal-record
 fn-bp-replay-records
 fn-bp-replay-journal
 fn-bp-step-effects-formula
 fn-bp-complete-effects-formula
 fn-bp-recover-effects-formula
 fn-bp-complete-result-state-formula
 fn-bp-recover-result-state-formula
 fn-bp-effect-for-pending-kind
 fn-bp-effect-for-pending-attempt-unfolds
 fn-bp-nth-0-of-cons
)))
(set-prover-step-limit 3000000)

; -----------------------------------------------------------------------------
; Selector facts

(defthm fn-bp-journal-nth-0-is-car
  (equal (fn-bp-journal-nth 0 x) (car x))
  :hints (("Goal" :in-theory (enable fn-bp-journal-nth))))

(defthm fn-bp-journal-nth-1-of-list3
  (equal (fn-bp-journal-nth 1 (list a b c)) b)
  :hints (("Goal" :in-theory (enable fn-bp-journal-nth))))

(defthm fn-bp-journal-nth-2-of-list3
  (equal (fn-bp-journal-nth 2 (list a b c)) c)
  :hints (("Goal" :in-theory (enable fn-bp-journal-nth))))

(defthm fn-bp-nth-of-cons
  (equal (fn-bp-nth n (cons a b))
         (if (and (integerp n) (< 0 n)) (fn-bp-nth (1- n) b) a))
  :hints (("Goal" :expand ((fn-bp-nth n (cons a b))))))

(defthm fn-bp-nth-of-atom
  (implies (not (consp x)) (equal (fn-bp-nth n x) nil))
  :hints (("Goal" :induct (fn-bp-nth n x) :in-theory (enable fn-bp-nth))))

(defthm fn-bp-statep-nil
  (not (fn-bp-statep nil))
  :hints (("Goal" :in-theory (enable fn-bp-statep))))

(defthm fn-bp-statep-of-initial-state-implies-inputs
  (implies (fn-bp-statep (fn-bp-initial-state node config))
           (and (fn-node-statep node) (fn-bp-configp config)))
  :hints (("Goal" :in-theory (enable fn-bp-initial-state))))

(defthm fn-bp-state-node-of-initial-state
  (implies (fn-bp-statep (fn-bp-initial-state node config))
           (equal (fn-bp-state-node (fn-bp-initial-state node config)) node))
  :hints (("Goal" :in-theory (enable fn-bp-initial-state))))

(defthm fn-bp-step-effects-true-listp
  (true-listp (fn-bp-result-effects (fn-bp-step s event)))
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-complete-effects-formula
                   fn-bp-recover-effects-formula))))

(defthm fn-bp-restart-step-emits-nothing
  (equal (fn-bp-result-effects (fn-bp-step s (fn-bp-restart-event))) nil)
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-restart-event
                   fn-bp-event-kind fn-bp-nth-of-cons))))

; The same fact on the evaluated constant, which is how the restart event
; appears once ACL2 has computed (fn-bp-restart-event).
(defthm fn-bp-restart-constant-step-emits-nothing
  (equal (fn-bp-result-effects (fn-bp-step s '(:restart))) nil)
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-event-kind fn-bp-nth))))

; -----------------------------------------------------------------------------
; The live entry point: one record is one fn-bp-step.

; What one record means to the live image (host/workflow-host.lisp:27, :40).
(defun fn-bp-record-live-event (r)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-bp-journal-nth 0 r) :outcome)
      (if (equal (fn-bp-journal-nth 3 r) :recovery)
          (fn-bp-storage-recover-event
           (fn-bp-journal-nth 1 r) (fn-bp-journal-nth 2 r)
           (fn-bp-journal-nth 4 r))
        (fn-bp-storage-complete-event
         (fn-bp-journal-nth 1 r) (fn-bp-journal-nth 2 r)
         (fn-bp-journal-nth 4 r)))
    (fn-bp-record-event r)))
(local (in-theory (disable fn-bp-record-live-event)))

(defthm fn-bp-apply-journal-record-is-step-when-ok
  (implies (car (fn-bp-apply-journal-record s r))
           (and (equal (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r))
                       (fn-bp-result-state
                        (fn-bp-step s (fn-bp-record-live-event r))))
                (equal (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r))
                       (fn-bp-result-effects
                        (fn-bp-step s (fn-bp-record-live-event r))))))
  :hints (("Goal" :in-theory
           (enable fn-bp-apply-journal-record fn-bp-record-live-event))))

(defthm fn-bp-apply-journal-record-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r))))
  :hints (("Goal" :in-theory (enable fn-bp-apply-journal-record))))

(defthm fn-bp-apply-journal-record-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r))))
  :hints (("Goal" :in-theory (enable fn-bp-apply-journal-record))))

(defthm fn-bp-apply-journal-record-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r)))
         (fn-bp-state-node s))
  :hints (("Goal" :in-theory (enable fn-bp-apply-journal-record))))

; A malformed record, or a configuration record after the first, is refused
; with okp = nil rather than applied as a no-op.
(defun fn-bp-replay-rejected-recordp (r)
  (declare (xargs :guard t :verify-guards nil))
  (or (not (fn-bp-journal-recordp r))
      (equal (fn-bp-journal-nth 0 r) :config)))
(local (in-theory (disable fn-bp-replay-rejected-recordp)))

(defthm fn-bp-apply-journal-record-malformed-unfolds
  (implies (fn-bp-replay-rejected-recordp r)
           (equal (fn-bp-apply-journal-record s r) (list nil s nil)))
  :hints (("Goal" :in-theory
           (enable fn-bp-apply-journal-record fn-bp-replay-rejected-recordp))))

; -----------------------------------------------------------------------------
; Disk replay over arbitrary record lists

(defthm fn-bp-replay-records-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records))))

(defthm fn-bp-replay-records-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records))))

(defthm fn-bp-replay-records-preserves-node
  (equal (fn-bp-state-node
          (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects)))
         (fn-bp-state-node s))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records))))

(defthm fn-bp-replay-records-rejects-any-malformed-record
  (implies (and (member-equal r records)
                (fn-bp-replay-rejected-recordp r))
           (not (car (fn-bp-replay-records s records effects))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records
                              fn-bp-replay-rejected-recordp))))

; Host line: host/workflow-host.lisp:9 installs the image only when (car answer).
(defthm fn-bp-replay-journal-success-is-binding-state
  (implies (car (fn-bp-replay-journal node records))
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-replay-journal node records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-of-initial-state-implies-inputs
                     (config (fn-bp-config-from-record (car records))))
          (:instance fn-bp-initial-state-is-binding-state
                     (config (fn-bp-config-from-record (car records))))
          (:instance fn-bp-replay-records-preserves-binding-state
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal)
                    (fn-bp-initial-state-is-binding-state
                     fn-bp-replay-records-preserves-binding-state
                     fn-bp-statep-of-initial-state-implies-inputs)))))

(defthm fn-bp-replay-journal-success-preserves-node
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-state-node
                   (fn-bp-journal-nth 1 (fn-bp-replay-journal node records)))
                  node))
  :hints
  (("Goal"
    :use ((:instance fn-bp-state-node-of-initial-state
                     (config (fn-bp-config-from-record (car records))))
          (:instance fn-bp-replay-records-preserves-node
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal)
                    (fn-bp-replay-records-preserves-node
                     fn-bp-state-node-of-initial-state)))))

(defthm fn-bp-replay-journal-rejects-any-malformed-record
  (implies (and (member-equal r (cdr records))
                (fn-bp-replay-rejected-recordp r))
           (not (car (fn-bp-replay-journal node records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-replay-records-rejects-any-malformed-record
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal)
                    (fn-bp-replay-records-rejects-any-malformed-record)))))

; -----------------------------------------------------------------------------
; What a journal denotes, and replay as a trace

; Disk replay resolves a recovery outcome by first fabricating the
; :indeterminate completion the crash implied (bp-workflow-records.lisp,
; fn-bp-replay-records), then applying the recorded recovery result.
(defun fn-bp-record-fence-events (r)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (equal (fn-bp-journal-nth 0 r) :outcome)
           (equal (fn-bp-journal-nth 3 r) :recovery))
      (list (fn-bp-storage-complete-event
             (fn-bp-journal-nth 1 r) (fn-bp-journal-nth 2 r) :indeterminate))
    nil))

(defun fn-bp-record-events (r)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bp-record-fence-events r) (list (fn-bp-record-live-event r))))

; The records after the configuration record, then the restart that
; fn-bp-replay-records appends.
(defun fn-bp-journal-events (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom records)
      (list (fn-bp-restart-event))
    (append (fn-bp-record-events (car records))
            (fn-bp-journal-events (cdr records)))))

(defun fn-bp-journal-denotation (records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bp-journal-events (cdr records)))

(defun fn-bp-trace-effects (s events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (append (fn-bp-result-effects (fn-bp-step s (car events)))
              (fn-bp-trace-effects
               (fn-bp-result-state (fn-bp-step s (car events)))
               (cdr events)))
    nil))

; Replay does not carry the :recover-required demand of a fabricated fence,
; because the very next event in the denotation is its recorded resolution.
(defun fn-bp-actionable-effects (effects)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp effects)
      (if (equal (fn-bp-nth 0 (car effects)) :recover-required)
          (fn-bp-actionable-effects (cdr effects))
        (cons (car effects) (fn-bp-actionable-effects (cdr effects))))
    nil))
(local (in-theory (disable fn-bp-record-fence-events fn-bp-record-events
                           fn-bp-journal-events fn-bp-journal-denotation
                           fn-bp-trace-effects fn-bp-actionable-effects)))

(local
 (defthm fn-bp-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-bp-true-listp-of-append
   (equal (true-listp (append x y)) (true-listp y))))

(defthm fn-bp-trace-of-append
  (equal (fn-bp-trace s (append a b))
         (fn-bp-trace (fn-bp-trace s a) b))
  :hints (("Goal" :induct (fn-bp-trace s a)
           :in-theory (enable fn-bp-trace))))

(defthm fn-bp-trace-effects-of-append
  (equal (fn-bp-trace-effects s (append a b))
         (append (fn-bp-trace-effects s a)
                 (fn-bp-trace-effects (fn-bp-trace s a) b)))
  :hints (("Goal" :induct (fn-bp-trace-effects s a)
           :in-theory (enable fn-bp-trace fn-bp-trace-effects))))

(defthm fn-bp-actionable-effects-of-append
  (equal (fn-bp-actionable-effects (append x y))
         (append (fn-bp-actionable-effects x) (fn-bp-actionable-effects y)))
  :hints (("Goal" :induct (fn-bp-actionable-effects x)
           :in-theory (enable fn-bp-actionable-effects))))

(defthm fn-bp-actionable-effects-of-true-list-effects
  (implies (true-listp x)
           (equal (fn-bp-actionable-effects (append x nil))
                  (fn-bp-actionable-effects x))))

; A record's own event never emits :recover-required: prepare, transport and
; retry events emit nothing; a recovery result emits an acknowledgement or
; nothing; an ordinary outcome is :durable or :aborted, never :indeterminate.
(defthm fn-bp-record-event-emits-nothing
  (equal (fn-bp-result-effects (fn-bp-step s (fn-bp-record-event r))) nil)
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-record-event
                   fn-bp-enqueue-prepare-event fn-bp-attempt-prepare-event
                   fn-bp-receipt-prepare-event fn-bp-transport-event
                   fn-bp-retry-request-event fn-bp-event-kind
                   fn-bp-nth-of-cons fn-bp-nth-of-atom))))

(defthm fn-bp-recover-event-effects-actionable
  (equal (fn-bp-actionable-effects
          (fn-bp-result-effects
           (fn-bp-step s (fn-bp-storage-recover-event a b c))))
         (fn-bp-result-effects
          (fn-bp-step s (fn-bp-storage-recover-event a b c))))
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-recover-effects-formula
                   fn-bp-effect-for-pending-kind fn-bp-actionable-effects
                   fn-bp-storage-recover-event fn-bp-event-kind
                   fn-bp-nth-of-cons))))

(defthm fn-bp-complete-event-effects-actionable
  (implies (not (equal c :indeterminate))
           (equal (fn-bp-actionable-effects
                   (fn-bp-result-effects
                    (fn-bp-step s (fn-bp-storage-complete-event a b c))))
                  (fn-bp-result-effects
                   (fn-bp-step s (fn-bp-storage-complete-event a b c)))))
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-complete-effects-formula
                   fn-bp-effect-for-pending-kind fn-bp-actionable-effects
                   fn-bp-storage-complete-event fn-bp-event-kind
                   fn-bp-nth-of-cons))))

(defthm fn-bp-fence-effects-not-actionable
  (equal (fn-bp-actionable-effects
          (fn-bp-result-effects
           (fn-bp-step s (fn-bp-storage-complete-event a b :indeterminate))))
         nil)
  :hints (("Goal" :in-theory
           (enable fn-bp-step-effects-formula fn-bp-complete-effects-formula
                   fn-bp-actionable-effects fn-bp-storage-complete-event
                   fn-bp-event-kind fn-bp-nth-of-cons))))

(defthm fn-bp-outcome-record-outcome-shape
  (implies (and (fn-bp-journal-recordp r) (equal (car r) :outcome))
           (and (not (equal (fn-bp-journal-nth 4 r) :indeterminate))
                (equal (equal (fn-bp-journal-nth 3 r) :ordinary)
                       (not (equal (fn-bp-journal-nth 3 r) :recovery)))))
  :hints (("Goal" :in-theory (enable fn-bp-journal-recordp))))

; Bridging rules: what the fence and the record contribute to a trace.
(defthm fn-bp-trace-of-fence-events
  (equal (fn-bp-trace s (fn-bp-record-fence-events r))
         (if (and (equal (car r) :outcome)
                  (equal (fn-bp-journal-nth 3 r) :recovery))
             (fn-bp-result-state
              (fn-bp-step s (fn-bp-storage-complete-event
                             (fn-bp-journal-nth 1 r) (fn-bp-journal-nth 2 r)
                             :indeterminate)))
           s))
  :hints (("Goal" :in-theory (enable fn-bp-record-fence-events fn-bp-trace))))

(defthm fn-bp-trace-of-record-events
  (equal (fn-bp-trace s (fn-bp-record-events r))
         (fn-bp-result-state
          (fn-bp-step (fn-bp-trace s (fn-bp-record-fence-events r))
                      (fn-bp-record-live-event r))))
  :hints (("Goal" :in-theory (e/d (fn-bp-record-events fn-bp-trace)
                                  (fn-bp-trace-of-fence-events)))))

(defthm fn-bp-actionable-trace-effects-of-fence-events
  (equal (fn-bp-actionable-effects
          (fn-bp-trace-effects s (fn-bp-record-fence-events r)))
         nil)
  :hints (("Goal" :in-theory (enable fn-bp-record-fence-events
                                      fn-bp-trace-effects
                                      fn-bp-actionable-effects))))

(defthm fn-bp-actionable-trace-effects-of-record-events
  (implies (fn-bp-journal-recordp r)
           (equal (fn-bp-actionable-effects
                   (fn-bp-trace-effects s (fn-bp-record-events r)))
                  (fn-bp-result-effects
                   (fn-bp-step (fn-bp-trace s (fn-bp-record-fence-events r))
                               (fn-bp-record-live-event r)))))
  :hints (("Goal"
           :in-theory (e/d (fn-bp-record-events fn-bp-record-live-event
                            fn-bp-trace-effects)
                           (fn-bp-trace-of-fence-events
                            fn-bp-trace-of-record-events)))))

; Keystone (D7).  Host line: host/workflow-host.lisp:9 (open) and :35
; (history preflight).  When replay succeeds, the recovered image is the trace
; of the initial state over the journal's denotation.
(defthm fn-bp-replay-records-is-trace-when-ok
  (implies (car (fn-bp-replay-records s records effects))
           (equal (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))
                  (fn-bp-trace s (fn-bp-journal-events records))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records fn-bp-journal-events
                              fn-bp-record-live-event fn-bp-trace))))

(defthm fn-bp-replay-records-effects-are-actionable-trace-effects-when-ok
  (implies (and (car (fn-bp-replay-records s records effects))
                (true-listp effects))
           (equal (fn-bp-journal-nth 2 (fn-bp-replay-records s records effects))
                  (append effects
                          (fn-bp-actionable-effects
                           (fn-bp-trace-effects
                            s (fn-bp-journal-events records))))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records fn-bp-journal-events
                              fn-bp-record-live-event fn-bp-trace
                              fn-bp-trace-effects fn-bp-actionable-effects))))

(defthm fn-bp-replay-journal-is-trace-when-ok
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-journal-nth 1 (fn-bp-replay-journal node records))
                  (fn-bp-trace
                   (fn-bp-initial-state
                    node (fn-bp-config-from-record (car records)))
                   (fn-bp-journal-denotation records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-replay-records-is-trace-when-ok
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal fn-bp-journal-denotation)
                    (fn-bp-replay-records-is-trace-when-ok)))))

(defthm fn-bp-replay-journal-effects-are-actionable-trace-effects-when-ok
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-journal-nth 2 (fn-bp-replay-journal node records))
                  (fn-bp-actionable-effects
                   (fn-bp-trace-effects
                    (fn-bp-initial-state
                     node (fn-bp-config-from-record (car records)))
                    (fn-bp-journal-denotation records)))))
  :hints
  (("Goal"
    :use ((:instance
           fn-bp-replay-records-effects-are-actionable-trace-effects-when-ok
           (s (fn-bp-initial-state
               node (fn-bp-config-from-record (car records))))
           (records (cdr records))
           (effects nil)))
    :in-theory
    (e/d (fn-bp-replay-journal fn-bp-journal-denotation)
         (fn-bp-replay-records-effects-are-actionable-trace-effects-when-ok)))))

; -----------------------------------------------------------------------------
; Durable intent before submission over the live entry point (D8).
; Host line: host/workflow-host.lisp:40 (fn-workflow-apply-record) stores these
; effects, and :60-68 (fn-workflow-take-submit) grants the BPA call only for a
; single :submit naming the exact work, attempt id and generation.

(defthm fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome
  (implies (and (member-equal
                 e (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r)))
                (equal (fn-bp-nth 0 e) :submit))
           (let ((pending (fn-bp-state-pending s)))
             (and (car (fn-bp-apply-journal-record s r))
                  (fn-bp-journal-recordp r)
                  (equal (car r) :outcome)
                  (equal (fn-bp-journal-nth 3 r) :ordinary)
                  (equal (fn-bp-journal-nth 4 r) :durable)
                  (fn-bp-statep s)
                  (not (fn-bp-state-fenced s))
                  (consp pending)
                  (equal (fn-bp-pending-kind pending) :attempt)
                  (equal (fn-bp-journal-nth 1 r) (fn-bp-pending-txid pending))
                  (equal (fn-bp-journal-nth 2 r)
                         (fn-bp-pending-generation pending))
                  (equal (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r))
                         (list e))
                  (equal e
                         (list :submit
                               (fn-bp-work-id (fn-bp-pending-work pending))
                               (fn-bp-attempt-id
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-attempt-generation
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-config-local-eid (fn-bp-state-config s))
                               (fn-bp-config-peer-eid (fn-bp-state-config s))
                               (fn-bp-attempt-lifetime
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending))))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           fn-bp-step-submit-requires-matching-durable-attempt-completion
           (event (fn-bp-record-live-event r))))
    :in-theory
    (enable fn-bp-apply-journal-record fn-bp-record-live-event
            fn-bp-storage-complete-event fn-bp-storage-recover-event
            fn-bp-event-kind fn-bp-nth-of-cons fn-bp-nth-of-atom
            fn-bp-outcome-record-outcome-shape))))


; -----------------------------------------------------------------------------
; A reopen keeps the works its history enqueued (w6/workflow-restart)
;
; The four-node lab read :absent for every work id after a journal reopen and
; concluded that fn-bp-replay-journal drops works.  It does not: the accessor
; the host called reported the attempt status, and an enqueued work has no
; attempt yet.  What the lab doubted is proved here rather than observed.
; fn-bp-replay-journal calls fn-bp-replay-records (bp-workflow-records.lisp:245),
; which host/workflow-host.lisp:9 and :35 reach through it; the keystone is
; stated over that interpreter.  The fn-bp-statep hypothesis these proofs began
; with proved unnecessary and was deleted: every transition that can drop a work
; id already demands a well-formed state through fn-bp-pending-matchesp, and the
; rest replace, cons or map over the list.
; ---- accessor-of-constructor, so every goal below stays in accessor terms --
(local (in-theory (enable fn-bp-nth-of-cons fn-bp-nth-of-atom)))
(local
(defthm fn-bp-wr-state-works-of-make-state
  (equal (fn-bp-state-works (fn-bp-make-state n c w r p f u)) w)
  :hints (("Goal" :in-theory (enable fn-bp-make-state fn-bp-state-works)))))
(local
(defthm fn-bp-wr-state-pending-of-make-state
  (equal (fn-bp-state-pending (fn-bp-make-state n c w r p f u)) p)
  :hints (("Goal" :in-theory (enable fn-bp-make-state fn-bp-state-pending)))))
(local
(defthm fn-bp-wr-pending-work-of-make-pending
  (equal (fn-bp-pending-work (fn-bp-make-pending k tx g w r)) w)
  :hints (("Goal" :in-theory (enable fn-bp-make-pending fn-bp-pending-work)))))
(local
(defthm fn-bp-wr-pending-kind-of-make-pending
  (equal (fn-bp-pending-kind (fn-bp-make-pending k tx g w r)) k)
  :hints (("Goal" :in-theory (enable fn-bp-make-pending fn-bp-pending-kind)))))
(local
(defthm fn-bp-wr-result-state-of-make-result
  (equal (fn-bp-result-state (fn-bp-make-result st e)) st)
  :hints (("Goal" :in-theory (enable fn-bp-make-result fn-bp-result-state)))))
(local (in-theory (disable fn-bp-make-state fn-bp-state-works
                           fn-bp-state-pending fn-bp-state-fenced
                           fn-bp-make-pending fn-bp-pending-work
                           fn-bp-pending-kind fn-bp-make-result
                           fn-bp-result-state fn-bp-nth)))

; ---- work lists: no operation the model performs drops a work id ----------
(local (in-theory (enable fn-bp-find-work fn-bp-replace-work
                          fn-bp-restart-work fn-bp-restart-works
                          fn-bp-work-with-attempt fn-bp-work-with-status
                          fn-bp-work-with-receipt fn-bp-make-work
                          fn-bp-work-id fn-bp-work-attempt fn-bp-work-receipt)))
(local
(defthm fn-bp-wr-find-work-of-replace-work
  (implies (and (consp w) (consp (fn-bp-find-work id xs)))
           (consp (fn-bp-find-work id (fn-bp-replace-work w xs))))))
(local
(defthm fn-bp-wr-find-work-of-cons-other
  (implies (and (consp w) (consp (fn-bp-find-work id xs)))
           (consp (fn-bp-find-work id (cons w xs))))))
(local
(defthm fn-bp-wr-find-work-of-cons-same-id
  (implies (consp w) (consp (fn-bp-find-work (fn-bp-work-id w) (cons w xs))))))
(local
(defthm fn-bp-wr-find-work-of-restart-works
  (implies (consp (fn-bp-find-work id xs))
           (consp (fn-bp-find-work id (fn-bp-restart-works xs))))))
(local
(defthm fn-bp-wr-work-with-status-is-consp (consp (fn-bp-work-with-status w st))))
(local
(defthm fn-bp-wr-work-with-receipt-is-consp (consp (fn-bp-work-with-receipt w r))))
(local
(defthm fn-bp-wr-workp-is-consp
  (implies (fn-bp-workp config w) (consp w))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bp-workp)))))
(local (in-theory (disable fn-bp-find-work fn-bp-replace-work
                           fn-bp-restart-work fn-bp-restart-works
                           fn-bp-work-with-attempt fn-bp-work-with-status
                           fn-bp-work-with-receipt fn-bp-make-work
                           fn-bp-work-id fn-bp-work-attempt
                           fn-bp-work-receipt)))

; ---- the pending work of a well-formed state is a work --------------------
(local
(defthm fn-bp-wr-statep-pending-work-is-consp
  (implies (and (fn-bp-statep s) (consp (fn-bp-state-pending s)))
           (consp (fn-bp-pending-work (fn-bp-state-pending s))))
  :hints (("Goal" :in-theory (enable fn-bp-statep fn-bp-pendingp)
           :use ((:instance fn-bp-wr-workp-is-consp
                            (config (fn-bp-state-config s))
                            (w (fn-bp-pending-work (fn-bp-state-pending s)))))))))
(local
(defthm fn-bp-wr-recovery-pending-work-is-consp
  (implies (consp (fn-bp-pending-work p))
           (consp (fn-bp-pending-work (fn-bp-recovery-pending p))))
  :hints (("Goal" :in-theory (enable fn-bp-recovery-pending)))))
(local
(defthm fn-bp-wr-pending-matchesp-has-pending
  (implies (fn-bp-pending-matchesp s txid gen) (consp (fn-bp-state-pending s)))
  :hints (("Goal" :in-theory (enable fn-bp-pending-matchesp)))))
(local
(defthm fn-bp-wr-pending-matchesp-is-statep
  (implies (fn-bp-pending-matchesp s txid gen) (fn-bp-statep s))
  :hints (("Goal" :in-theory (enable fn-bp-pending-matchesp)))))
(local (in-theory (disable fn-bp-statep fn-bp-workp fn-bp-work-listp
                           fn-bp-configp fn-bp-pendingp fn-bp-receiptp
                           fn-bp-receipt-listp fn-bp-attemptp
                           fn-bp-tx-key-listp fn-node-statep
                           fn-bp-pending-matchesp fn-bp-recovery-pending)))

(local
(defthm fn-bp-wr-find-work-of-apply-pending
  (implies (and (consp (fn-bp-pending-work pending))
                (consp (fn-bp-find-work id (fn-bp-state-works s))))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works (fn-bp-apply-pending s pending)))))
  :hints (("Goal" :in-theory (enable fn-bp-apply-pending)))))
(local
(defthm fn-bp-wr-state-works-of-apply-pending-enqueue
  (implies (equal (fn-bp-pending-kind pending) :enqueue)
           (equal (fn-bp-state-works (fn-bp-apply-pending s pending))
                  (cons (fn-bp-pending-work pending) (fn-bp-state-works s))))
  :hints (("Goal" :in-theory (enable fn-bp-apply-pending)))))
(local (in-theory (disable fn-bp-apply-pending)))

; ---- one lemma per transition ---------------------------------------------
(local
(defthm fn-bp-wr-state-works-of-prepare-enqueue
  (equal (fn-bp-state-works (fn-bp-prepare-enqueue s a b c d e f g))
         (fn-bp-state-works s))
  :hints (("Goal" :in-theory (enable fn-bp-prepare-enqueue)))))
(local
(defthm fn-bp-wr-state-works-of-prepare-attempt
  (equal (fn-bp-state-works (fn-bp-prepare-attempt s a b c d))
         (fn-bp-state-works s))
  :hints (("Goal" :in-theory (enable fn-bp-prepare-attempt)))))
(local
(defthm fn-bp-wr-state-works-of-prepare-receipt
  (equal (fn-bp-state-works (fn-bp-prepare-receipt s a b c d))
         (fn-bp-state-works s))
  :hints (("Goal" :in-theory (enable fn-bp-prepare-receipt)))))
(local
(defthm fn-bp-wr-find-work-of-complete
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-complete s a b c))))))
  :hints (("Goal" :in-theory (enable fn-bp-complete)))))
(local
(defthm fn-bp-wr-find-work-of-recover
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-recover s a b c))))))
  :hints (("Goal" :in-theory (enable fn-bp-recover)))))
(local
(defthm fn-bp-wr-find-work-of-observe-transport
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works (fn-bp-observe-transport s a b c d)))))
  :hints (("Goal" :in-theory (enable fn-bp-observe-transport)))))
(local
(defthm fn-bp-wr-find-work-of-request-retry
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works (fn-bp-request-retry s a b c d)))))
  :hints (("Goal" :in-theory (enable fn-bp-request-retry)))))
(local
(defthm fn-bp-wr-find-work-of-restart
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work id (fn-bp-state-works (fn-bp-restart s)))))
  :hints (("Goal" :in-theory (enable fn-bp-restart)))))
(local (in-theory (disable fn-bp-prepare-enqueue fn-bp-prepare-attempt
                           fn-bp-prepare-receipt fn-bp-complete fn-bp-recover
                           fn-bp-observe-transport fn-bp-request-retry
                           fn-bp-restart)))

(defthm fn-bp-step-preserves-works
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-result-state (fn-bp-step s event))))))
  :hints (("Goal" :in-theory (enable fn-bp-step fn-bp-event-kind))))

(defthm fn-bp-durable-enqueue-holds-the-work
  (implies (and (fn-bp-pending-matchesp s txid generation)
                (not (fn-bp-state-fenced s))
                (equal (fn-bp-pending-kind (fn-bp-state-pending s)) :enqueue))
           (consp (fn-bp-find-work
                   (fn-bp-work-id (fn-bp-pending-work (fn-bp-state-pending s)))
                   (fn-bp-state-works
                    (fn-bp-result-state
                     (fn-bp-complete s txid generation :durable))))))
  :hints (("Goal" :in-theory (enable fn-bp-complete))))

(defthm fn-bp-replay-preserves-works
  (implies (consp (fn-bp-find-work id (fn-bp-state-works s)))
           (consp (fn-bp-find-work
                   id (fn-bp-state-works
                       (fn-bp-journal-nth
                        1 (fn-bp-replay-records s records effects))))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory
           (e/d (fn-bp-replay-records fn-bp-step-preserves-state
                 fn-bp-journal-nth-1-of-list3)
                (fn-bp-record-event fn-bp-record-contextp
                 fn-bp-journal-recordp fn-bp-storage-complete-event
                 fn-bp-storage-recover-event fn-bp-restart-event
                 fn-bp-journal-nth fn-bp-result-effects fn-ag-append
                 fn-bp-step)))))
