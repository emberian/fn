; fn: inductive mixed traces of the actual live node/file composition.
(in-package "ACL2")
(include-book "store-node-invariants")
(include-book "topic-history-identity-disjoint")
(include-book "store-files-traces")
(include-book "records-seam")
(local (include-book "arithmetic/top" :dir :system))
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; The core definitions these correspondence proofs open (the core exports
; keystones only, docs/proof-style.md s2); local, named once.
(local (deftheory fn-snx-core-definitions
         (union-theories (union-theories '(fn-articlep fn-pendingp fn-statep fn-initial-state fn-install-pending
            fn-clear-pending fn-accept-prepare fn-accept-complete fn-accept-recover
            fn-pending-matchesp
            fn-retain-obligationp fn-retain-releasep fn-retain-statep
            fn-retain-initial-state fn-retain-admissiblep fn-retain-admit
            fn-retain-release
            fn-node-stagep fn-node-bindingp fn-node-statep fn-node-initial-state
            fn-node-pending-matchesp fn-node-prepare fn-node-complete fn-node-recover
            fn-replay-okp fn-replay-advance-okp fn-replay-advance-txid) (theory 'fn-acceptance-invariants-vocabulary)) (theory 'fn-node-invariants-vocabulary))))
; `fn-sn-identity-context' is withdrawn at store-node's export since
; 2026-09-23; the io-step proofs here carry it across `fn-sn-make-v2' by
; reading its two fields, so it stays open in this book as it was before.
(local (in-theory (e/d (fn-sn-statep fn-sn-initial fn-sn-pending-record
                        fn-sn-record-bindsp fn-sn-prepare
                        fn-sn-identity-context
                        fn-sn-completion-record fn-sn-completion-core-enabledp
                        fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                        fn-sn-recover fn-sn-committed-recordp
                        fn-sf-phase-shapep fn-sf-initial-state
                        fn-sf-start-frontier fn-sf-frontier-file-result
                        fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                        fn-sf-history-recoverablep fn-sf-refuse-reservation
                        fn-sf-prepare-record fn-sf-record-file-result
                        fn-sf-prepublish-abort fn-sf-abort-completion
                        fn-sf-record-link-result fn-sf-record-dir-result
                        fn-sf-core-completion fn-sf-emit-success
                        fn-sf-lose-success fn-sf-crash-imagep fn-sf-crash
                        fn-sf-recover fn-sf-recovery-barrier
                        fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary
                        fn-store-files-traces-vocabulary
                        fn-store-node-invariants-vocabulary)
                       (fn-node-statep fn-sf-statep fn-record-p
                        fn-node-prepare fn-node-complete fn-node-recover
                        fn-replay-advance-txid fn-replay fn-replay-loop
                        fn-sf-replay-node fn-sn-prepare-node
                        fn-sn-completion-enabledp
                        fn-retain-statep fn-node-initial-state
                         fn-state-next-txid
                          ))))

; Measured 2026-09-24 on persvati (REPL, whole book 18.3 s to 11.9 s):
; `fn-cp-idp-true-listp' is an unconditional-looking rewrite rule on
; `true-listp' that backchains into the consumer id's octet recognizer, and
; `fn-cp-id-length-bound' does the same on every `len' (40 759 tries of
; `fn-cp-idp' across this book, none needed); `fn-replay-identity-step' and
; the topic anchor recognizer split the preparation goals on arms they only
; carry.  A proof that reads one of them enables it in its hint.
(local (in-theory (disable fn-cp-idp-true-listp fn-cp-id-length-bound
                           fn-replay-identity-step fn-th-topic-v1-anchorp
                           fn-snt-history-recoverable-under-record-bound
                           fn-sn-new-success-requires-actual-matching-durable-node-completion)))

(defthm fn-snt-recoverable-prefix-facts
  (implies (fn-sf-history-recoverablep groups capacity history frontier)
           (and (fn-replay-okp (fn-replay groups capacity history))
                (fn-replay-advance-okp
                 (fn-replay-result-node (fn-replay groups capacity history)) frontier)))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node))))

(defthm fn-snt-prepare-replayed-node
  (implies (fn-sf-history-recoverablep
            groups capacity history (fn-record-txid record))
           (equal
            (fn-sn-prepare-node
             (fn-sf-replay-node groups capacity history (fn-record-txid record)) record)
            (fn-sn-prepare-node
             (fn-replay-result-node (fn-replay groups capacity history)) record)))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node fn-sn-prepare-node))))

; A recoverable history's frontier is the replayed node's next txid, hence a
; natural (fn-statep types it); the core no longer opens to say so.
(local
 (defthm fn-snt-recoverable-frontier-is-natural
   (implies (fn-sf-history-recoverablep groups capacity history frontier)
            (natp frontier))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-sf-history-recoverablep fn-node-statep
                                    fn-statep fn-snx-core-definitions)
                                   (fn-sf-replay-node))))))

(defthm fn-snt-canonical-preparation-advance-ok
  (implies (fn-sf-history-recoverablep groups capacity history frontier)
           (fn-replay-advance-okp
            (fn-sf-replay-node groups capacity history frontier) frontier))
  :hints (("Goal" :use ((:instance fn-snt-replayed-node-idle-and-frontier (records history))
                                fn-snt-recoverable-prefix-facts)
           :in-theory (e/d (fn-record-uint32p fn-replay-advance-okp)
                           (fn-sf-history-recoverablep)))))

(defthm fn-snt-replay-node-of-success
  (implies (and (equal (fn-replay groups capacity history) (fn-replay-ok node sequence))
                (fn-node-statep node) (natp sequence)
                (fn-replay-advance-okp node frontier)
                (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))
           (and (equal (fn-sf-replay-node groups capacity history frontier) node)
                (fn-sf-history-recoverablep groups capacity history frontier)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sf-replay-node))))

(defthm fn-snt-canonical-preparation-outcomes
  (let* ((txid (fn-record-txid record))
         (base (fn-sf-replay-node groups capacity history txid))
         (pending (fn-sn-prepare-node base record))
         (done (fn-node-complete pending txid (fn-record-generation record) :durable)))
    (implies
     (and (true-listp history)
          (fn-sf-history-recoverablep groups capacity history txid)
          (fn-record-p record)
          (equal (fn-record-sequence record) (len history))
          (fn-node-pending-matchesp pending txid (fn-record-generation record)))
     (and (equal (fn-node-complete pending txid (fn-record-generation record) :aborted)
                 (fn-sf-replay-node groups capacity history (1+ txid)))
          (equal done (fn-sf-replay-node groups capacity
                        (append history (list record)) (1+ txid)))
          (fn-sf-history-recoverablep groups capacity
            (append history (list record)) (1+ txid)))))
  :hints (("Goal"
    :use (fn-sn-extended-history-equals-live-completion
          fn-snt-prepare-replayed-node
          (:instance fn-snt-successful-replay-history-length (records history))
          (:instance fn-snt-replayed-node-idle-and-frontier
            (records history) (frontier (fn-record-txid record)))
          (:instance fn-snt-recoverable-prefix-facts
            (frontier (fn-record-txid record)))
          (:instance fn-snt-prepared-durable-is-idle-at-successor
            (node (fn-replay-result-node (fn-replay groups capacity history))))
          (:instance fn-snt-prepared-abort-is-frontier-advance
            (node (fn-sf-replay-node groups capacity history (fn-record-txid record))))
          (:instance fn-snt-replay-node-of-success
            (history (append history (list record)))
            (sequence (1+ (len history)))
            (frontier (1+ (fn-record-txid record)))
            (node (fn-node-complete
                   (fn-sn-prepare-node
                    (fn-replay-result-node (fn-replay groups capacity history)) record)
                   (fn-record-txid record) (fn-record-generation record) :durable))))
    :in-theory (disable fn-sf-history-recoverablep fn-replay-okp
                        fn-node-pending-matchesp))))

(defun fn-snt-idle-phasep (phase)
  (declare (xargs :guard t))
  (member-equal phase '(:ready :frontier-staged :frontier-data-durable
                       :frontier-attempted :fenced-frontier
                       :recovering :fenced-recovery)))

; Proof-side consumer history relation.  It is never called by a served
; command.  Live states interpret exactly the completed Store prefix; the
; one appended but unfinished completion and the staged candidate retain a
; separately checked next step.  A crash erases the process projection, and
; recovery must reconstruct it before entering :recovering.
(defun fn-snt-consumerp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files))
         (records (fn-sf-records files))
         (next (fn-sn-identity-next s))
         (consumer (fn-sn-consumer s)))
    (cond
     ((equal phase :replaying) (null consumer))
     ((equal phase :fault) t)
     ((equal phase :completing)
      (and (equal (len records) (1+ next))
           (equal (fn-cpe-projection-replay nil (take next records) 0)
                  (list :ok consumer))
           (equal (nth next records) (fn-sn-completion-record s))
           (eq (car (fn-cpe-projection-step
                     consumer (fn-sn-completion-record s) next)) :ok)))
     (t
      (and (equal (len records) next)
           (equal (fn-cpe-projection-replay nil records 0)
                  (list :ok consumer))
           (or (not (fn-sf-record-phasep phase))
               (eq (car (fn-cpe-projection-step
                         consumer (fn-sf-record-candidate files) next))
                   :ok)))))))

(verify-guards fn-snt-consumerp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep)))))

; This is a proof relation, never an executable transition guard.  Before
; publication the actual proposal's two resolutions match current/extended
; replay.  After publication only its durable resolution matches history.
;
; It is nevertheless guard verified (below, once fn-snt-typed-store-components
; is available), because fn-own-relation (books/owner-invariants.lisp:155)
; conjoins fn-snt-relation and fn-ocfg-statep (books/owner-config.lisp:191)
; declares :guard t over fn-own-relation, so the whole chain owes its guards.
; The two hypotheses are the ones the callees ask for and nothing more:
; fn-node-complete and fn-sn-record-bindsp are guarded by (fn-node-statep
; node), and the two `append's owe (true-listp (fn-sf-records files)), which
; is fn-sf-state-records-are-true-list of (fn-sf-statep files).
(defun fn-snt-pending-linkp (groups capacity files node)
  (declare (xargs :guard (and (fn-node-statep node) (fn-sf-statep files))
                  :verify-guards nil))
  (let ((record (fn-sf-record-candidate files)))
    (and (fn-sn-record-bindsp node record)
         (equal (fn-node-complete node (fn-record-txid record)
                  (fn-record-generation record) :aborted)
                (fn-sf-replay-node groups capacity (fn-sf-records files)
                                   (fn-sf-frontier files)))
         (equal (fn-node-complete node (fn-record-txid record)
                  (fn-record-generation record) :durable)
                (fn-sf-replay-node groups capacity
                  (append (fn-sf-records files) (list record)) (fn-sf-frontier files)))
         (fn-sf-history-recoverablep groups capacity
           (append (fn-sf-records files) (list record)) (fn-sf-frontier files)))))

; The other kind of staged candidate.  Since `6ab2c783' and `4bb7bb3d' the
; host also publishes retention and identity events through this reservation
; and file machine -- `fn-sn-prepare-retention' and `fn-sn-prepare-identity'
; (books/store-node), called from `host/owner-host.lisp' lines 375 and 387 --
; and those two DEFER the whole node effect to `fn-sn-finish': they stage the
; event and leave the live node exactly where the reservation left it.  A
; record phase whose candidate is not an article record therefore does not
; satisfy `fn-snt-pending-linkp' above, which asks for a staged proposal on
; the node, and before this arm existed `fn-snt-relation' was simply false of
; every state those two transitions produce.
;
; This says what they do establish, in the same shape: the live node is the
; replay of the durable history at the reservation's transaction id (one
; below the frontier, exactly as the `:reserved' arm has it); the event
; applies to that node, and for an identity event its identity step is `:ok',
; which are the two conditions `fn-sn-completion-enabledp' will ask for at
; the directory barrier; the applied node is the replay of the extended
; history at the frontier, which is what `fn-sn-finish' will publish; and the
; extended history is recoverable there, which `fn-sf-prepare-record' checks
; before it stages anything.
(defun fn-snt-deferred-linkp (s)
  (declare (xargs :guard (and (fn-sn-statep s)
                              (fn-sf-record-phasep (fn-sf-phase (fn-sn-files s))))
                  :verify-guards nil))
  (let* ((groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
         (files (fn-sn-files s)) (node (fn-sn-node s))
         (history (fn-sf-records files)) (frontier (fn-sf-frontier files))
         (record (fn-sf-record-candidate files)))
    (and (fn-store-event-p record)
         (posp frontier)
         (fn-sf-history-recoverablep groups capacity history (1- frontier))
         (equal node (fn-sf-replay-node groups capacity history (1- frontier)))
         (consp (fn-replay-apply-record node record))
         (cond ((fn-store-retention-event-p record) t)
               ((fn-cpe-eventp record)
                (eq (car (fn-cpe-projection-step
                          (fn-sn-consumer s) record
                          (fn-sn-identity-next s))) :ok))
               ((fn-th-topic-eventp record)
                (eq (fn-th-at 0
                             (fn-th-prefix-step (fn-sn-topic s) record)) :ok))
               (t (equal (fn-stxk-context-kind
                          (fn-replay-identity-step
                           (fn-sn-identity-context s) record)) :ok)))
         (equal (fn-replay-apply-record node record)
                (fn-sf-replay-node groups capacity
                                   (append history (list record)) frontier))
         (fn-sf-history-recoverablep groups capacity
                                     (append history (list record)) frontier))))

; The completing arm's link, in a function of its own so that every proof
; which only carries the relation across a step that touches neither the
; completion record nor the node can hold it CLOSED.  It has to be closed:
; the deferred branch names `fn-replay-apply-record', and with that term
; sitting in the relation's own body every goal that opens the relation
; unfolds the record and statement codec under it -- measured on
; `fn-snt-start-frontier-preserves-relation', which split into 3590 subgoals
; and then 3587 (hbox certify-20260922T140622Z-2999650).
;
; Two kinds since `6ab2c783' and `4bb7bb3d', for the reason the record-phase
; arm gives: `fn-sf-record-dir-result' is the only step into `:completing'
; and it carries the candidate over into the history as the completion
; record, so the arm the state was on is the arm `fn-sn-finish' will take.
; On the article arm the node `fn-sn-finish' publishes is the durable
; completion; on the other it is `fn-replay-apply-record' of the event, which
; is also the replay step the history now contains.
(defun fn-snt-completion-linkp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let* ((groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
         (files (fn-sn-files s)) (node (fn-sn-node s))
         (history (fn-sf-records files)) (frontier (fn-sf-frontier files))
         (record (fn-sn-completion-record s)))
    (if (fn-record-p record)
        (equal (fn-node-complete node (fn-record-txid record)
                                 (fn-record-generation record) :durable)
               (fn-sf-replay-node groups capacity history frontier))
      (equal (fn-replay-apply-record node record)
             (fn-sf-replay-node groups capacity history frontier)))))

(defun fn-snt-relation (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
         (files (fn-sn-files s)) (node (fn-sn-node s))
         (history (fn-sf-records files)) (frontier (fn-sf-frontier files))
         (phase (fn-sf-phase files)))
    (and (fn-sn-statep s)
         (fn-sf-history-recoverablep groups capacity history frontier)
         (cond
          ((fn-snt-idle-phasep phase)
           (equal node (fn-sf-replay-node groups capacity history frontier)))
          ((equal phase :reserved)
           (and (posp frontier)
                (fn-sf-history-recoverablep groups capacity history (1- frontier))
                (equal node (fn-sf-replay-node groups capacity history (1- frontier)))))
          ; Two kinds of staged candidate since `6ab2c783' and `4bb7bb3d';
          ; the article one is the proposal standing on the live node, the
          ; other is a publication whose node effect is deferred to
          ; `fn-sn-finish'.  `fn-sn-record-bindsp' inside the first arm is
          ; false of every event that is not an article record, so the test
          ; and the arm agree.
          ((fn-sf-record-phasep phase)
           (if (fn-record-p (fn-sf-record-candidate files))
               (fn-snt-pending-linkp groups capacity files node)
             (fn-snt-deferred-linkp s)))
          ; Before `6ab2c783' and `4bb7bb3d' the completing arm had one
          ; kind and nothing had to say which; this book has not certified
          ; since 2026-09-21 01:20.  See `fn-snt-completion-linkp' above.
          ((equal phase :completing)
           (and (fn-sn-completion-core-enabledp s)
                (fn-snt-completion-linkp s)))
          ((equal phase :replaying)
           (equal node (fn-node-initial-state groups capacity)))
          ; `40bb3f74' gave `fn-sn-recover' a fault arm: the article replay
          ; succeeded and the identity replay did not, and rather than leave
          ; `:recovering' visible on half a recovery it publishes `:fault'
          ; over the replayed history and frontier with the live node
          ; untouched -- which, on the `:replaying' arm above, is the initial
          ; node.  Without this arm the relation was simply false of every
          ; state that transition produces and `fn-snt-recover-preserves-
          ; relation' below could not hold.
          ((equal phase :fault)
           (equal node (fn-node-initial-state groups capacity)))
          (t nil)))))

(defthm fn-snt-relation-implies-structural-state
  (implies (fn-snt-relation s) (fn-sn-statep s))
  :hints (("Goal" :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                                      fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))
(local (in-theory (disable fn-snt-relation-implies-structural-state)))

(defthm fn-snt-initial-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node fn-replay fn-replay-loop
                         fn-node-initial-state  fn-node-acceptance
                           fn-state-fenced
                         fn-replay-advance-txid fn-node-statep fn-statep fn-retain-statep fn-snx-core-definitions))))

; Typed as forward-chaining and type-prescription: the counters must be
; known naturals for the frontier arithmetic below to normalise.
(defthm fn-snt-record-counters-natural
  (implies (fn-record-p record)
           (and (natp (fn-record-txid record))
                (natp (fn-record-generation record))
                (natp (fn-record-sequence record))))
  :rule-classes ((:forward-chaining)
                 (:type-prescription :corollary
                  (implies (fn-record-p record) (natp (fn-record-txid record))))
                 (:type-prescription :corollary
                  (implies (fn-record-p record) (natp (fn-record-generation record))))
                 (:type-prescription :corollary
                  (implies (fn-record-p record) (natp (fn-record-sequence record)))))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-uint32p))))

; `fn-sn-make' is the six-field constructor, which fills the four fields
; `6e992351' added to `fn-sn-state' with 0, NIL, NIL and 0.  Rebuilding a
; state through it therefore loses its keyring generation, its acceptance
; verdicts, its keyring snapshots and its identity sequence, and the equation
; was false for any state that carries them; books/store-node-traces has not
; certified since 2026-09-21 01:20, so it was never proved in the widened
; shape.  The reconstruction is `fn-sn-make-v6' over all fourteen fields.
(local
 (defthm fn-snt-store-event-nth-is-nth
   (implies (natp n)
            (equal (fn-store-event-nth n x) (nth n x)))
   :hints (("Goal" :induct (fn-store-event-nth n x)
            :in-theory (enable fn-store-event-nth nth)))))
(local
 (defthm fn-snt-zero-length-true-list-is-nil
   (implies (and (true-listp x) (equal (len x) 0))
            (equal x nil))
   :rule-classes nil))
(defthm fn-snt-state-reconstruction
  (implies (fn-sn-statep s)
           (equal (fn-sn-make-v6 (fn-sn-groups s) (fn-sn-capacity s)
                                 (fn-sn-files s) (fn-sn-node s)
                                 (fn-sn-keyring s) (fn-sn-index s)
                                 (fn-sn-keyring-generation s)
                                 (fn-sn-verdicts s)
                                 (fn-sn-keyring-snapshots s)
                                 (fn-sn-identity-next s)
                                 (fn-sn-config-history s)
                                 (fn-sn-consumer s) (fn-sn-topic s)
                                 (fn-sn-event-index s))
                  s))
  :hints (("Goal" :in-theory (enable len nth fn-sn-statep fn-sn-shapep
                                     fn-sn-make-v6 fn-sn-groups
                                     fn-sn-capacity fn-sn-files fn-sn-node
                                     fn-sn-keyring fn-sn-index
                                     fn-sn-keyring-generation fn-sn-verdicts
                                     fn-sn-keyring-snapshots
                                     fn-sn-identity-next fn-sn-config-history
                                     fn-sn-consumer fn-sn-topic
                                     fn-sn-event-index)
           :use ((:instance fn-snt-zero-length-true-list-is-nil
                   (x (cddr (cddddr (cddddr (cddddr s)))))))
           :expand ((len s) (len (cdr s)) (len (cddr s))
                    (len (cdddr s)) (len (cddddr s))
                    (len (cdr (cddddr s))) (len (cddr (cddddr s)))
                    (len (cdddr (cddddr s))) (len (cddddr (cddddr s)))
                    (len (cdr (cddddr (cddddr s))))
                    (len (cddr (cddddr (cddddr s))))
                    (len (cdddr (cddddr (cddddr s))))
                    (len (cddddr (cddddr (cddddr s))))
                    (len (cdr (cddddr (cddddr (cddddr s)))))
                    (len (cddr (cddddr (cddddr (cddddr s))))))
           :do-not-induct t)))

; The reconstruction theorem supplies the Store shape to later trace proofs.
; Keeping the fourteen-field constructor closed prevents every preparation
; and completion goal from expanding its unchanged projection slots.
(local (in-theory (disable fn-sn-make-v6)))

(defthm fn-snt-typed-store-components
  (implies (fn-sn-statep s)
           (and (fn-sf-statep (fn-sn-files s))
                (fn-node-statep (fn-sn-node s))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-node-statep fn-sf-statep))))

; The guards of the relation and its two links.  All are deferred to
; here because fn-snt-typed-store-components is what carries (fn-sn-statep s)
; --- the relation's own first conjunct, so the hypothesis is present in every
; guard obligation the `and' generates --- down to the two typed components
; the callees are guarded by.  Nothing is revalidated per operation: neither
; function is a transition guard and neither is on a served path (no caller
; outside proof vocabulary; grep fn-snt-relation over host/).
(verify-guards fn-snt-pending-linkp
  :hints (("Goal" :in-theory (disable fn-node-statep fn-sf-statep fn-sn-record-bindsp
                                      fn-node-complete fn-sf-replay-node
                                      fn-sf-history-recoverablep
                                      fn-sf-record-candidate))))

(defthm fn-snt-typed-frontier-phase
  (implies (and (fn-sf-statep files)
                (fn-sf-frontier-phasep (fn-sf-phase files)))
           (equal (fn-sf-frontier-candidate files) (1+ (fn-sf-frontier files))))
  :hints (("Goal" :in-theory (e/d (fn-sf-statep fn-sf-phase-shapep)
                                  (fn-sf-candidatep fn-sf-record-listp
                                   fn-sf-success-listp)))))
(defthm fn-snt-typed-frontier-natural
  (implies (fn-sf-statep files) (natp (fn-sf-frontier files)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sf-statep)
                                  (fn-sf-candidatep fn-sf-record-listp
                                   fn-sf-success-listp fn-sf-phase-shapep)))))

(defthm fn-snt-typed-record-phase
  (implies (and (fn-sf-statep files) (fn-sf-record-phasep (fn-sf-phase files)))
           (fn-sf-candidatep (fn-sf-record-candidate files)
                             (fn-sf-records files) (fn-sf-frontier files)))
  :hints (("Goal" :in-theory (e/d (fn-sf-statep fn-sf-phase-shapep)
                                  (fn-sf-candidatep fn-sf-record-listp
                                   fn-sf-success-listp)))))

; A record the completion pair finds in a durable history is one of that
; history's entries, so it is a store event and hence a proper list; and so
; is the NIL a miss returns.  The deferred arm of the relation's `:completing'
; case hands that record to `fn-replay-apply-record', which is guarded by a
; proper list, and nothing else in this book had needed to say so.
(local
 (defthm fn-snt-found-record-is-a-true-list
   (implies (fn-sf-record-listp records sequence lower frontier)
            (true-listp (fn-sn-find-record pair records)))
   :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
            :in-theory (e/d (fn-sn-find-record fn-sf-record-listp)
                            (fn-store-event-p fn-sf-record-pair
                             fn-record-shape-vocabulary
                             fn-record-record-vocabulary))))))

(local
 (defthm fn-snt-completion-record-is-a-true-list
   (implies (fn-sn-statep s)
            (true-listp (fn-sn-completion-record s)))
   :hints (("Goal"
            :use ((:instance fn-snt-found-record-is-a-true-list
                             (pair (fn-sf-completion (fn-sn-files s)))
                             (records (fn-sf-records (fn-sn-files s)))
                             (sequence 0) (lower 0)
                             (frontier (fn-sf-frontier (fn-sn-files s)))))
            :in-theory (e/d (fn-sn-statep fn-sf-statep fn-sn-completion-record)
                            (fn-sf-record-listp fn-sf-success-listp
                             fn-sf-phase-shapep fn-sn-find-record
                             fn-snt-found-record-is-a-true-list
                             fn-record-shape-vocabulary
                             fn-record-record-vocabulary))))))

; The deferred link and the relation are verified here rather than beside
; the pending link because `fn-replay-apply-record' is guarded by a node and
; a proper list, and what says the staged candidate is a proper list is
; `fn-snt-typed-record-phase' just above -- a record phase's candidate is a
; `fn-sf-candidatep', hence a `fn-store-event-p', hence a true list
; (`fn-replay-record-is-a-true-list', books/replay).  That is why the link
; carries the record-phase conjunct in its own guard: it is called in exactly
; that arm of the relation and nowhere else.
(verify-guards fn-snt-deferred-linkp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-node-statep fn-sf-statep
                                   fn-sf-replay-node
                                   fn-sf-history-recoverablep
                                   fn-replay-apply-record
                                   fn-replay-identity-step
                                   fn-sn-identity-context
                                   fn-sf-candidatep
                                   fn-sf-record-candidate)))))

; The completing link's own guards: `fn-replay-apply-record' is guarded by a
; node and a proper list, and `fn-snt-completion-record-is-a-true-list' above
; is what says the record a completion pair finds in a durable history is a
; proper list.
(verify-guards fn-snt-completion-linkp
  :hints (("Goal" :use (fn-snt-completion-record-is-a-true-list)
           :in-theory (disable fn-sn-statep fn-sf-statep fn-node-statep
                               fn-sf-history-recoverablep fn-sf-replay-node
                               fn-node-complete fn-sn-completion-record
                               fn-replay-apply-record fn-record-p
                               fn-snt-completion-record-is-a-true-list))))

(verify-guards fn-snt-relation
  :hints (("Goal" :use (fn-snt-completion-record-is-a-true-list)
           :in-theory (disable fn-sn-statep fn-sf-statep fn-node-statep
                               fn-sf-history-recoverablep fn-sf-replay-node
                               fn-node-complete fn-sn-completion-enabledp
                               fn-sn-completion-record fn-replay-apply-record
                               fn-snt-completion-record-is-a-true-list
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                               fn-sf-record-phasep))))

; `fn-store-event-sequence', not `fn-record-sequence': `fn-sf-record-listp'
; orders the sequence numbers of store events, and `fn-sf-record-pair' is
; built from the composed accessors, so the bound has to be stated in the same
; vocabulary.  Since `6ab2c783' and `4bb7bb3d' a history entry is not always
; an article record, and this book has not certified since 2026-09-21 01:20.
(defthm fn-snt-record-pair-after-prefix-absent
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (<= (+ sequence (len records))
                    (fn-store-event-sequence record)))
           (not (fn-sf-record-has-pairp (fn-sf-record-pair record) records)))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier))))

(defthm fn-snt-find-record-append-absent
  (implies (not (fn-sf-record-has-pairp (fn-sf-record-pair record) records))
           (equal (fn-sn-find-record (fn-sf-record-pair record)
                    (append records (list record))) record))
  :hints (("Goal" :induct (len records))))

(defthm fn-snt-find-published-candidate
  (implies (and (fn-sf-statep files)
                (fn-sf-candidatep record (fn-sf-records files) (fn-sf-frontier files)))
           (equal (fn-sn-find-record (fn-sf-record-pair record)
                    (append (fn-sf-records files) (list record))) record))
  :hints (("Goal" :use ((:instance fn-snt-find-record-append-absent
                          (records (fn-sf-records files)))
                        (:instance fn-snt-record-pair-after-prefix-absent
                          (records (fn-sf-records files)) (sequence 0) (lower 0)
                          (frontier (fn-sf-frontier files))))
           :in-theory (e/d (fn-sf-statep)
                            (fn-sf-record-listp fn-sf-success-listp
                             fn-sf-phase-shapep fn-sn-find-record
                             fn-sf-record-has-pairp)))))

(defthm fn-snt-bound-record-is-matching-proposal
  (implies (fn-sn-record-bindsp node record)
           (fn-node-pending-matchesp node (fn-record-txid record)
                                    (fn-record-generation record)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-node-pending-matchesp))))

; The other half of what binding a record says, and the half that decides
; which arm of `fn-sn-completion-enabledp' and `fn-sn-finish' a related state
; is on: a bound candidate is an article record.  Forward-chaining, because
; every proof below that needs it holds `fn-sn-record-bindsp' closed -- opening
; it there unfolds the record codec (books/replay.lisp, same measurement).
(defthm fn-snt-bound-record-is-an-article-record
  (implies (fn-sn-record-bindsp node record)
           (fn-record-p record))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sn-record-bindsp)
                                  (fn-node-pending-matchesp
                                   fn-sn-pending-record)))))

(defthm fn-snt-bound-record-excludes-consumer-by-shape
  (implies (fn-sn-record-bindsp node record)
           (not (fn-cpe-eventp record)))
  :hints (("Goal" :use fn-snt-bound-record-is-an-article-record
           :in-theory (disable fn-sn-record-bindsp fn-record-p
                               fn-cpe-eventp))))

; The reserved frontier is the candidate's successor, so the node the
; relation carries (replay at frontier - 1) is replay at the candidate txid.
; Stated as the arithmetic fact, :rule-classes nil, so the main proof does not
; depend on which way the rewriter orients the candidate equality.
; An article record is none of the other four store events, by length: ten
; fields against nine, eight, eight and six (books/defrecord.lisp writes the
; shape as a `len' check).  That is what lets the composed accessors below be
; read as the record's own.
; Exported, not local: books/store-node-resolution needs it of the candidate
; a related record phase carries, to dismiss the retention arm `6ab2c783'
; gave `fn-sn-known-abort'.
(defthm fn-snt-an-article-record-is-no-other-store-event
   (implies (fn-record-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-stxa-p record))
                 (not (fn-th-topic-eventp record))))
   :hints (("Goal"
            :in-theory (e/d ((:d fn-record-p) (:d fn-record-shapep)
                             (:d fn-store-retention-event-p)
                             (:d fn-stxe-p) (:d fn-stxe-shapep)
                             (:d fn-stxk-p) (:d fn-stxk-shapep)
                             (:d fn-stxa-p) (:d fn-stxa-shapep)
                             (:d fn-th-topic-eventp)
                             (:d fn-th-local-admin-eventp))
                            ((:d fn-stxe-bounded-octetsp)
                             (:d fn-record-uint32p) (:d fn-record-msgidp)
                             (:d fn-record-payloadp)
                             (:d fn-record-groups-validp)
                             (:d fn-record-metadata-bytes-p))))))

; Topic-admit and retention both have nine list fields. Their first tags,
; rather than length alone, separate the two payload grammars.
(local
 (defthm fn-snt-topic-event-is-not-retention-event
   (implies (fn-th-topic-eventp event)
            (not (fn-store-retention-event-p event)))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-store-retention-event-p
                   fn-th-local-admin-eventp fn-th-at fn-store-event-nth)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))

(local
 (defthm fn-snt-topic-event-is-not-consumer-event
   (implies (fn-th-topic-eventp event)
            (not (fn-cpe-eventp event)))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-cpe-eventp
                   fn-th-local-admin-eventp fn-th-at)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))

(local
 (defthm fn-snt-topic-event-is-not-identity-event
   (implies (fn-th-topic-eventp event)
            (and (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))))
   :hints (("Goal" :in-theory
            (e/d (fn-th-topic-eventp fn-stxe-p fn-stxk-p fn-stxa-p
                   fn-stxe-shapep fn-stxk-shapep fn-stxa-shapep
                   fn-stxe-sequence fn-stxk-sequence fn-stxa-sequence
                   fn-th-local-admin-eventp fn-th-at)
                 (fn-th-source-id-p fn-th-auth-ref-p
                  fn-th-exact-octets-p))))))

(local
 (defthm fn-snt-store-event-fields-of-an-article-record
   (implies (fn-record-p record)
            (and (equal (fn-store-event-sequence record)
                        (fn-record-sequence record))
                 (equal (fn-store-event-txid record) (fn-record-txid record))
                 (equal (fn-store-event-generation record)
                        (fn-record-generation record))))
   :hints (("Goal" :in-theory (enable fn-store-event-sequence
                                      fn-store-event-txid
                                      fn-store-event-generation)))))

; `fn-sf-candidatep' pins the composed transaction id, not the record's own:
; since 6ab2c783 and 4bb7bb3d a staged history entry is not always an article
; record.  On an article record the two are the same, by the bridge above.
(local
 (defthm fn-snt-candidate-is-frontier-predecessor
   (implies (fn-sf-candidatep record records frontier)
            (equal (+ -1 frontier) (fn-store-event-txid record)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-sf-candidatep)
                                   (fn-sf-next-lower fn-record-p
                                    fn-store-event-p
                                    fn-record-sequence fn-record-txid
                                    fn-record-generation))))))

; ---------------------------------------------------------------------------
; The deferred preparations, `6ab2c783' and `4bb7bb3d'.
;
; What the article preparation gets from `fn-snt-canonical-preparation-
; outcomes' the deferred ones need from the replay loop directly, because
; their node effect is not a preparation and a completion but one call of
; `fn-replay-apply-record' -- which IS the loop's one-record step.  Three
; small facts and then the outcome.

; `fn-snt-apply-event-from-idle-is-idle-and-monotone' and
; `fn-snt-apply-event-from-idle-is-at-the-successor'
; (books/store-node-invariants) are the per-arm step facts this book needs of
; `fn-replay-apply-record': every arm leaves the node idle at the successor
; of the event's own transaction id.  They were local there and are exported
; now, because applying the event is the WHOLE node effect of a deferred
; publication.

; This disjunction only unfolds the Store union.  Consumer and topic events
; are separate final arms; it does not prove their projections were applied.
(local
 (defthm fn-snt-store-event-final-arms-by-definition
   (implies (and (fn-store-event-p event)
                 (not (fn-record-p event))
                 (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event))
                 (not (fn-stxk-p event)))
            (or (fn-stxa-p event) (fn-cpe-eventp event)
                (fn-th-topic-eventp event)))
   :hints (("Goal" :in-theory (e/d (fn-store-event-p)
                                   (fn-record-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-cpe-eventp fn-th-topic-eventp
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

; `fn-replay-apply-record' IS the retention applier and the identity-neutral
; applier on their own arms.  Stated so every proof below can keep all three
; closed and still see that what `fn-sn-completion-enabledp' and
; `fn-sn-finish' ask for on an arm is the same step the relation carries.
(local
 (defthm fn-snt-apply-record-of-a-retention-event
   (implies (fn-store-retention-event-p event)
            (equal (fn-replay-apply-record node event)
                   (fn-replay-apply-retention-event node event)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-record)
                                   (fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-advance-txid
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary
                                    fn-store-event-p fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p))))))

; The loop over one event, from its own definition.
(local
 (defthm fn-snt-replay-singleton-is-the-applied-event
   (implies (and (fn-node-statep node)
                 (fn-store-event-p event)
                 (equal (fn-store-event-sequence event) sequence)
                 (fn-node-statep (fn-replay-apply-record node event)))
            (equal (fn-replay-loop node (list event) sequence)
                   (fn-replay-ok (fn-replay-apply-record node event)
                                 (1+ sequence))))
   :hints (("Goal" :in-theory (e/d (fn-replay-loop)
                                   (fn-replay-apply-record fn-node-statep
                                    fn-store-event-p))))))

; ... and so over a successful prefix extended by one event.
(local
 (defthm fn-snt-extended-history-is-the-applied-event
   (let ((base (fn-replay-result-node (fn-replay groups capacity history)))
         (sequence (fn-replay-result-sequence (fn-replay groups capacity history))))
     (implies
      (and (true-listp history)
           (fn-replay-okp (fn-replay groups capacity history))
           (fn-store-event-p event)
           (equal (fn-store-event-sequence event) sequence)
           (fn-node-statep (fn-replay-apply-record base event)))
      (equal (fn-replay groups capacity (append history (list event)))
             (fn-replay-ok (fn-replay-apply-record base event) (1+ sequence)))))
   :hints (("Goal" :in-theory (e/d (fn-replay)
                                   (fn-replay-loop fn-replay-apply-record
                                    fn-node-statep fn-store-event-p))))))

; Every arm of the step begins by advancing the node to the event's own
; transaction id and reads nothing else of the node afterwards, so advancing
; it there first changes nothing: `fn-snt-advance-twice' at one value.  The
; recognizers stay closed -- the arms do not need to be told apart for this.
(local
 (defthm fn-snt-apply-after-advance-to-its-txid
   (implies (fn-replay-advance-okp node (fn-store-event-txid event))
            (equal (fn-replay-apply-record
                    (fn-replay-advance-txid node (fn-store-event-txid event))
                    event)
                   (fn-replay-apply-record node event)))
   :hints (("Goal"
            :use ((:instance fn-snt-advance-twice
                             (first (fn-store-event-txid event))
                             (second (fn-store-event-txid event))))
            :in-theory (e/d (fn-replay-apply-record
                             fn-replay-apply-retention-event
                             fn-replay-apply-identity-neutral
                             fn-replay-advance-okp)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-replay-complete-retention
                             fn-replay-composite-record
                             fn-record-shape-vocabulary
                             fn-record-record-vocabulary
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-retain-admissiblep fn-retain-admit
                             fn-retain-release fn-retain-matching-releasep
                             fn-snt-advance-twice))))))

; The deferred analogue of `fn-snt-canonical-preparation-outcomes': staging
; one store event on a recoverable history leaves the replay of the extended
; history at the next frontier exactly where applying the event to the live
; node leaves it.  Where the applied node lands is
; `fn-snt-apply-event-from-idle-is-at-the-successor'.
(defthm fn-snt-deferred-preparation-outcome
  (let* ((node (fn-sf-replay-node groups capacity history txid))
         (applied (fn-replay-apply-record node event)))
    (implies
     (and (true-listp history)
          (fn-sf-history-recoverablep groups capacity history txid)
          (fn-store-event-p event)
          (equal (fn-store-event-sequence event) (len history))
          (equal (fn-store-event-txid event) txid)
          (fn-node-statep applied))
     (and (equal (fn-sf-replay-node groups capacity
                                    (append history (list event)) (1+ txid))
                 applied)
          (fn-sf-history-recoverablep groups capacity
                                      (append history (list event)) (1+ txid)))))
  :hints (("Goal"
           :use ((:instance fn-snt-extended-history-is-the-applied-event)
                 (:instance fn-snt-apply-after-advance-to-its-txid
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity history))))
                 (:instance fn-snt-replayed-node-idle-and-frontier
                            (records history) (frontier txid))
                 (:instance fn-snt-recoverable-prefix-facts
                            (frontier txid))
                 (:instance fn-snt-successful-replay-history-length
                            (records history))
                 (:instance fn-snt-apply-event-from-idle-is-at-the-successor
                            (node (fn-sf-replay-node groups capacity history txid))
                            (record event))
                 (:instance fn-snt-apply-event-from-idle-is-idle-and-monotone
                            (node (fn-sf-replay-node groups capacity history txid))
                            (record event)))
           :in-theory (e/d (fn-sf-replay-node fn-replay-advance-okp
                            fn-sf-history-recoverablep)
                           (fn-replay fn-replay-loop fn-replay-apply-record
                            fn-replay-advance-txid fn-node-statep
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-snt-extended-history-is-the-applied-event
                            fn-snt-apply-after-advance-to-its-txid
                            fn-snt-replayed-node-idle-and-frontier
                            fn-snt-recoverable-prefix-facts
                            fn-snt-apply-event-from-idle-is-at-the-successor
                            fn-snt-apply-event-from-idle-is-idle-and-monotone
                            fn-snt-successful-replay-history-length))))
  :rule-classes nil)

(defthm fn-snt-prepare-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare s record)))
  :hints (("Goal"
    ; Split on the transition's own gate; the instances about the staged
    ; proposal go to Subgoal 1, the case in which it holds, as in the two
    ; deferred preparations below.
    :use (fn-sn-prepare-preserves-state)
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (null (fn-node-stage (fn-sn-node s)))
                 (fn-record-p record)
                 (fn-sn-record-bindsp (fn-sn-prepare-node (fn-sn-node s) record) record)
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) record
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    ; The candidate this stages IS an article record -- that is the branch
    ; test of `fn-sn-prepare' -- so the deferred arm `6ab2c783' and
    ; `4bb7bb3d' made necessary is not the one taken, and it stays closed
    ; along with the codec it would otherwise unfold (measured: with it open
    ; this goal ran past the book's 1800 s limit, hbox
    ; certify-20260922T125743Z-2955378).
    :in-theory (e/d (fn-sf-prepare-record)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-snt-deferred-linkp
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p
                     fn-cpe-eventp fn-th-topic-eventp
                     fn-th-local-admin-eventp
                     fn-replay-apply-record
                     fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral
                     fn-replay-composite-record
                     fn-sn-identity-context fn-replay-identity-step)))
          ("Subgoal 1"
    :use (fn-snt-record-counters-natural
          (:instance fn-snt-candidate-is-frontier-predecessor
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-snt-bound-record-is-matching-proposal
            (node (fn-sn-prepare-node (fn-sn-node s) record)))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-canonical-preparation-outcomes
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s))))))))

; The other two preparations.  Both stage their event through the same
; `fn-sf-prepare-record' -- whose own gate is where the extended history's
; recoverability comes from -- and neither touches the node, so what they
; leave is the deferred link and not the pending one.  Before `6ab2c783' and
; `4bb7bb3d' these transitions did not exist; `books/store-node-resolution'
; puts both on `fn-snrt-step' and claims the relation of every step, and this
; book has not certified since 2026-09-21 01:20, so nothing had proved it.
(defthm fn-sn-prepare-retention-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare-retention s event)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-prepare-retention)
                                  (fn-sf-statep fn-node-statep
                                   fn-sf-prepare-record
                                   fn-replay-apply-retention-event
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sn-prepare-identity-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-prepare-identity)
                                  (fn-sf-statep fn-node-statep
                                   fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-replay-identity-step
                                   fn-sn-identity-context
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-sn-prepare-consumer-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare-consumer s event)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-prepare-consumer)
                                  (fn-sf-statep fn-node-statep
                                   fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-cpe-projection-step
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-cpe-eventp)))))

(defthm fn-sn-prepare-topic-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare-topic s event)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sn-prepare-topic)
                                  (fn-sf-statep fn-node-statep
                                   fn-sf-prepare-record
                                   fn-replay-apply-record fn-th-prefix-step
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-th-topic-eventp)))))

(defthm fn-snt-prepare-retention-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-retention s event)))
  :hints (("Goal"
    ; The transition changes the state only on its staging arm, and every
    ; instance below is about that arm.  Given to the whole goal they were
    ; also carried into each arm where the transition is the identity, and
    ; there the relation's own expansion rewrote them over again: 12 cases
    ; at 3.2 million steps each, 50.6 s on the seam run of 2026-09-23
    ; (planning/evidence/chain-remainder-cost-2026-09-23.md).  So the goal is
    ; split on the transition's own gate, and the instances go to the
    ; staging case alone.
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (fn-store-retention-event-p event)
                 (consp (fn-replay-apply-retention-event (fn-sn-node s) event))
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-replay-apply-record
                     fn-sn-prepare-retention)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral
                     fn-replay-composite-record
                     fn-replay-identity-step fn-sn-identity-context
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p
                     fn-th-topic-eventp fn-th-local-admin-eventp)))
          ; Subgoal 1 is the case in which the gate above holds.
          ("Subgoal 1"
    :use (fn-sn-prepare-retention-preserves-state
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-replay-apply-record-non-nil-is-node-state
            (node (fn-sn-node s)) (record event))
          (:instance fn-snt-typed-store-components)
          (:instance fn-replay-apply-record-non-nil-is-node-state
            (node (fn-sn-node s)) (record event))
          (:instance fn-snt-typed-store-components)
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

(defthm fn-snt-prepare-identity-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-identity s event)))
  :hints (("Goal"
    ; As for the retention arm above: split on the transition's own gate,
    ; and the instances about the staged event go to the staging case alone
    ; (115 subgoals and 10.9 s on the seam run of 2026-09-23 when they went
    ; to every case; planning/evidence/chain-remainder-cost-2026-09-23.md).
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (or (fn-stxe-p event) (fn-stxk-p event) (fn-stxa-p event))
                 (consp (fn-replay-apply-record (fn-sn-node s) event))
                 (equal (fn-stxk-context-kind
                         (fn-replay-identity-step (fn-sn-identity-context s) event))
                        :ok)
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-sn-prepare-identity)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-record
                     fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral
                     fn-replay-composite-record
                     ; `fn-sn-identity-context' stays OPEN: it reads the
                     ; snapshot list and the identity cursor and nothing
                     ; else, and what this goal owes is that the staged
                     ; state carries both unchanged.  Closed, the remaining
                     ; obligation is the identity step of a context the
                     ; prover cannot see through (hbox
                     ; certify-20260922T134536Z-2986916).
                     fn-replay-identity-step
                     ; and the retention bridge is withdrawn here: this
                     ; transition's guard and the outcome lemma are both
                     ; stated over `fn-replay-apply-record', and rewriting
                     ; one of them to the retention applier on a branch the
                     ; closed recognizers cannot rule out leaves the two
                     ; unable to meet.
                     fn-snt-apply-record-of-a-retention-event
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p fn-th-topic-eventp)))
          ; Subgoal 1 is the case in which the gate above holds.
          ("Subgoal 1"
    :use (fn-sn-prepare-identity-preserves-state
          fn-th-topic-event-is-not-stxe
          fn-th-topic-event-is-not-stxk
          fn-th-topic-event-is-not-stxa
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

(defthm fn-snt-prepare-consumer-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (fn-cpe-eventp event)
                 (eq (car (fn-cpe-projection-step
                           (fn-sn-consumer s) event
                           (fn-sn-identity-next s))) :ok)
                 (consp (fn-replay-apply-record (fn-sn-node s) event))
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-sn-prepare-consumer)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-record fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral fn-replay-composite-record
                     fn-replay-identity-step fn-cpe-projection-step
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                     fn-th-topic-eventp fn-th-prefix-step)))
          ("Subgoal 1"
    :use (fn-sn-prepare-consumer-preserves-state
          fn-snt-topic-event-is-not-consumer-event
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

(defthm fn-snt-prepare-topic-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare-topic s event)))
  :hints (("Goal"
    :cases ((and (fn-sn-statep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                 (fn-th-topic-eventp event)
                 (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) event)) :ok)
                 (consp (fn-replay-apply-record (fn-sn-node s) event))
                 (equal (fn-sf-phase (fn-sf-prepare-record
                                      (fn-sn-files s) event
                                      (fn-sn-groups s) (fn-sn-capacity s)))
                        :record-staged)))
    :in-theory (e/d (fn-sf-prepare-record fn-sn-prepare-topic)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp
                     fn-replay-apply-record fn-replay-apply-retention-event
                     fn-replay-apply-identity-neutral fn-replay-composite-record
                     fn-th-prefix-step
                     fn-snt-completion-linkp
                     fn-record-shape-vocabulary fn-record-record-vocabulary
                     fn-store-event-p fn-store-retention-event-p
                     fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                     fn-th-topic-eventp fn-th-local-admin-eventp)))
          ("Subgoal 1"
    :use (fn-sn-prepare-topic-preserves-state
          fn-snt-topic-event-is-not-retention-event
          fn-snt-topic-event-is-not-consumer-event
          fn-snt-topic-event-is-not-identity-event
          (:instance fn-snt-an-article-record-is-no-other-store-event
            (record event))
          (:instance fn-snt-candidate-is-frontier-predecessor
            (record event)
            (records (fn-sf-records (fn-sn-files s)))
            (frontier (fn-sf-frontier (fn-sn-files s))))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-deferred-preparation-outcome
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))
            (txid (+ -1 (fn-sf-frontier (fn-sn-files s)))))))))

; File stages that do not publish a record retain the same live proposal.
(defthm fn-snt-start-frontier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :start-frontier result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :start-frontier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-file result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-replace-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-replace result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-replace)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-directory result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :frontier-directory))
                        (:instance fn-snt-typed-frontier-phase (files (fn-sn-files s)))
                        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files s)))
                        (:instance fn-snt-history-recoverable-monotone
                          (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                          (records (fn-sf-records (fn-sn-files s)))
                          (first (fn-sf-frontier (fn-sn-files s)))
                          (second (1+ (fn-sf-frontier (fn-sn-files s))))))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-record-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-file result)))
  ; The staged candidate, the durable history and the frontier are all
  ; carried over, so whichever of the two links the state was on it is on
  ; after.  Both stay open for that and the codec stays closed.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :record-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))))

(defthm fn-snt-record-link-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-link result)))
  ; The staged candidate, the durable history and the frontier are all
  ; carried over, so whichever of the two links the state was on it is on
  ; after.  Both stay open for that and the codec stays closed.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :record-link)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))))

; This is the step that publishes the candidate and enters `:completing', so
; it is the step that owes the completing arm's article conjunct.  It owes it
; because `6ab2c783' and `4bb7bb3d' gave `fn-sn-completion-enabledp' a
; retention arm and an identity arm: with the candidate's kind unknown the
; goal reduced to `(NOT (FN-STORE-RETENTION-EVENT-P (FN-SF-RECORD-CANDIDATE
; (FN-SN-FILES S))))' and the book stopped there (hbox
; certify-20260922T114635Z-2909699).  The candidate's kind is not unknown: in
; a record phase the relation carries `fn-sn-record-bindsp' of it, which is
; `fn-snt-bound-record-is-an-article-record' above, and an article record is
; none of the other four store events by length
; (`fn-snt-an-article-record-is-no-other-store-event').  Those two are what
; dismiss the two new arms and establish the conjunct, and the published
; completion record is the candidate itself
; (`fn-snt-find-published-candidate').
(defthm fn-snt-record-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-directory result)))
  ; Only the observed durable directory in :record-attempted publishes
  ; anything; every other case leaves the files, history and node as they
  ; were, or fences the record.  The instances about the published
  ; candidate belong to that one case, and given to the whole goal they
  ; were carried through all 286 cases of its first split (9110 subgoals,
  ; 34.2 s on the seam run of 2026-09-23;
  ; planning/evidence/chain-remainder-cost-2026-09-23.md).  So the goal is
  ; split on that case, and Subgoal 1, where it holds, alone gets them.
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                   (operation :record-directory)))
           :cases ((and (fn-sn-statep s)
                       (equal (fn-sf-phase (fn-sn-files s)) :record-attempted)
                       (equal result :ok)))
           ; The five event recognizers and the three appliers stay closed,
           ; as they do in books/replay and books/store-node-invariants for
           ; the same reason: this goal DISPATCHES on the candidate's kind and
           ; does not look inside it, and with them open the two `cond's --
           ; `fn-store-event-p' under `fn-sf-candidatep' and
           ; `fn-sn-completion-enabledp' over the completion record -- unfold
           ; the record and statement codecs, which split Goal'' into 4970
           ; subgoals, the first of those into 4803, and exhaust the control
           ; stack (hbox certify-20260922T122534Z-2932993).  The instance of
           ; the disjointness lemma above supplies the four negations against
           ; the closed terms.
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-find-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-replay-identity-step))
          ("Subgoal 1" :use ((:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                        (:instance fn-snt-advance-that-lands-was-not-past-it
                          (node (fn-sn-node s))
                          (k (fn-store-event-txid
                              (fn-sf-record-candidate (fn-sn-files s)))))
                        (:instance fn-snt-an-article-record-is-no-other-store-event
                          (record (fn-sf-record-candidate (fn-sn-files s))))
                        (:instance fn-snt-bound-record-is-an-article-record
                          (node (fn-sn-node s))
                          (record (fn-sf-record-candidate (fn-sn-files s))))
                        (:instance fn-snt-find-published-candidate
                          (files (fn-sn-files s))
                          (record (fn-sf-record-candidate (fn-sn-files s))))))))

(defthm fn-snt-recovery-barrier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :recovery-barrier result)))
  :hints (("Goal" :use (fn-snt-state-reconstruction
                        (:instance fn-sn-io-preserves-state
                                     (operation :recovery-barrier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-completion-core-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-finish-image
  (implies (fn-sn-completion-enabledp s)
           (and (equal (fn-sf-phase (fn-sn-files (fn-sn-finish s))) :ready)
                (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-records (fn-sn-files s)))
                (equal (fn-sf-frontier (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-frontier (fn-sn-files s)))
                (equal (fn-sn-groups (fn-sn-finish s)) (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-finish s)) (fn-sn-capacity s))))
  ; `fn-store-event-sequence' and `fn-store-event-txid', not the article
  ; accessors: `6ab2c783' changed the pair `fn-sn-finish' hands
  ; `fn-sf-core-completion' to the composed ones, so the instance this proof
  ; supplied was about a different file step and its hypothesis reached the
  ; goal as `(CONS (CAR record) (CADR record))' against a `:completing' state
  ; whose completion pair is the composed one (hbox
  ; certify-20260922T123415Z-2939324).  All three arms of `fn-sn-finish' hand
  ; the same file state on, so the image is one equation and not three; the
  ; recognizers and appliers stay closed because nothing here looks inside
  ; the record.
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state
                    (s (fn-sn-files s))
                    (sequence (fn-store-event-sequence (fn-sn-completion-record s)))
                    (txid (fn-store-event-txid (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-sn-completion-enabledp)
                           (fn-sn-record-bindsp fn-sn-completion-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context
                               fn-replay-identity-step)))))

; The node the OTHER two arms of `fn-sn-finish' publish.  `6ab2c783' and
; `4bb7bb3d' added them and no theorem said what they produce;
; `fn-sn-finish-is-actual-durable-completion' (books/store-node-invariants)
; is the article arm's equation and names its arm, so this is the rest of the
; dispatch.  The hypothesis is enough to select them: on the remaining arm
; `fn-sn-completion-enabledp' demands `fn-sn-record-bindsp' of the completion
; record, which is `fn-record-p' of it.
(defthm fn-snt-finish-is-the-applied-event
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-record-p (fn-sn-completion-record s))))
           (equal (fn-sn-node (fn-sn-finish s))
                  (fn-replay-apply-record (fn-sn-node s)
                                          (fn-sn-completion-record s))))
  :hints (("Goal"
           :use ((:instance fn-snt-bound-record-is-an-article-record
                   (node (fn-sn-node s))
                   (record (fn-sn-completion-record s))))
           :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                           (fn-sn-completion-record fn-sn-record-bindsp
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary
                            fn-store-event-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p fn-th-topic-eventp
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-replay-apply-identity-neutral
                            fn-replay-composite-record
                            fn-replay-identity-step fn-sn-identity-context
                            fn-sn-accepted-delta fn-sn-composite-delta
                            fn-node-complete
                            fn-sf-core-completion fn-sf-emit-success)))))

; `fn-sn-finish-is-actual-durable-completion' (books/store-node-invariants)
; names the arm it is about: since `6ab2c783' and `4bb7bb3d' the node
; `fn-sn-finish' publishes is the durable completion only when the completion
; record is an article record.  The completing arm of the relation carries
; exactly that, and the disjointness lemma turns it into the four negative
; hypotheses that theorem asks for; the other arm is the equation above.
(defthm fn-snt-finish-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-finish s)))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-preserves-state fn-snt-finish-image
                 fn-sn-finish-is-actual-durable-completion
                 fn-snt-finish-is-the-applied-event
                 fn-sn-finish-disabled-is-no-op
                 (:instance fn-snt-an-article-record-is-no-other-store-event
                   (record (fn-sn-completion-record s))))
           ; Closed for the same reason as the directory step above: this
           ; goal dispatches on the completion record's kind through
           ; `fn-sn-completion-enabledp' and never looks inside it.
           :in-theory (e/d (fn-sn-completion-enabledp)
                           (fn-sn-finish fn-sn-statep fn-sn-record-bindsp
                               fn-sf-history-recoverablep fn-snt-pending-linkp fn-snt-deferred-linkp
                               fn-sn-completion-record
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp fn-th-local-admin-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context
                               fn-replay-identity-step)))))

(defthm fn-snt-crash-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal"
    :use (fn-sn-crash-preserves-state
          (:instance fn-snt-typed-frontier-phase (files (fn-sn-files s)))
                        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files s)))
          (:instance fn-snt-history-recoverable-monotone
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (records (fn-sf-records (fn-sn-files s)))
            (first (fn-sf-frontier (fn-sn-files s)))
            (second (1+ (fn-sf-frontier (fn-sn-files s))))))
    :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                        fn-sn-record-bindsp fn-sn-completion-enabledp
                        fn-snt-completion-linkp
                     fn-record-shape-vocabulary
                        fn-store-event-p fn-store-retention-event-p
                        fn-stxe-p fn-stxk-p fn-stxa-p fn-th-topic-eventp
                        fn-replay-apply-record
                        fn-replay-apply-retention-event
                        fn-replay-apply-identity-neutral
                        fn-replay-composite-record
                        fn-replay-identity-step))))

; Two arms since `40bb3f74', and the relation now has a case for each.  A
; related `:replaying' state has a recoverable history, so `fn-sf-recover'
; reaches `:recovering' over the same records and frontier; whether
; `fn-sn-recover' then publishes that phase or the `:fault' one turns on the
; identity replay alone, and on the fault arm it keeps those records and that
; frontier and does not touch the node.
(defthm fn-snt-recover-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-recover s)))
  :hints (("Goal" :use fn-sn-recover-preserves-state
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp
                               fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                               fn-record-shape-vocabulary
                               fn-store-event-p fn-store-retention-event-p
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-apply-identity-neutral
                               fn-replay-composite-record
                               fn-sn-identity-context fn-replay-identity-step))))

; -by-definition: the otherwise branch of fn-sn-file-step.
(defthm fn-snt-unknown-io-is-no-op
  (implies (not (member-equal operation
                  '(:start-frontier :frontier-file :frontier-replace
                    :frontier-directory :record-file :record-link
                    :record-directory :recovery-barrier)))
           (equal (fn-sn-io s operation result) s))
  :rule-classes nil
  :hints (("Goal" :use (fn-snt-state-reconstruction)
           :in-theory (disable fn-sn-statep))))

(defthm fn-snt-io-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s operation result)))
  :hints (("Goal"
    :cases ((equal operation :start-frontier) (equal operation :frontier-file)
            (equal operation :frontier-replace) (equal operation :frontier-directory)
            (equal operation :record-file) (equal operation :record-link)
            (equal operation :record-directory) (equal operation :recovery-barrier))
    :use fn-snt-unknown-io-is-no-op
    :in-theory (disable fn-snt-relation fn-sn-io))))

; Events are already-decoded logical data, never a raw external reader format.
; This dispatcher simply selects the actual wrapper operations.  It does not
; inspect the relation of the result, roll back failed proof checks, or assume
; that a trace preserves any invariant.
(defun fn-snt-step (s event)
  (case (car event)
    (:prepare (fn-sn-prepare s (cadr event)))
    (:io (fn-sn-io s (cadr event) (caddr event)))
    (:finish (fn-sn-finish s))
    (:crash (fn-sn-crash s (cadr event) (caddr event)))
    (:recover (fn-sn-recover s))
    (otherwise s)))
(defun fn-snt-run (s events)
  (if (consp events)
      (fn-snt-run (fn-snt-step s (car events)) (cdr events))
    s))

(defthm fn-snt-step-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snt-step s event)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-sn-prepare fn-sn-io
                      fn-sn-finish fn-sn-crash fn-sn-recover))))

(defthm fn-snt-mixed-trace-preserves-live-history-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-snt-run s events)))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step))))

(defthm fn-snt-initialized-mixed-trace-has-live-history-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-snt-run (fn-sn-initial groups capacity) events)))
  :hints (("Goal" :in-theory (disable fn-snt-relation fn-snt-run fn-sn-initial))))

; Isolate the one relation arm used by the public exact-replay claim.  The
; other arms contain record codecs and replay steps irrelevant to an idle
; phase; opening them in the final theorem makes a simple projection costly.
(local
 (defthm fn-snt-ready-or-recovered-phase-is-idle
   (implies (member-equal phase '(:ready :recovering :fenced-recovery))
            (fn-snt-idle-phasep phase))
   :hints (("Goal" :in-theory (enable fn-snt-idle-phasep)))))

(local
 (defthm fn-snt-idle-relation-node-is-exact-replay
   (implies (and (fn-snt-relation s)
                 (fn-snt-idle-phasep (fn-sf-phase (fn-sn-files s))))
            (equal (fn-sn-node s)
                   (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                      (fn-sf-records (fn-sn-files s))
                                      (fn-sf-frontier (fn-sn-files s)))))
   :hints (("Goal" :in-theory '(fn-snt-relation)))))

(defthm fn-snt-ready-or-recovered-node-is-exact-replay
  (implies (and (fn-snt-relation s)
                (member-equal (fn-sf-phase (fn-sn-files s))
                              '(:ready :recovering :fenced-recovery)))
           (equal (fn-sn-node s)
                  (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                     (fn-sf-records (fn-sn-files s))
                                     (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-phase-is-idle
                        (phase (fn-sf-phase (fn-sn-files s))))
                         fn-snt-idle-relation-node-is-exact-replay)
           :in-theory nil)))

(defthm fn-snt-mixed-trace-ready-node-is-exact-replay
  (let ((final (fn-snt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                      (fn-sf-records (fn-sn-files final))
                      (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal" :use ((:instance fn-snt-ready-or-recovered-node-is-exact-replay
                                   (s (fn-snt-run s events))))
           :in-theory (disable fn-snt-relation fn-snt-run))))

(defthm fn-snt-step-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snt-step s event)))))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-acknowledges-exact-pair
                 fn-sn-finish-disabled-is-no-op
                 (:instance fn-sf-state-successes-are-true-list (s (fn-sn-files s))))
           :in-theory (disable fn-sn-prepare fn-sn-io fn-sn-finish fn-sn-crash
             fn-sn-recover fn-sn-completion-enabledp 
              fn-sf-prefixp fn-snt-relation))))

(defthm fn-snt-related-successes-true-list
  (implies (fn-snt-relation s)
           (true-listp (fn-sf-successes (fn-sn-files s))))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                         fn-snt-typed-store-components
                         (:instance fn-sf-state-successes-are-true-list
                          (s (fn-sn-files s))))
           :in-theory (disable fn-snt-relation fn-sn-statep))))

(defthm fn-snt-mixed-trace-success-history-monotone
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-successes (fn-sn-files s))
                          (fn-sf-successes (fn-sn-files (fn-snt-run s events)))))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-successes (fn-sn-files s)))
                                 (ys (fn-sf-successes (fn-sn-files (fn-snt-step s (car events)))))
                                 (zs (fn-sf-successes (fn-sn-files (fn-snt-run
                                       (fn-snt-step s (car events)) (cdr events))))))))))

; Prior acknowledged pairs survive arbitrary mixed wrapper traces.  Whenever
; the final live node is ready/recovered it equals replay of precisely this
; surviving history, rather than an independently trusted completion cache.
(defthm fn-snt-acknowledged-history-retained-through-mixed-trace
  (let ((final (fn-snt-run s events)))
    (implies (and (fn-snt-relation s)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (and (member-equal pair (fn-sf-successes (fn-sn-files final)))
                  (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final))))))
  :hints (("Goal"
    :use (fn-snt-mixed-trace-success-history-monotone
          fn-snt-mixed-trace-preserves-live-history-relation
          (:instance fn-snt-relation-implies-structural-state (s (fn-snt-run s events)))
          (:instance fn-snt-typed-store-components (s (fn-snt-run s events)))
          (:instance fn-sf-state-success-member-has-record
            (s (fn-sn-files (fn-snt-run s events))))
          (:instance fn-sf-member-preserved-by-prefix
            (x pair) (xs (fn-sf-successes (fn-sn-files s)))
            (ys (fn-sf-successes (fn-sn-files (fn-snt-run s events))))))
    :in-theory (disable fn-snt-run fn-snt-relation 
                          fn-sf-record-has-pairp))))

; -----------------------------------------------------------------------------
; Stable records only grow along composed traces.  These footprint theorems
; carry the kernel's record prefix through every composed operation, so a
; record present when a process reopens remains present for the rest of that
; process (used across the reopen boundary by store-observed.lisp).

(defthm fn-snt-prepare-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare s record)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-sn-update )
                                  (fn-sn-statep fn-sn-record-bindsp
                                   fn-sf-prepare-record )))))

; The same of the two deferred preparations (`6ab2c783', `4bb7bb3d'): they
; stage through the same `fn-sf-prepare-record', which publishes nothing.
(defthm fn-snt-prepare-retention-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-retention s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-retention fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-retention-event
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-snt-prepare-identity-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-identity s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-identity fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-replay-identity-step
                                   fn-sn-identity-context
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-snt-prepare-consumer-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-prepare-consumer s event)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-consumer fn-sn-update)
                                  (fn-sn-statep fn-sf-prepare-record
                                   fn-replay-apply-record
                                   fn-cpe-projection-step
                                   fn-record-shape-vocabulary
                                   fn-store-event-p fn-cpe-eventp)))))

; The event-index update on a successful record-directory observation changes
; only the derived index.  Project files before proving the file-kernel prefix
; property, so this proof never opens the index insertion or its bounds codec.
(local
 (defthm fn-snt-files-of-io
   (equal (fn-sn-files (fn-sn-io s operation result))
          (if (fn-sn-statep s)
              (fn-sn-file-step (fn-sn-files s) operation result)
            (fn-sn-files s)))
   :hints (("Goal"
            :in-theory '(fn-sn-io
                         fn-sn-files-of-fn-sn-update
                         fn-sn-files-of-fn-sn-with-event-index)))))

(defthm fn-snt-io-records-prefix
  (implies (fn-sn-statep s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-sn-io s operation result)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-sf-stable-records-prefix-of-record-dir-result
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-file-step)
                           (fn-sn-statep fn-sf-statep  fn-sf-prefixp
                            fn-sn-io fn-sn-update fn-sn-with-event-index
                            fn-cei-put fn-cp-uintp
                            fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier)))))

; The three arms `6ab2c783' and `4bb7bb3d' gave `fn-sn-finish' hand the same
; file state on, so this is still one equation; the recognizers and the
; identity step stay closed so the dispatch does not unfold the codec under
; it.
(local
 (defthm fn-snt-files-of-with-topic
   (equal (fn-sn-files (fn-sn-with-topic s topic)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-with-topic fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-with-consumer
   (equal (fn-sn-files (fn-sn-with-consumer s consumer)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-with-consumer fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-advance-identity-next
   (equal (fn-sn-files (fn-sn-advance-identity-next s)) (fn-sn-files s))
   :hints (("Goal" :in-theory
            '(fn-sn-advance-identity-next fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-update-indexed
   (equal (fn-sn-files (fn-sn-update-indexed s files node index)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-update-indexed fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-update-accepted
   (equal (fn-sn-files (fn-sn-update-accepted
                         s files node index msgid verdict)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-update-accepted fn-sn-files-of-fn-sn-make-v6)))))
(local
 (defthm fn-snt-files-of-finish-identity
   (equal (fn-sn-files (fn-sn-finish-identity s files record node)) files)
   :hints (("Goal" :in-theory
            '(fn-sn-finish-identity fn-sn-files-of-fn-sn-make-v6)))))

(defthm fn-snt-finish-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory
           '(fn-sn-finish
             fn-snt-files-of-with-topic fn-snt-files-of-with-consumer
             fn-snt-files-of-advance-identity-next
             fn-snt-files-of-update-indexed fn-snt-files-of-update-accepted
             fn-snt-files-of-finish-identity
             fn-sf-records-of-core-completion fn-sf-records-of-emit-success))))

(defthm fn-snt-crash-records-prefix
  (implies (fn-sn-statep s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records
                           (fn-sn-files (fn-sn-crash s frontier-choice record-choice)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-sf-stable-records-prefix-of-crash (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-crash fn-sn-update )
                           (fn-sn-statep fn-sf-statep  fn-sf-prefixp
                            fn-sf-crash fn-sf-crash-choicep)))))

(defthm fn-snt-recover-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-recover s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-recover fn-sn-update )
                                  (fn-sn-statep  fn-sf-recover
                                   fn-sf-replay-node)))))

(defthm fn-snt-related-records-true-list
  (implies (fn-snt-relation s)
           (true-listp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                         fn-snt-typed-store-components
                         (:instance fn-sf-state-records-are-true-list
                          (s (fn-sn-files s))))
           :in-theory (disable fn-snt-relation fn-sn-statep))))

(defthm fn-snt-step-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snt-step s event)))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-related-records-true-list
                 (:instance fn-snt-io-records-prefix
                            (operation (cadr event)) (result (caddr event)))
                 (:instance fn-snt-crash-records-prefix
                            (frontier-choice (cadr event)) (record-choice (caddr event))))
           :in-theory (e/d (fn-snt-step)
                           (fn-snt-relation fn-sn-statep fn-sn-prepare fn-sn-io
                            fn-sn-finish fn-sn-crash fn-sn-recover 
                             fn-sf-prefixp
                            fn-snt-io-records-prefix fn-snt-crash-records-prefix)))))

(defthm fn-snt-mixed-trace-records-prefix
  (implies (fn-snt-relation s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-snt-run s events)))))
  :hints (("Goal" :induct (fn-snt-run s events)
           :in-theory (disable fn-snt-relation fn-snt-step 
                                fn-sf-prefixp))
          ("Subgoal *1/1" :use ((:instance fn-sf-prefixp-transitive
                                 (xs (fn-sf-records (fn-sn-files s)))
                                 (ys (fn-sf-records (fn-sn-files (fn-snt-step s (car events)))))
                                 (zs (fn-sf-records (fn-sn-files (fn-snt-run
                                       (fn-snt-step s (car events)) (cdr events))))))))))

; An admissible crash image of a related live state is replayable at its own
; frontier.  This is the fact that lets the observed reopen path succeed on
; every image the platform may leave behind (A-DURABILITY as hypothesis).
(defthm fn-snt-admissible-crash-image-is-recoverable
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records))
           (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                       records frontier))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-crash-preserves-relation
                            (frontier-choice
                             (fn-sf-image-frontier-choice (fn-sn-files s) frontier))
                            (record-choice
                             (fn-sf-image-record-choice (fn-sn-files s) records)))
                 (:instance fn-snt-relation-implies-structural-state
                            (s (fn-sn-crash s
                                 (fn-sf-image-frontier-choice (fn-sn-files s) frontier)
                                 (fn-sf-image-record-choice (fn-sn-files s) records)))))
           :in-theory (e/d (fn-snt-relation)
                           (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                            fn-sf-replay-node fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                            fn-sn-completion-enabledp
                            fn-sn-completion-core-enabledp fn-snt-idle-phasep
                            fn-sf-record-phasep fn-sn-crash fn-sf-crash
                            fn-sf-crash-imagep fn-sf-image-frontier-choice
                            fn-sf-image-record-choice  
                              
                             
                            fn-snt-crash-preserves-relation)))))

; The PLATFORM twin (D14-b, and K2f).  Every image the platform may leave --
; the two namespace choices, the record rollback and the frontier rollback --
; is replayable at its own frontier, so the observed reopen path succeeds on
; all of them.  The reliance-predicate theorem above is UNCHANGED and is this
; one's special case (fn-sf-crash-imagep-implies-recovery-crash-imagep); the
; host's reopen gate (fn-own-reopen, owner.lisp:911) still takes the narrow
; premise, which is the whole of D14-b.
;
; The record arm is fn-snt-history-recoverable-of-but-last.  The frontier arm
; is fn-snt-history-recoverable-under-record-bound at the rolled-back value,
; and its fn-sf-record-listp hypothesis is exactly the gate that
; fn-sf-frontier-rollback-visiblep carries -- the same conjunct that makes
; the rolled-back image a kernel state makes it replayable.
(defthm fn-snt-recovery-admissible-crash-image-is-recoverable
  (implies (and (fn-snt-relation s)
                (fn-sf-recovery-crash-imagep (fn-sn-files s) frontier records))
           (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                       records frontier))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 fn-snt-typed-store-components
                 fn-snt-related-records-true-list
                 fn-snt-admissible-crash-image-is-recoverable
                 (:instance fn-snt-admissible-crash-image-is-recoverable
                            (frontier (fn-sf-frontier (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-snt-recoverable-prefix-facts
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (history (fn-sf-records (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-snt-history-recoverable-of-but-last
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s))))
                 (:instance fn-snt-history-recoverable-under-record-bound
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (bound (1- (fn-sf-frontier (fn-sn-files s)))))
                 ; cited by :use and not left to forward chaining: the
                 ; trigger (fn-sf-frontier-rollback-visiblep ...) only
                 ; appears once fn-sf-recovery-crash-imagep opens during
                 ; this goal's own simplification, which is after forward
                 ; chaining has run.
                 (:instance fn-sf-frontier-rollback-visiblep-unfolds
                            (s (fn-sn-files s))))
           ; fn-sf-crash-imagep stays OPEN (the book's default): the
           ; identity image of a related state is admissible by it, and that
           ; instance of the narrow theorem is what the two rollback arms
           ; are then derived from.
           :in-theory (e/d (fn-sf-recovery-crash-imagep fn-sf-crash-imagep)
                           (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                            fn-sf-replay-node fn-sf-record-listp
                            fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp fn-snt-idle-phasep
                            fn-sn-completion-enabledp
                            fn-sn-completion-core-enabledp fn-sf-record-phasep
                            fn-sn-crash fn-sf-crash
                            fn-sf-image-frontier-choice fn-sf-image-record-choice
                            fn-snt-relation-implies-structural-state
                            fn-snt-typed-store-components
                            fn-snt-related-records-true-list
                            fn-snt-admissible-crash-image-is-recoverable
                            fn-snt-recoverable-prefix-facts
                            fn-snt-history-recoverable-of-but-last
                            fn-snt-history-recoverable-under-record-bound
                            fn-sf-frontier-rollback-visiblep-unfolds)))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the relation and its two links (proof relations,
; never executed), the dispatcher, and under a name the typed, footprint and
; canonical-preparation lemmas.  Enabled on include: the
; relation keystones (initial, preserved by every step, mixed traces), the
; exact-replay and acknowledged-history keystones, fn-snt-run and the two
; typed-list facts.
(deftheory fn-store-node-traces-vocabulary
  '(fn-snt-recoverable-prefix-facts fn-snt-prepare-replayed-node
    fn-snt-canonical-preparation-advance-ok fn-snt-canonical-preparation-outcomes
    fn-snt-record-counters-natural fn-snt-state-reconstruction
    fn-snt-typed-frontier-phase fn-snt-typed-frontier-natural
    fn-snt-typed-record-phase fn-snt-record-pair-after-prefix-absent
    fn-snt-find-record-append-absent fn-snt-find-published-candidate
    fn-snt-bound-record-is-matching-proposal
    fn-snt-bound-record-is-an-article-record
    fn-snt-an-article-record-is-no-other-store-event fn-snt-finish-image
    fn-snt-prepare-keeps-records
    fn-snt-prepare-retention-keeps-records
    fn-snt-prepare-identity-keeps-records fn-snt-io-records-prefix
    fn-snt-finish-keeps-records fn-snt-crash-records-prefix
    fn-snt-recover-keeps-records))
(in-theory (disable fn-store-node-traces-vocabulary
                    fn-snt-pending-linkp fn-snt-deferred-linkp fn-snt-completion-linkp
                    fn-snt-relation fn-snt-step))
