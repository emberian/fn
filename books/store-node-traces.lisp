; fn: inductive mixed traces of the actual live node/file composition.
(in-package "ACL2")
(include-book "store-node-invariants")
(include-book "store-files-traces")
(local (include-book "arithmetic/top" :dir :system))

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
(local (in-theory (e/d (fn-sn-statep fn-sn-initial fn-sn-pending-record
                        fn-sn-record-bindsp fn-sn-prepare
                        fn-sn-completion-record fn-sn-completion-enabledp
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
                        fn-retain-statep fn-node-initial-state
                         fn-state-next-txid
                          ))))

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
  (member-equal phase '(:ready :frontier-staged :frontier-data-durable
                       :frontier-attempted :fenced-frontier
                       :recovering :fenced-recovery)))

; This is a proof relation, never an executable transition guard.  Before
; publication the actual proposal's two resolutions match current/extended
; replay.  After publication only its durable resolution matches history.
(defun fn-snt-pending-linkp (groups capacity files node)
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

(defun fn-snt-relation (s)
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
          ((fn-sf-record-phasep phase)
           (fn-snt-pending-linkp groups capacity files node))
          ((equal phase :completing)
           (and (fn-sn-completion-enabledp s)
                (equal (fn-node-complete node
                         (fn-record-txid (fn-sn-completion-record s))
                         (fn-record-generation (fn-sn-completion-record s)) :durable)
                       (fn-sf-replay-node groups capacity history frontier))))
          ((equal phase :replaying)
           (equal node (fn-node-initial-state groups capacity)))
          (t nil)))))

(defthm fn-snt-relation-implies-structural-state
  (implies (fn-snt-relation s) (fn-sn-statep s))
  :hints (("Goal" :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                                      fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-initial-relation
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-snt-relation (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node fn-replay fn-replay-loop
                         fn-node-initial-state  fn-node-acceptance
                           fn-state-fenced
                         fn-replay-advance-txid fn-node-statep fn-statep fn-retain-statep fn-snx-core-definitions))))

(defthm fn-snt-record-counters-natural
  (implies (fn-record-p record)
           (and (natp (fn-record-txid record))
                (natp (fn-record-generation record))
                (natp (fn-record-sequence record))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-record-p))))

(defthm fn-snt-state-reconstruction
  (implies (fn-sn-statep s)
           (equal (fn-sn-make (fn-sn-groups s) (fn-sn-capacity s)
                              (fn-sn-files s) (fn-sn-node s))
                  s))
  :hints (("Goal" :in-theory (enable len fn-sn-statep fn-sn-shapep fn-sn-make fn-sn-groups
                                     fn-sn-capacity fn-sn-files fn-sn-node)
           :expand ((len s) (len (cdr s)) (len (cddr s))
                    (len (cdddr s)) (len (cddddr s)))
           :do-not-induct t)))

(defthm fn-snt-typed-store-components
  (implies (fn-sn-statep s)
           (and (fn-sf-statep (fn-sn-files s))
                (fn-node-statep (fn-sn-node s))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-node-statep fn-sf-statep))))

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

(defthm fn-snt-record-pair-after-prefix-absent
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (<= (+ sequence (len records)) (fn-record-sequence record)))
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

(defthm fn-snt-prepare-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-prepare s record)))
  :hints (("Goal"
    :use (fn-sn-prepare-preserves-state fn-snt-record-counters-natural
          (:instance fn-snt-bound-record-is-matching-proposal
            (node (fn-sn-prepare-node (fn-sn-node s) record)))
          (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
          (:instance fn-snt-canonical-preparation-outcomes
            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
            (history (fn-sf-records (fn-sn-files s)))))
    :in-theory (e/d (fn-sf-prepare-record)
                    (fn-sn-statep fn-sn-record-bindsp fn-sf-history-recoverablep
                     fn-sn-completion-enabledp fn-sn-completion-record
                     fn-sf-recover fn-sf-record-listp)))))

; File stages that do not publish a record retain the same live proposal.
(defthm fn-snt-start-frontier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :start-frontier result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :start-frontier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-file result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :frontier-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-replace-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-replace result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :frontier-replace)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-frontier-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :frontier-directory result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :frontier-directory))
                        (:instance fn-snt-typed-frontier-phase (files (fn-sn-files s)))
                        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files s)))
                        (:instance fn-snt-history-recoverable-monotone
                          (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                          (records (fn-sf-records (fn-sn-files s)))
                          (first (fn-sf-frontier (fn-sn-files s)))
                          (second (1+ (fn-sf-frontier (fn-sn-files s))))))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-record-file-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-file result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :record-file)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp))))

(defthm fn-snt-record-link-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-link result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :record-link)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp))))

(defthm fn-snt-record-directory-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :record-directory result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :record-directory))
                        (:instance fn-snt-typed-record-phase (files (fn-sn-files s)))
                        (:instance fn-snt-find-published-candidate
                          (files (fn-sn-files s))
                          (record (fn-sf-record-candidate (fn-sn-files s)))))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-find-record))))

(defthm fn-snt-recovery-barrier-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-io s :recovery-barrier result)))
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                     (operation :recovery-barrier)))
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-snt-pending-linkp fn-sn-completion-enabledp))))

(defthm fn-snt-finish-image
  (implies (fn-sn-completion-enabledp s)
           (and (equal (fn-sf-phase (fn-sn-files (fn-sn-finish s))) :ready)
                (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-records (fn-sn-files s)))
                (equal (fn-sf-frontier (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-frontier (fn-sn-files s)))
                (equal (fn-sn-groups (fn-sn-finish s)) (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-finish s)) (fn-sn-capacity s))))
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state
                    (s (fn-sn-files s))
                    (sequence (fn-record-sequence (fn-sn-completion-record s)))
                    (txid (fn-record-txid (fn-sn-completion-record s)))))
           :in-theory (disable fn-sn-record-bindsp fn-sn-completion-record))))

(defthm fn-snt-finish-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-finish s)))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-preserves-state fn-snt-finish-image
                 fn-sn-finish-is-actual-durable-completion
                 fn-sn-finish-disabled-is-no-op)
           :in-theory (disable fn-sn-finish fn-sn-statep fn-sn-record-bindsp
                               fn-sf-history-recoverablep fn-snt-pending-linkp
                               fn-sn-completion-record))))

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
                        fn-sn-record-bindsp fn-sn-completion-enabledp))))

(defthm fn-snt-recover-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-recover s)))
  :hints (("Goal" :use fn-sn-recover-preserves-state
           :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                               fn-sn-record-bindsp fn-sn-completion-enabledp))))

; -by-definition: the otherwise branch of fn-sn-file-step.
(defthm fn-snt-unknown-io-is-no-op
  (implies (not (member-equal operation
                  '(:start-frontier :frontier-file :frontier-replace
                    :frontier-directory :record-file :record-link
                    :record-directory :recovery-barrier)))
           (equal (fn-sn-io s operation result) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-sn-statep))))

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

(defthm fn-snt-ready-or-recovered-node-is-exact-replay
  (implies (and (fn-snt-relation s)
                (member-equal (fn-sf-phase (fn-sn-files s))
                              '(:ready :recovering :fenced-recovery)))
           (equal (fn-sn-node s)
                  (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                     (fn-sf-records (fn-sn-files s))
                                     (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory (disable fn-sn-statep fn-sf-history-recoverablep
                                      fn-sn-completion-enabledp fn-snt-pending-linkp))))

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

(defthm fn-snt-io-records-prefix
  (implies (fn-sn-statep s)
           (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                          (fn-sf-records (fn-sn-files (fn-sn-io s operation result)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-sf-stable-records-prefix-of-record-dir-result
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-io fn-sn-file-step fn-sn-update )
                           (fn-sn-statep fn-sf-statep  fn-sf-prefixp
                            fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result fn-sf-recovery-barrier)))))

(defthm fn-snt-finish-keeps-records
  (equal (fn-sf-records (fn-sn-files (fn-sn-finish s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-update )
                                  (fn-sn-completion-enabledp fn-sn-completion-record
                                    fn-sf-core-completion
                                   fn-sf-emit-success)))))

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
                            fn-sf-replay-node fn-snt-pending-linkp
                            fn-sn-completion-enabledp fn-snt-idle-phasep
                            fn-sf-record-phasep fn-sn-crash fn-sf-crash
                            fn-sf-crash-imagep fn-sf-image-frontier-choice
                            fn-sf-image-record-choice  
                              
                             
                            fn-snt-crash-preserves-relation)))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the relation and its pending link (proof
; relations, never executed), the dispatcher, and under a name the typed,
; footprint and canonical-preparation lemmas.  Enabled on include: the
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
    fn-snt-bound-record-is-matching-proposal fn-snt-finish-image
    fn-snt-prepare-keeps-records fn-snt-io-records-prefix
    fn-snt-finish-keeps-records fn-snt-crash-records-prefix
    fn-snt-recover-keeps-records))
(in-theory (disable fn-store-node-traces-vocabulary
                    fn-snt-pending-linkp fn-snt-relation fn-snt-step))
