; fn: the productive counterpart of the served POST's safety theorem
; (lane productive-contract, 2026-09-29; row W6; GPT-6's second review,
; warranty-quality-proof-engineering.md section 1 and section 9; PRF-1001,
; PRF-1002; specs/productive-contract.md).
;
; fn-own-240-follows-consumed-completion (books/owner-served-invariants.lisp)
; says a 240 was earned.  A machine that always answers uncertain satisfies
; it; fn once was that machine (a payload handle compared against the staged
; octets made every served POST finish :fault).  This book states the other
; direction: a request the CONTRACT admits, under the specified successful
; primitive completions -- the disk answers, the log appends complete, the
; completion is delivered -- reaches its specified successful outcome, the
; 240 line and the record in durable history, within a stated number of
; steps of the served step function fn-own-step.  The admission predicate is
; the Store's own staging condition, stated here as fn-pcx-admissiblep
; (specs/productive-contract.md section 2 names which of its conjuncts is
; validity, which is authorization and which is funding), never the host's
; word.  A second part names the cause of every uncertain outcome.
;
; This book shares the prefix `fn-pcx-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "owner-served-invariants")
(include-book "owner-prepare-outcome")

; -----------------------------------------------------------------------------
; 1. The specified successful primitive completions of one served POST, as
; the Store events the served step function takes after the writer took the
; submission (:take): the four frontier observations, the one prepare ACL2
; decided, the three record observations.  The owner's events wrap each in
; (:store E); the completion is the owner's own (:complete).

(defun fn-pcx-frontier-events ()
  (declare (xargs :guard t))
  '((:io :start-frontier nil)
    (:io :frontier-file :ok)
    (:io :frontier-replace :ok)
    (:io :frontier-directory :ok)))

(defun fn-pcx-record-events ()
  (declare (xargs :guard t))
  '((:io :record-file :ok)
    (:io :record-link :ok)
    (:io :record-directory :ok)))

(defun fn-pcx-store-script (prepare)
  (declare (xargs :guard t))
  (append (fn-pcx-frontier-events) (list prepare) (fn-pcx-record-events)))

(defun fn-pcx-wrap-store (events)
  (declare (xargs :guard t))
  (if (consp events)
      (cons (list :store (car events)) (fn-pcx-wrap-store (cdr events)))
    nil))

; The owner's events: the wrapped Store script, then the completion.
(defun fn-pcx-post-script (prepare)
  (declare (xargs :guard t))
  (append (fn-pcx-wrap-store (fn-pcx-store-script prepare)) (list '(:complete))))

; The bound: nine steps of fn-own-step from the take to the consumed
; completion; the tenth is the outcome (:outcome id :durable).
(defconst *fn-pcx-post-steps* 9)

(defthm fn-pcx-post-script-length
  (equal (len (fn-pcx-post-script prepare)) *fn-pcx-post-steps*))

; -----------------------------------------------------------------------------
; 2. The Store's admission of a record, stated at :ready.  fn-pcx-stageablep
; is what fn-sn-prepare tests at :reserved (books/store-node.lisp), with the
; two conditions it computes named: the node binds the record, and the file
; kernel accepts it as the candidate at the frontier the reservation will
; hold, with the extended history replayable.  fn-pcx-admissiblep is the
; same at :ready, over the frontier the four observations will reserve.

(defun fn-pcx-stageablep (s r)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
       (null (fn-node-stage (fn-sn-node s)))
       (fn-held-p r)
       (not (equal (fn-record-stamp r) :legacy))
       (equal (fn-hc-generation (fn-held-context r)) (fn-sn-keyring-generation s))
       (eq (car (fn-cpe-projection-step (fn-sn-consumer s) r (fn-sn-identity-next s))) :ok)
       (fn-sn-record-bindsp (fn-sn-prepare-node (fn-sn-node s) r) r)
       (fn-sf-candidatep r (fn-sf-records (fn-sn-files s)) (fn-sf-frontier (fn-sn-files s)))
       (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                   (append (fn-sf-records (fn-sn-files s)) (list r))
                                   (fn-sf-frontier (fn-sn-files s)))))

(defun fn-pcx-admissiblep (s r)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (let* ((files (fn-sn-files s))
         (frontier (1+ (fn-sf-frontier files))))
    (and (equal (fn-sf-phase files) :ready)
         (< (fn-sf-frontier files) *fn-sf-max-uint*)
         (null (fn-node-stage (fn-sn-node s)))
         (fn-held-p r)
         (not (equal (fn-record-stamp r) :legacy))
         (equal (fn-hc-generation (fn-held-context r)) (fn-sn-keyring-generation s))
         (eq (car (fn-cpe-projection-step (fn-sn-consumer s) r (fn-sn-identity-next s))) :ok)
         (fn-sn-record-bindsp (fn-sn-prepare-node (fn-sn-node s) r) r)
         (fn-sf-candidatep r (fn-sf-records files) frontier)
         (fn-sf-history-recoverablep (fn-sn-groups s) (fn-sn-capacity s)
                                     (append (fn-sf-records files) (list r))
                                     frontier))))

(defthm fn-pcx-admissible-ready
  (implies (fn-pcx-admissiblep s r)
           (and (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*)))
  :hints (("Goal" :in-theory (enable fn-pcx-admissiblep))))

(defthm fn-pcx-admissible-held
  (implies (fn-pcx-admissiblep s r) (fn-held-p r))
  :hints (("Goal" :in-theory (e/d (fn-pcx-admissiblep) (fn-held-p)))))

; -----------------------------------------------------------------------------
; 3. One primitive completion at a time.  Each observation with its
; specified successful answer moves the file kernel's phase and nothing
; else; fn-sn-io is closed (fn-cstp-io-fields, books/config-store-steps.lisp,
; is the fields lemma; fn-sn-io-preserves-state the shape).

(defthm fn-pcx-io-keeps-node-fields
  (let ((s2 (fn-sn-io s operation result)))
    (and (equal (fn-sn-groups s2) (fn-sn-groups s))
         (equal (fn-sn-capacity s2) (fn-sn-capacity s))
         (equal (fn-sn-node s2) (fn-sn-node s))
         (equal (fn-sn-keyring-generation s2) (fn-sn-keyring-generation s))
         (equal (fn-sn-identity-next s2) (fn-sn-identity-next s))
         (equal (fn-sn-consumer s2) (fn-sn-consumer s))
         (equal (fn-sn-topic s2) (fn-sn-topic s))))
  :hints (("Goal" :use (fn-cstp-io-fields) :in-theory (disable fn-sn-io fn-cstp-io-fields))))

(defthm fn-pcx-io-start-frontier
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (let ((s2 (fn-sn-io s :start-frontier nil)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :frontier-staged)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-frontier-candidate (fn-sn-files s2)) (1+ (fn-sf-frontier (fn-sn-files s))))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :start-frontier) (result nil)))
           :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-frontier-file
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :frontier-staged))
           (let ((s2 (fn-sn-io s :frontier-file :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :frontier-data-durable)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-frontier-candidate (fn-sn-files s2)) (fn-sf-frontier-candidate (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :frontier-file) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-frontier-file-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-frontier-replace
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :frontier-data-durable))
           (let ((s2 (fn-sn-io s :frontier-replace :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :frontier-attempted)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-frontier-candidate (fn-sn-files s2)) (fn-sf-frontier-candidate (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :frontier-replace) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-frontier-replace-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-frontier-directory
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :frontier-attempted))
           (let ((s2 (fn-sn-io s :frontier-directory :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :reserved)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier-candidate (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :frontier-directory) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-frontier-dir-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-record-file
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-staged))
           (let ((s2 (fn-sn-io s :record-file :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :record-data-durable)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-record-candidate (fn-sn-files s2)) (fn-sf-record-candidate (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :record-file) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-record-file-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-record-link
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-data-durable))
           (let ((s2 (fn-sn-io s :record-link :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :record-attempted)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-record-candidate (fn-sn-files s2)) (fn-sf-record-candidate (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :record-link) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-record-link-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

(defthm fn-pcx-io-record-directory
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
           (let ((s2 (fn-sn-io s :record-directory :ok)))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :completing)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2))
                         (append (fn-sf-records (fn-sn-files s))
                                 (list (fn-sf-record-candidate (fn-sn-files s)))))
                  (equal (fn-sf-completion (fn-sn-files s2))
                         (fn-sf-record-pair (fn-sf-record-candidate (fn-sn-files s))))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :use (fn-sn-io-preserves-state fn-cstp-sn-statep-files
                        (:instance fn-cstp-io-fields (operation :record-directory) (result :ok)))
           :in-theory (e/d (fn-sn-file-step fn-sf-record-dir-result)
                           (fn-sn-io fn-sn-statep fn-sf-statep fn-sn-io-preserves-state fn-cstp-io-fields)))))

; The prepare ACL2 decided: fn-sn-prepare stages exactly the stageable
; record (fn-opc-owner-prepare-equals-owner-store-step-under-relation names
; it as the host's fn-opc-prepare; fn-sbud-prepare-below-budget-is-the-owner-
; prepare and fn-psrv-prepare-when-served carry the budget and the served
; test to it, books/owner-store-budget.lisp, books/owner-prepare-served.lisp).
(defthm fn-pcx-prepare-step-fields
  (implies (and (fn-sn-statep s) (fn-pcx-stageablep s r))
           (let ((s2 (fn-sn-prepare s r)))
             (and (equal (fn-sf-phase (fn-sn-files s2)) :record-staged)
                  (equal (fn-sf-record-candidate (fn-sn-files s2)) r)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s2)) (fn-sf-barriers (fn-sn-files s)))
                  (equal (fn-sn-node s2) (fn-sn-prepare-node (fn-sn-node s) r))
                  (equal (fn-sn-groups s2) (fn-sn-groups s))
                  (equal (fn-sn-capacity s2) (fn-sn-capacity s))
                  (equal (fn-sn-keyring-generation s2) (fn-sn-keyring-generation s))
                  (equal (fn-sn-identity-next s2) (fn-sn-identity-next s))
                  (equal (fn-sn-consumer s2) (fn-sn-consumer s))
                  (equal (fn-sn-topic s2) (fn-sn-topic s)))))
  :hints (("Goal" :use (fn-cstp-sn-statep-files)
           :in-theory (e/d (fn-sn-prepare fn-sf-prepare-record fn-pcx-stageablep)
                           (fn-sn-statep fn-sf-statep fn-sf-candidatep
                            fn-sf-history-recoverablep fn-sn-record-bindsp fn-sn-prepare-node
                            fn-cpe-projection-step fn-held-p)))))

(defthm fn-pcx-prepare-step-statep
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare s r)))
  :hints (("Goal" :use (fn-sn-prepare-preserves-state) :in-theory (disable fn-sn-prepare fn-sn-statep))))

; -----------------------------------------------------------------------------
; 4. The Store's part of the productive theorem.  fn-cstp-io-fields is
; disabled in every composition below: enabled, it rewrites the files of an
; io step to fn-sn-file-step before the per-step rules above can read them.

(defthm fn-pcx-frontier-run
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (< (fn-sf-frontier (fn-sn-files s)) *fn-sf-max-uint*))
           (let ((s4 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil) :frontier-file :ok)
                                         :frontier-replace :ok)
                               :frontier-directory :ok)))
             (and (fn-sn-statep s4)
                  (equal (fn-sf-phase (fn-sn-files s4)) :reserved)
                  (equal (fn-sf-frontier (fn-sn-files s4)) (1+ (fn-sf-frontier (fn-sn-files s))))
                  (equal (fn-sf-records (fn-sn-files s4)) (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sf-successes (fn-sn-files s4)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sf-barriers (fn-sn-files s4)) (fn-sf-barriers (fn-sn-files s))))))
  :hints (("Goal" :in-theory (disable fn-sn-io fn-sn-statep fn-sf-statep fn-cstp-io-fields))))

(defthm fn-pcx-admissible-is-stageable-after-frontier
  (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r))
           (fn-pcx-stageablep (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil) :frontier-file :ok)
                                                  :frontier-replace :ok)
                                        :frontier-directory :ok)
                              r))
  :hints (("Goal" :in-theory (e/d (fn-pcx-stageablep fn-pcx-admissiblep)
                                  (fn-sn-io fn-sn-statep fn-sf-statep fn-sf-candidatep fn-cstp-io-fields
                                   fn-sf-history-recoverablep fn-sn-record-bindsp fn-sn-prepare-node
                                   fn-cpe-projection-step fn-held-p)))))

; KEYSTONE (store).  From :ready, an admissible record and the eight
; specified answers reach :completing with that record as the completion
; record, appended to the history, the successes untouched (nothing is
; acknowledged before the finish), the node the prepared node.
(defthm fn-pcx-store-run-fields
  (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r))
           (let ((s2 (fn-snrt-run s (fn-pcx-store-script (list :prepare r)))))
             (and (fn-sn-statep s2)
                  (equal (fn-sf-phase (fn-sn-files s2)) :completing)
                  (equal (fn-sf-frontier (fn-sn-files s2)) (1+ (fn-sf-frontier (fn-sn-files s))))
                  (equal (fn-sf-records (fn-sn-files s2))
                         (append (fn-sf-records (fn-sn-files s)) (list r)))
                  (equal (fn-sf-completion (fn-sn-files s2)) (fn-sf-record-pair r))
                  (equal (fn-sn-completion-record s2) r)
                  (equal (fn-sf-successes (fn-sn-files s2)) (fn-sf-successes (fn-sn-files s)))
                  (equal (fn-sn-node s2) (fn-sn-prepare-node (fn-sn-node s) r))
                  (equal (fn-sn-keyring-generation s2) (fn-sn-keyring-generation s))
                  (equal (fn-sn-identity-next s2) (fn-sn-identity-next s))
                  (equal (fn-sn-consumer s2) (fn-sn-consumer s))
                  (equal (fn-sn-topic s2) (fn-sn-topic s)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-pcx-admissible-is-stageable-after-frontier
                        (:instance fn-cstp-completion-record-after-dir
                                   (s (fn-sn-io (fn-sn-io (fn-sn-prepare
                                                           (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                                                                         :frontier-file :ok)
                                                                               :frontier-replace :ok)
                                                                     :frontier-directory :ok)
                                                           r)
                                                          :record-file :ok)
                                                :record-link :ok))))
           :in-theory (e/d (fn-snrt-run fn-snrt-step fn-snt-step fn-pcx-store-script
                                   fn-pcx-frontier-events fn-pcx-record-events)
                                  (fn-sn-io fn-sn-prepare fn-sn-statep fn-sf-statep fn-sf-candidatep
                                   fn-cstp-io-fields fn-pcx-stageablep fn-pcx-admissiblep
                                   fn-pcx-admissible-is-stageable-after-frontier fn-cstp-completion-record-after-dir
                                   fn-sf-history-recoverablep fn-sn-record-bindsp fn-sn-prepare-node
                                   fn-cpe-projection-step fn-held-p fn-sn-completion-record
                                   fn-sf-record-pair)))))

; The completion gate holds there: the node binds the prepared record under
; the generation in force, the consumer projection and the topic prefix
; accept it (the topic condition is the one fn-sn-prepare does not test and
; fn-sn-completion-enabledp does; it is a hypothesis, named).
(defthm fn-pcx-store-run-completion-enabled
  (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r)
                (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) r)) :ok))
           (fn-sn-completion-enabledp (fn-snrt-run s (fn-pcx-store-script (list :prepare r)))))
  :hints (("Goal" :use (fn-pcx-store-run-fields)
           :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp fn-pcx-admissiblep)
                           (fn-snrt-run fn-sn-statep fn-sf-statep fn-sf-candidatep fn-sn-prepare-node
                            fn-sf-history-recoverablep fn-sn-record-bindsp fn-cpe-projection-step
                            fn-held-p fn-sn-completion-record fn-sf-record-pair fn-th-prefix-step fn-th-at
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-hstxa-p fn-cpe-eventp
                            fn-th-topic-eventp fn-replay-apply-record fn-replay-apply-retention-event
                            fn-replay-identity-step fn-sn-identity-context)))))

; -----------------------------------------------------------------------------
; 5. The owner's part: a (:store E) step is the Store's step with every
; other owner field kept; (:complete) is fn-own-complete.

(defthm fn-pcx-own-store-step-fields
  (let ((o2 (fn-own-step o (list :store ev) fn-arena)))
    (and (equal (fn-own-store o2) (fn-snrt-step (fn-own-store o) ev))
         (equal (fn-own-conns o2) (fn-own-conns o))
         (equal (fn-own-inflight o2) (fn-own-inflight o))
         (equal (fn-own-ledger o2) (fn-own-ledger o))
         (equal (fn-own-pending o2) (fn-own-pending o))
         (equal (fn-own-clock o2) (fn-own-clock o))
         (equal (fn-own-config o2) (fn-own-config o))
         (equal (fn-own-queue o2) (fn-own-queue o))
         (equal (fn-own-next-id o2) (fn-own-next-id o))
         (equal (fn-own-max-conns o2) (fn-own-max-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-store-step fn-own-refresh-keeps-fields)
                                  (fn-snrt-step fn-sn-statep fn-own-refresh)))))

(defthm fn-pcx-own-store-step-node-secret
  (equal (fn-own-node-secret (fn-own-step o (list :store ev) fn-arena)) (fn-own-node-secret o))
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-store-step fn-own-refresh)
                                  (fn-snrt-step fn-sn-statep fn-own-store-idlep)))))

(defthm fn-pcx-own-complete-step
  (equal (fn-own-step o (list :complete) fn-arena) (fn-own-complete o))
  :hints (("Goal" :in-theory (e/d (fn-own-step) (fn-own-complete)))))

(defthm fn-pcx-own-run-store
  (let ((o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))
    (and (equal (fn-own-store o8) (fn-snrt-run (fn-own-store o) (fn-pcx-store-script (list :prepare r))))
         (equal (fn-own-conns o8) (fn-own-conns o))
         (equal (fn-own-inflight o8) (fn-own-inflight o))
         (equal (fn-own-ledger o8) (fn-own-ledger o))
         (equal (fn-own-pending o8) (fn-own-pending o))
         (equal (fn-own-clock o8) (fn-own-clock o))
         (equal (fn-own-config o8) (fn-own-config o))
         (equal (fn-own-queue o8) (fn-own-queue o))
         (equal (fn-own-next-id o8) (fn-own-next-id o))
         (equal (fn-own-max-conns o8) (fn-own-max-conns o))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-run fn-pcx-wrap-store fn-pcx-store-script fn-snrt-run
                                   fn-pcx-frontier-events fn-pcx-record-events)
                                  (fn-snrt-step fn-own-step fn-sn-statep)))))

(defthm fn-pcx-own-run-store-node-secret
  (equal (fn-own-node-secret (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))
         (fn-own-node-secret o))
  :hints (("Goal" :in-theory (e/d (fn-own-run fn-pcx-wrap-store fn-pcx-store-script
                                   fn-pcx-frontier-events fn-pcx-record-events)
                                  (fn-snrt-step fn-own-step fn-sn-statep)))))

(defthm fn-pcx-post-run-is-complete-of-store-run
  (equal (fn-own-run o (fn-pcx-post-script p) fn-arena)
         (fn-own-complete (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script p)) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-pcx-post-script fn-own-run fn-pcx-wrap-store fn-pcx-store-script
                                   fn-pcx-frontier-events fn-pcx-record-events)
                                  (fn-own-step fn-own-complete fn-pcx-own-store-step-fields
                                   fn-pcx-own-store-step-node-secret)))))

; The host's finish word (fn-own-finish, books/owner-served-invariants.lisp;
; host/owner-host.lisp fn-ccar-own-finish) is :durable exactly when the
; completion is enabled and the completed row names the submission through
; the arena.  Here the row is the admitted record, so the word is :durable
; when the record's Message-ID and payload -- read through fn-row-wire-of,
; never the handle -- are the submission's.  The regression's shape (the
; handle compared against the staged octets) fails this theorem: its word
; is :fault (tests/acl2/productive-contract-tests.lisp, the mutant).
(defthm fn-pcx-post-finish-word
  (let* ((s (fn-own-store o))
         (o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))
         (sub (fn-own-inflight o))
         (w (fn-row-wire-of r fn-arena)))
    (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r)
                  (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) r)) :ok)
                  sub
                  (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
                  (equal (fn-record-payload w) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o))))
             (and (equal (car (fn-own-finish o8 cfg fn-arena)) :durable)
                  (equal (cdr (fn-own-finish o8 cfg fn-arena)) (fn-own-complete o8))
                  (fn-sn-completion-enabledp (fn-own-store o8))
                  (equal (fn-sn-completion-record (fn-own-store o8)) r)
                  (equal (fn-sf-completion (fn-sn-files (fn-own-store o8))) (fn-sf-record-pair r)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-pcx-own-run-store fn-pcx-own-run-store-node-secret
                        (:instance fn-pcx-store-run-fields (s (fn-own-store o)))
                        (:instance fn-pcx-store-run-completion-enabled (s (fn-own-store o)))
                        (:instance fn-pcx-admissible-held (s (fn-own-store o))))
           :in-theory (e/d (fn-own-finish fn-own-completion-names-submission-p)
                           (fn-own-run fn-snrt-run fn-sn-statep fn-sf-statep fn-sf-candidatep fn-sn-prepare-node
                            fn-pcx-admissiblep fn-pcx-admissible-held fn-record-octets-string fn-record-msgid fn-record-payload
                            fn-own-sub-msgid fn-own-inflight fn-pcx-own-run-store-node-secret
                            fn-sf-history-recoverablep fn-sn-record-bindsp fn-cpe-projection-step
                            fn-held-p fn-sn-completion-record fn-sf-record-pair fn-th-prefix-step fn-th-at
                            fn-sn-completion-enabledp fn-own-complete fn-row-wire-of fn-own-sub-stored-octets
                            fn-own-node-secret fn-pcx-store-run-completion-enabled)))))

(local
 (defthm fn-pcx-member-of-append-last
   (member-equal x (append l (list x)))
   :hints (("Goal" :induct (len l) :in-theory (enable member-equal append)))))

(local
 (defthm fn-pcx-len-of-append-last
   (equal (len (append l (list x))) (+ 1 (len l)))
   :hints (("Goal" :induct (len l) :in-theory (enable append len)))))

(local
 (defthm fn-pcx-consumed-from-ledger
   (implies (and (fn-own-inflight o9)
                 (natp (fn-own-sub-mark (fn-own-inflight o9)))
                 (<= (fn-own-sub-mark (fn-own-inflight o9)) (len l))
                 (equal (fn-own-ledger o9) (append l (list p))))
            (fn-own-completion-consumedp o9))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pcx-len-of-append-last (x p)))
            :in-theory (e/d (fn-own-completion-consumedp)
                            (fn-own-ledger fn-own-inflight fn-own-sub-mark fn-own-ledger-count
                             fn-pcx-len-of-append-last append len))))))

; KEYSTONE (PRF-1001).  THE PRODUCTIVE COUNTERPART of
; fn-own-240-follows-consumed-completion.  An owner whose Store admits the
; record R (fn-pcx-admissiblep: the contract's validity and funding at this
; Store, specs/productive-contract.md section 2) and whose topic prefix
; accepts it, with connection ID's submission in flight (the authorization
; the served read decided before the take, fn-auth-postingp) whose ledger
; mark is at most the ledger's length (what :take sets), and with R naming
; that submission through the arena: the nine specified steps of
; fn-own-step -- *fn-pcx-post-steps* -- make the host's finish word :durable
; and the completion consumed; the ledger and the Store's successes each
; gain exactly R's pair; R is in the durable history; and the outcome the
; host renders for ID is fn-served-post-outcome's :durable effects, the 240
; line (books/productive-observer.lisp says what those octets are).
(defthm fn-pcx-post-productive
  (let* ((s (fn-own-store o))
         (sub (fn-own-inflight o))
         (w (fn-row-wire-of r fn-arena))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (o8 (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))
         (o9 (fn-own-run o (fn-pcx-post-script (list :prepare r)) fn-arena))
         (pair (fn-sf-record-pair r))
         (out (fn-own-outcome o9 id :durable)))
    (implies (and (fn-sn-statep s) (fn-pcx-admissiblep s r)
                  (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) r)) :ok)
                  sub (equal (fn-own-sub-id sub) id) conn
                  (natp (fn-own-sub-mark sub))
                  (<= (fn-own-sub-mark sub) (len (fn-own-ledger o)))
                  (equal (fn-record-msgid w) (fn-record-octets-string (fn-own-sub-msgid sub)))
                  (equal (fn-record-payload w) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o))))
             (and (equal (len (fn-pcx-post-script (list :prepare r))) *fn-pcx-post-steps*)
                  (equal (car (fn-own-finish o8 cfg fn-arena)) :durable)
                  (equal o9 (cdr (fn-own-finish o8 cfg fn-arena)))
                  (fn-own-completion-consumedp o9)
                  (equal (fn-own-ledger o9) (append (fn-own-ledger o) (list pair)))
                  (equal (fn-sf-successes (fn-sn-files (fn-own-store o9)))
                         (append (fn-sf-successes (fn-sn-files s)) (list pair)))
                  (member-equal r (fn-sf-records (fn-sn-files (fn-own-store o9))))
                  (equal (car out)
                         (fn-served-result-effects
                          (fn-served-post-outcome
                           (fn-served-make-conn-group-indexed
                            (fn-own-conn-wire conn) (fn-own-conn-session conn)
                            (fn-own-conn-archive conn) (fn-own-conn-config conn)
                            (fn-own-conn-observation conn) (fn-own-clock o)
                            (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
                            (fn-own-conn-group-index conn) (fn-own-conn-control conn))
                           :durable))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-pcx-post-finish-word fn-pcx-own-run-store
                 (:instance fn-pcx-post-script-length (prepare (list :prepare r)))
                 (:instance fn-pcx-post-run-is-complete-of-store-run (p (list :prepare r)))
                 (:instance fn-pcx-store-run-fields (s (fn-own-store o)))
                 (:instance fn-pcx-member-of-append-last (x r) (l (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-pcx-consumed-from-ledger (l (fn-own-ledger o)) (p (fn-sf-record-pair r))
                            (o9 (fn-own-complete (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))))
                 (:instance fn-own-complete-ledger-is-exact-pair
                            (o (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))
                 (:instance fn-own-complete-keeps-every-connection
                            (o (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))
                 (:instance fn-sn-finish-acknowledges-exact-pair
                            (s (fn-own-store (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena))))
                 (:instance fn-snt-finish-keeps-records
                            (s (fn-own-store (fn-own-run o (fn-pcx-wrap-store (fn-pcx-store-script (list :prepare r))) fn-arena)))))
           :in-theory (e/d (fn-own-outcome fn-own-outcome-completion fn-own-durable-wordp
                            fn-own-post-rendering fn-own-outcome-rendering)
                           (fn-own-run fn-own-step fn-own-complete fn-own-finish fn-snrt-run fn-snrt-step fn-sn-finish
                            fn-pcx-post-script fn-pcx-wrap-store fn-pcx-store-script fn-pcx-post-script-length
                            fn-pcx-post-run-is-complete-of-store-run fn-own-completion-consumedp
                            fn-own-find-conn fn-served-post-outcome fn-served-result-effects
                            fn-served-make-conn-group-indexed fn-own-feed-durable fn-own-advance
                            fn-sn-statep fn-sf-statep fn-pcx-admissiblep fn-sn-completion-enabledp
                            fn-sn-completion-record fn-sf-record-pair fn-row-wire-of fn-own-sub-stored-octets
                            fn-own-node-secret fn-th-prefix-step fn-th-at fn-own-refusal-wordp
                            fn-record-octets-string fn-record-msgid fn-record-payload fn-own-sub-msgid
                            fn-own-inflight fn-own-sub-mark fn-own-sub-id fn-own-ledger fn-own-make
                            fn-pcx-member-of-append-last fn-pcx-len-of-append-last member-equal len append
                            fn-own-complete-ledger-is-exact-pair fn-own-complete-keeps-every-connection
                            fn-sn-finish-acknowledges-exact-pair fn-snt-finish-keeps-records
                            fn-own-ledger-count fn-pcx-own-store-step-fields fn-pcx-own-complete-step)))))

; -----------------------------------------------------------------------------
; 6. THE UNCERTAINTY JUSTIFICATION (PRF-1002).  fn-own-outcome-completion
; (books/owner.lisp) answers :uncertain in two situations, and each is a
; named unresolved effect in the owner's own state, never the host's word
; alone: the completion was consumed but the host's word is not a durable
; one (an effect after publication failed -- the OS error raised after
; publication, campaign W2; what is lost is the reply, the record stands);
; or no completion was consumed after the take and the word names no
; refusal (the completion is outstanding: the host's :durable claim is
; unconfirmed, or its :fault stopped the sequence before the completion
; was delivered).  fn-own-transit-outcome (IHAVE/TAKETHIS, kind :want)
; renders the same function, so its uncertain has the same two causes.

(defun fn-pcx-uncertain-cause (o word)
  (declare (xargs :guard t))
  (cond ((and (fn-own-completion-consumedp o)
              (not (fn-own-durable-wordp word)))
         :effect-failed-after-publication)
        ((and (not (fn-own-completion-consumedp o))
              (not (fn-own-refusal-wordp word))
              (not (equal word :clock-unusable)))
         :completion-outstanding)
        (t nil)))

; KEYSTONE.  Uncertain if and only if one of the two named causes holds:
; no uncertain outcome is an escape without a cause, and a cause is never
; reported for a durable, refused or clock-refused outcome.
(defthm fn-pcx-uncertain-has-a-named-cause
  (iff (equal (fn-own-outcome-completion o word) :uncertain)
       (member-equal (fn-pcx-uncertain-cause o word)
                     '(:effect-failed-after-publication :completion-outstanding)))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome-completion fn-pcx-uncertain-cause fn-own-durable-wordp)
                                  (fn-own-completion-consumedp fn-own-refusal-wordp)))))

(in-theory (disable fn-pcx-uncertain-cause fn-pcx-admissiblep fn-pcx-stageablep))
