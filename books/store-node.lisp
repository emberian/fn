; fn: executable binding of live node transactions to the file kernel.
(in-package "ACL2")
; store-files-invariants is included because the kernel preservation
; keystones are this book's guard proofs: fn-sn-finish calls
; fn-sf-emit-success on the result of fn-sf-core-completion, and
; fn-sf-core-completion-preserves-state discharges that guard.
(include-book "store-files-invariants")

; Fixed configuration accompanies the file machine and the actual live node.
; No transition accepts a replacement configuration or a host 'matching' reply.
; Total MBE selectors preserve the original ACL2 values on malformed inputs.
; The composed record is opaque below its lemmas (docs/proof-style.md s1).
; Layout: (groups capacity files node)
(defun fn-sn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))

(defun fn-sn-groups (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car s)
       :exec (fn-ag-car s)))

(verify-guards fn-sn-groups)
(defun fn-sn-capacity (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr s)
       :exec (fn-ag-car (fn-ag-cdr s))))

(verify-guards fn-sn-capacity)
(defun fn-sn-files (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))

(verify-guards fn-sn-files)
(defun fn-sn-node (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(verify-guards fn-sn-node)
(defun fn-sn-make (groups capacity files node)
  (declare (xargs :guard t))
  (list groups capacity files node))

(defthm fn-sn-shapep-of-fn-sn-make
  (fn-sn-shapep (fn-sn-make groups capacity files node)))
(defthm fn-sn-groups-of-fn-sn-make
  (equal (fn-sn-groups (fn-sn-make groups capacity files node)) groups))
(defthm fn-sn-capacity-of-fn-sn-make
  (equal (fn-sn-capacity (fn-sn-make groups capacity files node)) capacity))
(defthm fn-sn-files-of-fn-sn-make
  (equal (fn-sn-files (fn-sn-make groups capacity files node)) files))
(defthm fn-sn-node-of-fn-sn-make
  (equal (fn-sn-node (fn-sn-make groups capacity files node)) node))
(in-theory (disable (:d fn-sn-shapep) (:d fn-sn-groups) (:d fn-sn-capacity)
                    (:d fn-sn-files) (:d fn-sn-node) (:d fn-sn-make)))

; Shape facts type reasoning used to supply while the record opened
; (docs/proof-style.md s1), exported as forward-chaining rules only.
(defthm fn-sn-shapep-forward-shape
  (implies (fn-sn-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-shapep))))
(defthm fn-sn-accessors-forward-consp
  (and (implies (fn-sn-groups x) (consp x))
       (implies (fn-sn-capacity x) (consp x))
       (implies (fn-sn-files x) (consp x))
       (implies (fn-sn-node x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-sn-groups x) (consp x))
                                    :trigger-terms ((fn-sn-groups x)))
                 (:forward-chaining :corollary (implies (fn-sn-capacity x) (consp x))
                                    :trigger-terms ((fn-sn-capacity x)))
                 (:forward-chaining :corollary (implies (fn-sn-files x) (consp x))
                                    :trigger-terms ((fn-sn-files x)))
                 (:forward-chaining :corollary (implies (fn-sn-node x) (consp x))
                                    :trigger-terms ((fn-sn-node x))))
  :hints (("Goal" :in-theory (enable fn-sn-groups fn-sn-capacity fn-sn-files fn-sn-node))))

(defun fn-sn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-shapep s)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-sf-statep (fn-sn-files s))
       (fn-node-statep (fn-sn-node s))))

(verify-guards fn-sn-statep)
(defthm fn-sn-statep-forward-shape
  (implies (fn-sn-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sn-shapep))))
(defun fn-sn-initial (groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make groups capacity (fn-sf-initial-state)
              (fn-node-initial-state groups capacity)))

(verify-guards fn-sn-initial)
(defun fn-sn-update (s files node)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make (fn-sn-groups s) (fn-sn-capacity s) files node))

(verify-guards fn-sn-update)

; The record is derived from the real pending proposal, including its retention
; stage, instead of a second host interpretation of the submission.
(defun fn-sn-pending-record (node sequence)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pending (fn-state-pending (fn-node-acceptance node)))
        (stage (fn-node-stage node)))
    (fn-record-make sequence (fn-pending-txid pending)
                    (fn-pending-generation pending)
                    (fn-pending-msgid pending) (fn-pending-payload pending)
                    (fn-pending-groups pending) (fn-node-stage-id stage)
                    (fn-node-stage-subject stage) (fn-node-stage-evidence stage)
                    (fn-node-stage-charge stage))))

(verify-guards fn-sn-pending-record)
(defun fn-sn-record-bindsp (node record)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (and (fn-record-p record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(verify-guards fn-sn-record-bindsp)

; Proper-list record helpers retain their original logical bodies.  Public
; preparation/completion gates establish the stronger fn-record-p condition.
(defun fn-sn-prepare-node (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                   (fn-record-generation record) (fn-record-msgid record)
                   (fn-record-payload record) (fn-record-groups record)
                   (fn-record-obligation-id record)
                   (fn-record-content-subject record)
                   (fn-record-release-evidence record) (fn-record-charge record)))

(verify-guards fn-sn-prepare-node)

; The guard proof of fn-sn-prepare: the speculative node is a node.
(defthm fn-sn-prepare-node-preserves-state
  (implies (fn-node-statep node)
           (fn-node-statep (fn-sn-prepare-node node record))))

; Pure preparation: a failed gate publishes neither the speculative node nor
; record.  The durable reservation stays available until refusal/abort/recovery.
(defun fn-sn-prepare (s record)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-record-p record))
      (let* ((node (fn-sn-prepare-node (fn-sn-node s) record))
             (files (fn-sf-prepare-record (fn-sn-files s) record
                                          (fn-sn-groups s) (fn-sn-capacity s))))
        (if (and (fn-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(verify-guards fn-sn-prepare
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                 fn-sn-pending-record fn-sn-prepare-node)))))

(defun fn-sn-find-record (pair records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (if (equal pair (fn-sf-record-pair (car records)))
          (car records)
        (fn-sn-find-record pair (cdr records)))
    nil))

(verify-guards fn-sn-find-record)
(defun fn-sn-completion-record (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-find-record (fn-sf-completion (fn-sn-files s))
                     (fn-sf-records (fn-sn-files s))))

(verify-guards fn-sn-completion-record)
(defun fn-sn-completion-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
       (equal (fn-sf-completion (fn-sn-files s))
              (fn-sf-record-pair (fn-sn-completion-record s)))))

(verify-guards fn-sn-completion-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; One logical completion operation.  Success is recorded only after calling
; the actual matching durable node branch; there is no externally supplied
; completion status.  The filesystem durability observation remains the file
; kernel's record-directory result, under its documented platform assumptions.
(defun fn-sn-finish (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-completion-enabledp s)
      (let* ((record (fn-sn-completion-record s))
             (node (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                     (fn-record-generation record) :durable))
             (files (fn-sf-core-completion
                     (fn-sn-files s) (fn-record-sequence record)
                     (fn-record-txid record))))
        (fn-sn-update s
                      (fn-sf-emit-success files (fn-record-sequence record)
                                           (fn-record-txid record))
                      node))
    s))

(verify-guards fn-sn-finish
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-sn-completion-record
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-prepare-node fn-sf-core-completion)))))

; The I/O surface cannot inject a core-completion observation or emit success.
; There is deliberately no :core-completion operation here: the kernel's
; fn-sf-core-completion is reachable only inside fn-sn-finish above, so a host
; word claiming completion is a no-op (fn-sn-io-cannot-acknowledge).
(defun fn-sn-file-step (files operation result)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (case operation
    (:start-frontier (fn-sf-start-frontier files))
    (:frontier-file (fn-sf-frontier-file-result files result))
    (:frontier-replace (fn-sf-frontier-replace-result files result))
    (:frontier-directory (fn-sf-frontier-dir-result files result))
    (:record-file (fn-sf-record-file-result files result))
    (:record-link (fn-sf-record-link-result files result))
    (:record-directory (fn-sf-record-dir-result files result))
    (:recovery-barrier (fn-sf-recovery-barrier files result))
    (otherwise files)))

(verify-guards fn-sn-file-step)
(defun fn-sn-io (s operation result)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (mbe :logic (fn-sn-statep s) :exec t)
      (fn-sn-update s (fn-sn-file-step (fn-sn-files s) operation result)
                    (fn-sn-node s))
    s))

(verify-guards fn-sn-io
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; A crash discards the live process view.  Recovery reconstructs a new node
; through the existing replay interpreter, whose individual records call the
; same actual fn-node-prepare/fn-node-complete pair used above.  The kernel
; crash is one constructor of an admissible image; the host never calls it.
; A real process reopens through fn-sn-open-observed (store-observed.lisp),
; whose theorems take fn-sf-crash-imagep as the platform premise.
(defun fn-sn-crash (s frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sn-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      (fn-sn-update s (fn-sf-crash (fn-sn-files s) frontier-choice record-choice)
                    (fn-node-initial-state (fn-sn-groups s) (fn-sn-capacity s)))
    s))

(verify-guards fn-sn-crash)
(defun fn-sn-recover (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :replaying))
      (let* ((files (fn-sf-recover (fn-sn-files s)
                                   (fn-sn-groups s) (fn-sn-capacity s)))
             (node (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                       (fn-sf-records files)
                                       (fn-sf-frontier files))))
        (fn-sn-update s files
                      (if (equal (fn-sf-phase files) :recovering)
                          node
                        (fn-sn-node s))))
    s))

(verify-guards fn-sn-recover
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; unreachable-in-composition: no host path calls fn-sn-fence-node or
; fn-sn-resolve-node (host/store-node-host.lisp resolves every uncertainty by
; reopening through fn-sn-open-observed).  They remain as proof notation for
; the in-process resolution correspondence and because other books name them
; in theory lists; they are not evidence for any host claim.
(defun fn-sn-fence-node (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-complete node (fn-record-txid record)
                    (fn-record-generation record) :indeterminate))

(verify-guards fn-sn-fence-node)
(defun fn-sn-resolve-node (node record committedp)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-recover node (fn-record-txid record) (fn-record-generation record)
                   (if committedp :committed :absent)))

(verify-guards fn-sn-resolve-node)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md s2).  Enabled on include: the record
; lemmas, fn-sn-update and fn-sn-find-record (glue and induction vocabulary)
; and fn-sn-prepare-node-preserves-state.  Withdrawn: the recognizer, the
; initial state and every transition; store-node-invariants opens them
; locally.
(in-theory (disable fn-sn-statep fn-sn-initial fn-sn-pending-record
                    fn-sn-record-bindsp fn-sn-prepare-node fn-sn-prepare
                    fn-sn-completion-record fn-sn-completion-enabledp
                    fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                    fn-sn-recover fn-sn-fence-node fn-sn-resolve-node))
