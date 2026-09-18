; fn: executable binding of live node transactions to the file kernel.
(in-package "ACL2")
(include-book "store-files")

; Fixed configuration accompanies the file machine and the actual live node.
; No transition accepts a replacement configuration or a host 'matching' reply.
; Total MBE selectors preserve the original ACL2 values on malformed inputs.
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
  (declare (xargs :guard t :verify-guards nil))
  (list groups capacity files node))

(verify-guards fn-sn-make)
(defun fn-sn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp s) (equal (len s) 4)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-sf-statep (fn-sn-files s))
       (fn-node-statep (fn-sn-node s))))

(verify-guards fn-sn-statep)
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
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-record-p record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(verify-guards fn-sn-record-bindsp)

; Proper-list record helpers retain their original logical bodies.  Public
; preparation/completion gates establish the stronger fn-record-p condition.
(defun fn-sn-prepare-node (node record)
  (declare (xargs :guard (true-listp record) :verify-guards nil))
  (fn-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                   (fn-record-generation record) (fn-record-msgid record)
                   (fn-record-payload record) (fn-record-groups record)
                   (fn-record-obligation-id record)
                   (fn-record-content-subject record)
                   (fn-record-release-evidence record) (fn-record-charge record)))

(verify-guards fn-sn-prepare-node)

; Pure preparation: a failed gate publishes neither the speculative node nor
; record.  The durable reservation stays available until refusal/abort/recovery.
(defun fn-sn-prepare (s record)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sn-statep s)
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
           (disable fn-sn-statep fn-sf-statep fn-node-statep
                    fn-node-pending-matchesp
                    fn-sn-pending-record fn-sn-prepare-node))))

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
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-statep s)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
       (equal (fn-sf-completion (fn-sn-files s))
              (fn-sf-record-pair (fn-sn-completion-record s)))))

(verify-guards fn-sn-completion-enabledp)

; One logical completion operation.  Success is recorded only after calling
; the actual matching durable node branch; there is no externally supplied
; completion status.  The filesystem durability observation remains the file
; kernel's record-directory result, under its documented platform assumptions.
(defun fn-sn-finish (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sn-completion-enabledp s)
      (let* ((record (fn-sn-completion-record s))
             (node (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                     (fn-record-generation record) :durable))
             (files (fn-sf-core-completion
                     (fn-sn-files s) (fn-record-sequence record)
                     (fn-record-txid record) :matching)))
        (fn-sn-update s
                      (fn-sf-emit-success files (fn-record-sequence record)
                                           (fn-record-txid record))
                      node))
    s))

(verify-guards fn-sn-finish
  :hints (("Goal" :in-theory
           (disable fn-sn-statep fn-sf-statep fn-node-statep
                    fn-sn-completion-record fn-node-pending-matchesp
                    fn-sn-pending-record fn-sn-prepare-node))))

; The I/O surface cannot inject a core-completion observation or emit success.
(defun fn-sn-file-step (files operation result)
  (declare (xargs :guard t :verify-guards nil))
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
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sn-statep s)
      (fn-sn-update s (fn-sn-file-step (fn-sn-files s) operation result)
                    (fn-sn-node s))
    s))

(verify-guards fn-sn-io)

; A crash discards the live process view.  Recovery reconstructs a new node
; through the existing replay interpreter, whose individual records call the
; same actual fn-node-prepare/fn-node-complete pair used above.
(defun fn-sn-crash (s frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sn-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      (fn-sn-update s (fn-sf-crash (fn-sn-files s) frontier-choice record-choice)
                    (fn-node-initial-state (fn-sn-groups s) (fn-sn-capacity s)))
    s))

(verify-guards fn-sn-crash)
(defun fn-sn-recover (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sn-statep s)
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

(verify-guards fn-sn-recover)

; In-process uncertain completion can also be resolved through the actual node
; recovery primitive.  These helpers expose no new acceptance implementation.
(defun fn-sn-fence-node (node record)
  (declare (xargs :guard (true-listp record) :verify-guards nil))
  (fn-node-complete node (fn-record-txid record)
                    (fn-record-generation record) :indeterminate))

(verify-guards fn-sn-fence-node)
(defun fn-sn-resolve-node (node record committedp)
  (declare (xargs :guard (true-listp record) :verify-guards nil))
  (fn-node-recover node (fn-record-txid record) (fn-record-generation record)
                   (if committedp :committed :absent)))

(verify-guards fn-sn-resolve-node)
