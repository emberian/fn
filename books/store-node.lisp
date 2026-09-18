; fn: executable binding of live node transactions to the file kernel.
(in-package "ACL2")
(include-book "store-files")

; Fixed configuration accompanies the file machine and the actual live node.
; No transition accepts a replacement configuration or a host 'matching' reply.
(defun fn-sn-groups (s) (car s))
(defun fn-sn-capacity (s) (cadr s))
(defun fn-sn-files (s) (caddr s))
(defun fn-sn-node (s) (cadddr s))
(defun fn-sn-make (groups capacity files node)
  (list groups capacity files node))
(defun fn-sn-statep (s)
  (and (true-listp s) (equal (len s) 4)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-sf-statep (fn-sn-files s))
       (fn-node-statep (fn-sn-node s))))
(defun fn-sn-initial (groups capacity)
  (fn-sn-make groups capacity (fn-sf-initial-state)
              (fn-node-initial-state groups capacity)))
(defun fn-sn-update (s files node)
  (fn-sn-make (fn-sn-groups s) (fn-sn-capacity s) files node))

; The record is derived from the real pending proposal, including its retention
; stage, instead of a second host interpretation of the submission.
(defun fn-sn-pending-record (node sequence)
  (let ((pending (fn-state-pending (fn-node-acceptance node)))
        (stage (fn-node-stage node)))
    (fn-record-make sequence (fn-pending-txid pending)
                    (fn-pending-generation pending)
                    (fn-pending-msgid pending) (fn-pending-payload pending)
                    (fn-pending-groups pending) (fn-node-stage-id stage)
                    (fn-node-stage-subject stage) (fn-node-stage-evidence stage)
                    (fn-node-stage-charge stage))))
(defun fn-sn-record-bindsp (node record)
  (and (fn-record-p record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(defun fn-sn-prepare-node (node record)
  (fn-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                   (fn-record-generation record) (fn-record-msgid record)
                   (fn-record-payload record) (fn-record-groups record)
                   (fn-record-obligation-id record)
                   (fn-record-content-subject record)
                   (fn-record-release-evidence record) (fn-record-charge record)))

; Pure preparation: a failed gate publishes neither the speculative node nor
; record.  The durable reservation stays available until refusal/abort/recovery.
(defun fn-sn-prepare (s record)
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

(defun fn-sn-find-record (pair records)
  (if (consp records)
      (if (equal pair (fn-sf-record-pair (car records)))
          (car records)
        (fn-sn-find-record pair (cdr records)))
    nil))
(defun fn-sn-completion-record (s)
  (fn-sn-find-record (fn-sf-completion (fn-sn-files s))
                     (fn-sf-records (fn-sn-files s))))
(defun fn-sn-completion-enabledp (s)
  (and (fn-sn-statep s)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
       (equal (fn-sf-completion (fn-sn-files s))
              (fn-sf-record-pair (fn-sn-completion-record s)))))

; One logical completion operation.  Success is recorded only after calling
; the actual matching durable node branch; there is no externally supplied
; completion status.  The filesystem durability observation remains the file
; kernel's record-directory result, under its documented platform assumptions.
(defun fn-sn-finish (s)
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

; The I/O surface cannot inject a core-completion observation or emit success.
(defun fn-sn-file-step (files operation result)
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
(defun fn-sn-io (s operation result)
  (if (fn-sn-statep s)
      (fn-sn-update s (fn-sn-file-step (fn-sn-files s) operation result)
                    (fn-sn-node s))
    s))

; A crash discards the live process view.  Recovery reconstructs a new node
; through the existing replay interpreter, whose individual records call the
; same actual fn-node-prepare/fn-node-complete pair used above.
(defun fn-sn-crash (s frontier-choice record-choice)
  (if (and (fn-sn-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      (fn-sn-update s (fn-sf-crash (fn-sn-files s) frontier-choice record-choice)
                    (fn-node-initial-state (fn-sn-groups s) (fn-sn-capacity s)))
    s))
(defun fn-sn-recover (s)
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

; In-process uncertain completion can also be resolved through the actual node
; recovery primitive.  These helpers expose no new acceptance implementation.
(defun fn-sn-fence-node (node record)
  (fn-node-complete node (fn-record-txid record)
                    (fn-record-generation record) :indeterminate))
(defun fn-sn-resolve-node (node record committedp)
  (fn-node-recover node (fn-record-txid record) (fn-record-generation record)
                   (if committedp :committed :absent)))
