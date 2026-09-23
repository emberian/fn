; Historical configuration/Store correspondence across the file phases.
; This relation is proof vocabulary; no served transition evaluates it.
(in-package "ACL2")
(include-book "config-observed")
(include-book "store-node-traces")

(defun fn-cst-replay-node (configs events frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((replayed (fn-cpr-replay configs events))
         (cn (fn-replay-result-node replayed))
         (node (fn-cnode-node cn)))
    (if (and (equal (fn-replay-result-kind replayed) :ok)
             (fn-cnode-statep cn)
             (fn-replay-advance-okp node frontier))
        (fn-replay-advance-txid node frontier)
      nil)))

(verify-guards fn-cst-replay-node
  :hints (("Goal"
           :use ((:instance fn-cpr-replay-ok-is-configured
                            (configs configs) (events events)))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-loop
                            fn-cpr-replay-ok-is-configured)))))

(defun fn-cst-recoverablep (configs events frontier)
  (declare (xargs :guard t))
  (let ((node (fn-cst-replay-node configs events frontier)))
    (and (consp node)
         (fn-node-statep node)
         (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))))

(defun fn-cst-final-configurationp (st)
  (declare (xargs :guard t))
  (let* ((replayed
          (fn-cpr-replay (fn-sn-config-history st)
                         (fn-sf-records (fn-sn-files st))))
         (cn (fn-replay-result-node replayed)))
    (and (equal (fn-replay-result-kind replayed) :ok)
         (fn-cnode-statep cn)
         (equal (fn-sn-groups st)
                (fn-cnode-domain-of (fn-cnode-config cn)))
         (equal (fn-sn-capacity st)
                (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn)))))))

(defun fn-cst-pending-linkp (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files st))
         (node (fn-sn-node st))
         (configs (fn-sn-config-history st))
         (events (fn-sf-records files))
         (frontier (fn-sf-frontier files))
         (record (fn-sf-record-candidate files)))
    (and (fn-sn-record-bindsp node record)
         (equal (fn-node-complete node (fn-record-txid record)
                                  (fn-record-generation record) :aborted)
                (fn-cst-replay-node configs events frontier))
         (equal (fn-node-complete node (fn-record-txid record)
                                  (fn-record-generation record) :durable)
                (fn-cst-replay-node configs
                                    (append events (list record)) frontier))
         (fn-cst-recoverablep configs
                              (append events (list record)) frontier))))

(defun fn-cst-deferred-linkp (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files st))
         (node (fn-sn-node st))
         (configs (fn-sn-config-history st))
         (events (fn-sf-records files))
         (frontier (fn-sf-frontier files))
         (record (fn-sf-record-candidate files)))
    (and (fn-store-event-p record)
         (posp frontier)
         (fn-cst-recoverablep configs events (1- frontier))
         (equal node (fn-cst-replay-node configs events (1- frontier)))
         (consp (fn-replay-apply-record node record))
         (or (fn-store-retention-event-p record)
             (equal (fn-stxk-context-kind
                     (fn-replay-identity-step
                      (fn-sn-identity-context st) record)) :ok))
         (equal (fn-replay-apply-record node record)
                (fn-cst-replay-node configs
                                    (append events (list record)) frontier))
         (fn-cst-recoverablep configs
                              (append events (list record)) frontier))))

(defun fn-cst-completion-linkp (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files st))
         (node (fn-sn-node st))
         (record (fn-sn-completion-record st))
         (expected (fn-cst-replay-node (fn-sn-config-history st)
                                        (fn-sf-records files)
                                        (fn-sf-frontier files))))
    (if (fn-record-p record)
        (equal (fn-node-complete node (fn-record-txid record)
                                 (fn-record-generation record) :durable)
               expected)
      (equal (fn-replay-apply-record node record) expected))))

(defun fn-cst-relation (st)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((files (fn-sn-files st))
         (node (fn-sn-node st))
         (configs (fn-sn-config-history st))
         (events (fn-sf-records files))
         (frontier (fn-sf-frontier files))
         (phase (fn-sf-phase files)))
    (and (fn-sn-statep st)
         (true-listp configs)
         (fn-sn-observed-historyp frontier events)
         (fn-cst-final-configurationp st)
         (fn-cst-recoverablep configs events frontier)
         (cond
          ((fn-snt-idle-phasep phase)
           (equal node (fn-cst-replay-node configs events frontier)))
          ((equal phase :reserved)
           (and (posp frontier)
                (fn-cst-recoverablep configs events (1- frontier))
                (equal node (fn-cst-replay-node configs events
                                                (1- frontier)))))
          ((fn-sf-record-phasep phase)
           (if (fn-record-p (fn-sf-record-candidate files))
               (fn-cst-pending-linkp st)
             (fn-cst-deferred-linkp st)))
          ((equal phase :completing)
           (and (fn-sn-completion-enabledp st)
                (fn-cst-completion-linkp st)))
          ((or (equal phase :replaying) (equal phase :fault))
           (equal node (fn-node-initial-state
                        (fn-sn-groups st) (fn-sn-capacity st))))
          (t nil)))))

(deftheory fn-cst-vocabulary
  '(fn-cst-replay-node fn-cst-recoverablep fn-cst-final-configurationp
    fn-cst-pending-linkp fn-cst-deferred-linkp fn-cst-completion-linkp
    fn-cst-relation))
(in-theory (disable fn-cst-vocabulary))
