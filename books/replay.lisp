; fn M1 pure replay of validated committed records into the composite node.
;
; Records arrive here only after their byte framing/integrity boundary has
; selected a complete candidate.  This book does not model a disk, signatures,
; or power-failure behavior.  A replay fault is fail-closed: its saved node is
; diagnostic last-good-prefix state, never authority to continue recovery.

(in-package "ACL2")
(include-book "node")
(include-book "records")

; -----------------------------------------------------------------------------
; Result records

; Result accessors preserve ACL2 total selector semantics even for atoms and
; dotted inputs; MBE guard verification proves the safe execution identical.
; Success: (:ok node next-journal-sequence)
; Fault:   (:fault last-good-node expected-journal-sequence reason)
(defun fn-replay-result-kind (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x)
       :exec (fn-ag-car x)))

(verify-guards fn-replay-result-kind)
(defun fn-replay-result-node (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x))
       :exec (fn-ag-car (fn-ag-cdr x))))

(verify-guards fn-replay-result-node)
(defun fn-replay-result-sequence (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(verify-guards fn-replay-result-sequence)
(defun fn-replay-result-reason (x) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(verify-guards fn-replay-result-reason)

(defun fn-replay-ok (node next-sequence)
  (declare (xargs :guard t :verify-guards nil))
  (list :ok node next-sequence))

(verify-guards fn-replay-ok)

(defun fn-replay-fault (node expected-sequence reason)
  (declare (xargs :guard t :verify-guards nil))
  (list :fault node expected-sequence reason))

(verify-guards fn-replay-fault)

(defun fn-replay-okp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 3)
       (equal (fn-replay-result-kind x) :ok)
       (fn-node-statep (fn-replay-result-node x))
       (natp (fn-replay-result-sequence x))))

(verify-guards fn-replay-okp)

(defun fn-replay-faultp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp x) (equal (len x) 4)
       (equal (fn-replay-result-kind x) :fault)
       (fn-node-statep (fn-replay-result-node x))
       (natp (fn-replay-result-sequence x))))

(verify-guards fn-replay-faultp)

; -----------------------------------------------------------------------------
; Explicit reconstruction of txids consumed by known-aborted transactions.

; Journal sequence is contiguous, while acceptance transaction IDs may have
; known-aborted gaps.  This helper advances an idle, unfenced node only forward
; to the next committed record's txid.  It changes no article, retention pin,
; binding, group watermark, or capacity accounting.
(defun fn-replay-advance-txid (node recorded-txid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((acceptance (fn-node-acceptance node)))
    (if (and (fn-node-statep node)
             (natp recorded-txid)
             (null (fn-node-stage node))
             (null (fn-state-pending acceptance))
             (equal (fn-state-fenced acceptance) nil)
             (<= (fn-state-next-txid acceptance) recorded-txid))
        (fn-node-make-state
         (fn-make-state (fn-state-groups acceptance)
                        (fn-state-nexts acceptance)
                        (fn-state-articles acceptance)
                        recorded-txid nil nil)
         (fn-node-retention node)
         nil
         (fn-node-bindings node))
      node)))

(verify-guards fn-replay-advance-txid)

(defun fn-replay-advance-okp (node recorded-txid)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-node-statep node)
       (natp recorded-txid)
       (null (fn-node-stage node))
       (null (fn-state-pending (fn-node-acceptance node)))
       (equal (fn-state-fenced (fn-node-acceptance node)) nil)
       (<= (fn-state-next-txid (fn-node-acceptance node)) recorded-txid)))

(verify-guards fn-replay-advance-okp)

; Apply exactly one record only after its sequence has been checked.  NIL is a
; refusal signal; it is deliberately not a normal partial state.
; Its proper-list helper guard is established by the public replay loop
; through fn-record-p.  No validity test is added to the logical transition.
(defun fn-replay-apply-record (node record)
  (declare (xargs :guard (true-listp record) :verify-guards nil))
  (let ((advanced (fn-replay-advance-txid node (fn-record-txid record))))
    (if (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                    (fn-record-txid record)))
        nil
      (let ((prepared
             (fn-node-prepare advanced
                              (fn-record-generation record)
                              (fn-record-msgid record)
                              (fn-record-payload record)
                              (fn-record-groups record)
                              (fn-record-obligation-id record)
                              (fn-record-content-subject record)
                              (fn-record-release-evidence record)
                              (fn-record-charge record))))
        (if (not (fn-node-pending-matchesp
                  prepared
                  (fn-record-txid record)
                  (fn-record-generation record)))
            nil
          (fn-node-complete prepared
                            (fn-record-txid record)
                            (fn-record-generation record)
                            :durable))))))

(verify-guards fn-replay-apply-record)

; The replay loop is total.  It inspects no later record after a fault.
(defun fn-replay-loop (node records expected-sequence)
  (declare (xargs :guard t :verify-guards nil :measure (len records)))
  (if (not (fn-node-statep node))
      (fn-replay-fault node expected-sequence :invalid-initial-node)
    (if (consp records)
        (let ((record (car records)))
          (if (not (fn-record-p record))
              (fn-replay-fault node expected-sequence :invalid-record)
            (if (not (equal (fn-record-sequence record) expected-sequence))
                (fn-replay-fault node expected-sequence :sequence)
              (let ((next (fn-replay-apply-record node record)))
                (if (not (fn-node-statep next))
                    (fn-replay-fault node expected-sequence :node-refusal)
                  (fn-replay-loop next (cdr records)
                                  (1+ expected-sequence)))))))
      (if (null records)
          (fn-replay-ok node expected-sequence)
        (fn-replay-fault node expected-sequence :improper-record-list)))))

(verify-guards fn-replay-loop)

(defun fn-replay (groups capacity records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-replay-loop (fn-node-initial-state groups capacity) records 0))

(verify-guards fn-replay)

; -----------------------------------------------------------------------------
; Mechanical facts about fail-closed replay boundaries.

(defthm fn-replay-advance-keeps-committed-retention
  (equal (fn-node-retention (fn-replay-advance-txid node recorded-txid))
         (fn-node-retention node))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-replay-advance-keeps-committed-bindings
  (equal (fn-node-bindings (fn-replay-advance-txid node recorded-txid))
         (fn-node-bindings node))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-replay-advance-keeps-committed-articles
  (equal (fn-state-articles
          (fn-node-acceptance (fn-replay-advance-txid node recorded-txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-replay-advance-reconstructs-recorded-txid
  (implies (fn-replay-advance-okp node recorded-txid)
           (equal (fn-state-next-txid
                   (fn-node-acceptance
                    (fn-replay-advance-txid node recorded-txid)))
                  recorded-txid))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp
                                      fn-replay-advance-txid))))

(defthm fn-replay-empty-prefix-is-ok
  (implies (fn-node-statep node)
           (equal (fn-replay-loop node nil expected-sequence)
                  (fn-replay-ok node expected-sequence)))
  :hints (("Goal" :in-theory (enable fn-replay-loop))))

(defthm fn-replay-nonrecord-faults-with-last-good-node
  (implies (and (fn-node-statep node)
                (not (fn-record-p record)))
           (equal (fn-replay-loop node (cons record records) expected-sequence)
                  (fn-replay-fault node expected-sequence :invalid-record)))
  :hints (("Goal" :in-theory (enable fn-replay-loop))))

(defthm fn-replay-out-of-sequence-faults-with-last-good-node
  (implies (and (fn-node-statep node)
                (fn-record-p record)
                (not (equal (fn-record-sequence record) expected-sequence)))
           (equal (fn-replay-loop node (cons record records) expected-sequence)
                  (fn-replay-fault node expected-sequence :sequence)))
  :hints (("Goal" :in-theory (enable fn-replay-loop))))
