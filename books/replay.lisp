; fn M1 pure replay of validated committed records into the composite node.
;
; Records arrive here only after their byte framing/integrity boundary has
; selected a complete candidate.  This book does not model a disk, signatures,
; or power-failure behavior.  A replay fault is fail-closed: its saved node is
; diagnostic last-good-prefix state, never authority to continue recovery.
;
; `fn-node-statep' is carried through replay: it is checked once, on the
; initial node in `fn-replay', and every per-record step is guarded by it.
; The guards are discharged from the node preservation keystones, which is
; why this book includes node-invariants.  The former replay-invariants book
; is folded in here beside the definitions whose guards it discharges; the
; :logic bodies are the original total ones.

(in-package "ACL2")
(include-book "node-invariants")
(include-book "records")
; The codecs cluster withdraws (:d fn-record-p) at export (2026-09-19); the
; loop's guard proof needs only that a record is a true list.  Interim
; local fact applied by the store deputy so its closure certifies; the
; convergence lane owns the final form.
(local
 (defthm fn-replay-record-is-a-true-list
   (implies (fn-record-p record) (true-listp record))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-record-codec-vocabulary
                                      fn-record-record-vocabulary)))))
(local
 (defthm fn-replay-record-counters-are-natural
   (implies (fn-record-p record)
            (and (natp (fn-record-sequence record))
                 (natp (fn-record-txid record))
                 (natp (fn-record-generation record))))
   :rule-classes ((:forward-chaining)
                  (:type-prescription :corollary
                   (implies (fn-record-p record) (natp (fn-record-sequence record))))
                  (:type-prescription :corollary
                   (implies (fn-record-p record) (natp (fn-record-txid record))))
                  (:type-prescription :corollary
                   (implies (fn-record-p record) (natp (fn-record-generation record)))))
   :hints (("Goal" :in-theory (enable fn-record-codec-vocabulary
                                      fn-record-record-vocabulary)))))

; -----------------------------------------------------------------------------
; Result records

; Success: (:ok node next-journal-sequence)
; Fault:   (:fault last-good-node expected-journal-sequence reason)
(defun fn-replay-ok-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-replay-fault-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-replay-result-kind (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-replay-result-kind)
(defun fn-replay-result-node (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-replay-result-node)
(defun fn-replay-result-sequence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-replay-result-sequence)
(defun fn-replay-result-reason (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-replay-result-reason)

(defun fn-replay-ok (node next-sequence)
  (declare (xargs :guard t))
  (list :ok node next-sequence))

(defun fn-replay-fault (node expected-sequence reason)
  (declare (xargs :guard t))
  (list :fault node expected-sequence reason))

(defthm fn-replay-ok-shapep-of-fn-replay-ok
  (fn-replay-ok-shapep (fn-replay-ok node next-sequence)))
(defthm fn-replay-result-kind-of-fn-replay-ok
  (equal (fn-replay-result-kind (fn-replay-ok node next-sequence)) :ok))
(defthm fn-replay-result-node-of-fn-replay-ok
  (equal (fn-replay-result-node (fn-replay-ok node next-sequence)) node))
(defthm fn-replay-result-sequence-of-fn-replay-ok
  (equal (fn-replay-result-sequence (fn-replay-ok node next-sequence))
         next-sequence))
(defthm fn-replay-fault-shapep-of-fn-replay-fault
  (fn-replay-fault-shapep (fn-replay-fault node expected-sequence reason)))
(defthm fn-replay-result-kind-of-fn-replay-fault
  (equal (fn-replay-result-kind (fn-replay-fault node expected-sequence reason))
         :fault))
(defthm fn-replay-result-node-of-fn-replay-fault
  (equal (fn-replay-result-node (fn-replay-fault node expected-sequence reason))
         node))
(defthm fn-replay-result-sequence-of-fn-replay-fault
  (equal (fn-replay-result-sequence
          (fn-replay-fault node expected-sequence reason))
         expected-sequence))
(defthm fn-replay-result-reason-of-fn-replay-fault
  (equal (fn-replay-result-reason (fn-replay-fault node expected-sequence reason))
         reason))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-replay-ok-shapep-forward-shape
  (implies (fn-replay-ok-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-ok-shapep))))
(defthm fn-replay-fault-shapep-forward-shape
  (implies (fn-replay-fault-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-fault-shapep))))
(defthm fn-replay-result-accessors-forward-consp
  (and
   (implies (fn-replay-result-kind x) (consp x))
   (implies (fn-replay-result-node x) (consp x))
   (implies (fn-replay-result-sequence x) (consp x))
   (implies (fn-replay-result-reason x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-replay-result-kind x) (consp x))
                      :trigger-terms ((fn-replay-result-kind x)))
   (:forward-chaining :corollary (implies (fn-replay-result-node x) (consp x))
                      :trigger-terms ((fn-replay-result-node x)))
   (:forward-chaining :corollary (implies (fn-replay-result-sequence x) (consp x))
                      :trigger-terms ((fn-replay-result-sequence x)))
   (:forward-chaining :corollary (implies (fn-replay-result-reason x) (consp x))
                      :trigger-terms ((fn-replay-result-reason x)))
   )
  :hints (("Goal" :in-theory (enable fn-replay-result-kind fn-replay-result-node fn-replay-result-sequence fn-replay-result-reason))))

(in-theory (disable (:d fn-replay-ok-shapep) (:d fn-replay-fault-shapep)
                    (:d fn-replay-result-kind) (:d fn-replay-result-node)
                    (:d fn-replay-result-sequence) (:d fn-replay-result-reason)
                    (:d fn-replay-ok) (:d fn-replay-fault)))

(defun fn-replay-okp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-replay-ok-shapep x)
       (equal (fn-replay-result-kind x) :ok)
       (fn-node-statep (fn-replay-result-node x))
       (natp (fn-replay-result-sequence x))))

(defthm fn-replay-okp-forward-shape
  (implies (fn-replay-okp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-okp))))

(verify-guards fn-replay-okp)

(defun fn-replay-faultp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-replay-fault-shapep x)
       (equal (fn-replay-result-kind x) :fault)
       (fn-node-statep (fn-replay-result-node x))
       (natp (fn-replay-result-sequence x))))

(defthm fn-replay-faultp-forward-shape
  (implies (fn-replay-faultp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-replay-faultp))))

(verify-guards fn-replay-faultp)

(defthm fn-replay-ok-constructor-is-typed
  (implies (and (fn-node-statep node) (natp sequence))
           (fn-replay-okp (fn-replay-ok node sequence)))
  :hints (("Goal" :in-theory (enable fn-replay-okp))))

(defthm fn-replay-fault-constructor-is-typed
  (implies (and (fn-node-statep node) (natp sequence))
           (fn-replay-faultp (fn-replay-fault node sequence reason)))
  :hints (("Goal" :in-theory (enable fn-replay-faultp))))

; -----------------------------------------------------------------------------
; Explicit reconstruction of txids consumed by known-aborted transactions.

; Journal sequence is contiguous, while acceptance transaction IDs may have
; known-aborted gaps.  This helper advances an idle, unfenced node only forward
; to the next committed record's txid.  It changes no article, retention pin,
; binding, group watermark, or capacity accounting.
(defun fn-replay-advance-txid (node recorded-txid)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (let ((acceptance (fn-node-acceptance node)))
    (if (and (mbe :logic (fn-node-statep node) :exec t)
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

(verify-guards fn-replay-advance-txid
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defun fn-replay-advance-okp (node recorded-txid)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-node-statep node)
       (natp recorded-txid)
       (null (fn-node-stage node))
       (null (fn-state-pending (fn-node-acceptance node)))
       (equal (fn-state-fenced (fn-node-acceptance node)) nil)
       (<= (fn-state-next-txid (fn-node-acceptance node)) recorded-txid)))

(verify-guards fn-replay-advance-okp
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

; Raising an idle acceptance txid models a known-aborted transaction gap.  It
; cannot create a partial article or pin and preserves the full node invariant.
(defthm fn-replay-advance-preserves-node-statep
  (implies (fn-node-statep node)
           (fn-node-statep (fn-replay-advance-txid node recorded-txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid
                                      fn-node-statep fn-statep))))

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

(in-theory (disable (:d fn-replay-advance-txid)))

; Apply exactly one record only after its sequence has been checked.  NIL is a
; refusal signal; it is deliberately not a normal partial state.  The guard
; on the node is discharged through the two node transitions by their
; preservation keystones; the record's proper-list guard is established by the
; public replay loop through fn-record-p.
(defun fn-replay-apply-record (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
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

; A non-NIL one-record result is the existing node transaction machine's
; durable branch, hence remains a valid node.  NIL is intentionally a refusal,
; not a partially reconstructed state.
(defthm fn-replay-apply-record-non-nil-is-node-state
  (implies (and (fn-node-statep node)
                (fn-record-p record)
                (consp (fn-replay-apply-record node record)))
           (fn-node-statep (fn-replay-apply-record node record)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-record))))

; Under the carried invariant a one-record result is a node exactly when it is
; non-NIL.  This is the equality the replay loop's :exec test relies on; it is
; used by :use in the guard proof and is not a rewrite rule.
(defthm fn-replay-apply-record-statep-iff-consp
  (implies (and (fn-node-statep node)
                (fn-record-p record))
           (iff (fn-node-statep (fn-replay-apply-record node record))
                (consp (fn-replay-apply-record node record))))
  :rule-classes nil
  :hints (("Goal"
           :use fn-replay-apply-record-non-nil-is-node-state
           :in-theory (e/d (fn-node-statep fn-node-state-shapep)
                           (fn-replay-apply-record
                            fn-replay-apply-record-non-nil-is-node-state)))))

; The replay loop is total.  It inspects no later record after a fault.  Its
; :exec path tests one-record refusal by NIL rather than by the recognizer.
(defun fn-replay-loop (node records expected-sequence)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil
                  :measure (len records)))
  (if (mbe :logic (not (fn-node-statep node)) :exec nil)
      (fn-replay-fault node expected-sequence :invalid-initial-node)
    (if (consp records)
        (let ((record (car records)))
          (if (not (fn-record-p record))
              (fn-replay-fault node expected-sequence :invalid-record)
            (if (not (equal (fn-record-sequence record) expected-sequence))
                (fn-replay-fault node expected-sequence :sequence)
              (let ((next (fn-replay-apply-record node record)))
                (if (mbe :logic (not (fn-node-statep next))
                         :exec (not (consp next)))
                    (fn-replay-fault node expected-sequence :node-refusal)
                  (fn-replay-loop next (cdr records)
                                  (1+ expected-sequence)))))))
      (if (null records)
          (fn-replay-ok node expected-sequence)
        (fn-replay-fault node expected-sequence :improper-record-list)))))

(verify-guards fn-replay-loop
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-statep-iff-consp
                            (record (car records))))
           :in-theory (disable fn-node-statep fn-replay-apply-record))))

; The initial node is checked once; the loop then carries the invariant.
; Logically identical to the former `(fn-replay-loop initial records 0)',
; whose first test was exactly this one.
(defun fn-replay (groups capacity records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-node-initial-state groups capacity)))
    (if (fn-node-statep node)
        (fn-replay-loop node records 0)
      (fn-replay-fault node 0 :invalid-initial-node))))

(verify-guards fn-replay)

; -----------------------------------------------------------------------------
; Mechanical facts about fail-closed replay boundaries.

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

; From a valid node and natural expected sequence, replay always returns a
; typed success or a typed fault containing a valid diagnostic prefix node.
(defthm fn-replay-loop-result-is-typed
  (implies (and (fn-node-statep node)
                (natp expected-sequence))
           (or (fn-replay-okp
                (fn-replay-loop node records expected-sequence))
               (fn-replay-faultp
                (fn-replay-loop node records expected-sequence))))
  :hints (("Goal" :induct (fn-replay-loop node records expected-sequence)
           :in-theory (e/d (fn-replay-loop)
                           (fn-node-statep fn-replay-okp fn-replay-faultp
                            fn-replay-apply-record fn-record-p)))))

; Valid configured initial inputs inherit the typed replay-result boundary.
(defthm fn-replay-result-is-typed-from-valid-configuration
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (or (fn-replay-okp (fn-replay groups capacity records))
               (fn-replay-faultp (fn-replay groups capacity records))))
  :hints (("Goal"
           :use ((:instance fn-replay-loop-result-is-typed
                            (node (fn-node-initial-state groups capacity))
                            (expected-sequence 0)))
           :in-theory (e/d (fn-replay)
                           (fn-node-statep fn-replay-okp fn-replay-faultp
                            fn-replay-loop fn-node-initial-state
                            fn-replay-loop-result-is-typed)))))

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  Withdrawn here: the
; result recognizers, the advance predicate, the one-record step, the loop and
; the entry point.  Keystones stay enabled: the typed-constructor lemmas, the
; advance preservation and projection lemmas, the non-NIL-is-node lemma, the
; three boundary facts and the two typed-result theorems.
(in-theory (disable (:d fn-replay-okp) (:d fn-replay-faultp)
                    (:d fn-replay-advance-okp) (:d fn-replay-apply-record)
                    (:d fn-replay-loop) (:d fn-replay)))
