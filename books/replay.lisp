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
(include-book "node-retention-transitions")
(include-book "store-events")
(include-book "hybrid-store")
(include-book "records-seam")
; The codecs cluster withdraws (:d fn-store-event-p) at export (2026-09-19); the
; loop's guard proof needs only that a record is a true list.  Interim
; local fact applied by the store deputy so its closure certifies; the
; convergence lane owns the final form.
; Exported: with `fn-store-event-p' withdrawn on export (books/store-events)
; these are the facts a book above needs about an event, and proving them
; there means opening the recognizer again -- which is a 15018-way splitter
; case in books/store-files (measured 2026-09-22).
(defthm fn-replay-record-is-a-true-list
   (implies (fn-store-event-p record) (true-listp record))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-store-event-p
                                      fn-store-retention-event-p
                                      fn-cpe-eventp
                                      fn-record-shape-vocabulary
                                      fn-record-record-vocabulary))))
(local
 (defthm fn-replay-article-counters-are-natural
   (implies (fn-record-p record)
            (and (natp (fn-record-sequence record))
                 (natp (fn-record-txid record))
                 (natp (fn-record-generation record))))
   :hints (("Goal" :in-theory (enable fn-record-record-vocabulary
                                      fn-record-shape-vocabulary)))))
(local
 (defthm fn-replay-retention-counters-are-natural
   (implies (fn-store-retention-event-p record)
            (and (natp (fn-store-event-nth 2 record))
                 (natp (fn-store-event-nth 3 record))
                 (natp (fn-store-event-nth 4 record))))
   :hints (("Goal" :in-theory (enable fn-store-retention-event-p
                                      fn-record-uint32p)))))
(local
 (defthm fn-replay-stxe-counters-are-natural
   (implies (fn-stxe-p record)
            (and (natp (fn-stxe-sequence record))
                 (natp (fn-stxe-txid record))
                 (natp (fn-stxe-generation record))))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))
(local
 (defthm fn-replay-stxk-counters-are-natural
   (implies (fn-stxk-p record)
            (and (natp (fn-stxk-sequence record))
                 (natp (fn-stxk-txid record))
                 (natp (fn-stxk-generation record))))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))
(local
 (defthm fn-replay-stxa-counters-are-natural
   (implies (fn-stxa-p record)
            (and (natp (fn-stxa-sequence record))
                 (natp (fn-stxa-txid record))
                 (natp (fn-stxa-generation record))))
   :hints (("Goal" :in-theory (enable fn-record-uint32p)))))
(local
 (defthm fn-replay-cpe-counters-are-natural
   (implies (fn-cpe-eventp record)
            (and (natp (fn-cpe-sequence record))
                 (natp (fn-cpe-txid record))
                 (natp (fn-cpe-generation record))))
   :hints (("Goal" :in-theory (enable fn-cpe-eventp fn-cp-uintp)))))
(defthm fn-replay-record-counters-are-natural
   (implies (fn-store-event-p record)
            (and (natp (fn-store-event-sequence record))
                 (natp (fn-store-event-txid record))
                 (natp (fn-store-event-generation record))))
   :rule-classes ((:forward-chaining)
                  (:type-prescription :corollary
                   (implies (fn-store-event-p record) (natp (fn-store-event-sequence record))))
                  (:type-prescription :corollary
                   (implies (fn-store-event-p record) (natp (fn-store-event-txid record))))
                  (:type-prescription :corollary
                   (implies (fn-store-event-p record) (natp (fn-store-event-generation record)))))
   :hints (("Goal"
            :use (fn-replay-article-counters-are-natural
                  fn-replay-retention-counters-are-natural
                  fn-replay-stxe-counters-are-natural
                  fn-replay-stxk-counters-are-natural
                  fn-replay-stxa-counters-are-natural
                  fn-replay-cpe-counters-are-natural)
            :cases ((fn-record-p record)
                    (fn-store-retention-event-p record)
                    (fn-stxe-p record)
                    (fn-stxk-p record)
                    (fn-stxa-p record))
            :in-theory
            (e/d (fn-store-event-p fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation)
                 (fn-record-p fn-store-retention-event-p fn-stxe-p fn-stxk-p
                              fn-stxa-p fn-cpe-eventp
                              fn-replay-article-counters-are-natural
                              fn-replay-retention-counters-are-natural
                              fn-replay-stxe-counters-are-natural
                              fn-replay-stxk-counters-are-natural
                              fn-replay-stxa-counters-are-natural
                              fn-replay-cpe-counters-are-natural)))))

; Convergence (board, codecs CHANGE on records): `fn-store-event-p' is opaque and exports no forward shape rule; the loop guard needs true-listp from it.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))
(local (in-theory (enable fn-retention-invariants-vocabulary)))

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

; Identity evidence is folded beside the article/retention node.  Every Store
; event advances this context exactly once.  Standalone kind-2 evidence is
; validated against its historical snapshot but is deliberately removed from
; the accepted-verdict projection; only a bound kind-4 composite contributes
; an accepted article verdict.
; `nfix' on the counter, the same totalization `fn-sn-advance-identity-next'
; (books/store-node) got in 7740f605, the commit that also asked for this
; function's guards.  The one caller below reaches this branch for an event
; that is none of the three identity records, so the counter it advances is
; not decided by a record recognizer here and `:guard t' leaves
; (acl2-numberp (fn-stxk-context-next ctx)) with nothing to prove it: the
; guard conjecture suggests no induction and fails (hbox
; run-20260922T031236Z-c1fb).  Every reachable context is built by
; `fn-stxk-initial-context' from 0 and advanced by this function, so `nfix'
; is the identity on the composed machine.
(defun fn-replay-identity-advance (ctx)
  (declare (xargs :guard t :verify-guards nil))
  (fn-stxk-context :ok (1+ (nfix (fn-stxk-context-next ctx)))
                   (fn-stxk-context-snapshots ctx)
                   (fn-stxk-context-verdicts ctx)
                   (fn-stxk-context-current-generation ctx) nil))

(verify-guards fn-replay-identity-advance)

(defun fn-replay-identity-step (ctx event)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal (fn-stxk-context-kind ctx) :ok)) ctx
    (if (not (equal (fn-store-event-sequence event)
                    (fn-stxk-context-next ctx)))
        (fn-stxk-fault ctx :sequence)
      (cond
       ((fn-stxk-p event) (fn-stxk-apply-snapshot ctx event))
       ((fn-stxe-p event)
        (let ((checked (fn-stxk-apply-verdict ctx event)))
          (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
            (fn-stxk-context :ok (fn-stxk-context-next checked)
                             (fn-stxk-context-snapshots checked)
                             (fn-stxk-context-verdicts ctx)
                             (fn-stxk-context-current-generation checked) nil))))
       ((fn-stxa-p event)
        (let ((snapshot
               (fn-stxk-find (fn-stxa-keyring-generation event)
                              (fn-stxk-context-snapshots ctx))))
          (if (or (not (fn-stxa-bindsp event))
                  (not snapshot)
                  (not (fn-hsig-article-event-snapshot-bindsp event snapshot)))
              (fn-stxk-fault ctx :composite-binding)
            (let ((decoded (fn-stxe-decode-exact
                            (fn-stxa-verdict-event event))))
            (if (not (fn-stmt-okp decoded))
                (fn-stxk-fault ctx :composite-verdict)
                (fn-stxk-apply-verdict ctx (fn-stmt-value decoded)))))))
       (t (fn-replay-identity-advance ctx))))))

(verify-guards fn-replay-identity-step)

(defun fn-replay-identity-loop (records ctx)
  (declare (xargs :guard t :measure (len records) :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-store-event-p)))))
  (if (consp records)
      (if (not (fn-store-event-p (car records)))
          (fn-stxk-fault ctx :invalid-record)
        (fn-replay-identity-loop
         (cdr records) (fn-replay-identity-step ctx (car records))))
    (if (null records) ctx (fn-stxk-fault ctx :improper-record-list))))

(verify-guards fn-replay-identity-loop)

(defun fn-replay-identity (records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-replay-identity-loop records (fn-stxk-initial-context 0)))

(verify-guards fn-replay-identity)

(defun fn-replay-verdict-pairs (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (let ((e (car events)))
        (if (fn-stxe-p e)
            (cons (cons (fn-stxe-msgid e)
                        (fn-stx-make-verdict
                         (fn-stxe-token e) (fn-stxe-detail e)
                         (fn-stxe-keyring-generation e)))
                  (fn-replay-verdict-pairs (cdr events)))
          (fn-replay-verdict-pairs (cdr events))))
    nil))

(verify-guards fn-replay-verdict-pairs)

; Apply exactly one record only after its sequence has been checked.  NIL is a
; refusal signal; it is deliberately not a normal partial state.  The guard
; on the node is discharged through the two node transitions by their
; preservation keystones; the record's proper-list guard is established by the
; public replay loop through fn-store-event-p.
(defun fn-replay-node-with-retention (node retention)
  (declare (xargs :guard t))
  (fn-node-make-state (fn-node-acceptance node) retention
                      (fn-node-stage node) (fn-node-bindings node)))

(defun fn-replay-complete-retention (node retention event)
  (declare (xargs :guard
                  (and (fn-node-statep node)
                       (fn-retain-statep retention)
                       (fn-store-retention-event-p event)
                       (fn-node-statep
                        (fn-replay-node-with-retention node retention)))
                  :verify-guards nil))
  ; A retention event consumes its Store transaction id just as article
  ; completion does.  Advancing here keeps the live node at the durable
  ; allocator frontier and makes the next mixed event strictly later.
  (fn-replay-advance-txid
   (fn-replay-node-with-retention node retention)
   (1+ (fn-store-event-txid event))))

(defun fn-replay-apply-retention-event (node event)
  (declare (xargs :guard (and (fn-node-statep node)
                              (fn-store-retention-event-p event))
                  :verify-guards nil))
  (let* ((advanced (fn-replay-advance-txid node (fn-store-event-txid event)))
         (retention (fn-node-retention advanced))
         (id (fn-store-event-obligation-id event))
         (subject (fn-store-event-subject event))
         (evidence (fn-store-event-evidence event)))
    (if (or (not (fn-node-statep advanced))
            (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                        (fn-store-event-txid event)))
            (not (null (fn-node-stage advanced)))
            (member-equal id (fn-node-binding-ids (fn-node-bindings advanced))))
        nil
      (if (equal (fn-store-event-kind event) :undertake)
          (if (not (fn-retain-admissiblep retention id subject :forward evidence
                                         (fn-store-event-charge event)))
              nil
            (fn-replay-complete-retention
             advanced (fn-retain-admit retention id subject :forward evidence
                                       (fn-store-event-charge event)) event))
        (let ((pin (fn-retain-find-id id (fn-retain-pins retention))))
          (if (not (fn-retain-matching-releasep pin id subject :forward evidence))
              nil
            (fn-replay-complete-retention
             advanced (fn-retain-release retention id subject :forward evidence)
             event)))))))

(defun fn-replay-apply-identity-neutral (node event)
  (declare (xargs :guard (and (fn-node-statep node)
                              (fn-store-event-p event))))
  (let ((advanced (fn-replay-advance-txid node (fn-store-event-txid event))))
    (if (equal (fn-state-next-txid (fn-node-acceptance advanced))
               (fn-store-event-txid event))
        (fn-replay-advance-txid advanced (1+ (fn-store-event-txid event)))
      nil)))

(defun fn-replay-composite-record (event)
  (declare (xargs :guard t))
  (if (and (fn-stxa-p event) (fn-stxa-bindsp event))
      (let ((decoded (fn-record-decode-exact (fn-stxa-article-record event))))
        (if (fn-record-result-okp decoded)
            (fn-record-result-record decoded)
          nil))
    nil))

(defun fn-replay-apply-record (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (if (fn-store-retention-event-p record)
      (fn-replay-apply-retention-event node record)
    (if (or (fn-stxe-p record) (fn-stxk-p record) (fn-cpe-eventp record))
        (if (and (fn-cpe-eventp record) (not (null (fn-node-stage node))))
            nil
          (fn-replay-apply-identity-neutral node record))
      ; Unreachable-in-composition: journal replay enters with no pending
      ; transaction.  A standalone article step refuses a staged node, lest a
      ; record with matching coordinates complete that different article.
      (if (not (null (fn-node-stage node)))
          nil
      (let* ((article (if (fn-stxa-p record)
                          (fn-replay-composite-record record)
                        record))
             (advanced (fn-replay-advance-txid node (fn-store-event-txid record))))
      (if (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                      (fn-store-event-txid record)))
          nil
        (if (not (fn-record-p article)) nil
          (let ((prepared
               (fn-node-prepare advanced
                                (fn-record-generation article)
                                (fn-record-msgid article)
                                (fn-record-payload article)
                                (fn-record-groups article)
                                (fn-record-obligation-id article)
                                (fn-record-content-subject article)
                                (fn-record-release-evidence article)
                                (fn-record-charge article)
                                (fn-record-stamp article))))
          (if (not (fn-node-pending-matchesp
                    prepared
                    (fn-record-txid article)
                    (fn-record-generation article)))
              nil
            (fn-node-complete prepared
                              (fn-record-txid article)
                              (fn-record-generation article)
                              :durable))))))))))

; From here down the event recognizers and the composite article decoder are
; closed.  `fn-record-shape-vocabulary' is enabled for this book (above), so an
; open `fn-record-p', `fn-stxe-p', `fn-stxk-p', `fn-stxa-p' or
; `fn-store-retention-event-p' lets a goal that merely dispatches on the event
; kind unfold the whole record and statement codec underneath it: measured
; 2026-09-22, `fn-replay-apply-record-non-nil-is-node-state' ran 600 s without
; leaving Goal\'\' and took the book past its 1800 s and 2400 s limits on hbox
; (run-20260922T031236Z-c1fb, run certify-20260922T034701Z-2641627); with the
; recognizers closed it proves in 0.32 s over 90 subgoals.  The proofs below
; dispatch on these terms, they do not need to see inside them --
; `fn-replay-record-counters-are-natural' above already closes exactly this set
; for the same reason.
(local (in-theory (disable fn-store-event-p fn-store-event-sequence
                           fn-record-p fn-stxe-p fn-stxk-p fn-stxa-p
                           fn-store-retention-event-p fn-cpe-eventp
                           fn-replay-composite-record)))

; A non-NIL one-record result is the existing node transaction machine's
; durable branch, hence remains a valid node.  NIL is intentionally a refusal,
; not a partially reconstructed state.
(defthm fn-replay-apply-record-non-nil-is-node-state
  (implies (and (fn-node-statep node)
                (fn-store-event-p record)
                (consp (fn-replay-apply-record node record)))
           (fn-node-statep (fn-replay-apply-record node record)))
  :hints (("Goal"
           :use ((:instance fn-nrt-node-admit-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid record)))
                            (id (fn-store-event-obligation-id record))
                            (subject (fn-store-event-subject record))
                            (kind :forward)
                            (evidence (fn-store-event-evidence record))
                            (charge (fn-store-event-charge record)))
                 (:instance fn-nrt-node-release-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid record)))
                            (id (fn-store-event-obligation-id record))
                            (subject (fn-store-event-subject record))
                            (kind :forward)
                            (evidence (fn-store-event-evidence record))))
           :in-theory (enable fn-replay-apply-record
                              fn-replay-apply-retention-event
                              fn-replay-complete-retention
                              fn-replay-node-with-retention
                              fn-nrt-node-with-retention))))

; Under the carried invariant a one-record result is a node exactly when it is
; non-NIL.  This is the equality the replay loop's :exec test relies on; it is
; used by :use in the guard proof and is not a rewrite rule.
(defthm fn-replay-apply-record-statep-iff-consp
  (implies (and (fn-node-statep node)
                (fn-store-event-p record))
           (iff (fn-node-statep (fn-replay-apply-record node record))
                (consp (fn-replay-apply-record node record))))
  :rule-classes nil
  :hints (("Goal"
           :use fn-replay-apply-record-non-nil-is-node-state
           :in-theory (e/d (fn-node-statep fn-node-state-shapep)
                           (fn-replay-apply-record
                            fn-replay-apply-record-non-nil-is-node-state)))))

(defthm fn-replay-retain-pins-typed
  (implies (fn-retain-statep retention)
           (fn-retain-obligation-listp
            (fn-retain-pins retention)))
  :hints (("Goal"
           :in-theory (enable fn-retain-statep fn-retain-state-shapep
                              fn-retain-capacity fn-retain-reserved
                              fn-retain-pins fn-retain-releases))))

(verify-guards fn-replay-complete-retention)
(verify-guards fn-replay-apply-retention-event
  :hints (("Goal"
           :use ((:instance fn-nrt-node-admit-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event)))
                            (id (fn-store-event-obligation-id event))
                            (subject (fn-store-event-subject event))
                            (kind :forward)
                            (evidence (fn-store-event-evidence event))
                            (charge (fn-store-event-charge event)))
                 (:instance fn-nrt-node-release-preserves-statep
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event)))
                            (id (fn-store-event-obligation-id event))
                            (subject (fn-store-event-subject event))
                            (kind :forward)
                            (evidence (fn-store-event-evidence event)))
                 (:instance fn-nrt-node-statep-retention
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid event))))
                 (:instance fn-replay-retain-pins-typed
                            (retention
                             (fn-node-retention
                              (fn-replay-advance-txid
                               node (fn-store-event-txid event))))))
           :in-theory (enable fn-replay-node-with-retention
                              fn-nrt-node-with-retention))))
(verify-guards fn-replay-apply-record)

; The replay loop is total.  It inspects no later record after a fault.  Its
; :exec path tests one-record refusal by NIL rather than by the recognizer.
(defun fn-replay-loop (node records expected-sequence)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil
                  :measure (len records)))
  (if (mbe :logic (not (fn-node-statep node)) :exec nil)
      (fn-replay-fault node expected-sequence :invalid-initial-node)
    (if (consp records)
        (let ((record (car records)))
          (if (not (fn-store-event-p record))
              (fn-replay-fault node expected-sequence :invalid-record)
            (if (not (equal (fn-store-event-sequence record) expected-sequence))
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
                (not (fn-store-event-p record)))
           (equal (fn-replay-loop node (cons record records) expected-sequence)
                  (fn-replay-fault node expected-sequence :invalid-record)))
  :hints (("Goal" :in-theory (enable fn-replay-loop))))

(defthm fn-replay-out-of-sequence-faults-with-last-good-node
  (implies (and (fn-node-statep node)
                (fn-store-event-p record)
                (not (equal (fn-store-event-sequence record) expected-sequence)))
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
                            fn-replay-apply-record fn-store-event-p)))))

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
