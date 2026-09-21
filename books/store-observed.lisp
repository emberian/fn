; Observed physical-image entry to the executable node/file recovery kernel.
;
; The host supplies records only after its bounded framed-file scanner has
; exact-codec-decoded them.  This book does not parse files or claim that a
; fresh process image detects rollback.  It validates the decoded logical image,
; enters the existing :replaying file state with no inherited acknowledgements,
; and calls the actual fn-sn-recover transition.  Recovered operation remains
; gated on five subsequent host fsync observations through fn-sn-io.
;
; This is the root of every process: host/store-node-host.lisp:27 calls
; fn-sn-open-observed on each start.  The theorems that root the trace
; relation at this entry (D6) and carry acknowledged-record retention across
; the reopen boundary with A-DURABILITY as the hypothesis fn-sf-crash-imagep
; (D5) live in store-observed-traces.lisp, which includes this book and the
; resolution trace book.  The opening theorems below stay in the lighter
; theory of store-node-invariants, where they certify; under the rewrite
; rules the trace books export, fn-sn-observed-one-ok-barrier does not.

(in-package "ACL2")
(include-book "store-node-resolution")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))
(local (in-theory (enable fn-store-files-invariants-vocabulary
                          fn-store-node-invariants-vocabulary
                          fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        )))

; The host-facing tagged boundary.  It exposes a recovering node/file state or
; a refusal code; callers never inspect an intermediate replay result.
(defun fn-sn-open-ok (st) (declare (xargs :guard t :verify-guards nil))
  (list :ok st))

(verify-guards fn-sn-open-ok)
(defun fn-sn-open-error (code) (declare (xargs :guard t :verify-guards nil))
  (list :error code))

(verify-guards fn-sn-open-error)
(defun fn-sn-open-kind (result) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car result)
       :exec (fn-ag-car result)))

(verify-guards fn-sn-open-kind)
(defun fn-sn-open-state (result) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr result)
       :exec (fn-ag-car (fn-ag-cdr result))))

(verify-guards fn-sn-open-state)
(defun fn-sn-open-code (result) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr result)
       :exec (fn-ag-car (fn-ag-cdr result))))

(verify-guards fn-sn-open-code)

; The open result is an opaque two-field record (docs/proof-style.md s1).
(defun fn-sn-open-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defthm fn-sn-open-shapep-of-fn-sn-open-ok
  (fn-sn-open-shapep (fn-sn-open-ok st)))
(defthm fn-sn-open-kind-of-fn-sn-open-ok
  (equal (fn-sn-open-kind (fn-sn-open-ok st)) :ok))
(defthm fn-sn-open-state-of-fn-sn-open-ok
  (equal (fn-sn-open-state (fn-sn-open-ok st)) st))
(defthm fn-sn-open-shapep-of-fn-sn-open-error
  (fn-sn-open-shapep (fn-sn-open-error code)))
(defthm fn-sn-open-kind-of-fn-sn-open-error
  (equal (fn-sn-open-kind (fn-sn-open-error code)) :error))
(defthm fn-sn-open-code-of-fn-sn-open-error
  (equal (fn-sn-open-code (fn-sn-open-error code)) code))
(in-theory (disable (:d fn-sn-open-shapep) (:d fn-sn-open-ok) (:d fn-sn-open-error)
                    (:d fn-sn-open-kind) (:d fn-sn-open-state) (:d fn-sn-open-code)))

; Shape facts type reasoning used to supply while the record opened
; (docs/proof-style.md s1), exported as forward-chaining rules only.
(defthm fn-sn-open-shapep-forward-shape
  (implies (fn-sn-open-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-open-shapep))))
(defthm fn-sn-open-accessors-forward-consp
  (and (implies (fn-sn-open-kind x) (consp x))
       (implies (fn-sn-open-state x) (consp x))
       (implies (fn-sn-open-code x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-sn-open-kind x) (consp x))
                                    :trigger-terms ((fn-sn-open-kind x)))
                 (:forward-chaining :corollary (implies (fn-sn-open-state x) (consp x))
                                    :trigger-terms ((fn-sn-open-state x)))
                 (:forward-chaining :corollary (implies (fn-sn-open-code x) (consp x))
                                    :trigger-terms ((fn-sn-open-code x))))
  :hints (("Goal" :in-theory (enable fn-sn-open-kind fn-sn-open-state fn-sn-open-code))))

(defun fn-sn-open-okp (result)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-open-shapep result)
       (equal (fn-sn-open-kind result) :ok)
       (fn-sn-statep (fn-sn-open-state result))))

(verify-guards fn-sn-open-okp)
(defun fn-sn-open-errorp (result)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-open-shapep result)
       (equal (fn-sn-open-kind result) :error)))

(verify-guards fn-sn-open-errorp)
(defthm fn-sn-open-okp-forward-shape
  (implies (fn-sn-open-okp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-open-okp fn-sn-open-shapep))))
(defthm fn-sn-open-errorp-forward-shape
  (implies (fn-sn-open-errorp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-open-errorp fn-sn-open-shapep))))

(defun fn-sn-observed-configurationp (groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-string-listp groups)
       (fn-no-duplicatesp groups)
       (natp capacity)))

(verify-guards fn-sn-observed-configurationp)

; A seed contains only image facts: no reservation/candidate/completion state,
; no success history from another process, and zero completed recovery barriers.
(defun fn-sn-observed-seed (groups capacity frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make groups capacity
              (fn-sf-make :replaying frontier nil records nil nil nil 0)
              (fn-node-initial-state groups capacity)
              ; A seed is an image fact, so it carries the empty verification
              ; context and the empty index (D21); fn-sn-recover recomputes
              ; the index over the replayed store.
              nil (fn-stx-index-empty)))

(verify-guards fn-sn-observed-seed)

(defun fn-sn-observed-historyp (frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-record-uint32p frontier)
       (fn-sf-record-listp records 0 0 frontier)))

(verify-guards fn-sn-observed-historyp)

; The guard proof of fn-sn-open-observed: a seed built from a valid
; configuration and history is a composed state, so the kernel entry below
; carries the recognizer instead of re-running it.
(defthm fn-sn-observed-seed-is-state
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records))
           (fn-sn-statep (fn-sn-observed-seed groups capacity frontier records)))
  :hints (("Goal"
           :use ((:instance fn-node-initial-state-is-state
                            (groups groups) (capacity capacity)))
           :in-theory (enable fn-sn-observed-configurationp
                               fn-sn-observed-historyp fn-sn-observed-seed
                               fn-sn-statep fn-sf-statep fn-sf-phase-shapep))))

; Structural checks precede replay.  A structurally valid but semantically
; unreplayable history reaches the actual recovery transition and returns the
; distinct :replay refusal below.  The :image refusal is
; unreachable-in-composition: fn-sn-observed-seed-is-state shows the seed is
; always a state, and fn-sn-recover-preserves-state that the opened state is;
; both tests are carried (mbe) and never executed.
(defun fn-sn-open-observed (groups capacity frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-sn-observed-configurationp groups capacity))
      (fn-sn-open-error :configuration)
    (if (not (fn-record-uint32p frontier))
        (fn-sn-open-error :frontier)
      (if (not (fn-sf-record-listp records 0 0 frontier))
          (fn-sn-open-error :history)
        (let ((seed (fn-sn-observed-seed groups capacity frontier records)))
          (if (mbe :logic (not (fn-sn-statep seed)) :exec nil)
              (fn-sn-open-error :image)
            (let ((opened (fn-sn-recover seed)))
              (if (and (mbe :logic (fn-sn-statep opened) :exec t)
                       (equal (fn-sf-phase (fn-sn-files opened)) :recovering))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :replay)))))))))

(verify-guards fn-sn-open-observed
  :hints (("Goal"
           :use (fn-sn-observed-seed-is-state
                 (:instance fn-sn-recover-preserves-state
                            (s (fn-sn-observed-seed groups capacity frontier records))))
           :in-theory (e/d (fn-sn-observed-historyp)
                           (fn-sn-statep fn-sn-observed-seed fn-sn-recover
                            fn-sn-observed-configurationp
                            fn-sn-observed-seed-is-state
                            fn-sn-recover-preserves-state)))))

; The host dispatches on the result kind; the theorem below is what makes
; that dispatch sound without a second recognizer pass over the opened state.
(defthm fn-sn-open-observed-result-is-typed
  (or (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
      (fn-sn-open-errorp (fn-sn-open-observed groups capacity frontier records)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-sn-observed-seed-is-state
                 (:instance fn-sn-recover-preserves-state
                            (s (fn-sn-observed-seed groups capacity frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp fn-sn-open-errorp
                                                 fn-sn-observed-historyp)
                           (fn-sn-statep fn-sn-observed-seed fn-sn-recover
                            fn-sn-observed-configurationp
                            fn-sn-observed-seed-is-state
                            fn-sn-recover-preserves-state)))))

; This is a direct consequence of the live recovery transition.  It is stated
; separately so the observed entry proof does not reimplement replay.
(defthm fn-sn-recover-replaying-output-is-exact
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :replaying)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-recover st)))
                       :recovering))
           (and (equal (fn-sf-records (fn-sn-files (fn-sn-recover st)))
                       (fn-sf-records (fn-sn-files st)))
                (equal (fn-sf-frontier (fn-sn-files (fn-sn-recover st)))
                       (fn-sf-frontier (fn-sn-files st)))
                (equal (fn-sf-successes (fn-sn-files (fn-sn-recover st)))
                       (fn-sf-successes (fn-sn-files st)))
                (equal (fn-sf-barriers (fn-sn-files (fn-sn-recover st))) 0)
                (equal (fn-sn-node (fn-sn-recover st))
                       (fn-sf-replay-node (fn-sn-groups st)
                                          (fn-sn-capacity st)
                                          (fn-sf-records (fn-sn-files st))
                                          (fn-sf-frontier (fn-sn-files st))))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-recover fn-sf-recover fn-sn-update
                                            )
                            (fn-sn-statep fn-sf-statep
                             fn-sf-history-recoverablep fn-sf-replay-node)))))

; These calls are the existing host-I/O path.  The helper is only notation for
; finite proof/test sequences; it does not write a barrier directly.
(defun fn-sn-observed-rebarrier (st count)
  (declare (xargs :guard (and (fn-sn-statep st) (natp count))
                  :verify-guards nil :measure (nfix count)))
  (if (zp count)
      st
    (fn-sn-observed-rebarrier
     (fn-sn-io st :recovery-barrier :ok) (1- count))))

; The composed state is carried through the recursion by fn-sn-io-preserves-state.
(verify-guards fn-sn-observed-rebarrier
  :hints (("Goal" :use ((:instance fn-sn-io-preserves-state
                                   (s st) (operation :recovery-barrier) (result :ok)))
           :in-theory (disable fn-sn-statep fn-sn-io fn-sn-io-preserves-state))))

(defthm fn-sn-statep-implies-files-statep
  (implies (fn-sn-statep st)
           (fn-sf-statep (fn-sn-files st)))
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(defthm fn-sn-observed-one-ok-barrier
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                (natp barriers)
                (equal (fn-sf-barriers (fn-sn-files st)) barriers)
                (< barriers 4))
           (and (fn-sn-statep (fn-sn-io st :recovery-barrier :ok))
                (equal (fn-sf-phase
                        (fn-sn-files
                         (fn-sn-io st :recovery-barrier :ok)))
                       :recovering)
                (equal (fn-sf-barriers
                        (fn-sn-files
                         (fn-sn-io st :recovery-barrier :ok)))
                       (1+ barriers))))
  :hints (("Goal"
           :use ((:instance fn-sn-io-preserves-state
                            (s st) (operation :recovery-barrier) (result :ok))
                 (:instance fn-sn-statep-implies-files-statep (st st)))
           :in-theory (e/d (fn-sn-io fn-sn-file-step fn-sf-recovery-barrier
                                      fn-sn-update  )
                            (fn-sn-statep fn-sf-statep)))))

(defthm fn-sn-observed-fifth-ok-barrier-is-ready
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                (equal (fn-sf-barriers (fn-sn-files st)) 4))
           (equal (fn-sf-phase
                   (fn-sn-files (fn-sn-io st :recovery-barrier :ok)))
                  :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-statep-implies-files-statep (st st)))
           :in-theory (e/d (fn-sn-io fn-sn-file-step fn-sf-recovery-barrier
                                      fn-sn-update  )
                            (fn-sn-statep fn-sf-statep)))))

(defthm fn-sn-observed-rebarrier-successor
  (implies (natp count)
           (equal (fn-sn-observed-rebarrier st (1+ count))
                  (fn-sn-io (fn-sn-observed-rebarrier st count)
                            :recovery-barrier :ok)))
  :hints (("Goal" :induct (fn-sn-observed-rebarrier st count)
           :expand ((fn-sn-observed-rebarrier st 1))
           :in-theory (e/d (fn-sn-observed-rebarrier)
                            (fn-sn-io)))))

(defthm fn-sn-observed-four-ok-barriers-remain-recovering
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                (equal (fn-sf-barriers (fn-sn-files st)) 0))
           (and (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 0))) :recovering)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 1))) :recovering)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 2))) :recovering)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 3))) :recovering)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 4))) :recovering)
                (fn-sn-statep (fn-sn-observed-rebarrier st 4))
                (equal (fn-sf-barriers (fn-sn-files (fn-sn-observed-rebarrier st 4))) 4)))
  :hints (("Goal"
           :use ((:instance fn-sn-observed-one-ok-barrier (st st) (barriers 0))
                 (:instance fn-sn-observed-one-ok-barrier (st (fn-sn-io st :recovery-barrier :ok)) (barriers 1))
                 (:instance fn-sn-observed-one-ok-barrier (st (fn-sn-io (fn-sn-io st :recovery-barrier :ok) :recovery-barrier :ok)) (barriers 2))
                 (:instance fn-sn-observed-one-ok-barrier (st (fn-sn-io (fn-sn-io (fn-sn-io st :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok)) (barriers 3)))
           :in-theory (e/d (fn-sn-observed-rebarrier)
                            (fn-sn-observed-one-ok-barrier fn-sn-io
                             fn-sn-statep fn-sf-statep 
                              )))))

(defthm fn-sn-observed-five-ok-barriers-is-ready
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :recovering)
                (equal (fn-sf-barriers (fn-sn-files st)) 0))
           (equal (fn-sf-phase
                   (fn-sn-files (fn-sn-observed-rebarrier st 5))) :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-observed-rebarrier-successor (count 4))
                 (:instance fn-sn-observed-four-ok-barriers-remain-recovering)
                 (:instance fn-sn-observed-fifth-ok-barrier-is-ready
                            (st (fn-sn-observed-rebarrier st 4))))
           :in-theory (e/d ()
                            (fn-sn-observed-rebarrier
                             fn-sn-observed-rebarrier-successor
                             fn-sn-observed-four-ok-barriers-remain-recovering
                             fn-sn-observed-fifth-ok-barrier-is-ready
                             fn-sn-statep fn-sf-statep 
                             fn-sn-io  )))))

(defthm fn-sn-open-observed-success-is-state
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sn-statep
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-okp )
                            (fn-sn-open-observed fn-sn-statep)))))

; -----------------------------------------------------------------------------
; The carried statement index at open (D21)
;
; host/store-node-host.lisp line 79 installs (fn-sn-open-state opened) into
; the 'fn-store-sn global, so without these two the claim that fn-sn-indexedp
; holds of every state the host installs would have a hole at open -- the one
; place where the node does not come from a step of this machine.

; The seed's node is fn-node-initial-state, whose store is empty, and the
; index of an empty store is the empty index under EVERY keyring, so the
; seed's empty keyring costs nothing here.
(defthm fn-sn-observed-seed-is-indexed
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records))
           (fn-sn-indexedp (fn-sn-observed-seed groups capacity frontier records)))
  :hints (("Goal"
           :use ((:instance fn-sn-observed-seed-is-state))
           :in-theory (e/d (fn-sn-indexedp fn-sn-observed-seed
                            fn-stx-index-invariantp)
                           (fn-sn-statep fn-node-initial-state
                            fn-stx-index-of-store fn-stx-store
                            fn-sn-observed-seed-is-state)))))

; The opened state is the seed recovered, so its index is the recomputation
; over the replayed store.  -by-recomputation, like fn-sn-recover's own row.
(defthm fn-sn-open-observed-is-indexed-by-recomputation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sn-indexedp
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal"
           :use ((:instance fn-sn-recover-preserves-indexedp-by-recomputation
                            (s (fn-sn-observed-seed groups capacity frontier
                                                    records)))
                 (:instance fn-sn-observed-seed-is-indexed))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                            fn-sn-observed-historyp fn-record-uint32p)
                           (fn-sn-indexedp fn-sn-recover fn-sn-observed-seed
                            fn-sn-statep fn-sn-observed-configurationp
                            fn-sn-observed-seed-is-indexed
                            fn-sn-recover-preserves-indexedp-by-recomputation)))))

(defthm fn-sn-open-observed-success-remains-recovering
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and (equal (fn-sf-phase
                        (fn-sn-files
                         (fn-sn-open-state
                          (fn-sn-open-observed groups capacity frontier records))))
                       :recovering)
                (equal (fn-sf-barriers
                        (fn-sn-files
                         (fn-sn-open-state
                          (fn-sn-open-observed groups capacity frontier records))))
                       0)))
  :hints (("Goal"
           :use ((:instance fn-sn-recover-replaying-output-is-exact
                            (st (fn-sn-observed-seed groups capacity
                                                     frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                                                  )
                            (fn-sn-recover fn-sn-statep fn-sf-statep
                             fn-sf-history-recoverablep fn-sf-replay-node)))))

; Successful reopening has no fresh-process ghost acknowledgements.  The
; returned file state contains exactly the observed records and frontier, while
; the node is the actual replay-plus-frontier result used by fn-sn-recover.
(defthm fn-sn-open-observed-success-exact-history
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and (equal (fn-sf-records
                        (fn-sn-files
                         (fn-sn-open-state
                          (fn-sn-open-observed groups capacity frontier records))))
                       records)
                (equal (fn-sf-frontier
                        (fn-sn-files
                         (fn-sn-open-state
                          (fn-sn-open-observed groups capacity frontier records))))
                       frontier)
                (equal (fn-sf-successes
                        (fn-sn-files
                         (fn-sn-open-state
                          (fn-sn-open-observed groups capacity frontier records))))
                       nil)
                (equal (fn-sn-node
                        (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       (fn-sf-replay-node groups capacity records frontier))))
  :hints (("Goal"
           :use ((:instance fn-sn-recover-replaying-output-is-exact
                            (st (fn-sn-observed-seed groups capacity
                                                     frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                                                 fn-sn-observed-seed)
                            (fn-sn-recover fn-sn-statep fn-sf-statep
                             fn-sf-history-recoverablep fn-sf-replay-node)))))

(defthm fn-sn-open-observed-invalid-frontier-refuses
  (implies (not (fn-record-uint32p frontier))
           (equal (fn-sn-open-observed groups capacity frontier records)
                  (if (fn-sn-observed-configurationp groups capacity)
                      (fn-sn-open-error :frontier)
                    (fn-sn-open-error :configuration))))
  :hints (("Goal" :in-theory (enable fn-sn-open-observed))))

(defthm fn-sn-open-observed-invalid-history-refuses
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-record-uint32p frontier)
                (not (fn-sf-record-listp records 0 0 frontier)))
           (equal (fn-sn-open-observed groups capacity frontier records)
                  (fn-sn-open-error :history)))
  :hints (("Goal" :in-theory (enable fn-sn-open-observed))))

; Four actual successful fsync observations leave recovery closed; the fifth
; is the first transition to :ready.  No constructor or host result can bypass
; fn-sn-io/fn-sf-recovery-barrier in these statements.
(defthm fn-sn-open-observed-not-ready-before-five-barriers
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and
            (equal (fn-sf-phase
                    (fn-sn-files
                     (fn-sn-observed-rebarrier
                      (fn-sn-open-state
                       (fn-sn-open-observed groups capacity frontier records)) 0)))
                   :recovering)
            (equal (fn-sf-phase
                    (fn-sn-files
                     (fn-sn-observed-rebarrier
                      (fn-sn-open-state
                       (fn-sn-open-observed groups capacity frontier records)) 1)))
                   :recovering)
            (equal (fn-sf-phase
                    (fn-sn-files
                     (fn-sn-observed-rebarrier
                      (fn-sn-open-state
                       (fn-sn-open-observed groups capacity frontier records)) 2)))
                   :recovering)
            (equal (fn-sf-phase
                    (fn-sn-files
                     (fn-sn-observed-rebarrier
                      (fn-sn-open-state
                       (fn-sn-open-observed groups capacity frontier records)) 3)))
                   :recovering)
            (equal (fn-sf-phase
                    (fn-sn-files
                     (fn-sn-observed-rebarrier
                      (fn-sn-open-state
                       (fn-sn-open-observed groups capacity frontier records)) 4)))
                   :recovering)))
  :hints (("Goal"
           :use ((:instance fn-sn-open-observed-success-is-state)
                 (:instance fn-sn-open-observed-success-remains-recovering)
                 (:instance fn-sn-observed-four-ok-barriers-remain-recovering
                            (st (fn-sn-open-state
                                 (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-sn-open-observed-success-is-state
                               fn-sn-open-observed-success-remains-recovering
                               fn-sn-observed-four-ok-barriers-remain-recovering
                               fn-sn-open-observed
                               fn-sn-open-okp fn-sn-observed-rebarrier
                                ))))

(defthm fn-sn-open-observed-five-barriers-open-ready
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (equal (fn-sf-phase
                   (fn-sn-files
                    (fn-sn-observed-rebarrier
                     (fn-sn-open-state
                      (fn-sn-open-observed groups capacity frontier records)) 5)))
                  :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-open-observed-success-is-state)
                 (:instance fn-sn-open-observed-success-remains-recovering)
                 (:instance fn-sn-observed-five-ok-barriers-is-ready
                            (st (fn-sn-open-state
                                 (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-sn-open-observed-success-is-state
                               fn-sn-open-observed-success-remains-recovering
                               fn-sn-observed-five-ok-barriers-is-ready
                               fn-sn-open-observed
                               fn-sn-open-okp fn-sn-observed-rebarrier
                                ))))

; =============================================================================
; Trace theorems rooted at the observed physical-image entry (folded from
; store-observed-traces.lisp, 2026-09-19 realignment).  host/store-node-host.lisp:27
; calls fn-sn-open-observed on each process start.  This part (1) establishes
; fn-snt-relation at that root, so every trace theorem in store-node-traces
; and store-node-resolution applies to the state the host resumes from (D6),
; and (2) carries acknowledged-record retention across the reopen boundary
; with A-DURABILITY as the hypothesis fn-sf-crash-imagep (D5).  The retention
; claim is stated over records, which the adapter persists; no acknowledgement
; anchor is reconstructed from the image.
(local (in-theory (enable fn-store-files-traces-vocabulary
                          fn-store-node-traces-vocabulary
                          fn-store-node-resolution-vocabulary)))

; -----------------------------------------------------------------------------
; The process root establishes the live-history relation (D6).

(defthm fn-sn-open-observed-success-configuration
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (and (equal (fn-sn-groups
                        (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       groups)
                (equal (fn-sn-capacity
                        (fn-sn-open-state
                         (fn-sn-open-observed groups capacity frontier records)))
                       capacity)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                                                  fn-sn-observed-seed
                                                 fn-sn-recover fn-sn-update
                                                  
                                                 )
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sf-recover)))))

; The opened kernel state reached :recovering, which fn-sf-recover grants only
; to a replayable history at its own frontier.
(defthm fn-sn-open-observed-success-implies-recoverable-history
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sf-history-recoverablep groups capacity records frontier))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                                                  fn-sn-observed-seed
                                                 fn-sn-recover fn-sf-recover
                                                 fn-sn-update 
                                                   )
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node)))))

; Every process starts here.  A successful open satisfies the same relation
; that fn-sn-initial satisfies, so fn-snrt-mixed-trace-preserves-live-history-relation
; and its consequences hold for the host's actual starting state.
(defthm fn-sn-open-observed-success-has-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-is-state
                 fn-sn-open-observed-success-remains-recovering
                 fn-sn-open-observed-success-exact-history
                 fn-sn-open-observed-success-configuration
                 fn-sn-open-observed-success-implies-recoverable-history)
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep)
                            (fn-sn-open-observed fn-sn-open-okp
                             fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-snt-pending-linkp
                             fn-sn-completion-enabledp  
                               
                               
                             fn-sf-record-phasep
                             fn-sn-open-observed-success-is-state
                             fn-sn-open-observed-success-remains-recovering
                             fn-sn-open-observed-success-exact-history
                             fn-sn-open-observed-success-configuration
                             fn-sn-open-observed-success-implies-recoverable-history)))))

; -----------------------------------------------------------------------------
; Reopen succeeds on every structurally valid replayable image, and retains
; every acknowledged record under A-DURABILITY as a hypothesis (D5).

(defthm fn-sn-recover-of-recoverable-replaying-is-recovering
  (implies (and (fn-sn-statep st)
                (equal (fn-sf-phase (fn-sn-files st)) :replaying)
                (fn-sf-history-recoverablep (fn-sn-groups st) (fn-sn-capacity st)
                                            (fn-sf-records (fn-sn-files st))
                                            (fn-sf-frontier (fn-sn-files st))))
           (equal (fn-sf-phase (fn-sn-files (fn-sn-recover st))) :recovering))
  :hints (("Goal"
           :use ((:instance fn-sn-statep-implies-files-statep (st st)))
           :in-theory (e/d (fn-sn-recover fn-sf-recover fn-sn-update 
                                           )
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node)))))

(defthm fn-sn-open-observed-succeeds-on-recoverable-image
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records)
                (fn-sf-history-recoverablep groups capacity records frontier))
           (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records)))
  :hints (("Goal"
           :use (fn-sn-observed-seed-is-state
                 (:instance fn-sn-recover-preserves-state
                            (s (fn-sn-observed-seed groups capacity frontier records)))
                 (:instance fn-sn-recover-of-recoverable-replaying-is-recovering
                            (st (fn-sn-observed-seed groups capacity frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                                                 fn-sn-observed-configurationp
                                                 fn-sn-observed-historyp
                                                 fn-sn-observed-seed 
                                                  
                                                  
                                                  
                                                 )
                            (fn-sn-statep fn-sf-statep fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sn-recover
                             fn-sn-observed-seed-is-state
                             fn-sn-recover-preserves-state
                             fn-sn-recover-of-recoverable-replaying-is-recovering)))))

; A-DURABILITY as hypothesis.  For every image the platform may leave behind
; from a related live state (fn-sf-crash-imagep, store-files.lisp), the host's
; reopen entry succeeds and every pair acknowledged before the crash names a
; record of the reopened state.  The acknowledgement list itself is nil after
; reopen (fn-sn-open-observed-success-exact-history); the guarantee is carried
; by the records the adapter persists, not by a reconstructed ghost.
; The live-history relation carries the observed configuration predicate
; through fn-sn-statep (fn-snt-relation-implies-structural-state).
(defthm fn-snt-relation-implies-observed-configuration
  (implies (fn-snt-relation s)
           (fn-sn-observed-configurationp (fn-sn-groups s) (fn-sn-capacity s)))
  :hints (("Goal"
           :use fn-snt-relation-implies-structural-state
           :in-theory (e/d (fn-sn-statep fn-sn-observed-configurationp)
                            (fn-snt-relation fn-sf-statep fn-node-statep
                             fn-snt-relation-implies-structural-state
                             fn-snt-typed-store-components)))))

(defthm fn-sn-acknowledged-record-survives-observed-reopen
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (and (fn-sn-open-okp
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                (fn-sf-record-has-pairp
                 pair
                 (fn-sf-records
                  (fn-sn-files
                   (fn-sn-open-state
                    (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                         frontier records)))))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-observed-configuration
                 fn-snt-admissible-crash-image-is-recoverable
                 (:instance fn-sf-admissible-image-facts (s (fn-sn-files s)))
                 (:instance fn-sn-open-observed-succeeds-on-recoverable-image
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-observed-historyp)
                            (fn-snt-relation fn-sn-statep fn-sf-statep fn-node-statep
                             fn-sn-observed-configurationp
                             fn-snt-relation-implies-observed-configuration
                             fn-snt-relation-implies-structural-state
                             fn-sf-crash-imagep fn-sn-open-observed fn-sn-open-okp
                              fn-sf-history-recoverablep
                             fn-sf-replay-node fn-sf-record-has-pairp
                             fn-sf-record-listp  
                               
                             fn-snt-admissible-crash-image-is-recoverable
                             fn-sf-admissible-image-facts
                             fn-sn-open-observed-succeeds-on-recoverable-image
                             fn-sn-open-observed-success-exact-history)))))

; The PLATFORM twin of the reopen guarantee (D14-b, D14-c).  The host's reopen
; entry succeeds on EVERY image the platform may leave, including both
; rollbacks, and not only on the images a consumer may rely on.  This is the
; half of specs/crash-model-v2.md K4 that the wider predicate makes new.
;
; The acknowledged-record half is deliberately NOT restated over the wider
; predicate: on both rollback arms the arm's own (null (fn-sf-successes s))
; and this theorem's member-equal hypothesis are contradictory, so the
; restatement would be fn-sn-acknowledged-record-survives-observed-reopen
; with two vacuous arms, which is not a theorem worth citing.  What carries
; the acknowledged record across the wider predicate is
; fn-sf-recovery-admissible-image-facts (books/store-files-invariants.lisp),
; which says it over every arm without a vacuous one.
(defthm fn-sn-recovery-admissible-image-reopens
  (implies (and (fn-snt-relation s)
                (fn-sf-recovery-crash-imagep (fn-sn-files s) frontier records))
           (fn-sn-open-okp
            (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                 frontier records)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-observed-configuration
                 fn-snt-recovery-admissible-crash-image-is-recoverable
                 (:instance fn-sf-recovery-admissible-image-facts
                            (s (fn-sn-files s)))
                 (:instance fn-sn-open-observed-succeeds-on-recoverable-image
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-observed-historyp)
                           (fn-snt-relation fn-sn-statep fn-sf-statep fn-node-statep
                            fn-sn-observed-configurationp
                            fn-snt-relation-implies-observed-configuration
                            fn-snt-relation-implies-structural-state
                            fn-sf-crash-imagep fn-sf-recovery-crash-imagep
                            fn-sn-open-observed fn-sn-open-okp
                            fn-sf-history-recoverablep
                            fn-sf-replay-node fn-sf-record-has-pairp
                            fn-sf-record-listp
                            fn-snt-recovery-admissible-crash-image-is-recoverable
                            fn-sf-recovery-admissible-image-facts
                            fn-sn-open-observed-succeeds-on-recoverable-image)))))

; -----------------------------------------------------------------------------
; The trace theorems re-rooted at the process entry.

(defthm fn-snrt-observed-open-mixed-trace-preserves-live-history-relation
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-snt-relation
            (fn-snrt-run
             (fn-sn-open-state
              (fn-sn-open-observed groups capacity frontier records))
             events)))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-has-live-history-relation
                 (:instance fn-snrt-mixed-trace-preserves-live-history-relation
                            (s (fn-sn-open-state
                                (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp ))))

; The ready or recovered node of any process that started from an observed
; image and ran any finite mixed trace is exact replay of its own surviving
; history and frontier.
(defthm fn-snrt-observed-open-ready-node-is-exact-replay
  (let ((final (fn-snrt-run
                (fn-sn-open-state
                 (fn-sn-open-observed groups capacity frontier records))
                events)))
    (implies (and (fn-sn-open-okp
                   (fn-sn-open-observed groups capacity frontier records))
                  (member-equal (fn-sf-phase (fn-sn-files final))
                                '(:ready :recovering :fenced-recovery)))
             (equal (fn-sn-node final)
                    (fn-sf-replay-node (fn-sn-groups final) (fn-sn-capacity final)
                                       (fn-sf-records (fn-sn-files final))
                                       (fn-sf-frontier (fn-sn-files final))))))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-has-live-history-relation
                 (:instance fn-snrt-mixed-trace-ready-node-is-exact-replay
                            (s (fn-sn-open-state
                                (fn-sn-open-observed groups capacity frontier records)))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp  fn-sf-replay-node))))

; Acknowledged before the crash, present after reopen, present after any
; further mixed trace of the reopened process.
(defthm fn-snrt-acknowledged-record-retained-across-observed-reopen
  (let ((final (fn-snrt-run
                (fn-sn-open-state
                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                      frontier records))
                events)))
    (implies (and (fn-snt-relation s)
                  (fn-sf-crash-imagep (fn-sn-files s) frontier records)
                  (member-equal pair (fn-sf-successes (fn-sn-files s))))
             (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files final)))))
  :hints (("Goal"
           :use (fn-sn-acknowledged-record-survives-observed-reopen
                 (:instance fn-sn-open-observed-success-has-live-history-relation
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-snrt-mixed-trace-records-prefix
                            (s (fn-sn-open-state
                                (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                     frontier records))))
                 (:instance fn-sf-record-pair-preserved-by-prefix
                            (records
                             (fn-sf-records
                              (fn-sn-files
                               (fn-sn-open-state
                                (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                     frontier records)))))
                            (more-records
                             (fn-sf-records
                              (fn-sn-files
                               (fn-snrt-run
                                (fn-sn-open-state
                                 (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                                      frontier records))
                                events))))))
           :in-theory (disable fn-snt-relation fn-snrt-run fn-sn-open-observed
                               fn-sn-open-okp  fn-sf-crash-imagep
                               fn-sf-record-has-pairp fn-sf-prefixp 
                                 
                               
                               fn-sn-acknowledged-record-survives-observed-reopen
                               fn-sn-open-observed-success-has-live-history-relation
                               fn-snrt-mixed-trace-records-prefix
                               fn-sf-record-pair-preserved-by-prefix))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn: the open recognizers, the seed, the entry point
; and the rebarrier helper, and under a name the barrier-counting and
; recovery-projection lemmas.  Enabled on include: the open-result record
; lemmas, the seed and success keystones, the refusal keystones, the
; five-barrier keystones, the process-root relation keystone (D6), the
; reopen retention keystones (D5) and the re-rooted trace keystones.
(deftheory fn-store-observed-vocabulary
  '(fn-sn-recover-replaying-output-is-exact fn-sn-statep-implies-files-statep
    fn-sn-observed-one-ok-barrier fn-sn-observed-fifth-ok-barrier-is-ready
    fn-sn-observed-rebarrier-successor
    fn-sn-observed-four-ok-barriers-remain-recovering
    fn-sn-observed-five-ok-barriers-is-ready
    fn-sn-open-observed-success-configuration
    fn-sn-open-observed-success-implies-recoverable-history
    fn-sn-recover-of-recoverable-replaying-is-recovering))
(in-theory (disable fn-store-observed-vocabulary
                    fn-sn-open-okp fn-sn-open-errorp fn-sn-observed-configurationp
                    fn-sn-observed-seed fn-sn-observed-historyp
                    fn-sn-open-observed fn-sn-observed-rebarrier))
