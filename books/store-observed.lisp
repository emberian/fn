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
(include-book "store-node-invariants")

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
(defun fn-sn-open-okp (result)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp result) (equal (len result) 2)
       (equal (fn-sn-open-kind result) :ok)
       (fn-sn-statep (fn-sn-open-state result))))

(verify-guards fn-sn-open-okp)
(defun fn-sn-open-errorp (result)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp result) (equal (len result) 2)
       (equal (fn-sn-open-kind result) :error)))

(verify-guards fn-sn-open-errorp)

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
              (fn-node-initial-state groups capacity)))

(verify-guards fn-sn-observed-seed)

(defun fn-sn-observed-historyp (frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-record-uint32p frontier)
       (fn-sf-record-listp records 0 0 frontier)))

(verify-guards fn-sn-observed-historyp)

; Structural checks precede replay.  A structurally valid but semantically
; unreplayable history reaches the actual recovery transition and returns the
; distinct :replay refusal below.
(defun fn-sn-open-observed (groups capacity frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-sn-observed-configurationp groups capacity))
      (fn-sn-open-error :configuration)
    (if (not (fn-record-uint32p frontier))
        (fn-sn-open-error :frontier)
      (if (not (fn-sf-record-listp records 0 0 frontier))
          (fn-sn-open-error :history)
        (let ((seed (fn-sn-observed-seed groups capacity frontier records)))
          ; Keep the constructed composition independently checked before it is
          ; allowed to enter the kernel.  This is fail-closed if either side of
          ; the composed state representation changes.
          (if (not (fn-sn-statep seed))
              (fn-sn-open-error :image)
            (let ((opened (fn-sn-recover seed)))
              (if (and (fn-sn-statep opened)
                       (equal (fn-sf-phase (fn-sn-files opened)) :recovering))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :replay)))))))))

(verify-guards fn-sn-open-observed)

(defthm fn-sn-observed-seed-is-state
  (implies (and (fn-sn-observed-configurationp groups capacity)
                (fn-sn-observed-historyp frontier records))
           (fn-sn-statep (fn-sn-observed-seed groups capacity frontier records)))
  :hints (("Goal"
           :use ((:instance fn-node-initial-state-is-state
                            (groups groups) (capacity capacity)))
           :in-theory (enable fn-sn-observed-configurationp
                               fn-sn-observed-historyp fn-sn-observed-seed
                               fn-sn-statep fn-sn-make
                               fn-sf-statep fn-sf-make fn-sf-phase-shapep))))

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
                                           fn-sn-make fn-sf-make)
                            (fn-sn-statep fn-sf-statep
                             fn-sf-history-recoverablep fn-sf-replay-node)))))

; These calls are the existing host-I/O path.  The helper is only notation for
; finite proof/test sequences; it does not write a barrier directly.
(defun fn-sn-observed-rebarrier (st count)
  (declare (xargs :guard t :verify-guards nil :measure (nfix count)))
  (mbe :logic (if (zp count)
      st
    (fn-sn-observed-rebarrier
     (fn-sn-io st :recovery-barrier :ok) (1- count)))
       :exec (if (not (posp count))
      st
    (fn-sn-observed-rebarrier
     (fn-sn-io st :recovery-barrier :ok) (1- count)))))

; The mbe conjecture is zp versus not-posp; keep the composed-machine
; definitions out of it (the composed-machine rules otherwise stall it).
(verify-guards fn-sn-observed-rebarrier
  :hints (("Goal" :in-theory (union-theories '(zp posp)
                                             (theory 'minimal-theory)))))

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
                                      fn-sn-update fn-sn-make fn-sf-make)
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
                                      fn-sn-update fn-sn-make fn-sf-make)
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
                             fn-sn-statep fn-sf-statep fn-sf-barriers
                             fn-sf-phase fn-sn-files)))))

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
                             fn-sn-statep fn-sf-statep fn-sf-barriers
                             fn-sn-io fn-sf-phase fn-sn-files)))))

(defthm fn-sn-open-observed-success-is-state
  (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
           (fn-sn-statep
            (fn-sn-open-state
             (fn-sn-open-observed groups capacity frontier records))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-open-okp fn-sn-open-state)
                            (fn-sn-open-observed fn-sn-statep)))))

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
                                                 fn-sn-open-state fn-sn-open-ok)
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
                                                 fn-sn-open-state fn-sn-open-ok
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
                               fn-sn-open-observed fn-sn-open-state
                               fn-sn-open-okp fn-sn-observed-rebarrier
                               fn-sf-phase fn-sn-files))))

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
                               fn-sn-open-observed fn-sn-open-state
                               fn-sn-open-okp fn-sn-observed-rebarrier
                               fn-sf-phase fn-sn-files))))
