; Commit durability over every execution and every environment (ember,
; 2026-11-07). FN2-ENV-RUN interprets any list of host-boundary actions,
; interleaved with fn2-turn, over a live core; the device is whatever
; books/assumptions-device.lisp's A-FENCE-PERSISTS admits; recovery is the
; real recovery row driven by fn2-turn over a fresh core reading a crash
; image. FN2-COMMIT-ACK-IMPLIES-DURABLE (the simulator run) is to become a
; tested instance of the statement here.
(in-package "ACL2")
(include-book "host-boundary")
(include-book "executor-contracts")
(include-book "pointwise-contracts")
(include-book "commit-turn-frame")
(include-book "assumptions-device")
(include-book "owed")
(include-book "stobj-scope")
(deflabel fn2-env-before-ops-conservation)
(include-book "ops-conservation")
; FN2-OPS-CREDIT-CONSERVATION's per-operation exports are used by name only.
(local (in-theory (set-difference-theories
                   (current-theory :here)
                   (set-difference-theories (universal-theory :here)
                                            (universal-theory 'fn2-env-before-ops-conservation)))))
; D26: the proofs here reason about the core and the children named below;
; every other stobj's column facts (keyed on NTH and LEN) only cost type-set
; work, and FN2-LAYOUTP-LIST backchains every TRUE-LISTP goal through the
; recursive layout recognizer (2.0M of this book's prover frames, all useless).
(local (fn2-stobj-scope fn2-core fn2-ops fn2-pool fn2-commit fn2-commit-root fn2-commit-io fn2-commit-settled
                        fn2-commit-member fn2-recovery-machine fn2-alloc-edges fn2-extents fn2-machines
                        fn2-control fn2-trace fn2-sched fn2-scribe fn2-listener))
(local (in-theory (disable fn2-layoutp-list fn2-layoutp-cdr)))
; The device log's list lemmas and the ops, pool and loan lemmas that read no
; core, proved over the core's children alone.
(include-book "commit-durable-children")
; Born there, in that book's order, after the core-level events up to here:
(local (in-theory (disable fn2-env-pool-octets-is-logical fn2-env-logical-octets-prefix)))

;; ---------------------------------------------------------------------------
;; THE VOCABULARY. An action is any object; one the vocabulary does not name,
;; or one the core refuses, changes nothing the statement observes but the
;; core's own stray count. No action list is excluded.
;;   (:turn)                                     fn2-turn
;;   (:take)                                     the device takes the outbox head:
;;       fn2-host-outbox-peek, fn2-host-action, fn2-host-op-span, the payload
;;       octets of an output loan, fn2-host-outbox-ack (and fn2-host-op-finish
;;       for a resultless kind, as host/adapter.lisp's fn2-n-take); during
;;       recovery a read's loan is filled from the crash image at take
;;   (:post-result cell slot gen evkind outcome reason count aux0 aux1)
;;   (:accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3)
;;                                               fn2-host-post-result / -accept-result:
;;       any completion, any order, any outcome, any delay; the core decides
;;       which it accepts
;;   (:loan-write slot gen at octets)            arbitrary octets into an input
;;       loan (network bytes; reads outside recovery), through the core's
;;       fn2-pool-adapter-write, from loan index AT
;;   (:clock mono real flags) (:signal bits)     fn2-host-post-clock / -signal
;;   (:epoch e)                                  fn2-alloc-begin-epoch: the host opens
;;       writer epoch E (alloc.lisp: on its BEGIN_WRITER_EPOCH fence's completion)
;;   (:admit members mode)                       the host's commit admission
;;       (fn2-commit-admit-keyed, the B fixture's call between turns) and the
;;       executor's wake for the admitted row; not during recovery

; The stobj-let pieces see the core invariant opened; nothing after them does.
(encapsulate ()
(local (in-theory (enable fn2-core-wfp)))
(defun fn2-env-octets (addr n fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp addr) (natp n))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (octets) (fn2-env-pool-octets n addr fn2-pool) octets))

(defun fn2-env-pool-fill (rslot rgen slot gen idx octets fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp idx))))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-adapter-write rslot rgen slot gen idx (car octets) fn2-pool)
      (declare (ignore code))
      (fn2-env-pool-fill rslot rgen slot gen (+ 1 idx) (cdr octets) fn2-pool))))
(fn2-pool-preserves fn2-env-pool-fill (rslot rgen slot gen idx octets fn2-pool) :disable nil)
(defun fn2-env-fill (rslot rgen slot gen idx octets fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp idx))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (fn2-pool) (fn2-env-pool-fill rslot rgen slot gen idx octets fn2-pool) fn2-core))
(fn2-core-preserves fn2-env-fill (rslot rgen slot gen idx octets fn2-core) :rows nil)

(defun fn2-env-begin-epoch (epoch fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (unsigned-byte-p 60 epoch)) fn2-core
    (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
      (code fn2-extents) (fn2-alloc-begin-epoch epoch fn2-extents)
      (let ((ignored code)) (declare (ignore ignored)) fn2-core))))
(fn2-core-preserves fn2-env-begin-epoch (epoch fn2-core) :rows nil
  :hints (("Goal" :in-theory (enable fn2-alloc-begin-epoch))))

(defun fn2-env-post-count (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-post-count fn2-ops) n))

(fn2-core-preserves fn2-host-post-result (cell slot gen evkind outcome reason count aux0 aux1 fn2-core) :rows nil)
(fn2-core-preserves fn2-host-post-accept-result
  (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core) :rows nil)
(fn2-core-preserves fn2-host-post-clock (mono real flags fn2-core) :rows nil)
(fn2-core-preserves fn2-host-post-signal (bits fn2-core) :rows nil)
(fn2-core-preserves fn2-host-outbox-ack (n fn2-core) :position 1 :rows nil)
(fn2-core-preserves fn2-host-op-finish (slot gen fn2-core) :position 1 :rows nil))
(in-theory (disable fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-host-stray
                    fn2-host-outbox-queued))

; The device takes the outbox head. (mv entry fn2-core); ENTRY nil: nothing taken.
(defun fn2-env-take (recoveryp image fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code slot gen) (fn2-host-outbox-peek 0 fn2-core))
       ((unless (eq code :ok)) (mv nil fn2-core))
       ((mv acode kind & & rslot rgen off len offset fua & & & & &) (fn2-host-action slot fn2-core))
       ((unless (eq acode :ok)) (mv nil fn2-core))
       ((mv span address span-len) (fn2-host-op-span slot gen fn2-core))
       ((unless (eq span :ok)) (mv nil fn2-core))
       (octets (cond ((fn2-op-output-kindp kind) (fn2-env-octets (nfix address) (nfix span-len) fn2-core))
                     ((and recoveryp (equal kind *fn2-action-read*))
                      (fn2-dev-image-octets image (nfix offset) (nfix len)))
                     (t nil)))
       ((mv ack fn2-core) (fn2-host-outbox-ack 1 fn2-core))
       ((unless (eq ack :ok)) (mv nil fn2-core))
       ((mv & fn2-core) (if (fn2-action-completionp kind) (mv :ok fn2-core)
                          (fn2-host-op-finish slot gen fn2-core)))
       (fn2-core (if (and recoveryp (equal kind *fn2-action-read*))
                     (fn2-env-fill rslot rgen slot gen (nfix off) octets fn2-core)
                   fn2-core)))
    (mv (list :take slot gen kind offset fua octets) fn2-core)))
(fn2-core-preserves fn2-env-take (recoveryp image fn2-core) :position 1 :rows nil)

; A completion. During recovery a read the device took is answered honestly:
; a done read reports the octets the image delivered at take.
(defun fn2-env-post (action recoveryp rlog fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((cell (fn2-env-arg 1 action)) (slot (fn2-env-arg 2 action)) (gen (fn2-env-arg 3 action))
       (evkind (fn2-env-arg 4 action)) (outcome (fn2-env-arg 5 action))
       (count (fn2-env-arg 7 action))
       (e (fn2-env-taken slot gen rlog))
       ((when (and recoveryp e (equal (nth 3 e) *fn2-action-read*)
                   (equal outcome *fn2-outcome-done*)
                   (not (equal count (len (nth 6 e))))))
        (mv nil fn2-core))
       (before (fn2-env-post-count fn2-core))
       (fn2-core (fn2-host-post-result cell slot gen evkind outcome (fn2-env-arg 6 action)
                                       count (fn2-env-arg 8 action) (fn2-env-arg 9 action) fn2-core))
       (accepted (not (equal before (fn2-env-post-count fn2-core)))))
    (mv (and accepted (equal cell 0) (list :result slot gen evkind outcome count)) fn2-core)))
(fn2-core-preserves fn2-env-post (action recoveryp rlog fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-env-taken fn2-env-post-count fn2-env-arg))))

; Octets into an input loan the device holds (never a recovery read's).
(defun fn2-env-loan-write (action recoveryp fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((slot (fn2-env-arg 1 action)) (gen (fn2-env-arg 2 action))
       ((mv acode kind & & rslot rgen off & & & & & & & &) (fn2-host-action slot fn2-core))
       ((unless (and (eq acode :ok) (fn2-op-input-kindp kind)
                     (not (and recoveryp (equal kind *fn2-action-read*)))))
        fn2-core))
    (fn2-env-fill rslot rgen slot gen (+ (nfix off) (nfix (fn2-env-arg 3 action)))
                  (fn2-env-arg 4 action) fn2-core)))
(fn2-core-preserves fn2-env-loan-write (action recoveryp fn2-core) :rows nil)

(defun fn2-env-admit (members mode fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (code id batch event fn2-core) (fn2-commit-admit-keyed members mode 0 0 0 fn2-core)
    (declare (ignore batch event))
    (if (eq code :ok) (fn2-exec-wake id fn2-core) fn2-core)))
(fn2-core-preserves fn2-env-admit (members mode fn2-core) :rows nil)

; One action. (mv entry fn2-core): ENTRY is the device-log entry it made, or nil.
(defun fn2-env-step (action recoveryp image rlog fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (case (fn2-env-tag action)
    (:turn (mv-let (status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)
             (declare (ignore status nobs nvisits nactions))
             (mv nil fn2-core)))
    (:take (fn2-env-take recoveryp image fn2-core))
    (:post-result (fn2-env-post action recoveryp rlog fn2-core))
    (:accept-result
     (let ((fn2-core (fn2-host-post-accept-result
                      (fn2-env-arg 1 action) (fn2-env-arg 2 action) (fn2-env-arg 3 action)
                      (fn2-env-arg 4 action) (fn2-env-arg 5 action) (fn2-env-arg 6 action)
                      (fn2-env-arg 7 action) (fn2-env-arg 8 action) (fn2-env-arg 9 action)
                      (fn2-env-arg 10 action) (fn2-env-arg 11 action) (fn2-env-arg 12 action) fn2-core)))
       (mv nil fn2-core)))
    (:loan-write (let ((fn2-core (fn2-env-loan-write action recoveryp fn2-core))) (mv nil fn2-core)))
    (:clock (let ((fn2-core (fn2-host-post-clock (fn2-env-arg 1 action) (fn2-env-arg 2 action)
                                                 (fn2-env-arg 3 action) fn2-core)))
              (mv nil fn2-core)))
    (:signal (let ((fn2-core (fn2-host-post-signal (fn2-env-arg 1 action) fn2-core))) (mv nil fn2-core)))
    (:epoch (let ((fn2-core (fn2-env-begin-epoch (fn2-env-arg 1 action) fn2-core))) (mv nil fn2-core)))
    (:admit (let ((fn2-core (if recoveryp fn2-core
                              (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core))))
              (mv nil fn2-core)))
    (otherwise (mv nil fn2-core))))
(fn2-core-preserves fn2-env-step (action recoveryp image rlog fn2-core) :position 1 :rows nil)

;; ---------------------------------------------------------------------------
;; ACKNOWLEDGED: a batch some commit row shows with a member reply (cb-acks
;; positive), observed after every action. B1's ack is batch-level: one reply
;; obliges the whole batch.
(defun fn2-env-commit-ids (profile)
  (declare (xargs :guard t))
  (list (fn2-machine-global-id *fn2-commit-kind* 0 profile)
        (fn2-machine-global-id *fn2-commit-kind* 1 profile)))
(defun fn2-env-observe (ids acked fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (true-listp acked))))
  (if (atom ids) acked
    (fn2-env-observe
     (cdr ids)
     (if (and (eq (fn2-machine-cb-acks-read-code (car ids) fn2-core) :ok)
              (eq (fn2-machine-batch-no-read-code (car ids) fn2-core) :ok)
              (posp (fn2-machine-cb-acks (car ids) fn2-core)))
         (add-to-set-equal (fn2-machine-batch-no (car ids) fn2-core) acked)
       acked)
     fn2-core)))

; (mv rlog acked fn2-core): RLOG newest first.
(defthm fn2-env-observe-true-listp
  (implies (true-listp acked) (true-listp (fn2-env-observe ids acked fn2-core)))
  :hints (("Goal" :induct (fn2-env-observe ids acked fn2-core)
           :in-theory '(fn2-env-observe atom add-to-set-equal true-listp))))
(defun fn2-env-steps (actions ids rlog acked fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (true-listp acked))))
  (if (atom actions) (mv rlog acked fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (fn2-env-steps (cdr actions) ids (if entry (cons entry rlog) rlog)
                     (fn2-env-observe ids acked fn2-core) fn2-core))))
(fn2-core-preserves fn2-env-steps (actions ids rlog acked fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (disable fn2-env-observe))))

(defthm fn2-env-init-executor-shape
  (implies (and (fn2-corep fn2-core) (fn2-core-profilep profile))
           (and (fn2-corep (fn2-init-executor profile mode scribe-p fn2-core))
                (fn2-core-wfp (fn2-init-executor profile mode scribe-p fn2-core))))
  :hints (("Goal" :in-theory (enable fn2-init-executor))))
(in-theory (disable fn2-init-executor))
(make-event
 `(defthm fn2-corep-of-fresh-core
    (fn2-corep (create-fn2-core))
    :hints (("Goal" :in-theory (enable fn2-corep create-fn2-core
                                       ,@(fn2-env-create-runes *fn2-core-children* (w state)))))))
(in-theory (disable create-fn2-core))
(defthm fn2-env-steps-rlog-true-listp
  (implies (true-listp rlog) (true-listp (mv-nth 0 (fn2-env-steps actions ids rlog acked fn2-core))))
  :hints (("Goal" :induct (fn2-env-steps actions ids rlog acked fn2-core)
           :in-theory (e/d (fn2-env-steps) (fn2-env-step fn2-env-observe)))))

; The run: (LOG ACKED). Genesis as the native host's (fn2-n-make-host).
(defun fn2-env-run (profile actions)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn2-core-profilep profile)) (list nil nil)
    (with-local-stobj fn2-core
      (mv-let (run fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv rlog acked fn2-core)
              (fn2-env-steps actions (fn2-env-commit-ids profile) nil nil fn2-core)))
          (mv (list (reverse rlog) acked) fn2-core))
        run))))
(verify-guards fn2-env-run)

;; ---------------------------------------------------------------------------
;; RECOVERY: a fresh core (listeners :null, as B5's harness), the recovery
;; row started by the host (fn2-recovery-start) with the device assumption's
;; bits (crash-only, persistence fence), then RECOVERY-ACTIONS. The result
;; is (DONE CHAIN): DONE once the row has reached :done, CHAIN its chain
;; length then; the recovered batches are 1..CHAIN, the commits the chain
;; links from genesis.

(defun fn2-env-recovery-id (profile)
  (declare (xargs :guard t))
  (fn2-machine-global-id *fn2-recovery-machine-kind* 0 profile))
(defun fn2-env-recovery-done (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-machine-phase-read-code id fn2-core) :ok)
       (equal (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*)
       (eq (fn2-machine-rc-chain-read-code id fn2-core) :ok)
       (list t (fn2-machine-rc-chain id fn2-core))))
(defun fn2-env-recover-steps (actions id image rlog done fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (or (atom actions) done) (mv done fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) t image rlog fn2-core)
      (fn2-env-recover-steps (cdr actions) id image (if entry (cons entry rlog) rlog)
                             (fn2-env-recovery-done id fn2-core) fn2-core))))
(fn2-core-preserves fn2-env-recover-steps (actions id image rlog done fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable fn2-env-recovery-done))))
(defun fn2-env-recover (profile image actions)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn2-core-profilep profile)) (list nil 0)
    (with-local-stobj fn2-core
      (mv-let (rec fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :null nil fn2-core))
             (id (fn2-env-recovery-id profile))
             ((mv code fn2-core) (fn2-recovery-start id *fn2-env-recovery-assume* 0 fn2-core))
             ((unless (eq code :ok)) (mv (list nil 0) fn2-core))
             ((mv done fn2-core) (fn2-env-recover-steps actions id image nil nil fn2-core)))
          (mv (or done (list nil 0)) fn2-core))
        rec))))
(verify-guards fn2-env-recover)

; Every core profile is supported: a profile without commit rows acknowledges
; nothing and the statement holds of it trivially.
(defun fn2-profile-supportedp (profile)
  (declare (xargs :guard t))
  (fn2-core-profilep profile))

;; ---------------------------------------------------------------------------
;; THE INVARIANT toward the statement, over the run's state after each action:
;; the core, the device log so far, and the acknowledged batches.
;;  OBSERVED: every commit row showing a member reply has its batch in ACKED;
;;  DURABLE:  every batch up to every acknowledged one is durable in the log:
;;            a fenced write of its seal (role 2 of an extent, the frame's
;;            commit field naming it) and fenced writes of that extent's
;;            page and records units (roles 0 and 1).
;; The step kinds that change no commit row's (cb-acks, batch-no) preserve
;; it through log extension alone; :admit and :turn carry the obligations.
(defun fn2-env-seal-commit (octets)
  (declare (xargs :verify-guards nil))
  (b* (((mv code header rest) (fn2-layout-parse *fn2-format-frame-header* octets))
       (n (nth *fn2-format-frame-header-field-payload-length* header))
       ((unless (and (eq code :ok) (natp n) (<= n (len rest))
                     (equal (nth *fn2-format-frame-header-field-frame-kind* header) *frame-kind-seal*)))
        nil)
       ((mv code seal &) (fn2-layout-parse *fn2-format-sealed-batch* (take n rest))))
    (and (eq code :ok) (nth *fn2-format-sealed-batch-field-commit* seal))))
; Entry W of LOG is a fenced seal write of commit B, its extent's page and
; records units fenced too.
(defun fn2-env-seal-durable-at (w b log)
  (declare (xargs :verify-guards nil))
  (let* ((e (nth w log)) (offset (nth 4 e))
         (base (- (nfix offset) (* 2 *fn2-commit-unit-bytes*))))
    (and (fn2-dev-fenced-write-p w log) (natp offset)
         (equal (mod offset *fn2-commit-extent-bytes*) (* 2 *fn2-commit-unit-bytes*))
         (equal (fn2-env-seal-commit (nth 6 e)) b)
         (fn2-dev-fenced-offset-from 0 base log)
         (fn2-dev-fenced-offset-from 0 (+ base *fn2-commit-unit-bytes*) log))))
(defun fn2-env-seal-durable-from (w b log)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-env-seal-durable-at)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((fn2-env-seal-durable-at w b log) t)
        (t (fn2-env-seal-durable-from (+ 1 w) b log))))
(defun fn2-env-batch-durable-p (b log)
  (declare (xargs :verify-guards nil))
  (fn2-env-seal-durable-from 0 b log))
(defun fn2-env-prefix-durable-p (n log)
  (declare (xargs :verify-guards nil))
  (if (zp n) t (and (fn2-env-batch-durable-p n log) (fn2-env-prefix-durable-p (- n 1) log))))
(defun fn2-env-acked-durable-p (acked log)
  (declare (xargs :verify-guards nil))
  (if (atom acked) t
    (and (fn2-env-prefix-durable-p (nfix (car acked)) log)
         (fn2-env-acked-durable-p (cdr acked) log))))

; What a commit row shows the observer.
(defun fn2-env-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) nil
    (cons (list (fn2-machine-cb-acks-read-code (car ids) fn2-core)
                (fn2-machine-batch-no-read-code (car ids) fn2-core)
                (fn2-machine-cb-acks (car ids) fn2-core)
                (fn2-machine-batch-no (car ids) fn2-core))
          (fn2-env-rows (cdr ids) fn2-core))))
(defthm fn2-env-observe-is-rows
  (equal (fn2-env-observe ids acked fn2-core)
         (fn2-env-observe-rows (fn2-env-rows ids fn2-core) acked)))

(defun fn2-env-inv (ids acked log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-observed-p (fn2-env-rows ids fn2-core) acked)
       (fn2-env-acked-durable-p acked log)))

;; ---------------------------------------------------------------------------
;; J1-J4, THE PHASE/HISTORY STRENGTHENING. FN2-ENV-INV is only the evidence
;; projection: a row at :notify with no durable log is consistent with it, and
;; one fn2-turn acknowledges that row's batch (tests/commit-executor-contracts-
;; unit). FN2-ENV-DUR-INV adds what a commit row's phase and flags promise
;; about the device log:
;;  J1 a row past :free has a positive batch (admission assigns it; no arm
;;     writes the column); a row whose reply count is positive, or at :publish
;;     or :notify, has its batch at or below the installed root; a row at
;;     :install has its batch durable in the log;
;;  J2 a row's dependency flag names a write of its role-0 unit answered done
;;     in full, its log flag the role-1 unit and the role-2 seal of its batch;
;;     each fenced once the fence flag is set (or FUA in barrier mode 1); the
;;     three roles share one extent;
;;  J4 the published root is at or below the installed one and at most one
;;     below it, and batches 1..installed are durable in the log (publication
;;     follows predecessor publication: the root installs batch B only as
;;     published + 1, and publishes only the installed batch).
;; J3 (submitted bytes stay bound to their loans) is the link the flags'
;; rises need from the operations table; see FN2-ENV-DUR-INV's owed list.
(defun fn2-env-root (fn2-core)
  ; (ROWSP INSTALLED PUBLISHED) of the commit root's row 0
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (r)
    (if (< 0 (fn2-commit-root-rows fn2-commit-root))
        (list t (nfix (fn2-commit-root-installed 0 fn2-commit-root))
              (nfix (fn2-commit-root-published 0 fn2-commit-root)))
      (list nil 0 0))
    r))
(defun fn2-env-installed (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (nth 1 (fn2-env-root fn2-core)))
; Some write from W on at OFFSET, answered done in full; carrying the seal of
; commit B when B is non-nil; fenced (FN2-DEV-FENCED-WRITE-P) when FENCED.
(defun fn2-env-written-from (w offset b fenced log)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-seal-commit)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((and (fn2-env-done-write-p w log) (equal (nth 4 (nth w log)) offset)
              (or (not b) (equal (fn2-env-seal-commit (nth 6 (nth w log))) b))
              (or (not fenced) (fn2-dev-fenced-write-p w log)))
         t)
        (t (fn2-env-written-from (+ 1 w) offset b fenced log))))
(defun fn2-env-role-offset (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (mv-let (e epoch counter slot gen) (fn2-commit-resource id role fn2-core)
    (declare (ignore epoch counter slot gen))
    (+ (* (nfix e) *fn2-commit-extent-bytes*) (* role *fn2-commit-unit-bytes*))))
(defun fn2-env-role-extent (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (mv-let (e epoch counter slot gen) (fn2-commit-resource id role fn2-core)
    (declare (ignore epoch counter slot gen))
    e))
(defun fn2-env-j1-row (id log fn2-core)
  ; J1
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((batch (fn2-machine-batch-no id fn2-core))
        (installed (fn2-env-installed fn2-core))
        (ackedp (and (eq (fn2-machine-cb-acks-read-code id fn2-core) :ok)
                     (eq (fn2-machine-batch-no-read-code id fn2-core) :ok)
                     (posp (fn2-machine-cb-acks id fn2-core))))
        (rowp (fn2-commit-idp id fn2-core))
        (phase (fn2-machine-phase id fn2-core)))
    (and (implies (and rowp (not (equal phase *fn2-commit-state-free*))) (posp batch))
         (implies (or ackedp (and rowp (member-equal phase (list *fn2-commit-state-publish*
                                                                 *fn2-commit-state-notify*))))
                  (and (posp batch) (<= batch installed)))
         (implies (and rowp (equal phase *fn2-commit-state-install*))
                  (and (posp batch) (fn2-env-batch-durable-p batch log))))))
(defun fn2-env-j2-row (id log fn2-core)
  ; J2
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((batch (fn2-machine-batch-no id fn2-core))
        (rowp (fn2-commit-idp id fn2-core))
        (fenced (or (equal (fn2-machine-cb-fence-ok id fn2-core) 1)
                    (equal (fn2-machine-cb-mode id fn2-core) 1))))
    (and
     (implies (and rowp (or (equal (fn2-machine-cb-deps-ok id fn2-core) 1)
                            (equal (fn2-machine-cb-log-ok id fn2-core) 1)))
              (and (natp (fn2-env-role-extent id 0 fn2-core))
                   (equal (fn2-env-role-extent id 1 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                   (equal (fn2-env-role-extent id 2 fn2-core) (fn2-env-role-extent id 0 fn2-core))))
     (implies (and rowp (equal (fn2-machine-cb-deps-ok id fn2-core) 1))
              (fn2-env-written-from 0 (fn2-env-role-offset id 0 fn2-core) nil
                                    (equal (fn2-machine-cb-fence-ok id fn2-core) 1) log))
     (implies (and rowp (equal (fn2-machine-cb-log-ok id fn2-core) 1))
              (and (fn2-env-written-from 0 (fn2-env-role-offset id 1 fn2-core) nil fenced log)
                   (fn2-env-written-from 0 (fn2-env-role-offset id 2 fn2-core) batch fenced log))))))
(defun fn2-env-j-row (id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-j1-row id log fn2-core) (fn2-env-j2-row id log fn2-core)))
(defun fn2-env-j-rows (ids log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j-row (car ids) log fn2-core) (fn2-env-j-rows (cdr ids) log fn2-core))))
(defun fn2-env-j-frontier (log fn2-core)
  ; J4
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((root (fn2-env-root fn2-core)))
    ; a core without a root row reads (nil 0 0): nothing installed
    (and (<= (nth 2 root) (nth 1 root))
         (<= (nth 1 root) (+ 1 (nth 2 root)))
         (fn2-env-prefix-durable-p (nth 1 root) log))))
;; J3, THE COUNTED-COMPLETION LINK: a row in a write phase has its three
;; role extents shared, and each completion it counted (cb-done) is a write
;; of one of the phase's roles answered done in full in the log at the
;; role's offset (role 2 carrying the seal of its batch), fenced as J2 asks
;; once the fence flag is set (or FUA in barrier mode 1); its entry clauses
;; (FN2-ENV-J3E-ROW) make each write phase start with nothing counted.
(defun fn2-env-role-written (id role fenced log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-env-written-from 0 (fn2-env-role-offset id role fn2-core)
                        (and (equal role 2) (fn2-machine-batch-no id fn2-core)) fenced log))
(defun fn2-env-j3-row (id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)) (done (fn2-machine-cb-done id fn2-core))
        (fence-ok (equal (fn2-machine-cb-fence-ok id fn2-core) 1)))
    (implies (and (fn2-commit-idp id fn2-core)
                  (member-equal phase (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*)))
             (and (natp (fn2-env-role-extent id 0 fn2-core))
                  (equal (fn2-env-role-extent id 1 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                  (equal (fn2-env-role-extent id 2 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                  (if (equal phase *fn2-commit-state-dependencies*)
                      (implies (<= 1 (nfix done)) (fn2-env-role-written id 0 fence-ok log fn2-core))
                    (let ((fenced (or fence-ok (equal (fn2-machine-cb-mode id fn2-core) 1))))
                      (and (implies (<= 1 (nfix done))
                                    (or (fn2-env-role-written id 1 fenced log fn2-core)
                                        (fn2-env-role-written id 2 fenced log fn2-core)))
                           (implies (<= 2 (nfix done))
                                    (and (fn2-env-role-written id 1 fenced log fn2-core)
                                         (fn2-env-role-written id 2 fenced log fn2-core))))))))))
(defun fn2-env-j3e-row (id fn2-core)
  ; J3's entry: a row at :collect, :seal or :fence has its three role extents
  ; shared and no counted completion (so :dependencies and :log-write start
  ; at zero); before its fence (:collect .. :dependencies, and :log-write in
  ; barrier mode 0) its fence flag is down
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)))
    (implies (fn2-commit-idp id fn2-core)
             (and (implies (member-equal phase (list *fn2-commit-state-collect* *fn2-commit-state-seal* *fn2-commit-state-fence*))
                           (and (natp (fn2-env-role-extent id 0 fn2-core))
                                (equal (fn2-env-role-extent id 1 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                                (equal (fn2-env-role-extent id 2 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                                (equal (fn2-machine-cb-done id fn2-core) 0)))
                  (implies (or (member-equal phase (list *fn2-commit-state-collect* *fn2-commit-state-seal*
                                                         *fn2-commit-state-dependencies*))
                               (and (equal phase *fn2-commit-state-log-write*)
                                    (not (equal (fn2-machine-cb-mode id fn2-core) 1))))
                           (not (equal (fn2-machine-cb-fence-ok id fn2-core) 1)))))))
(defun fn2-env-j3-rows (ids log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j3-row (car ids) log fn2-core) (fn2-env-j3e-row (car ids) fn2-core)
         (fn2-env-j3-rows (cdr ids) log fn2-core))))
(defun fn2-env-dur-inv (ids acked log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-inv ids acked log fn2-core)
       (fn2-env-j-rows ids log fn2-core)
       (fn2-env-j3-rows ids log fn2-core)
       (fn2-env-j-frontier log fn2-core)))

;; J5, THE OPERATION LINK, and J6, THE SUBMITTED BYTES. The write/fence
;; handler (fn2-commit-arm-observe) counts whichever result the harvest
;; delivers to the row; it never sees the operation. J5 pins it: every live
;; operation the row owns at its own generation is the write of an issued,
;; uncounted role of the row's phase (commit-io's op-slot/op-gen at unit
;; 3*row+role) or, at :fence, its one fence. A role's live write has the
;; role's offset, FUA and pool range; once taken, the log holds its take
;; (4096 octets, role 2 carrying the batch's seal) and, once its terminal
;; cell is posted, that cell is the take's first answer; before, no answer.
;; An issued role whose write is no longer live is written (J3's evidence,
;; per role), and the phase's count is exact: cb-done plus the live roles is
;; cb-issued. The fence, once taken, follows the answers of the writes its
;; rise fences (role 0; in barrier mode 0 roles 1 and 2 too). J6: through the
;; write phases each role's pool range lies in the pool (its take reads 4096
;; octets) and role 2's range carries the batch's seal until role 2 is taken.
(defun fn2-env-op (s fn2-core)
  ; (VALID GEN PHASE KIND OKIND OSLOT OGEN RSLOT RGEN ROFF RLEN OFFSET FUA C0P C0H C0E C0O C0C MAYREL C1P)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (r)
    (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
        (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
              (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
              (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
              (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
              (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
              (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
              (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops)
              (fn2-ops-may-release s fn2-ops) (fn2-ops-c1-posted s fn2-ops))
      (list nil))
    r))
(defun fn2-env-ops-rows (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-rows fn2-ops) n))
(defun fn2-env-io (u fn2-core)
  ; (VALID OP-SLOT OP-GEN LENT POOL-SLOT POOL-GEN) of commit-io's unit U
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-commit-io (fn2-core-commit-io fn2-core))) (r)
    (if (and (natp u) (< u (fn2-commit-io-rows fn2-commit-io)))
        (list t (fn2-commit-io-op-slot u fn2-commit-io) (fn2-commit-io-op-gen u fn2-commit-io)
              (fn2-commit-io-lent u fn2-commit-io) (fn2-commit-io-pool-slot u fn2-commit-io)
              (fn2-commit-io-pool-gen u fn2-commit-io))
      (list nil))
    r))
(defun fn2-env-role-io (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-env-io (+ (* 3 (fn2-commit-row id fn2-core)) role) fn2-core))
; The octets the role's pool range holds (its pool slot's base, 4096 on).
(defun fn2-env-role-octets (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((slot (nth 4 (fn2-env-role-io id role fn2-core))))
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (octets)
      (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool)))
          (fn2-env-pool-octets *fn2-commit-unit-bytes* (fn2-pool-base slot fn2-pool) fn2-pool)
        nil)
      octets)))
(defun fn2-env-j5-take-ok (e offset fua b)
  (declare (xargs :verify-guards nil))
  (and (fn2-dev-take-writep e) (equal (nth 4 e) offset) (equal (nth 5 e) fua)
       (equal (len (nth 6 e)) *fn2-commit-unit-bytes*)
       (or (not b) (equal (fn2-env-seal-commit (nth 6 e)) b))))
(defun fn2-env-role-live (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((io (fn2-env-role-io id role fn2-core)) (op (fn2-env-op (nth 1 io) fn2-core)))
    (and (nth 0 io) (equal (nth 3 io) 1) (nth 0 op) (equal (nth 1 op) (nth 2 io))
         (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-retired*))))))
(in-theory (disable fn2-env-j5-event-ok))
(defun fn2-env-j5-role (id role log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((phase (fn2-machine-phase id fn2-core)) (mode (fn2-machine-cb-mode id fn2-core))
         (fua (if (equal phase *fn2-commit-state-log-write*) mode 0))
         (io (fn2-env-role-io id role fn2-core)) (slot (nth 1 io)) (op (fn2-env-op slot fn2-core))
         (offset (fn2-env-role-offset id role fn2-core))
         (b (and (equal role 2) (fn2-machine-batch-no id fn2-core))))
    (if (fn2-env-role-live id role fn2-core)
        (and (equal (nth 3 op) *fn2-action-write*) (equal (nth 4 op) *fn2-commit-kind*)
             (equal (nth 5 op) id) (equal (nth 6 op) (fn2-machine-generation id fn2-core))
             (equal (nth 7 op) (nth 4 io)) (equal (nth 8 op) (nth 5 io))
             (equal (nth 9 op) 0) (equal (nth 10 op) *fn2-commit-unit-bytes*)
             (equal (nth 11 op) offset) (equal (nth 12 op) fua)
             (fn2-env-j5-taken op slot log) (fn2-env-j5-event-ok op)
             (let ((w (fn2-env-take-index slot (nth 1 op) log)))
               (if w (fn2-env-j5-take-ok (nth w log) offset fua b) t)))
      (fn2-env-role-written id role (or (equal (fn2-machine-cb-fence-ok id fn2-core) 1)
                                         (and (equal phase *fn2-commit-state-log-write*) (equal mode 1)))
                            log fn2-core))))
; At :log-write a live role is issued (role 1: cb-issued at least 1; role 2:
; cb-issued 2), and a live role 1 is another operation than role 2: one
; harvested result answers one issued role, whose J5-ROLE J5-ROLES carries.
(defun fn2-env-j5-apart (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (implies (fn2-env-role-live id 1 fn2-core)
                (<= 1 (nfix (fn2-machine-cb-issued id fn2-core))))
       (implies (fn2-env-role-live id 2 fn2-core)
                (and (equal (fn2-machine-cb-issued id fn2-core) 2)
                     (implies (fn2-env-role-live id 1 fn2-core)
                              (not (equal (nth 1 (fn2-env-role-io id 1 fn2-core))
                                          (nth 1 (fn2-env-role-io id 2 fn2-core)))))))))
; The issued roles of a write phase: (FIRST . COUNT).
(defun fn2-env-j5-roles (id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)) (issued (fn2-machine-cb-issued id fn2-core))
        (done (fn2-machine-cb-done id fn2-core)))
    (cond ((equal phase *fn2-commit-state-dependencies*)
           (and (natp issued) (<= issued 1) (natp done)
                ;; a live role 0 is issued
                (implies (fn2-env-role-live id 0 fn2-core) (equal issued 1))
                (implies (equal issued 1) (fn2-env-j5-role id 0 log fn2-core))
                (equal (+ done (if (equal issued 1) (fn2-env-b2n (fn2-env-role-live id 0 fn2-core)) 0)) issued)))
          ((equal phase *fn2-commit-state-log-write*)
           (and (natp issued) (<= issued 2) (natp done)
                (implies (<= 1 issued) (fn2-env-j5-role id 1 log fn2-core))
                (implies (<= 2 issued) (fn2-env-j5-role id 2 log fn2-core))
                (equal (+ done (if (<= 1 issued) (fn2-env-b2n (fn2-env-role-live id 1 fn2-core)) 0)
                          (if (<= 2 issued) (fn2-env-b2n (fn2-env-role-live id 2 fn2-core)) 0))
                       issued)
                (fn2-env-j5-apart id fn2-core)))
          (t t))))
; The fence's take (a fence) follows the answers of the writes its rise
; fences: role 0's once the dependency flag is up, roles 1 and 2 once the log
; flag is.
(defun fn2-env-j5-fence (id op slot log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-j5-taken op slot log)
       (let ((w (fn2-env-take-index slot (nth 1 op) log)))
         (if w (let ((pre (take w log)))
                 (and (equal (nth 3 (nth w log)) *fn2-action-fence*)
                      (implies (equal (fn2-machine-cb-deps-ok id fn2-core) 1)
                               (fn2-env-role-written id 0 nil pre fn2-core))
                      (implies (equal (fn2-machine-cb-log-ok id fn2-core) 1)
                               (and (fn2-env-role-written id 1 nil pre fn2-core)
                                    (fn2-env-role-written id 2 nil pre fn2-core)))))
           t))))
; Op S, live and owned by commit row ID: at most the row's generation; at
; it, one the row's phase accounts for.
(defun fn2-env-j5-op (s id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (implies (and (nth 0 op) (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-retired*)))
                  (equal (nth 4 op) *fn2-commit-kind*) (equal (nth 5 op) id))
             (let ((gen (fn2-machine-generation id fn2-core)) (phase (fn2-machine-phase id fn2-core))
                   (row (fn2-commit-row id fn2-core)))
               (and (<= (nfix (nth 6 op)) (nfix gen))
                    (implies (equal (nth 6 op) gen)
                             ;; one terminal cell: no release cell, none posted
                             (and (equal (nth 18 op) 0) (equal (nth 19 op) 0)
                             (cond ((member-equal phase (list *fn2-commit-state-draining* *fn2-commit-state-uncertain*
                                                              *fn2-commit-state-dropping*))
                                    ;; settling: a live fence may still rise the flag
                                    (implies (equal (nth 3 op) *fn2-action-fence*)
                                             (fn2-env-j5-fence id op s log fn2-core)))
                                   ((member-equal phase (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                                    (and (equal (nth 3 op) *fn2-action-write*)
                                         (let ((roles (if (equal phase *fn2-commit-state-log-write*) '(1 2) '(0))))
                                           (or (let ((io (fn2-env-io (+ (* 3 row) (car roles)) fn2-core)))
                                                 (and (nth 0 io) (equal (nth 1 io) s) (equal (nth 2 io) (nth 1 op))
                                                      (equal (nth 3 io) 1)))
                                               (and (consp (cdr roles))
                                                    (let ((io (fn2-env-io (+ (* 3 row) (cadr roles)) fn2-core)))
                                                      (and (nth 0 io) (equal (nth 1 io) s) (equal (nth 2 io) (nth 1 op))
                                                           (equal (nth 3 io) 1))))))))
                                   ((equal phase *fn2-commit-state-fence*)
                                    (and (equal (nth 3 op) *fn2-action-fence*)
                                         (equal (fn2-machine-cb-fence-live id fn2-core) 1)
                                         (fn2-env-j5-fence id op s log fn2-core)))
                                   (t nil)))))))))
; Ops S .. S+K-1.
(defun fn2-env-j5-ops (s k id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (acl2-count k) :hints (("Goal" :in-theory (disable fn2-env-j5-op)))))
  (if (zp k) t
    (and (fn2-env-j5-op s id log fn2-core) (fn2-env-j5-ops (+ 1 (nfix s)) (- k 1) id log fn2-core))))
; The live fences the row owns at its generation.
(defun fn2-env-owned-fence-at (s id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (if (and (nth 0 op) (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-retired*)))
             (equal (nth 4 op) *fn2-commit-kind*) (equal (nth 5 op) id)
             (equal (nth 6 op) (fn2-machine-generation id fn2-core))
             (equal (nth 3 op) *fn2-action-fence*))
        1 0)))
(defun fn2-env-owned-fences (s k id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (acl2-count k)
                  :hints (("Goal" :in-theory (disable fn2-env-owned-fence-at)))))
  (if (zp k) 0
    (+ (fn2-env-owned-fence-at s id fn2-core)
       (fn2-env-owned-fences (+ 1 (nfix s)) (- k 1) id fn2-core))))
(defun fn2-env-j5-row (id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)) (fence-live (fn2-machine-cb-fence-live id fn2-core)))
    (implies (fn2-commit-idp id fn2-core)
             (and (fn2-env-j5-ops 0 (fn2-env-ops-rows fn2-core) id log fn2-core)
                  (fn2-env-j5-roles id log fn2-core)
                  (or (member-equal phase (list *fn2-commit-state-draining* *fn2-commit-state-uncertain*
                                                *fn2-commit-state-dropping*))
                      (and (equal fence-live (if (equal phase *fn2-commit-state-fence*) fence-live 0))
                           (member-equal fence-live '(0 1))
                           (equal (fn2-env-owned-fences 0 (fn2-env-ops-rows fn2-core) id fn2-core) fence-live)))))))
; J6
(defun fn2-env-j6-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((phase (fn2-machine-phase id fn2-core)) (issued (fn2-machine-cb-issued id fn2-core))
         (mode (fn2-machine-cb-mode id fn2-core))
         (writes (member-equal phase (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*
                                           *fn2-commit-state-fence*)))
         (role2-untaken
          (or (equal phase *fn2-commit-state-dependencies*)
              (and (equal phase *fn2-commit-state-fence*) (equal mode 1))
              (and (equal phase *fn2-commit-state-log-write*)
                   (or (not (and (natp issued) (<= 2 issued)))
                       (and (fn2-env-role-live id 2 fn2-core)
                            (equal (nth 2 (fn2-env-op (nth 1 (fn2-env-role-io id 2 fn2-core)) fn2-core))
                                   *fn2-op-phase-queued*)))))))
    (implies (and (fn2-commit-idp id fn2-core) writes)
             (and (equal (len (fn2-env-role-octets id 0 fn2-core)) *fn2-commit-unit-bytes*)
                  (equal (len (fn2-env-role-octets id 1 fn2-core)) *fn2-commit-unit-bytes*)
                  (equal (len (fn2-env-role-octets id 2 fn2-core)) *fn2-commit-unit-bytes*)
                  (implies role2-untaken
                           (equal (fn2-env-seal-commit (fn2-env-role-octets id 2 fn2-core))
                                  (fn2-machine-batch-no id fn2-core)))))))
(defun fn2-env-j5-rows (ids log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j5-row (car ids) log fn2-core) (fn2-env-j6-row (car ids) fn2-core)
         (fn2-env-j5-rows (cdr ids) log fn2-core))))
;; J5E, WHERE A ROLE IS LIVE. A role's write is live only in its own write
;; phase or while the row settles: no role outside :dependencies, :log-write
;; and the settling phases, roles 1 and 2 not at :dependencies, role 0 not
;; at :log-write; in both write phases the row's byte count is one unit per
;; done write (the handler adds a write's count, a unit, as it counts it).
;; The row's pending count covers its live roles and the live
;; fences it owns at its generation (each issue adds one; the terminal of
;; each delivered result takes one), so a settling row, which releases its
;; pool rows only at pending 0, releases them with no write live.
(defun fn2-env-j5e-live (id fn2-core)
  ; the row's live roles and owned live fences
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (+ (fn2-env-b2n (fn2-env-role-live id 0 fn2-core)) (fn2-env-b2n (fn2-env-role-live id 1 fn2-core))
     (fn2-env-b2n (fn2-env-role-live id 2 fn2-core))
     (fn2-env-owned-fences 0 (fn2-env-ops-rows fn2-core) id fn2-core)))
(defun fn2-env-j5e-bytes (id fn2-core)
  ; a write phase's byte count: one unit per done write
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (equal (fn2-machine-cb-bytes id fn2-core) (* *fn2-commit-unit-bytes* (nfix (fn2-machine-cb-done id fn2-core)))))
(defun fn2-env-j5e-phases (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)))
    (cond ((equal phase *fn2-commit-state-dependencies*)
           (and (not (fn2-env-role-live id 1 fn2-core)) (not (fn2-env-role-live id 2 fn2-core))
                (fn2-env-j5e-bytes id fn2-core)))
          ((equal phase *fn2-commit-state-log-write*)
           (and (not (fn2-env-role-live id 0 fn2-core)) (fn2-env-j5e-bytes id fn2-core)))
          ((member-equal phase (list *fn2-commit-state-draining* *fn2-commit-state-uncertain*
                                     *fn2-commit-state-dropping*))
           t)
          (t (and (not (fn2-env-role-live id 0 fn2-core)) (not (fn2-env-role-live id 1 fn2-core))
                  (not (fn2-env-role-live id 2 fn2-core)))))))
(defun fn2-env-j5e-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (fn2-commit-idp id fn2-core)
           (and (fn2-env-j5e-phases id fn2-core)
                (<= (fn2-env-j5e-live id fn2-core) (nfix (fn2-machine-pending id fn2-core))))))
(defun fn2-env-j5e-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j5e-row (car ids) fn2-core) (fn2-env-j5e-rows (cdr ids) fn2-core))))

; Durability only grows with the log.
(local (defthm fn2-env-nth-append-low
  (implies (< (nfix n) (len x)) (equal (nth n (append x y)) (nth n x)))))
(local (defthm fn2-env-seal-durable-at-extends
  (implies (and (fn2-env-seal-durable-at w b log) (true-listp log) (natp w) (< w (len log)) (true-listp more))
           (fn2-env-seal-durable-at w b (append log more)))
  :hints (("Goal" :in-theory (e/d (fn2-env-nth-append-low)
                                  (fn2-env-seal-commit mod fn2-dev-fenced-write-p fn2-dev-fenced-offset-from
                                   nth binary-append len))))))
(local (defthm fn2-env-len-append (equal (len (append x y)) (+ (len x) (len y)))))
(defthm fn2-env-seal-durable-extends
  (implies (and (fn2-env-seal-durable-from w b log) (true-listp more))
           (fn2-env-seal-durable-from w b (append log more)))
  :hints (("Goal" :induct (fn2-env-seal-durable-from w b log)
           :in-theory (e/d (fn2-env-nth-append-low)
                           (fn2-env-seal-durable-at nth binary-append len)))))
(defthm fn2-env-prefix-durable-extends
  (implies (and (fn2-env-prefix-durable-p n log) (true-listp more))
           (fn2-env-prefix-durable-p n (append log more)))
  :hints (("Goal" :in-theory (disable fn2-env-seal-durable-from binary-append))))
(defthm fn2-env-acked-durable-extends
  (implies (and (fn2-env-acked-durable-p acked log) (true-listp more))
           (fn2-env-acked-durable-p acked (append log more)))
  :hints (("Goal" :in-theory (disable fn2-env-prefix-durable-p binary-append))))
(defthm fn2-env-inv-frame-step
  (implies (and (fn2-env-inv ids acked log core)
                (equal (fn2-env-rows ids core2) (fn2-env-rows ids core))
                (true-listp more))
           (fn2-env-inv ids (fn2-env-observe ids acked core2) (append log more) core2))
  :hints (("Goal" :in-theory (disable fn2-env-rows fn2-env-observe-rows fn2-env-observed-p
                                      fn2-env-acked-durable-p binary-append))))

; THE FRAME STEP: an action that changes no commit row the observer reads
; preserves the invariant, whatever it appends to the log. The step kinds
; other than :turn and :admit touch only the ops, pool and extents children.
(defthm fn2-env-rows-child-frame
  (and (equal (fn2-env-rows ids (update-fn2-core-ops x fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (update-fn2-core-pool x fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (update-fn2-core-extents x fn2-core)) (fn2-env-rows ids fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-machine-cb-acks fn2-machine-batch-no fn2-machine-idp
                                     fn2-machine-kind fn2-machine-slot))))
(defthm fn2-env-rows-host-frame
  (and (equal (fn2-env-rows ids (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-host-post-signal bits fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-rows ids fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                   fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                   fn2-env-fill fn2-env-begin-epoch)
                                  (fn2-env-rows)))))
(defthm fn2-env-rows-take-frame
  (equal (fn2-env-rows ids (mv-nth 1 (fn2-env-take nil image fn2-core))) (fn2-env-rows ids fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-env-take) (fn2-env-rows)))))
(defthm fn2-env-rows-host-step-frame
  (implies (not (member-eq (fn2-env-tag action) '(:turn :admit)))
           (equal (fn2-env-rows ids (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                  (fn2-env-rows ids fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post) (fn2-env-rows fn2-env-take)))))
(defthm fn2-env-inv-host-step
  (implies (and (fn2-env-inv ids acked log fn2-core)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-inv ids (fn2-env-observe ids acked after)
                          (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :use ((:instance fn2-env-inv-frame-step (core fn2-core)
                         (core2 (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                         (more (if (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))
                                   (list (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))) nil))))
           :in-theory (disable fn2-env-inv fn2-env-inv-frame-step fn2-env-observe fn2-env-step))))

;; J SUFFICES FOR THE EVIDENCE PROJECTION. Under J1 and J4 every batch a row
;; shows acknowledged is at or below the installed root, and 1..installed are
;; durable: re-observing ANY core satisfying J keeps ACKED-DURABLE, and the
;; re-observed set covers the rows. So a turn (which logs nothing) preserves
;; FN2-ENV-TURN-INV once it preserves J's rows and frontier at the fixed log.
(defthm fn2-env-prefix-durable-down
  (implies (and (fn2-env-prefix-durable-p n log) (natp m) (<= m (nfix n)))
           (fn2-env-prefix-durable-p m log))
  :hints (("Goal" :induct (fn2-env-prefix-durable-p n log)
           :in-theory (disable fn2-env-batch-durable-p))))
(defthm fn2-env-acked-durable-add-nat
  (implies (and (natp b) (fn2-env-acked-durable-p acked log) (fn2-env-prefix-durable-p b log))
           (fn2-env-acked-durable-p (add-to-set-equal b acked) log))
  :hints (("Goal" :in-theory (disable fn2-env-prefix-durable-p))))
(defthm fn2-env-observe-rows-durable
  (implies (and (fn2-env-acks-bounded-p rows n) (fn2-env-prefix-durable-p n log)
                (fn2-env-acked-durable-p acked log))
           (fn2-env-acked-durable-p (fn2-env-observe-rows rows acked) log))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked)
           :in-theory (disable fn2-env-prefix-durable-p fn2-env-acked-durable-p add-to-set-equal))))
(defthm fn2-env-installed-natp
  (natp (fn2-env-installed fn2-core))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-env-installed fn2-env-root))))
(in-theory (disable fn2-env-installed))
(defthm fn2-env-j-row-acks-bounded
  (implies (and (fn2-env-j-row id log fn2-core)
                (eq (fn2-machine-cb-acks-read-code id fn2-core) :ok)
                (eq (fn2-machine-batch-no-read-code id fn2-core) :ok)
                (posp (fn2-machine-cb-acks id fn2-core)))
           (and (natp (fn2-machine-batch-no id fn2-core))
                (<= (fn2-machine-batch-no id fn2-core) (nfix (fn2-env-installed fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-j-row) (fn2-env-written-from fn2-env-batch-durable-p fn2-env-role-offset
                                                    fn2-env-role-extent fn2-commit-idp)))))
(defthm fn2-env-j-rows-acks-bounded
  (implies (fn2-env-j-rows ids log fn2-core)
           (fn2-env-acks-bounded-p (fn2-env-rows ids fn2-core) (fn2-env-installed fn2-core)))
  :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core)
           :in-theory '(fn2-env-j-rows fn2-env-rows fn2-env-acks-bounded-p car-cons cdr-cons
                        nth-0-cons nth-add1 (:executable-counterpart zp) zp-open atom))
          ("Subgoal *1/2" :use ((:instance fn2-env-j-row-acks-bounded (id (car ids)))))))
(defthm fn2-env-j-frontier-installed
  (implies (fn2-env-j-frontier log fn2-core)
           (fn2-env-prefix-durable-p (fn2-env-installed fn2-core) log))
  :hints (("Goal" :in-theory (e/d (fn2-env-installed) (fn2-env-prefix-durable-p fn2-env-root)))))
(defthm fn2-env-written-extends
  (implies (and (fn2-env-written-from w offset b fenced log) (true-listp more))
           (fn2-env-written-from w offset b fenced (append log more)))
  :hints (("Goal" :induct (fn2-env-written-from w offset b fenced log)
           :in-theory '(fn2-env-written-from fn2-env-done-write-extends fn2-dev-fenced-write-extends
                        fn2-env-nth-append-low fn2-env-len-append (:type-prescription true-listp-append)
                        true-listp-append natp nfix fix (:type-prescription len)))))
(defthm fn2-env-batch-durable-extends
  (implies (and (fn2-env-batch-durable-p b log) (true-listp more))
           (fn2-env-batch-durable-p b (append log more)))
  :hints (("Goal" :in-theory '(fn2-env-batch-durable-p) :use ((:instance fn2-env-seal-durable-extends (w 0))))))
(defun-nx fn2-env-j3-point (key g c)
  (and (fn2-env-j3-row key g c) (fn2-env-j3e-row key c)))
(defthm fn2-env-j-log-locality
  (implies (and (fn2-env-log-step delta g a h b) (fn2-env-j-row key g a))
           (fn2-env-j-row key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-log-step fn2-env-j-row fn2-env-j1-row fn2-env-j2-row
                               fn2-env-written-extends fn2-env-batch-durable-extends))))
(fn2-pw-lift-locality fn2-env-j-log-transport
  :point fn2-env-j-row :all fn2-env-j-rows :step fn2-env-log-step
  :locality fn2-env-j-log-locality)
(defthm fn2-env-j3-log-locality
  (implies (and (fn2-env-log-step delta g a h b) (fn2-env-j3-point key g a))
           (fn2-env-j3-point key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-log-step fn2-env-j3-point fn2-env-j3-row
                               fn2-env-role-written fn2-env-written-extends))))
(fn2-pw-lift-locality fn2-env-j3-log-transport
  :point fn2-env-j3-point :all fn2-env-j3-rows :step fn2-env-log-step
  :locality fn2-env-j3-log-locality :open (fn2-env-j3-point))

(defthm fn2-env-j-rows-extends
  (implies (and (fn2-env-j-rows ids log fn2-core) (true-listp more))
           (fn2-env-j-rows ids (append log more) fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-log-step)
           :use ((:instance fn2-env-j-log-transport
                    (keys ids) (g log) (a fn2-core) (h (append log more)) (b fn2-core) (delta more))))))
(defthm fn2-env-j-frontier-extends
  (implies (and (fn2-env-j-frontier log fn2-core) (true-listp more))
           (fn2-env-j-frontier (append log more) fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-prefix-durable-extends))))
(defthm fn2-env-j3-rows-extends
  (implies (and (fn2-env-j3-rows ids log fn2-core) (true-listp more))
           (fn2-env-j3-rows ids (append log more) fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-log-step)
           :use ((:instance fn2-env-j3-log-transport
                    (keys ids) (g log) (a fn2-core) (h (append log more)) (b fn2-core) (delta more))))))
(make-event
 (value (cons 'progn
   (fn2-env-j-reader-frame-events
    '((fn2-machine-idp id) (fn2-machine-kind id) (fn2-machine-slot id) (fn2-machine-phase id) (fn2-machine-batch-no id) (fn2-machine-cb-acks id)
      (fn2-machine-cb-acks-read-code id) (fn2-machine-batch-no-read-code id)
      (fn2-machine-cb-fence-ok id) (fn2-machine-cb-mode id) (fn2-machine-cb-deps-ok id)
      (fn2-machine-cb-log-ok id) (fn2-machine-cb-done id) (fn2-machine-generation id)
      (fn2-machine-cb-fence-live id) (fn2-machine-cb-issued id) (fn2-commit-idp id) (fn2-commit-row id) (fn2-commit-resource id role) (fn2-env-root))
    '(update-fn2-core-ops update-fn2-core-pool update-fn2-core-extents)))))
(defthm fn2-env-j-row-child-frame
  (and (equal (fn2-env-j-row id log (update-fn2-core-ops x fn2-core)) (fn2-env-j-row id log fn2-core))
       (equal (fn2-env-j-row id log (update-fn2-core-pool x fn2-core)) (fn2-env-j-row id log fn2-core))
       (equal (fn2-env-j-row id log (update-fn2-core-extents x fn2-core)) (fn2-env-j-row id log fn2-core))
       (equal (fn2-env-root (update-fn2-core-ops x fn2-core)) (fn2-env-root fn2-core))
       (equal (fn2-env-root (update-fn2-core-pool x fn2-core)) (fn2-env-root fn2-core))
       (equal (fn2-env-root (update-fn2-core-extents x fn2-core)) (fn2-env-root fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-j-row fn2-env-j1-row fn2-env-j2-row fn2-env-role-offset fn2-env-role-extent fn2-env-installed
                                fn2-machine-phase-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-pool fn2-machine-phase-of-update-fn2-core-extents fn2-machine-batch-no-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-pool fn2-machine-batch-no-of-update-fn2-core-extents fn2-machine-cb-acks-of-update-fn2-core-ops fn2-machine-cb-acks-of-update-fn2-core-pool fn2-machine-cb-acks-of-update-fn2-core-extents fn2-machine-cb-acks-read-code-of-update-fn2-core-ops fn2-machine-cb-acks-read-code-of-update-fn2-core-pool fn2-machine-cb-acks-read-code-of-update-fn2-core-extents fn2-machine-batch-no-read-code-of-update-fn2-core-ops fn2-machine-batch-no-read-code-of-update-fn2-core-pool fn2-machine-batch-no-read-code-of-update-fn2-core-extents fn2-machine-cb-fence-ok-of-update-fn2-core-ops fn2-machine-cb-fence-ok-of-update-fn2-core-pool fn2-machine-cb-fence-ok-of-update-fn2-core-extents fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-cb-mode-of-update-fn2-core-pool fn2-machine-cb-mode-of-update-fn2-core-extents fn2-machine-cb-deps-ok-of-update-fn2-core-ops fn2-machine-cb-deps-ok-of-update-fn2-core-pool fn2-machine-cb-deps-ok-of-update-fn2-core-extents fn2-machine-cb-log-ok-of-update-fn2-core-ops fn2-machine-cb-log-ok-of-update-fn2-core-pool fn2-machine-cb-log-ok-of-update-fn2-core-extents fn2-commit-idp-of-update-fn2-core-ops fn2-commit-idp-of-update-fn2-core-pool fn2-commit-idp-of-update-fn2-core-extents fn2-commit-resource-of-update-fn2-core-ops fn2-commit-resource-of-update-fn2-core-pool fn2-commit-resource-of-update-fn2-core-extents fn2-env-root-of-update-fn2-core-ops fn2-env-root-of-update-fn2-core-pool fn2-env-root-of-update-fn2-core-extents))))
(defun-nx fn2-env-child-step (delta g a h b)
  (and (equal g h)
       (or (equal b (update-fn2-core-ops delta a))
           (equal b (update-fn2-core-pool delta a))
           (equal b (update-fn2-core-extents delta a))
           (equal a (update-fn2-core-ops delta b))
           (equal a (update-fn2-core-pool delta b))
           (equal a (update-fn2-core-extents delta b)))))
(defthm fn2-env-j-child-locality
  (implies (and (fn2-env-child-step delta g a h b) (fn2-env-j-row key g a))
           (fn2-env-j-row key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-child-step fn2-env-j-row-child-frame))))
(fn2-pw-lift-locality fn2-env-j-child-transport
  :point fn2-env-j-row :all fn2-env-j-rows :step fn2-env-child-step
  :locality fn2-env-j-child-locality)

(defthm fn2-env-j-child-frame
  (and (equal (fn2-env-j-rows ids log (update-fn2-core-ops x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (update-fn2-core-pool x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (update-fn2-core-extents x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-ops x fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-pool x fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-extents x fn2-core)) (fn2-env-j-frontier log fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-child-step (:type-prescription fn2-env-j-rows) fn2-env-j-frontier fn2-env-j-row-child-frame)
           :use ((:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-ops x fn2-core)) (delta x)) (:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-ops x fn2-core)) (b fn2-core) (delta x)) (:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-pool x fn2-core)) (delta x)) (:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-pool x fn2-core)) (b fn2-core) (delta x)) (:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-extents x fn2-core)) (delta x)) (:instance fn2-env-j-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-extents x fn2-core)) (b fn2-core) (delta x))))))
(defthm fn2-env-j-host-frame
  (and (equal (fn2-env-j-rows ids log (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (fn2-host-post-signal bits fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-host-post-signal bits fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-j-frontier log fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                   fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                   fn2-env-fill fn2-env-begin-epoch)
                                  (fn2-env-j-rows fn2-env-j-frontier)))))
(defthm fn2-env-j-take-frame
  (and (equal (fn2-env-j-rows ids log (mv-nth 1 (fn2-env-take nil image fn2-core))) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-frontier log (mv-nth 1 (fn2-env-take nil image fn2-core))) (fn2-env-j-frontier log fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-env-take) (fn2-env-j-rows fn2-env-j-frontier)))))
(defthm fn2-env-j-host-step-frame
  (implies (not (member-eq (fn2-env-tag action) '(:turn :admit)))
           (and (equal (fn2-env-j-rows ids log (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                       (fn2-env-j-rows ids log fn2-core))
                (equal (fn2-env-j-frontier log (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                       (fn2-env-j-frontier log fn2-core))))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post)
                                  (fn2-env-j-rows fn2-env-j-frontier fn2-env-take)))))
;; J3 reads the same children as J (and the commit table's count column)
(defthm fn2-env-j3-row-child-frame
  (and (equal (fn2-env-j3-row id log (update-fn2-core-ops x fn2-core)) (fn2-env-j3-row id log fn2-core))
       (equal (fn2-env-j3-row id log (update-fn2-core-pool x fn2-core)) (fn2-env-j3-row id log fn2-core))
       (equal (fn2-env-j3-row id log (update-fn2-core-extents x fn2-core)) (fn2-env-j3-row id log fn2-core))
       (equal (fn2-env-j3e-row id (update-fn2-core-ops x fn2-core)) (fn2-env-j3e-row id fn2-core))
       (equal (fn2-env-j3e-row id (update-fn2-core-pool x fn2-core)) (fn2-env-j3e-row id fn2-core))
       (equal (fn2-env-j3e-row id (update-fn2-core-extents x fn2-core)) (fn2-env-j3e-row id fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-role-offset fn2-env-role-extent
                                fn2-machine-phase-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-pool fn2-machine-phase-of-update-fn2-core-extents
                                fn2-machine-batch-no-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-pool fn2-machine-batch-no-of-update-fn2-core-extents
                                fn2-machine-cb-fence-ok-of-update-fn2-core-ops fn2-machine-cb-fence-ok-of-update-fn2-core-pool fn2-machine-cb-fence-ok-of-update-fn2-core-extents
                                fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-cb-mode-of-update-fn2-core-pool fn2-machine-cb-mode-of-update-fn2-core-extents
                                fn2-machine-cb-done-of-update-fn2-core-ops fn2-machine-cb-done-of-update-fn2-core-pool fn2-machine-cb-done-of-update-fn2-core-extents
                                fn2-commit-idp-of-update-fn2-core-ops fn2-commit-idp-of-update-fn2-core-pool fn2-commit-idp-of-update-fn2-core-extents
                                fn2-commit-resource-of-update-fn2-core-ops fn2-commit-resource-of-update-fn2-core-pool fn2-commit-resource-of-update-fn2-core-extents))))
(defthm fn2-env-j3-child-locality
  (implies (and (fn2-env-child-step delta g a h b) (fn2-env-j3-point key g a))
           (fn2-env-j3-point key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-child-step fn2-env-j3-point fn2-env-j3-row-child-frame))))
(fn2-pw-lift-locality fn2-env-j3-child-transport
  :point fn2-env-j3-point :all fn2-env-j3-rows :step fn2-env-child-step
  :locality fn2-env-j3-child-locality :open (fn2-env-j3-point))

(defthm fn2-env-j3-child-frame
  (and (equal (fn2-env-j3-rows ids log (update-fn2-core-ops x fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (update-fn2-core-pool x fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (update-fn2-core-extents x fn2-core)) (fn2-env-j3-rows ids log fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-child-step (:type-prescription fn2-env-j3-rows))
           :use ((:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-ops x fn2-core)) (delta x)) (:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-ops x fn2-core)) (b fn2-core) (delta x)) (:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-pool x fn2-core)) (delta x)) (:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-pool x fn2-core)) (b fn2-core) (delta x)) (:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a fn2-core) (b (update-fn2-core-extents x fn2-core)) (delta x)) (:instance fn2-env-j3-child-transport (keys ids) (g log) (h log) (a (update-fn2-core-extents x fn2-core)) (b fn2-core) (delta x))))))
(defthm fn2-env-j3-host-frame
  (and (equal (fn2-env-j3-rows ids log (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (fn2-host-post-signal bits fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-j3-rows ids log fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                   fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                   fn2-env-fill fn2-env-begin-epoch)
                                  (fn2-env-j3-rows)))))
(defthm fn2-env-j3-take-frame
  (equal (fn2-env-j3-rows ids log (mv-nth 1 (fn2-env-take nil image fn2-core))) (fn2-env-j3-rows ids log fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-env-take) (fn2-env-j3-rows)))))
(defthm fn2-env-j3-host-step-frame
  (implies (not (member-eq (fn2-env-tag action) '(:turn :admit)))
           (equal (fn2-env-j3-rows ids log (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                  (fn2-env-j3-rows ids log fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post)
                                  (fn2-env-j3-rows fn2-env-take)))))
(defthm fn2-env-dur-inv-host-step
  (implies (and (fn2-env-dur-inv ids acked log fn2-core)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-dur-inv ids (fn2-env-observe ids acked after)
                              (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (e/d (fn2-env-dur-inv)
                                  (fn2-env-inv fn2-env-j-rows fn2-env-j3-rows fn2-env-j-frontier fn2-env-observe fn2-env-step))
           :use ((:instance fn2-env-inv-host-step)
                 (:instance fn2-env-j3-rows-extends
                            (fn2-core (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                            (more (if (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))
                                      (list (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))) nil)))
                 (:instance fn2-env-j-rows-extends
                            (fn2-core (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                            (more (if (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))
                                      (list (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))) nil)))
                 (:instance fn2-env-j-frontier-extends
                            (fn2-core (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                            (more (if (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))
                                      (list (mv-nth 0 (fn2-env-step action nil image rlog fn2-core))) nil)))))))

;; J2 AT :DURABLE. A row whose dependency, log and fence flags are set has
;; its batch durable: the fenced role-2 write carries its seal, and the
;; fenced role-0 and role-1 writes are its extent's page and records units.
(defthm fn2-env-written-fenced-offset
  (implies (fn2-env-written-from w offset b t log)
           (fn2-dev-fenced-offset-from w offset log))
  :hints (("Goal" :induct (fn2-env-written-from w offset b t log)
           :in-theory (disable fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-seal-commit))))
(defthm fn2-env-written-seal-durable
  (implies (and (fn2-env-written-from w offset b t log) b (natp offset)
                (equal (mod offset *fn2-commit-extent-bytes*) (* 2 *fn2-commit-unit-bytes*))
                (fn2-dev-fenced-offset-from 0 (- offset (* 2 *fn2-commit-unit-bytes*)) log)
                (fn2-dev-fenced-offset-from 0 (+ (- offset (* 2 *fn2-commit-unit-bytes*)) *fn2-commit-unit-bytes*) log))
           (fn2-env-seal-durable-from w b log))
  :hints (("Goal" :induct (fn2-env-written-from w offset b t log)
           :in-theory (disable fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-seal-commit
                               fn2-dev-fenced-offset-from mod))))
(defthm fn2-env-extent-offset-mod
  (implies (natp e)
           (equal (mod (+ (* e *fn2-commit-extent-bytes*) (* 2 *fn2-commit-unit-bytes*)) *fn2-commit-extent-bytes*)
                  (* 2 *fn2-commit-unit-bytes*)))
  :hints (("Goal" :in-theory (enable mod))))
(defthm fn2-env-j-row-durable-flags
  (implies (and (fn2-env-j-row id log fn2-core) (fn2-commit-idp id fn2-core)
                (equal (fn2-machine-cb-deps-ok id fn2-core) 1)
                (equal (fn2-machine-cb-log-ok id fn2-core) 1)
                (equal (fn2-machine-cb-fence-ok id fn2-core) 1)
                (fn2-machine-batch-no id fn2-core))
           (fn2-env-batch-durable-p (fn2-machine-batch-no id fn2-core) log))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-role-offset fn2-env-role-extent)
                                  (fn2-env-written-from fn2-dev-fenced-offset-from fn2-env-seal-durable-from
                                   fn2-env-installed fn2-commit-idp fn2-commit-resource))
           :use ((:instance fn2-env-written-seal-durable (w 0) (b (fn2-machine-batch-no id fn2-core))
                            (offset (fn2-env-role-offset id 2 fn2-core)))
                 (:instance fn2-env-written-fenced-offset (w 0) (b nil) (offset (fn2-env-role-offset id 0 fn2-core)))
                 (:instance fn2-env-written-fenced-offset (w 0) (b nil) (offset (fn2-env-role-offset id 1 fn2-core)))
                 (:instance fn2-env-extent-offset-mod (e (fn2-env-role-extent id 0 fn2-core)))))))

(defthm fn2-env-prefix-durable-batch
  (implies (and (fn2-env-prefix-durable-p n log) (posp m) (<= m (nfix n)))
           (fn2-env-batch-durable-p m log))
  :hints (("Goal" :in-theory (disable fn2-env-batch-durable-p fn2-env-prefix-durable-p)
           :use ((:instance fn2-env-prefix-durable-down)
                 (:instance fn2-env-prefix-durable-p (n m))))))
(defun-nx fn2-env-j-same-evidence (id a b)
  ; the columns and children J2 reads of row ID agree in cores A and B
  (and (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
       (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
       (equal (fn2-machine-batch-no-read-code id b) (fn2-machine-batch-no-read-code id a))
       (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
       (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))
       (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
       (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
       (equal (fn2-env-role-extent id 0 b) (fn2-env-role-extent id 0 a))
       (equal (fn2-env-role-extent id 1 b) (fn2-env-role-extent id 1 a))
       (equal (fn2-env-role-extent id 2 b) (fn2-env-role-extent id 2 a))))
(defthm fn2-env-role-offset-of-extent
  (equal (fn2-env-role-offset id role c)
         (+ (* (nfix (fn2-env-role-extent id role c)) *fn2-commit-extent-bytes*) (* role *fn2-commit-unit-bytes*)))
  :hints (("Goal" :in-theory (enable fn2-env-role-offset fn2-env-role-extent))))
;; THE ROW TRANSFER: a step that keeps J2's evidence of row ID, keeps the
;; frontier and does not lower the installed root keeps J at ID, provided it
;; changes neither the row's phase nor its acknowledgement, or the row's
;; batch was already at or below the installed root (then every phase and
;; reply count is consistent with J1, the batch being durable by J4). Each
;; commit arm's lift instantiates it with the arm's FRAME and WRITES.
(defthm fn2-env-j2-row-congruence
  (implies (fn2-env-j-same-evidence id a b)
           (equal (fn2-env-j2-row id log b) (fn2-env-j2-row id log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j2-row fn2-env-j-same-evidence fn2-env-role-offset-of-extent))))
(defthm fn2-env-j1-row-transfer
  (implies (and (fn2-env-j1-row id log a)
                (fn2-env-j-frontier log b)
                (fn2-env-j-same-evidence id a b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (or (and (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                         (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a))
                         (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a)))
                    (and (posp (fn2-machine-batch-no id a))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed a)))))
           (fn2-env-j1-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j1-row fn2-env-j-same-evidence posp natp nfix
                               (:type-prescription fn2-env-installed-natp) member-equal)
           :use ((:instance fn2-env-j-frontier-installed (fn2-core b))
                 (:instance fn2-env-prefix-durable-batch (n (fn2-env-installed b))
                            (m (fn2-machine-batch-no id a)))))))
(defthm fn2-env-j-row-transfer
  (implies (and (fn2-env-j-row id log a)
                (fn2-env-j-frontier log b)
                (fn2-env-j-same-evidence id a b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (or (and (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                         (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a))
                         (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a)))
                    (and (posp (fn2-machine-batch-no id a))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed a)))))
           (fn2-env-j-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-row)
           :use ((:instance fn2-env-j1-row-transfer) (:instance fn2-env-j2-row-congruence)))))
(defthm fn2-env-rows-len
  (equal (len (fn2-env-rows ids fn2-core)) (len ids)))

; Where the observer reads: the directory, the commit table's rows field and
; its cb-acks and batch-no columns.
(make-event
 (let* ((world (w state)) (tcols (strip-cars (fn2-machine-property 'fn2-commit :table world))))
   (value `(progn (defconst *fn2-env-tk* ,(fn2-arm-frame-child-index 'fn2-commit-table world))
                  (defconst *fn2-env-m* ,(fn2-arm-frame-m world))
                  (defconst *fn2-env-ri* ,(len tcols))
                  (defconst *fn2-env-acks* ,(position-eq 'cb-acks tcols))
                  (defconst *fn2-env-batch* ,(position-eq 'batch-no tcols))))))
; The two columns of tables TA and TB agree but at ROW, where the reply
; count is 0 or both cells agree.
(defun fn2-env-cells-ok (row ta tb)
  (declare (xargs :verify-guards nil))
  (and (equal (update-nth row nil (nth *fn2-env-acks* ta)) (update-nth row nil (nth *fn2-env-acks* tb)))
       (equal (update-nth row nil (nth *fn2-env-batch* ta)) (update-nth row nil (nth *fn2-env-batch* tb)))
       (or (equal (nth row (nth *fn2-env-acks* tb)) 0)
           (and (equal (nth row (nth *fn2-env-acks* tb)) (nth row (nth *fn2-env-acks* ta)))
                (equal (nth row (nth *fn2-env-batch* tb)) (nth row (nth *fn2-env-batch* ta)))))))
(defthm fn2-env-cells-ok-refl (fn2-env-cells-ok row ta ta))
(defthm fn2-env-cells-ok-cell
  (implies (and (fn2-env-cells-ok row ta tb) (natp row) (natp s))
           (or (equal (nth s (nth *fn2-env-acks* tb)) 0)
               (and (equal (nth s (nth *fn2-env-acks* tb)) (nth s (nth *fn2-env-acks* ta)))
                    (equal (nth s (nth *fn2-env-batch* tb)) (nth s (nth *fn2-env-batch* ta))))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal s row))
           :in-theory (disable nth update-nth)
           :use ((:instance fn2-env-nth-off-update-nth (r row) (x (nth *fn2-env-acks* ta)) (y (nth *fn2-env-acks* tb)))
                 (:instance fn2-env-nth-off-update-nth (r row) (x (nth *fn2-env-batch* ta)) (y (nth *fn2-env-batch* tb)))))))
; A commit row's cell is readable: the directory has the id and the slot is
; under the table's rows.
(defun-nx fn2-env-cell-code (id fn2-core)
  (declare (xargs :verify-guards nil))
  (let ((slot (fn2-machine-slot id fn2-core)))
    (if (and (fn2-machine-idp id fn2-core) (natp slot) (< slot (nth *fn2-env-ri* (nth *fn2-env-tk* fn2-core))))
        :ok :bounds)))
(defthm fn2-env-cell-code-slot
  (implies (equal (fn2-env-cell-code id fn2-core) :ok) (natp (fn2-machine-slot id fn2-core)))
  :rule-classes :forward-chaining)
(defthm fn2-env-acks-off-kind
  (implies (not (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*))
           (equal (fn2-machine-cb-acks id fn2-core) 0))
  :hints (("Goal" :in-theory (enable fn2-machine-cb-acks))))
(defthm fn2-env-commit-row-unfolds
  (implies (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
           (and (equal (fn2-machine-cb-acks-read-code id fn2-core) (fn2-env-cell-code id fn2-core))
                (equal (fn2-machine-batch-no-read-code id fn2-core) (fn2-env-cell-code id fn2-core))
                (equal (fn2-machine-cb-acks id fn2-core)
                       (if (eq (fn2-env-cell-code id fn2-core) :ok)
                           (nth (fn2-machine-slot id fn2-core) (nth *fn2-env-acks* (nth *fn2-env-tk* fn2-core))) 0))
                (equal (fn2-machine-batch-no id fn2-core)
                       (if (eq (fn2-env-cell-code id fn2-core) :ok)
                           (nth (fn2-machine-slot id fn2-core) (nth *fn2-env-batch* (nth *fn2-env-tk* fn2-core))) 0))))
  :hints (("Goal" :in-theory (e/d (fn2-machine-cb-acks fn2-machine-cb-acks-read-code fn2-machine-batch-no
                                   fn2-machine-batch-no-read-code fn2-commit-table fn2-commit-rows
                                   fn2-commit-cb-acks fn2-commit-cb-acks$ai fn2-commit-batch-no fn2-commit-batch-no$ai)
                                  (fn2-machine-slot fn2-machine-idp fn2-machine-kind)))))
(in-theory (disable fn2-env-commit-row-unfolds))
(defthm fn2-env-cell-code-congruence
  (implies (and (equal (nth *fn2-env-m* b) (nth *fn2-env-m* a))
                (equal (nth *fn2-env-ri* (nth *fn2-env-tk* b)) (nth *fn2-env-ri* (nth *fn2-env-tk* a))))
           (equal (fn2-env-cell-code id b) (fn2-env-cell-code id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-machine-idp fn2-core-machines) (fn2-machine-slot))
           :use ((:instance fn2-arm-slot-congruence (a b) (b a))))))
; One id: after B, a positive reply count is one A showed, with its batch.
(defthm fn2-env-row-no-new-ack
  (implies (and (equal (nth *fn2-env-m* b) (nth *fn2-env-m* a))
                (equal (nth *fn2-env-ri* (nth *fn2-env-tk* b)) (nth *fn2-env-ri* (nth *fn2-env-tk* a)))
                (fn2-env-cells-ok row (nth *fn2-env-tk* a) (nth *fn2-env-tk* b)) (natp row))
           (or (not (posp (fn2-machine-cb-acks id b)))
               (and (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                    (equal (fn2-machine-batch-no-read-code id b) (fn2-machine-batch-no-read-code id a))
                    (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a))
                    (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a)))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
           :in-theory (e/d (fn2-env-commit-row-unfolds) (fn2-env-cells-ok fn2-env-cell-code fn2-machine-slot fn2-machine-kind nth))
           :use ((:instance fn2-arm-slot-congruence (a b) (b a))
                 (:instance fn2-arm-kind-congruence (a b) (b a))
                 (:instance fn2-env-cell-code-congruence)
                 (:instance fn2-env-cells-ok-cell (ta (nth *fn2-env-tk* a)) (tb (nth *fn2-env-tk* b)) (s (fn2-machine-slot id a)))))))
(defthm fn2-env-no-new-acks-of-cells
  (implies (and (equal (nth *fn2-env-m* b) (nth *fn2-env-m* a))
                (equal (nth *fn2-env-ri* (nth *fn2-env-tk* b)) (nth *fn2-env-ri* (nth *fn2-env-tk* a)))
                (fn2-env-cells-ok row (nth *fn2-env-tk* a) (nth *fn2-env-tk* b)) (natp row))
           (fn2-env-no-new-acks-p (fn2-env-rows ids b) (fn2-env-rows ids a)))
  :rule-classes nil
  :hints (("Goal" :induct (len ids)
           :in-theory (disable fn2-env-cells-ok nth fn2-machine-cb-acks fn2-machine-batch-no
                               fn2-machine-cb-acks-read-code fn2-machine-batch-no-read-code))
          ("Subgoal *1/1" :use ((:instance fn2-env-row-no-new-ack (id (car ids)))))))
; THE BRIDGE: an arm-frames row frame over the commit table that leaves the
; directory and the commit table's rows, cb-acks and batch-no alone.
(defthm fn2-env-no-new-acks-of-row-frame
  (implies (and (fn2-arm-row-frame *fn2-env-tk* row cs ch a b)
                (not (member-equal *fn2-env-tk* ch)) (not (member-equal *fn2-env-m* ch))
                (not (member-equal *fn2-env-ri* cs)) (not (member-equal *fn2-env-acks* cs))
                (not (member-equal *fn2-env-batch* cs)))
           (fn2-env-no-new-acks-p (fn2-env-rows ids b) (fn2-env-rows ids a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-arm-row-frame) (fn2-arm-kids fn2-arm-cols fn2-env-rows fn2-env-no-new-acks-p nth update-nth))
           :use ((:instance fn2-env-no-new-acks-of-cells (row 0))
                 (:instance fn2-arm-kids-nth (i 0) (k *fn2-env-m*) (free (cons *fn2-env-tk* ch)))
                 (:instance fn2-arm-row-frame-cols (table *fn2-env-tk*) (columns cs) (children ch))
                 (:instance fn2-arm-cols-nth (k 0) (j *fn2-env-ri*) (columns cs) (a (nth *fn2-env-tk* a)) (b (nth *fn2-env-tk* b)))
                 (:instance fn2-arm-cols-nth (k 0) (j *fn2-env-acks*) (columns cs) (a (nth *fn2-env-tk* a)) (b (nth *fn2-env-tk* b)))
                 (:instance fn2-arm-cols-nth (k 0) (j *fn2-env-batch*) (columns cs) (a (nth *fn2-env-tk* a)) (b (nth *fn2-env-tk* b)))))))

;; The admission's sub-operations' contracts, derived under the commit kind
;; by the arm-frames generator (callees first).
; Admission producer contracts are materialized in commit-turn-frame.
; FN's no-new-acks step from its contract through the bridge: the rows after
; FN show no reply the rows before PRE did not. Refused when the contract
; may change what the observer reads.
(defun fn2-env-acks-step-event (fn world)
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (e (fn2-arm-frame-known fn kind world))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (tk (fn2-arm-frame-entry-tk e world))
         (ch (fn2-arm-frame-entry-s e))
         (cs (fn2-arm-frame-entry-j e))
         (row (if tk '(fn2-machine-slot id fn2-core) 0))
         (name (packn (list 'fn2-env- fn '-no-new-acks))))
    (if (or (not (member-eq (car e) '(:row :op)))
            (and tk (not (equal tk *fn2-env-tk*)))
            (member *fn2-env-tk* ch) (member *fn2-env-m* ch)
            (intersectp-equal cs (list *fn2-env-ri* *fn2-env-acks* *fn2-env-batch*)))
        (er hard 'fn2-env-acks-step-event "~x0's contract ~x1 may change what the observer reads." fn e)
      `(defthm ,name
         (implies (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids fn2-core) fn2-env-pre)
                  (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids ,out) fn2-env-pre))
         :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                  :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world)
                                   (fn2-arm-tb ,*fn2-env-tk*) (fn2-arm-row ,row) (fn2-arm-cs ',cs) (fn2-arm-ch ',ch)
                                   (fn2-arm-c0 fn2-core))
                        (:instance fn2-env-no-new-acks-of-row-frame (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,out)
                                   (ids fn2-env-ids))
                        (:instance fn2-env-no-new-acks-trans (c (fn2-env-rows fn2-env-ids ,out))
                                   (b (fn2-env-rows fn2-env-ids fn2-core)) (a fn2-env-pre))
                        (:instance fn2-env-rows-len (ids fn2-env-ids) (fn2-core ,out))
                        (:instance fn2-env-rows-len (ids fn2-env-ids)))))))))
(defun fn2-env-acks-step-events (fns world)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons (fn2-env-acks-step-event (car fns) world) (fn2-env-acks-step-events (cdr fns) world))))
(make-event
 (value (cons 'progn (fn2-env-acks-step-events
                      '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool
                        fn2-commit-reserve-extent fn2-commit-release-pools fn2-commit-prepare-root fn2-commit-ready
                        fn2-commit-put-members fn2-exec-wake)
                      (w state)))))
; The reserve loop's contract stays at the children level (its table write is
; the row's pool columns, but the loop's row frame is not derived): its step
; by induction over the loop, each pass through its two steps' contracts.
(defthm fn2-env-fn2-commit-reserve-pools-no-new-acks
  (implies (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids fn2-core) fn2-env-pre)
           (fn2-env-no-new-acks-p
            (fn2-env-rows fn2-env-ids (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core))) fn2-env-pre))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-env-fn2-core-reserve-no-new-acks
                                        fn2-env-fn2-commit-keep-pool-no-new-acks fn2-env-fn2-commit-unwind-pool-no-new-acks)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-commit-row-acks-unfolds
  (implies (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
           (equal (fn2-commit-row-cb-acks id fn2-core)
                  (if (eq (fn2-env-cell-code id fn2-core) :ok)
                      (nth (fn2-machine-slot id fn2-core) (nth *fn2-env-acks* (nth *fn2-env-tk* fn2-core))) 0)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-row-cb-acks fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                   fn2-commit-table fn2-commit-rows fn2-commit-cb-acks fn2-commit-cb-acks$ai)
                                  (fn2-machine-slot fn2-machine-idp fn2-machine-kind)))))
(in-theory (disable fn2-env-commit-row-acks-unfolds))
(defun fn2-env-start-write-events (world)
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (formals (formals w world))
         (wformals (butlast (cdr formals) 1))
         (call (cons w formals))
         (acks (nth (position-eq 'cb-acks ord) wformals))
         (g (fn2-arm-frame-write-guards kind ord wformals world))
         (e (fn2-arm-frame-known w kind world))
         (cs (fn2-arm-frame-entry-j e))
         (ch (fn2-arm-frame-entry-s e))
         (row '(fn2-machine-slot id fn2-core))
         (ta `(nth ,*fn2-env-tk* fn2-core))
         (tb `(nth ,*fn2-env-tk* ,call))
         ; the phase argument's own fit (the write maps any argument to a
         ; phase constant, so refusal is the other conjuncts')
         (pfit (if (eq (car ord) 'phase) (nth 5 g) (er hard 'fn2-env-start-write-events "~x0 writes no phase." w))))
    `((defun-nx fn2-env-start-write-accepted ,formals
        (declare (xargs :verify-guards nil) (ignorable ,@formals))
        ,g)
      (defthm fn2-env-start-write-accepted-suff
        (implies ,g (fn2-env-start-write-accepted ,@formals)))
      (in-theory (disable fn2-env-start-write-accepted))
      ; refused: neither the directory nor the commit table changes
      (defthm fn2-env-start-write-refused
        (implies (and (not (fn2-env-start-write-accepted ,@formals)) ,pfit)
                 (and (equal (nth ,*fn2-env-tk* ,call) (nth ,*fn2-env-tk* fn2-core))
                      (equal (nth ,*fn2-env-m* ,call) (nth ,*fn2-env-m* fn2-core))))
        :rule-classes nil
        :hints (("Goal" :in-theory (e/d (fn2-env-start-write-accepted-suff ,w fn2-machine-refuse-write fn2-core-stop
                                         update-fn2-core-control update-fn2-commit-table fn2-commit-table)
                                        (fn2-machine-idp fn2-machine-kind fn2-machine-slot)))))
      ; its frame: the directory and the rows field kept, the two columns but at its row
      (defthm fn2-env-start-write-frame
        (and (equal (nth ,*fn2-env-m* ,call) (nth ,*fn2-env-m* fn2-core))
             (equal (nth ,*fn2-env-ri* ,tb) (nth ,*fn2-env-ri* ,ta))
             (equal (update-nth ,row nil (nth ,*fn2-env-acks* ,ta)) (update-nth ,row nil (nth ,*fn2-env-acks* ,tb)))
             (equal (update-nth ,row nil (nth ,*fn2-env-batch* ,ta)) (update-nth ,row nil (nth ,*fn2-env-batch* ,tb))))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-arm-row-frame) (theory 'fn2-arm-frame-base))
                 :use ((:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb ,*fn2-env-tk*)
                                  (fn2-arm-row ,row) (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k ,*fn2-env-m*) (free (cons ,*fn2-env-tk* ',ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-cols-nth (k 0) (j ,*fn2-env-ri*) (columns ',cs) (row ,row) (a ,ta) (b ,tb))
                       (:instance fn2-env-cols-nth-in (k 0) (j ,*fn2-env-acks*) (columns ',cs) (row ,row) (a ,ta) (b ,tb))
                       (:instance fn2-env-cols-nth-in (k 0) (j ,*fn2-env-batch*) (columns ',cs) (row ,row) (a ,ta) (b ,tb))))))
      ; accepted with cb-acks 0: its row's reply count is 0
      (defthm fn2-env-start-write-acks
        (implies (and (fn2-env-start-write-accepted ,@formals) (equal ,acks 0))
                 (and (natp ,row) (equal (nth ,row (nth ,*fn2-env-acks* ,tb)) 0)))
        :rule-classes nil
        :hints (("Goal" :in-theory (e/d (fn2-env-start-write-accepted fn2-commit-rows fn2-commit-table fn2-env-cell-code)
                                        (,w fn2-machine-idp fn2-machine-kind fn2-machine-slot))
                 :use ((:instance ,(fn2-columns-sym w "-READS"))
                       (:instance fn2-env-commit-row-acks-unfolds (fn2-core ,call))
                       (:instance fn2-env-start-write-frame)
                       (:instance fn2-env-cell-code-congruence (a fn2-core) (b ,call))
                       (:instance fn2-arm-slot-congruence (a ,call) (b fn2-core))
                       (:instance fn2-arm-kind-congruence (a ,call) (b fn2-core))))))
      (defthm fn2-env-start-write-cells
        (implies (and (equal ,acks 0) ,pfit)
                 (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids ,call) (fn2-env-rows fn2-env-ids fn2-core)))
        :rule-classes nil
        :hints (("Goal" :cases ((fn2-env-start-write-accepted ,@formals))
                 :in-theory (union-theories '(fn2-env-cells-ok-refl) (theory 'fn2-arm-frame-base)))
                ("Subgoal 2" :use (fn2-env-start-write-refused
                                   (:instance fn2-env-no-new-acks-of-cells (row 0) (a fn2-core) (b ,call) (ids fn2-env-ids))))
                ("Subgoal 1"
                 :in-theory (union-theories '(fn2-env-cells-ok) (theory 'fn2-arm-frame-base))
                 :use (fn2-env-start-write-frame fn2-env-start-write-acks
                       (:instance fn2-env-no-new-acks-of-cells (row ,row) (a fn2-core) (b ,call) (ids fn2-env-ids))))))
      (defthm fn2-env-start-write-no-new-acks
        (implies (and (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids fn2-core) fn2-env-pre) (equal ,acks 0) ,pfit)
                 (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids ,call) fn2-env-pre))
        :hints (("Goal" :in-theory (theory 'minimal-theory)
                 :use (fn2-env-start-write-cells
                       (:instance fn2-env-no-new-acks-trans (c (fn2-env-rows fn2-env-ids ,call))
                                  (b (fn2-env-rows fn2-env-ids fn2-core)) (a fn2-env-pre))
                       (:instance fn2-env-rows-len (ids fn2-env-ids) (fn2-core ,call))
                       (:instance fn2-env-rows-len (ids fn2-env-ids)))))))))
(make-event (value (cons 'progn (fn2-env-start-write-events (w state)))))

; The admission: fn2-commit-start, then its members, then the row's wake.
; Each opening sees its callees only through their steps above.
(defthm fn2-env-commit-start-no-new-acks
  (implies (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids fn2-core) fn2-env-pre)
           (fn2-env-no-new-acks-p
            (fn2-env-rows fn2-env-ids (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)))
            fn2-env-pre))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-env-start-write-no-new-acks
                                              fn2-env-fn2-core-stop-no-new-acks fn2-env-fn2-commit-reserve-pools-no-new-acks
                                              fn2-env-fn2-commit-reserve-extent-no-new-acks
                                              fn2-env-fn2-commit-release-pools-no-new-acks
                                              fn2-env-fn2-commit-prepare-root-no-new-acks
                                              fn2-env-fn2-commit-ready-no-new-acks)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-commit-admit-keyed-no-new-acks
  (implies (fn2-env-no-new-acks-p (fn2-env-rows fn2-env-ids fn2-core) fn2-env-pre)
           (fn2-env-no-new-acks-p
            (fn2-env-rows fn2-env-ids (mv-nth 4 (fn2-commit-admit-keyed n mode okind oslot ogen fn2-core)))
            fn2-env-pre))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-admit-keyed fn2-env-commit-start-no-new-acks
                                              fn2-env-fn2-commit-put-members-no-new-acks
                                              fn2-env-fn2-core-stop-no-new-acks)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-admit-no-new-acks
  (fn2-env-no-new-acks-p (fn2-env-rows ids (fn2-env-admit members mode fn2-core)) (fn2-env-rows ids fn2-core))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-env-commit-admit-keyed-no-new-acks
                                              fn2-env-fn2-exec-wake-no-new-acks fn2-env-no-new-acks-refl)
                                             (theory 'fn2-arm-frame-base)))))
; THE ADMISSION STEP preserves the invariant.
(defthm fn2-env-inv-admit-step
  (implies (and (fn2-env-inv ids acked log fn2-core)
                (equal (fn2-env-tag action) :admit))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-inv ids (fn2-env-observe ids acked after)
                          (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-inv)
                                  (fn2-env-admit fn2-env-rows fn2-env-observed-p fn2-env-acked-durable-p
                                   fn2-env-no-new-acks-p fn2-env-observe-rows))
           :use ((:instance fn2-env-admit-no-new-acks (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))
                 (:instance fn2-env-observed-no-new-acks
                            (pre (fn2-env-rows ids fn2-core))
                            (post (fn2-env-rows ids (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core))))
                 (:instance fn2-env-acked-durable-extends (more nil))))))
; Every step kind but :turn preserves the invariant.
(defthm fn2-env-inv-step-but-turn
  (implies (and (fn2-env-inv ids acked log fn2-core)
                (not (equal (fn2-env-tag action) :turn)))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-inv ids (fn2-env-observe ids acked after)
                          (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (union-theories '(member-equal) (theory 'minimal-theory))
           :use (fn2-env-inv-admit-step fn2-env-inv-host-step))))

;; THE COLUMN BRIDGE: a commit-table row frame (table child 9) that keeps
;; the rows field (column 33) and the directory's kinds and slots
;; (fn2-ctf-dir) keeps every J reader of a commit id outside the frame's
;; columns, and every column at a slot other than the frame's row; J is
;; trivially true of a non-commit id. FN2-ENV-J-ROW-OF-ROW-FRAME is the lift
;; each commit arm instantiates with its FRAME (fn2-commit-run-arm-row-frame).
;; Column and child indices are the commit table's (cross-checked below).
(make-event
 (let* ((world (w state)) (tcols (strip-cars (fn2-machine-property 'fn2-commit :table world))))
   (value `(assert-event
            (and (equal *fn2-env-tk* 9) (equal *fn2-env-ri* 33) (equal *fn2-env-m* 3)
                 (equal ',(list (position-eq 'phase tcols) (position-eq 'batch-no tcols) (position-eq 'cb-mode tcols)
                                (position-eq 'cb-fence-ok tcols) (position-eq 'cb-deps-ok tcols)
                                (position-eq 'cb-log-ok tcols) (position-eq 'cb-acks tcols)
                                (fn2-arm-frame-child-index 'fn2-core-commit-io world)
                                (fn2-arm-frame-child-index 'fn2-core-commit-root world))
                        '(0 9 13 23 24 25 27 30 31)))))))
(defthm fn2-env-j-row-off-kind
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (not (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)))
           (fn2-env-j-row id log fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-env-j-row fn2-env-j1-row fn2-env-j2-row fn2-machine-cb-acks-read-code)
                                  (fn2-env-written-from fn2-env-batch-durable-p fn2-env-installed))
           :use ((:instance fn2-commit-idp-kind-value)))))
(make-event (value (cons 'progn (fn2-env-row-read-events
  '((phase . 0) (batch-no . 9) (cb-mode . 13) (cb-fence-ok . 23) (cb-deps-ok . 24) (cb-log-ok . 25) (cb-acks . 27))))))
(make-event (value (cons 'progn (fn2-env-row-read-events '((cb-done . 17) (cb-issued . 16))))))
(defthm fn2-env-read-codes-of-row-frame
  (implies (and (fn2-arm-row-frame 9 row cs ch a b) (not (member-equal 9 ch))
                (not (member-equal 33 cs)) (fn2-ctf-dir b a))
           (and (equal (fn2-machine-batch-no-read-code id b) (fn2-machine-batch-no-read-code id a))
                (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-machine-batch-no-read-code fn2-machine-cb-acks-read-code fn2-commit-idp
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-commit-row
                                   fn2-commit-table fn2-commit-rows)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp nth update-nth
                                   fn2-arm-row-frame fn2-ctf-dir))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)
                 (:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch))
                 (:instance fn2-arm-cols-nth (k 0) (j 33) (columns cs) (a (nth 9 a)) (b (nth 9 b)))))))
(defthm fn2-env-child-congruences
  (implies (and (equal (nth 30 b) (nth 30 a)) (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a)))
           (equal (fn2-commit-resource id role b) (fn2-commit-resource id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-commit-resource fn2-core-commit-io))))
(defthm fn2-env-root-congruence
  (implies (equal (nth 31 b) (nth 31 a)) (equal (fn2-env-root b) (fn2-env-root a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-root fn2-core-commit-root))))
;; KEPT EVIDENCE. J2 reads a row's role extents (commit-io's extent column
;; and row count, FN2-ENV-EK) and J4 the root triple (FN2-ENV-RK); arms that
;; write commit-io's other columns or the root's other fields keep them.
; Whole-child consumers use views too; cardinality is not inferred from
; a footprint that permits replacement of the observed child.
(fn2-defview fn2-env-io-view :carrier fn2-core :select ((fn2-commit-io :whole t)))
(fn2-defview fn2-env-root-table-view :carrier fn2-core :select ((fn2-commit-root :whole t)))
(fn2-defview fn2-env-commit-table-view :carrier fn2-core :select ((fn2-commit :whole t)))
(fn2-defview fn2-env-directory-view :carrier fn2-core :select ((fn2-machines :whole t)))
(fn2-defview fn2-env-ek :carrier fn2-core
  :select ((fn2-commit-io :columns (extent) :rows t :scalars (rows))))
(defthm fn2-env-ek-view-equivalence
  (equal (fn2-env-ek b a) (and (equal (nth *fn2-commit-io-extent$ai* (nth 30 b)) (nth *fn2-commit-io-extent$ai* (nth 30 a)))
       (equal (nth *fn2-commit-io-rows* (nth 30 b)) (nth *fn2-commit-io-rows* (nth 30 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-ek fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-ek))
(fn2-defview fn2-env-rk :carrier fn2-core
  :select ((fn2-commit-root :columns (installed published) :rows (:one 0) :scalars (rows)))
  :observe fn2-env-root
  :open (fn2-env-root fn2-core-commit-root fn2-commit-root-rows
         fn2-commit-root-installed fn2-commit-root-published
         fn2-commit-root-installed$ai fn2-commit-root-published$ai))
(defthm fn2-env-rk-view-equivalence
  (equal (fn2-env-rk b a) (equal (fn2-env-root b) (fn2-env-root a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-rk fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-rk))
(defthm fn2-env-ek-refl (fn2-env-ek a a))
(defthm fn2-env-rk-refl (fn2-env-rk a a))
(defthm fn2-env-ek-of-nth
  (implies (and (equal (nth 30 b) (nth 30 x)) (fn2-env-ek x a)) (fn2-env-ek b a))
  :rule-classes nil)
(defthm fn2-env-rk-of-nth
  (implies (and (equal (nth 31 b) (nth 31 x)) (fn2-env-rk x a)) (fn2-env-rk b a))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-env-root-congruence (a x))))))
(in-theory (disable fn2-env-ek fn2-env-rk))
(defthm fn2-env-role-extent-of-ek
  (implies (and (fn2-env-ek b a) (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a)))
           (equal (fn2-env-role-extent id role b) (fn2-env-role-extent id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-ek fn2-env-role-extent fn2-commit-resource fn2-core-commit-io
                                     fn2-commit-io-extent fn2-commit-io-rows))))
(defthm fn2-env-j-frontier-of-rk
  (implies (fn2-env-rk b a)
           (and (equal (fn2-env-j-frontier log b) (fn2-env-j-frontier log a))
                (equal (fn2-env-installed b) (fn2-env-installed a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-rk fn2-env-j-frontier fn2-env-installed))))
(defthm fn2-env-ek-of-update-same
  (equal (fn2-env-ek (update-fn2-core-commit-io (fn2-core-commit-io x) y) a) (fn2-env-ek x a))
  :hints (("Goal" :in-theory (enable fn2-env-ek update-fn2-core-commit-io fn2-core-commit-io))))
(make-event (value (cons 'progn (fn2-env-ek-col-events '(epoch counter pool-slot pool-gen op-slot op-gen ready lent)))))
(defthm fn2-env-rk-of-update-same
  (equal (fn2-env-rk (update-fn2-core-commit-root (fn2-core-commit-root x) y) a) (fn2-env-rk x a))
  :hints (("Goal" :in-theory (enable fn2-env-rk fn2-env-root update-fn2-core-commit-root fn2-core-commit-root))))
(make-event (value (cons 'progn (fn2-env-rk-col-events '(parent extent first-key members proposed abort-event aborting barrier-mode seal-ready)))))

; FN2-ENV-REL-COLS: a relation's commit-table columns, for a relation that
; reads the table (FN2-ENV-TK); a writer of the table at one row whose
; columns miss them keeps it by its row frame and REL-OF-ROW-FRAME.




(defthm fn2-env-j-evidence-of-row-frame
  ; what a commit-table frame at ROW keeps of row ID: J2's evidence and the
  ; acknowledgement's readability always; its phase and reply count when ID
  ; is at another slot or the frame's columns exclude them
  (implies (and (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (fn2-env-ek b a)
                (not (member-equal 33 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs))
                (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs))
                (fn2-ctf-dir b a)
                (equal (fn2-machine-kind id a) *fn2-commit-kind*))
           (and (fn2-env-j-same-evidence id a b)
                (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                (implies (or (not (equal (fn2-machine-slot id a) row)) (not (member-equal 0 cs)))
                         (equal (fn2-machine-phase id b) (fn2-machine-phase id a)))
                (implies (or (not (equal (fn2-machine-slot id a) row)) (not (member-equal 27 cs)))
                         (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-role-extent natp member-equal)
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-read-codes-of-row-frame)
                 (:instance fn2-env-role-extent-of-ek (role 0))
                 (:instance fn2-env-role-extent-of-ek (role 1))
                 (:instance fn2-env-role-extent-of-ek (role 2))
                 (:instance fn2-machine-phase-of-row-frame)
                 (:instance fn2-machine-batch-no-of-row-frame)
                 (:instance fn2-machine-cb-mode-of-row-frame)
                 (:instance fn2-machine-cb-fence-ok-of-row-frame)
                 (:instance fn2-machine-cb-deps-ok-of-row-frame)
                 (:instance fn2-machine-cb-log-ok-of-row-frame)
                 (:instance fn2-machine-cb-acks-of-row-frame)))))
(defthm fn2-env-j-frontier-of-root
  (implies (equal (nth 31 b) (nth 31 a))
           (and (equal (fn2-env-j-frontier log b) (fn2-env-j-frontier log a))
                (equal (fn2-env-installed b) (fn2-env-installed a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-installed) :use ((:instance fn2-env-root-congruence)))))
(defthm fn2-env-j-row-of-row-frame
  ; the frame lift: J at ID survives a commit-table frame that keeps J2's
  ; evidence, when the frontier holds after and the installed root does not
  ; drop, and either ID is at another slot, the frame leaves phase and
  ; reply count, or ID's batch is already installed
  (implies (and (fn2-env-j-row id log a) (fn2-env-j-frontier log b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (fn2-corep b) (fn2-core-wfp b)
                (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (fn2-env-ek b a)
                (not (member-equal 33 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs))
                (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs))
                (fn2-ctf-dir b a)
                (or (not (equal (fn2-machine-slot id a) row))
                    (and (not (member-equal 0 cs)) (not (member-equal 27 cs)))
                    (and (posp (fn2-machine-batch-no id a))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed a)))))
           (fn2-env-j-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp) (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)
                 (:instance fn2-env-j-row-off-kind (fn2-core b))
                 (:instance fn2-env-j-evidence-of-row-frame)
                 (:instance fn2-env-j-row-transfer)))))
;; ---------------------------------------------------------------------------
;; THE COMMIT ARMS' J LIFTS. Each visit of a commit row (fn2-commit-run at a
;; phase) keeps J at every id: its FRAME is the arm's declaration (the
;; commit table at the row's slot in the declared columns, the declared
;; children; FN2-ENV-<PHASE>-ARM-FRAME), and the directory is kept.  An id that
;; is not a readable row at the visited slot keeps J by the frame alone
;; (FN2-ENV-J-ROW-OF-ROW-FRAME-OFF-ROW); one at the slot reads the visited
;; row (FN2-ENV-SAME-SLOT-READS) and keeps J by the arm's own WRITES.
(defthm fn2-env-j-row-not-idp
  (implies (not (fn2-commit-idp id fn2-core)) (fn2-env-j-row id log fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-env-j-row fn2-env-j1-row fn2-env-j2-row fn2-commit-idp fn2-commit-snapshot-read-code
                                   fn2-machine-phase-read-code fn2-machine-cb-acks-read-code)
                                  (fn2-env-written-from fn2-env-batch-durable-p fn2-env-installed fn2-machine-kind
                                   fn2-machine-slot fn2-machine-idp)))))
(defthm fn2-env-row-phase-snapshot
  (implies (not (equal (fn2-commit-row-phase id fn2-core) 0))
           (equal (fn2-commit-snapshot-read-code id fn2-core) :ok))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-row-phase))))
(defthm fn2-env-same-slot-reads
  ; two readable commit rows at one slot read the same row
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp id fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
           (and (equal (fn2-machine-phase i fn2-core) (fn2-machine-phase id fn2-core))
                (equal (fn2-machine-batch-no i fn2-core) (fn2-machine-batch-no id fn2-core))
                (equal (fn2-machine-cb-deps-ok i fn2-core) (fn2-machine-cb-deps-ok id fn2-core))
                (equal (fn2-machine-cb-log-ok i fn2-core) (fn2-machine-cb-log-ok id fn2-core))
                (equal (fn2-machine-cb-fence-ok i fn2-core) (fn2-machine-cb-fence-ok id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-machine-phase
                                   fn2-machine-batch-no fn2-machine-batch-no-read-code fn2-machine-cb-deps-ok
                                   fn2-machine-cb-deps-ok-read-code fn2-machine-cb-log-ok fn2-machine-cb-log-ok-read-code
                                   fn2-machine-cb-fence-ok fn2-machine-cb-fence-ok-read-code)
                                  (fn2-machine-kind fn2-machine-slot)))))
(defthm fn2-env-j1-row-phase-facts
  ; what J1 promises of a readable row by its phase
  (implies (and (fn2-env-j-row id log fn2-core) (fn2-commit-idp id fn2-core))
           (let ((phase (fn2-machine-phase id fn2-core)) (batch (fn2-machine-batch-no id fn2-core)))
             (and (implies (not (equal phase *fn2-commit-state-free*)) (posp batch))
                  (implies (member-equal phase (list *fn2-commit-state-publish* *fn2-commit-state-notify*))
                           (<= batch (fn2-env-installed fn2-core)))
                  (implies (equal phase *fn2-commit-state-install*) (fn2-env-batch-durable-p batch log)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-row fn2-env-j1-row member-equal (:e member-equal)))))
(defthm fn2-env-j1-row-phase-transfer
  ; a step that keeps J2's evidence and the reply count of row ID, does not
  ; lower the installed root, and moves a row past :free only to phases whose
  ; J1 obligations it meets, keeps J1 at ID
  (implies (and (fn2-env-j1-row id log a)
                (fn2-env-j-same-evidence id a b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a))
                (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                (fn2-commit-idp id a)
                (implies (not (equal (fn2-machine-phase id b) *fn2-commit-state-free*))
                         (not (equal (fn2-machine-phase id a) *fn2-commit-state-free*)))
                (implies (member-equal (fn2-machine-phase id b) (list *fn2-commit-state-publish* *fn2-commit-state-notify*))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed b)))
                (implies (equal (fn2-machine-phase id b) *fn2-commit-state-install*)
                         (fn2-env-batch-durable-p (fn2-machine-batch-no id a) log)))
           (fn2-env-j1-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j1-row fn2-env-j-same-evidence posp natp nfix
                               (:type-prescription fn2-env-installed-natp) member-equal (:e member-equal)))))
(defthm fn2-env-j-row-of-row-frame-off-row
  ; every commit arm's frame keeps J at an id that is not a readable row at the frame's slot
  (implies (and (fn2-env-j-row i log a) (fn2-env-j-frontier log b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (fn2-corep b) (fn2-core-wfp b)
                (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (fn2-env-ek b a)
                (not (member-equal 33 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs))
                (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs))
                (fn2-ctf-dir b a)
                (or (not (fn2-commit-idp i a)) (not (equal (fn2-machine-slot i a) row))))
           (fn2-env-j-row i log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-row-not-idp)
           :do-not-induct t
           :use ((:instance fn2-env-j-row-of-row-frame (id i))
                 (:instance fn2-env-read-codes-of-row-frame (id i))))))
(defthm fn2-env-commit-idp-kind
  (implies (fn2-commit-idp id fn2-core) (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-idp fn2-commit-snapshot-read-code))))
(defthm fn2-env-j-row-of-row-frame-same-row
  ; at the frame's slot: a step that leaves the reply count keeps J when it
  ; reaches :publish or :notify only from them or with the batch installed,
  ; and :install only from it or with the three durability flags set
  (implies (and (fn2-env-j-row i log a) (fn2-env-j-frontier log b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (fn2-env-ek b a)
                (not (member-equal 33 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs))
                (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs))
                (not (member-equal 27 cs))
                (fn2-ctf-dir b a)
                (fn2-commit-idp i a) (fn2-commit-idp id a)
                (equal (fn2-machine-slot i a) row) (equal (fn2-machine-slot id a) row)
                (implies (not (equal (fn2-machine-phase id b) *fn2-commit-state-free*))
                         (not (equal (fn2-machine-phase id a) *fn2-commit-state-free*)))
                (implies (and (member-equal (fn2-machine-phase id b) (list *fn2-commit-state-publish* *fn2-commit-state-notify*))
                              (not (member-equal (fn2-machine-phase id a) (list *fn2-commit-state-publish* *fn2-commit-state-notify*))))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed b)))
                (implies (and (equal (fn2-machine-phase id b) *fn2-commit-state-install*)
                              (not (equal (fn2-machine-phase id a) *fn2-commit-state-install*)))
                         (and (fn2-machine-batch-no id a)
                              (equal (fn2-machine-cb-deps-ok id a) 1)
                              (equal (fn2-machine-cb-log-ok id a) 1)
                              (equal (fn2-machine-cb-fence-ok id a) 1))))
           (fn2-env-j-row i log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-row member-equal (:e member-equal))
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-kind (id i) (fn2-core a))
                 (:instance fn2-env-j-evidence-of-row-frame (id i))
                 (:instance fn2-env-read-codes-of-row-frame (id i))
                 (:instance fn2-env-read-codes-of-row-frame (id id))
                 (:instance fn2-ctf-dir-readers (id i))
                 (:instance fn2-ctf-dir-readers (id id))
                 (:instance fn2-env-j1-row-phase-facts (id i) (fn2-core a))
                 (:instance fn2-env-same-slot-reads (fn2-core a))
                 (:instance fn2-env-same-slot-reads (fn2-core b))
                 (:instance fn2-env-j-row-durable-flags (id i) (fn2-core a))
                 (:instance fn2-env-j1-row-phase-transfer (id i))
                 (:instance fn2-env-j2-row-congruence (id i))))))
(defun fn2-env-arm-frame-events (state-name code)
  (declare (xargs :mode :program))
  (let* ((e (assoc code *fn2-commit-arm-decls*)) (ch (cadr e)) (cs (caddr e))
         (const (fn2-env-arm-state-const state-name))
         (frame (fn2-columns-sym (fn2-columns-col-name 'fn2-env state-name) "-ARM-FRAME"))
         (b '(mv-nth 4 (fn2-commit-run id budget fn2-core)))
         (kids (append (and (not (member 30 ch)) `((fn2-env-ek ,b fn2-core)))
                       (and (not (member 31 ch)) `((equal (nth 31 ,b) (nth 31 fn2-core)))))))
    (cons
     `(defthm ,frame
        (implies (equal (fn2-commit-row-phase id fn2-core) ,const)
                 (and (fn2-arm-row-frame 9 (fn2-machine-slot id fn2-core) ',cs ',ch fn2-core ,b)
                      (fn2-ctf-dir ,b fn2-core)
                      ,@kids))
        :rule-classes nil
        :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e fn2-commit-arm-children)
                                     (:e fn2-commit-arm-columns) (:e subsetp-equal) (:e member-equal))
                 :do-not-induct t
                 :use ((:instance fn2-commit-run-arm-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id fn2-core))
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id fn2-core))
                                  (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance fn2-commit-run-ctf-dir (fn2-ctf-c0 fn2-core))
                       (:instance fn2-ctf-dir-refl (a fn2-core))
                       ,@(and kids
                              `((:instance fn2-env-ek-of-nth (b ,b) (x fn2-core) (a fn2-core))
                                (:instance fn2-env-ek-refl (a fn2-core))
                                (:instance fn2-env-row-frame-child (tb 9) (k 30) (row (fn2-machine-slot id fn2-core))
                                           (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
                                (:instance fn2-env-row-frame-child (tb 9) (k 31) (row (fn2-machine-slot id fn2-core))
                                           (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))))))))
     (and (not (member 31 ch))
          `((defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-frontier state-name) "-ARM")
              (implies (equal (fn2-commit-row-phase id fn2-core) ,const)
                       (and (equal (fn2-env-j-frontier log ,b) (fn2-env-j-frontier log fn2-core))
                            (equal (fn2-env-installed ,b) (fn2-env-installed fn2-core))))
              :hints (("Goal" :in-theory nil
                       :use ((:instance ,frame) (:instance fn2-env-j-frontier-of-root (a fn2-core) (b ,b)))))))))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :notify 9))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :durable 6))))

;; :NOTIFY. The row at the visited slot is at :notify, so J1 already bounds
;; its batch by the installed root (FN2-ENV-J1-ROW-PHASE-FACTS) and the frame
;; lift applies even though the arm writes the phase and the reply count.
(defthm fn2-env-j-row-notify-arm
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-notify*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) (:e tau-system)
                               fn2-commit-idp fn2-commit-arm-row-phase)
           :do-not-induct t
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :use ((:instance fn2-env-notify-arm-frame)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-same-slot-reads)
                 (:instance fn2-env-j1-row-phase-facts (id i))
                 (:instance fn2-env-j-frontier-notify-arm)
                 (:instance fn2-env-j-row-of-row-frame-off-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 14 27 15 19 21 6)) (ch '(29 28 3 2 5)))
                 (:instance fn2-env-j-row-of-row-frame (id i) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 14 27 15 19 21 6)) (ch '(29 28 3 2 5)))))))
(make-event (value (cons 'progn (fn2-env-arm-rows-events :notify nil))))

;; :DURABLE. The arm reaches :install only through its guard (batch number
;; and the three flags set: FN2-ENV-COMMIT-RUN-DURABLE-PHASE), and then J2's
;; evidence makes the batch durable (FN2-ENV-J-ROW-DURABLE-FLAGS).  Its
;; declared children include commit-io (30) because fn2-commit-allocate's
;; defcost names the table it reads; the allocator writes only the extents,
;; so commit-io stays. FN2-ENV-COMMIT-RUN-DURABLE-KEEPS-COMMIT-IO
;; projects the composed producer footprint onto FN2-ENV-IO-VIEW.





(fn2-with-column-projections (fn2-env-io-view)
(defthm fn2-env-commit-run-durable-keeps-commit-io
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-durable*)
           (equal (nth 30 (mv-nth 4 (fn2-commit-run id budget fn2-core))) (nth 30 fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run
                                                )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-io-view) clause world)))))
(defthm fn2-env-commit-row-flag-reads
  (implies (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
           (and (equal (fn2-commit-row-cb-deps-ok id fn2-core) (fn2-machine-cb-deps-ok id fn2-core))
                (equal (fn2-commit-row-cb-log-ok id fn2-core) (fn2-machine-cb-log-ok id fn2-core))
                (equal (fn2-commit-row-cb-fence-ok id fn2-core) (fn2-machine-cb-fence-ok id fn2-core))
                (equal (fn2-commit-row-batch-no id fn2-core) (fn2-machine-batch-no id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-row-cb-deps-ok fn2-commit-row-cb-log-ok fn2-commit-row-cb-fence-ok
                                   fn2-commit-row-batch-no fn2-machine-cb-deps-ok fn2-machine-cb-log-ok
                                   fn2-machine-cb-fence-ok fn2-machine-batch-no
                                   fn2-machine-cb-deps-ok-read-code fn2-machine-cb-log-ok-read-code
                                   fn2-machine-cb-fence-ok-read-code fn2-machine-batch-no-read-code
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp)))))
(defthm fn2-env-commit-row-count-reads
  (implies (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
           (and (equal (fn2-commit-row-cb-done id fn2-core) (fn2-machine-cb-done id fn2-core))
                (equal (fn2-commit-row-cb-issued id fn2-core) (fn2-machine-cb-issued id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-row-cb-done fn2-commit-row-cb-issued fn2-machine-cb-done fn2-machine-cb-issued
                                   fn2-machine-cb-done-read-code fn2-machine-cb-issued-read-code
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp)))))
(defthm fn2-env-durable-arm-phase
  (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                (subsetp-equal '(11 6) fn2-arm-pset)
                (or (member-equal 7 fn2-arm-pset)
                    (not (and (unsigned-byte-p 60 (fn2-commit-row-batch-no id fn2-core))
                              (equal (fn2-commit-row-cb-deps-ok id fn2-core) 1)
                              (equal (fn2-commit-row-cb-log-ok id fn2-core) 1)
                              (equal (fn2-commit-row-cb-fence-ok id fn2-core) 1)))))
           (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run-durable id budget fn2-core))) fn2-arm-pset))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-durable fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase
                                               fn2-commit~fn2-commit-allocate-arm-phase fn2-commit-write+phase-arm-phase
                                               fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-commit-run-durable-phase
  ; the visit at :durable moves the row's phase only to :uncertain, or to
  ; :install with its batch number and its three durability flags set
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-durable*)
           (let ((phase (fn2-machine-phase id (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
             (and (member-equal phase (list *fn2-commit-state-install* *fn2-commit-state-uncertain* *fn2-commit-state-durable*))
                  (implies (equal phase *fn2-commit-state-install*)
                           (and (unsigned-byte-p 60 (fn2-machine-batch-no id fn2-core))
                                (equal (fn2-machine-cb-deps-ok id fn2-core) 1)
                                (equal (fn2-machine-cb-log-ok id fn2-core) 1)
                                (equal (fn2-machine-cb-fence-ok id fn2-core) 1))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-durable-arm-phase (fn2-arm-pset '(11 6)))
                 (:instance fn2-env-durable-arm-phase (fn2-arm-pset '(7 11 6)))
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-row-flag-reads)))))
(defthm fn2-env-j-row-durable-arm
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-durable*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                               fn2-commit-idp fn2-commit-arm-row-phase unsigned-byte-p integer-range-p)
           :do-not-induct t
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :use ((:instance fn2-env-durable-arm-frame)
                 (:instance fn2-env-row-frame-child (tb 9) (k 31) (row (fn2-machine-slot id fn2-core))
                            (cs '(0 15 19 21 6)) (ch '(20 30 5))
                            (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-commit-run-durable-keeps-commit-io)
                 (:instance fn2-env-ek-of-nth (b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (x fn2-core) (a fn2-core))
                 (:instance fn2-env-ek-refl (a fn2-core))
                 (:instance fn2-env-j-frontier-durable-arm)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-run-durable-phase)
                 (:instance fn2-env-j-row-of-row-frame-off-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 15 19 21 6)) (ch '(20 30 5)))
                 (:instance fn2-env-j-row-of-row-frame-same-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 15 19 21 6)) (ch '(20 30 5)))))))
(make-event (value (cons 'progn (fn2-env-arm-rows-events :durable nil))))
;; :INSTALL and :PUBLISH. The root swap (FN2-ENV-ROOT-SWAP-FACTS) installs
;; the row's batch only as published + 1 and publishes only the installed
;; batch; every other callee keeps FN2-ENV-ROOT-TABLE-VIEW by its producer
;; footprint. The visit at :install keeps J4 (the
;; batch is durable by J1 at :install) and does not lower the installed root,
;; and reaches :publish only by its install (FN2-ENV-COMMIT-RUN-INSTALL-FACTS);
;; the visit at :publish keeps the installed root.  Both read J at the
;; visited id itself (its batch's durability, its positive batch number).

(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-root-swap-facts
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let ((r (fn2-env-root fn2-core)) (batch (fn2-machine-batch-no id fn2-core)))
             (mv-let (ok after) (fn2-commit-root-swap id publish fn2-core)
               (if ok
                   (and (nth 0 r)
                        (if publish
                            (and (equal batch (nth 1 r))
                                 (equal (fn2-env-root after) (list t (nth 1 r) batch)))
                          (and (equal batch (+ 1 (nth 2 r)))
                               (equal (fn2-env-root after) (list t batch (nth 2 r))))))
                 (equal (nth 31 after) (nth 31 fn2-core))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (e/d (fn2-commit-root-swap fn2-env-root  update-fn2-core-commit-root fn2-core-commit-root) (fn2-machine-batch-no fn2-commit-frontier fn2-core-stop))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))

(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-install-arm-phase
  (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                (subsetp-equal '(11 7) fn2-arm-pset)
                (or (member-equal 8 fn2-arm-pset)
                    (not (and (mv-nth 0 (fn2-commit-root-swap id nil fn2-core))
                              (equal (nth 31 (mv-nth 4 (fn2-commit-run-install id budget fn2-core)))
                                     (nth 31 (mv-nth 1 (fn2-commit-root-swap id nil fn2-core))))))))
           (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run-install id budget fn2-core))) fn2-arm-pset))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run-install fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase



                                               fn2-commit~fn2-commit-root-swap-arm-phase fn2-commit~fn2-commit-root-edge-arm-phase
                                               fn2-commit-write+phase-arm-phase
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))
(defthm fn2-env-publish-arm-phase
  (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                (subsetp-equal '(9 11 8) fn2-arm-pset))
           (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run-publish id budget fn2-core))) fn2-arm-pset))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-publish fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase
                                               fn2-commit~fn2-commit-root-swap-arm-phase fn2-successor-publish-arm-phase
                                               fn2-commit-stream-wake-arm-phase fn2-commit-write+phase+cb-published-arm-phase
                                               fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-install-arm-root
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let ((b (mv-nth 4 (fn2-commit-run-install id budget fn2-core))))
             (mv-let (ok s) (fn2-commit-root-swap id nil fn2-core)
               (or (equal (nth 31 b) (nth 31 fn2-core))
                   (and ok (equal (nth 31 b) (nth 31 s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run-install


                                               )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-root-swap-facts (publish nil))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))
(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-publish-arm-root
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let ((b (mv-nth 4 (fn2-commit-run-publish id budget fn2-core))))
             (mv-let (ok s) (fn2-commit-root-swap id t fn2-core)
               (or (equal (nth 31 b) (nth 31 fn2-core))
                   (and ok (equal (nth 31 b) (nth 31 s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run-publish



                                               )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-root-swap-facts (publish t))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))
(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-commit-run-install-facts
  ; the visit at :install leaves the root, or installs the row's batch as
  ; published + 1; it reaches :publish only by that install
  (implies (and (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-install*)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let* ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (r (fn2-env-root fn2-core))
                  (batch (fn2-machine-batch-no id fn2-core))
                  (swap (and (nth 0 r) (equal batch (+ 1 (nth 2 r)))
                             (equal (fn2-env-root b) (list t batch (nth 2 r))))))
             (and (member-equal (fn2-machine-phase id b) '(8 11 7))
                  (or (equal (nth 31 b) (nth 31 fn2-core)) swap)
                  (implies (equal (fn2-machine-phase id b) *fn2-commit-state-publish*) swap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase

                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-install-arm-phase (fn2-arm-pset '(8 11 7)))
                 (:instance fn2-env-install-arm-phase (fn2-arm-pset '(11 7)))
                 (:instance fn2-env-install-arm-root)
                 (:instance fn2-env-root-swap-facts (publish nil))
                 (:instance fn2-env-root-congruence (a (mv-nth 1 (fn2-commit-root-swap id nil fn2-core)))
                            (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))
(fn2-with-column-projections (fn2-env-root-table-view)
(defthm fn2-env-commit-run-publish-facts
  ; the visit at :publish leaves the root, or publishes the row's batch,
  ; which is the installed one
  (implies (and (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let* ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (r (fn2-env-root fn2-core))
                  (batch (fn2-machine-batch-no id fn2-core)))
             (and (member-equal (fn2-machine-phase id b) '(9 11 8))
                  (or (equal (nth 31 b) (nth 31 fn2-core))
                      (and (nth 0 r) (equal batch (nth 1 r))
                           (equal (fn2-env-root b) (list t (nth 1 r) batch)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase

                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-publish-arm-phase (fn2-arm-pset '(9 11 8)))
                 (:instance fn2-env-publish-arm-root)
                 (:instance fn2-env-root-swap-facts (publish t))
                 (:instance fn2-env-root-congruence (a (mv-nth 1 (fn2-commit-root-swap id t fn2-core)))
                            (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-root-table-view) clause world)))))
(defthm fn2-env-root-shape
  (and (natp (nth 1 (fn2-env-root fn2-core))) (natp (nth 2 (fn2-env-root fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-root))))
(defthm fn2-env-frontier-of-install
  ; installing published + 1, durable, keeps J4 and does not lower the installed root
  (let ((r (fn2-env-root a)))
    (implies (and (fn2-env-j-frontier log a) (nth 0 r)
                  (equal batch (+ 1 (nth 2 r)))
                  (equal (fn2-env-root b) (list t batch (nth 2 r)))
                  (fn2-env-batch-durable-p batch log))
             (and (fn2-env-j-frontier log b) (<= (fn2-env-installed a) (fn2-env-installed b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-installed fn2-env-prefix-durable-p natp zp nfix (:e nth) car-cons cdr-cons nth
                               (:e zp) (:e natp) fix)
           :use ((:instance fn2-env-root-shape (fn2-core a))
                 (:instance fn2-env-root-fields (r (fn2-env-root b)) (x batch) (y (nth 2 (fn2-env-root a))))
                 (:instance fn2-env-prefix-durable-down (n (nth 1 (fn2-env-root a))) (m (nth 2 (fn2-env-root a))))))))
(defthm fn2-env-frontier-of-publish
  ; publishing the installed batch keeps J4 and the installed root
  (let ((r (fn2-env-root a)))
    (implies (and (fn2-env-j-frontier log a) (nth 0 r)
                  (equal batch (nth 1 r))
                  (equal (fn2-env-root b) (list t (nth 1 r) batch)))
             (and (fn2-env-j-frontier log b) (equal (fn2-env-installed b) (fn2-env-installed a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-installed natp nfix car-cons cdr-cons nth (:e nth) fix)
           :use ((:instance fn2-env-root-shape (fn2-core a))
                 (:instance fn2-env-root-fields (r (fn2-env-root b)) (x (nth 1 (fn2-env-root a))) (y batch))))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :install 7))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :publish 8))))
(defthm fn2-env-j-frontier-install-arm
  (implies (and (fn2-env-j-frontier log fn2-core) (fn2-env-j-row id log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-install*))
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (and (fn2-env-j-frontier log b) (<= (fn2-env-installed fn2-core) (fn2-env-installed b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-idp fn2-commit-arm-row-phase posp (:e member-equal) member-equal)
           :do-not-induct t
           :use ((:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-j1-row-phase-facts)
                 (:instance fn2-env-commit-run-install-facts)
                 (:instance fn2-env-frontier-of-install (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (batch (fn2-machine-batch-no id fn2-core)))
                 (:instance fn2-env-j-frontier-of-root (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(defthm fn2-env-install-arm-publish-bound
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-j-row id log fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-install*))
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (implies (member-equal (fn2-machine-phase id b) (list *fn2-commit-state-publish* *fn2-commit-state-notify*))
                      (<= (fn2-machine-batch-no id fn2-core) (fn2-env-installed b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-idp fn2-commit-arm-row-phase posp (:e member-equal) member-equal fn2-env-installed)
           :do-not-induct t
           :use ((:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-j1-row-phase-facts)
                 (:instance fn2-env-commit-run-install-facts)
                 (:instance fn2-env-root-fields (r (fn2-env-root (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                            (x (fn2-machine-batch-no id fn2-core)) (y (nth 2 (fn2-env-root fn2-core))))))))
(defthm fn2-env-j-row-install-arm
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-install*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                               fn2-commit-idp fn2-commit-arm-row-phase)
           :do-not-induct t
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :use ((:instance fn2-env-install-arm-frame)
                 (:instance fn2-env-j-frontier-install-arm)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-install-arm-publish-bound)
                 (:instance fn2-env-j-row-of-row-frame-off-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 15 19 21 6)) (ch '(20 21 31 5)))
                 (:instance fn2-env-j-row-of-row-frame-same-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 15 19 21 6)) (ch '(20 21 31 5)))))))

(fn2-with-column-projections (fn2-env-io-view)
(defthm fn2-env-commit-run-publish-keeps-commit-io
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*)
           (equal (nth 30 (mv-nth 4 (fn2-commit-run id budget fn2-core))) (nth 30 fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)) (union-theories '(fn2-commit-run
                                                )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-io-view) clause world)))))
(defthm fn2-env-j-frontier-publish-arm
  (implies (and (fn2-env-j-frontier log fn2-core) (fn2-env-j-row id log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*))
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (and (fn2-env-j-frontier log b) (equal (fn2-env-installed b) (fn2-env-installed fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-idp fn2-commit-arm-row-phase posp (:e member-equal) member-equal)
           :do-not-induct t
           :use ((:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-j1-row-phase-facts)
                 (:instance fn2-env-commit-run-publish-facts)
                 (:instance fn2-env-frontier-of-publish (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (batch (fn2-machine-batch-no id fn2-core)))
                 (:instance fn2-env-j-frontier-of-root (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(defthm fn2-env-publish-arm-phase-bound
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-j-row id log fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*))
           (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run id budget fn2-core))) '(9 11 8)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-idp fn2-commit-arm-row-phase posp (:e member-equal) member-equal)
           :do-not-induct t
           :use ((:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-j1-row-phase-facts)
                 (:instance fn2-env-commit-run-publish-facts)))))
(defthm fn2-env-j-row-publish-arm
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                               fn2-commit-idp fn2-commit-arm-row-phase (:e fn2-commit-arm-children))
           :do-not-induct t
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :use ((:instance fn2-env-publish-arm-frame)
                 (:instance fn2-env-commit-run-publish-keeps-commit-io)
                 (:instance fn2-env-ek-of-nth (b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (x fn2-core) (a fn2-core))
                 (:instance fn2-env-ek-refl (a fn2-core))
                 (:instance fn2-env-j-frontier-publish-arm)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-publish-arm-phase-bound)
                 (:instance fn2-env-j-row-of-row-frame-off-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 26 15 19 21 6)) (ch (fn2-commit-arm-children 8)))
                 (:instance fn2-env-j-row-of-row-frame-same-row (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                            (row (fn2-machine-slot id fn2-core)) (cs '(0 26 15 19 21 6)) (ch (fn2-commit-arm-children 8)))))))
(defthm fn2-env-j-rows-member
  (implies (and (fn2-env-j-rows ids log fn2-core) (member-equal id ids))
           (fn2-env-j-row id log fn2-core))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-rows member-equal) :induct (member-equal id ids))))
(make-event (value (cons 'progn (fn2-env-arm-rows-events :install '((fn2-env-j-row id log fn2-core))))))
(make-event (value (cons 'progn (fn2-env-arm-rows-events :publish '((fn2-env-j-row id log fn2-core))))))
;; THE QUIET ARMS: an arm whose columns exclude J's flags, batch and reply
;; count, and whose declared successors exclude :install, :publish and
;; :notify, keeps J by the frame alone (FN2-ENV-J-ROW-OF-ROW-FRAME-OFF-ROW,
;; -SAME-ROW) once its children keep commit-io and the root.
(defun fn2-env-quiet-arm-events (state-name code extra world)
  (declare (xargs :mode :program))
  (let* ((e (assoc code *fn2-commit-arm-decls*)) (ch (cadr e)) (cs (caddr e))
         (const (fn2-env-arm-state-const state-name))
         (ek (member 30 ch)) (rk (member 31 ch))
         (run-ek (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-EK"))
         (run-rk (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-RK"))
         (front (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-frontier state-name) "-ARM"))
         (b '(mv-nth 4 (fn2-commit-run id budget fn2-core))))
    (if (intersectp cs '(9 13 23 24 25 27 33))
        (er hard 'fn2-env-quiet-arm-events "~x0 is not a quiet arm: ~x1." state-name e)
      `(,@(fn2-env-arm-frame-events state-name code)
        ,@(fn2-env-arm-phase-events state-name extra world)
        ,@(and ek
               `(
                 (fn2-with-column-projections (fn2-env-ek)
(defthm ,run-ek
                   (implies (equal (fn2-commit-row-phase id fn2-core) ,const) (fn2-env-ek ,b fn2-core))
                   :rule-classes nil
                   :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run

                                                                 fn2-env-ek-refl)
                                                              (theory 'fn2-arm-frame-base)))
                            :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek) clause world)))))))
        ,@(and rk
               `(
                 (fn2-with-column-projections (fn2-env-rk)
(defthm ,run-rk
                   (implies (equal (fn2-commit-row-phase id fn2-core) ,const) (fn2-env-rk ,b fn2-core))
                   :rule-classes nil
                   :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run

                                                                 fn2-env-rk-refl)
                                                              (theory 'fn2-arm-frame-base)))
                            :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-rk) clause world)))))
                 (defthm ,front
                   (implies (equal (fn2-commit-row-phase id fn2-core) ,const)
                            (and (equal (fn2-env-j-frontier log ,b) (fn2-env-j-frontier log fn2-core))
                                 (equal (fn2-env-installed ,b) (fn2-env-installed fn2-core))))
                   :hints (("Goal" :in-theory nil
                            :use ((:instance ,run-rk) (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b ,b))))))))
        (defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-row state-name) "-ARM")
          (implies (and (fn2-env-j-row i log fn2-core) ,@extra (fn2-env-j-frontier log fn2-core)
                        (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (equal (fn2-commit-row-phase id fn2-core) ,const))
                   (fn2-env-j-row i log ,b))
          :rule-classes nil
          :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                                       fn2-commit-idp fn2-commit-arm-row-phase (:e fn2-commit-arm-children))
                   :do-not-induct t
                   :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                   :use ((:instance ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env state-name) "-ARM-FRAME"))
                         (:instance ,front)
                         ,@(and ek `((:instance ,run-ek)))
                         (:instance ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-NEXT"))
                         (:instance fn2-env-row-phase-snapshot)
                         (:instance fn2-env-j-row-of-row-frame-off-row (a fn2-core) (b ,b)
                                    (row (fn2-machine-slot id fn2-core)) (cs ',cs) (ch ',ch))
                         (:instance fn2-env-j-row-of-row-frame-same-row (a fn2-core) (b ,b)
                                    (row (fn2-machine-slot id fn2-core)) (cs ',cs) (ch ',ch))))))
        ,@(fn2-env-arm-rows-events state-name extra)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :fence 5 nil (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :free 0 '((fn2-commit-idp id fn2-core)) (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :draining 10 nil (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :uncertain 11 nil (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :collect 1 nil (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :seal 2 nil (w state)))))
(make-event (value (cons 'progn (fn2-env-quiet-arm-events :dropping 12 nil (w state)))))
;; ---------------------------------------------------------------------------
;; :ADMIT KEEPS J. Off the started row an admission writes nothing J reads:
;; FN2-ENV-TK (the directory's kinds and slots, and the commit table's rows
;; field and J's columns) with FN2-ENV-EK and FN2-ENV-RK carry J over each
;; sub-operation (FN2-ENV-J-ROWS-OF-TK). The started row's write leaves it
;; at :collect with its batch, no reply and no durability flag, which J
;; asks nothing more of; its extent reservation writes only that row's
;; three extents.
(fn2-defview fn2-env-tk :carrier fn2-core
  :select ((fn2-machines :columns (kind slot) :rows t :scalars (rows))
             (fn2-commit :columns (phase batch-no cb-mode cb-fence-ok cb-deps-ok cb-log-ok cb-acks cb-done)
                         :rows t :scalars (rows))))
(defthm fn2-env-tk-view-equivalence
  (equal (fn2-env-tk b a) (and (fn2-ctf-dir b a)
       (equal (nth 0 (nth 9 b)) (nth 0 (nth 9 a))) (equal (nth 9 (nth 9 b)) (nth 9 (nth 9 a)))
       (equal (nth 13 (nth 9 b)) (nth 13 (nth 9 a))) (equal (nth 23 (nth 9 b)) (nth 23 (nth 9 a)))
       (equal (nth 24 (nth 9 b)) (nth 24 (nth 9 a))) (equal (nth 25 (nth 9 b)) (nth 25 (nth 9 a)))
       (equal (nth 27 (nth 9 b)) (nth 27 (nth 9 a))) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))
       (equal (nth 17 (nth 9 b)) (nth 17 (nth 9 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-tk fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-tk))
(defthm fn2-env-tk-refl (fn2-env-tk a a))
(defthm fn2-env-tk-trans
  (implies (and (fn2-env-tk c b) (fn2-env-tk b a)) (fn2-env-tk c a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-tk)) :use ((:instance fn2-ctf-dir-trans)))))
(defthm fn2-env-tk-of-nth
  (implies (and (equal (nth 3 b) (nth 3 x)) (equal (nth 9 b) (nth 9 x)) (fn2-env-tk x a)) (fn2-env-tk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-tk)) :use ((:instance fn2-ctf-dir-of-nth)))))
(defthm fn2-env-tk-of-row-frame-cols
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch)) (not (member-equal 3 ch))
                (not (member-equal 0 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs)) (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs)) (not (member-equal 27 cs)) (not (member-equal 33 cs)) (not (member-equal 17 cs)))
           (fn2-env-tk b x))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-tk fn2-ctf-dir-refl member-equal car-cons cdr-cons (:e natp) (:e binary-+) (:e equal)) (theory 'minimal-theory)))
           :do-not-induct t
           :use ((:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-row-frame (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-kids-nth (i 0) (k 3) (free (cons 9 ch)) (a x))
                 (:instance fn2-ctf-dir-of-nth (x x) (a x))
                 (:instance fn2-arm-cols-nth (k 0) (j 0) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 9) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 13) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 23) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 24) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 25) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 27) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 33) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 17) (columns cs) (a (nth 9 x)) (b (nth 9 b)))))))
(defthm fn2-env-tk-of-row-frame
  ; a commit-table frame whose columns miss J's keeps TK
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch)) (not (member-equal 3 ch))
                (not (intersectp-equal cs '(0 9 13 17 23 24 25 27 33))) (fn2-env-tk x a))
           (fn2-env-tk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '((:e member-equal)) (theory 'minimal-theory))
           :do-not-induct t
           :use (fn2-env-tk-of-row-frame-cols (:instance fn2-env-tk-trans (c b) (b x))
                 (:instance fn2-env-not-intersectp-member (j 0) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 9) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 13) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 23) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 24) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 25) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 27) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 33) (x cs) (y '(0 9 13 17 23 24 25 27 33)))
                 (:instance fn2-env-not-intersectp-member (j 17) (x cs) (y '(0 9 13 17 23 24 25 27 33)))))))
(in-theory (disable fn2-env-tk))
(make-event (value (cons 'progn (fn2-env-tk-read-events '(phase batch-no cb-mode cb-fence-ok cb-deps-ok cb-log-ok cb-acks cb-done)))))
(defthm fn2-env-read-codes-of-tk
  (implies (fn2-env-tk b a)
           (and (equal (fn2-machine-batch-no-read-code id b) (fn2-machine-batch-no-read-code id a))
                (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (equal (fn2-machine-kind id b) (fn2-machine-kind id a))
                (equal (fn2-machine-slot id b) (fn2-machine-slot id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-tk fn2-ctf-dir fn2-machines-directory-keeps
                                  fn2-machine-batch-no-read-code fn2-machine-cb-acks-read-code fn2-commit-idp
                                  fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-commit-row
                                  fn2-commit-table fn2-commit-rows)
                                  (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)))))
(defthm fn2-env-j-row-of-tk
  ; J at ID survives a step that keeps TK, EK and RK
  (implies (and (fn2-env-j-row id log a) (fn2-env-j-frontier log a)
                (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a) (fn2-corep b) (fn2-core-wfp b))
           (fn2-env-j-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence) (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-env-read-codes-of-tk)
                 (:instance fn2-env-j-row-off-kind (fn2-core b))
                 (:instance fn2-machine-phase-of-tk)
                 (:instance fn2-machine-batch-no-of-tk)
                 (:instance fn2-machine-cb-mode-of-tk)
                 (:instance fn2-machine-cb-fence-ok-of-tk)
                 (:instance fn2-machine-cb-deps-ok-of-tk)
                 (:instance fn2-machine-cb-log-ok-of-tk)
                 (:instance fn2-machine-cb-acks-of-tk)
                 (:instance fn2-env-role-extent-of-ek (role 0))
                 (:instance fn2-env-role-extent-of-ek (role 1))
                 (:instance fn2-env-role-extent-of-ek (role 2))
                 (:instance fn2-env-j-frontier-of-rk)
                 (:instance fn2-env-j-row-transfer)))))
; One semantic locality obligation; the conjunction lift is an instance of
; the shared transport theorem, including its recursive defining equation.
(defun-nx fn2-env-j-view-step (delta g a h b)
  (declare (ignorable delta))
  (and (equal g h) (fn2-env-j-frontier g a)
       (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a)
       (fn2-corep b) (fn2-core-wfp b)))
(defthm fn2-env-j-view-locality
  (implies (and (fn2-env-j-view-step delta g a h b) (fn2-env-j-row key g a))
           (fn2-env-j-row key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-view-step)
           :use ((:instance fn2-env-j-row-of-tk (id key) (log g))))))
(fn2-pw-lift-locality fn2-env-j-view-transport
  :point fn2-env-j-row :all fn2-env-j-rows :step fn2-env-j-view-step
  :locality fn2-env-j-view-locality)

(defthm fn2-env-j-rows-of-tk-rows
  (implies (and (fn2-env-j-rows ids log a) (fn2-env-j-frontier log a)
                (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a) (fn2-corep b) (fn2-core-wfp b))
           (fn2-env-j-rows ids log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-view-step)
           :use ((:instance fn2-env-j-view-transport (keys ids) (g log) (h log))))))
(defthm fn2-env-j-rows-of-tk
  (implies (and (fn2-env-j-rows ids log a) (fn2-env-j-frontier log a)
                (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a) (fn2-corep b) (fn2-core-wfp b))
           (and (fn2-env-j-rows ids log b) (fn2-env-j-frontier log b)))
  :rule-classes nil
  :hints (("Goal" :in-theory nil :use (fn2-env-j-rows-of-tk-rows (:instance fn2-env-j-frontier-of-rk)))))
;; J3 at ID depends on J2's evidence, the phase and the count alone; TK and EK keep them.
(defthm fn2-env-j3-congruence
  (implies (and (fn2-env-j-same-evidence id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a)))
           (and (equal (fn2-env-j3-row id log b) (fn2-env-j3-row id log a))
                (equal (fn2-env-j3e-row id b) (fn2-env-j3e-row id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-j-same-evidence
                               fn2-env-role-offset-of-extent))))
(defthm fn2-env-j3-off-commit
  (implies (not (fn2-commit-idp id fn2-core))
           (and (fn2-env-j3-row id log fn2-core) (fn2-env-j3e-row id fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row))))
(defthm fn2-env-j3-of-tk
  (implies (and (fn2-env-tk b a) (fn2-env-ek b a))
           (and (equal (fn2-env-j3-row id log b) (fn2-env-j3-row id log a))
                (equal (fn2-env-j3e-row id b) (fn2-env-j3e-row id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-j3-off-commit) (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-env-read-codes-of-tk)
                 (:instance fn2-env-commit-idp-kind (fn2-core a))
                 (:instance fn2-machine-phase-of-tk)
                 (:instance fn2-machine-batch-no-of-tk)
                 (:instance fn2-machine-cb-mode-of-tk)
                 (:instance fn2-machine-cb-fence-ok-of-tk)
                 (:instance fn2-machine-cb-deps-ok-of-tk)
                 (:instance fn2-machine-cb-log-ok-of-tk)
                 (:instance fn2-machine-cb-done-of-tk)
                 (:instance fn2-env-role-extent-of-ek (role 0))
                 (:instance fn2-env-role-extent-of-ek (role 1))
                 (:instance fn2-env-role-extent-of-ek (role 2))
                 (:instance fn2-env-j3-congruence)))))

(defun-nx fn2-env-j3-view-step (delta g a h b)
  (declare (ignorable delta))
  (and (equal g h)
       (or (and (fn2-env-tk b a) (fn2-env-ek b a))
           (and (fn2-env-tk a b) (fn2-env-ek a b)))))
(defthm fn2-env-j3-view-locality
  (implies (and (fn2-env-j3-view-step delta g a h b) (fn2-env-j3-point key g a))
           (fn2-env-j3-point key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-point fn2-env-j3-view-step)
           :use ((:instance fn2-env-j3-of-tk (id key) (log g))
                 (:instance fn2-env-j3-of-tk (id key) (log g) (a b) (b a))))))
(fn2-pw-lift-locality fn2-env-j3-view-transport
  :point fn2-env-j3-point :all fn2-env-j3-rows :step fn2-env-j3-view-step
  :locality fn2-env-j3-view-locality :open (fn2-env-j3-point))

(defthm fn2-env-j3-rows-of-tk
  (implies (and (fn2-env-tk b a) (fn2-env-ek b a))
           (equal (fn2-env-j3-rows ids log b) (fn2-env-j3-rows ids log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-view-step (:type-prescription fn2-env-j3-rows))
           :use ((:instance fn2-env-j3-view-transport (keys ids) (g log) (h log))
                 (:instance fn2-env-j3-view-transport (keys ids) (g log) (h log) (a b) (b a))))))
;; The admission's sub-operations keep TK, EK and RK (but the extent
;; reservation, which writes its row's extents): by contract, by row frame,
;; or by one opening; the two pool loops by induction over their passes.



(fn2-with-column-projections (fn2-env-tk)
(defthm fn2-commit-reserve-pools-fn2-env-tk
  (implies (fn2-env-tk fn2-core fn2-rel-c0)
           (fn2-env-tk (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
(fn2-with-column-projections (fn2-env-ek)
(defthm fn2-commit-reserve-pools-fn2-env-ek
  (implies (fn2-env-ek fn2-core fn2-rel-c0)
           (fn2-env-ek (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek) clause world)))))
(fn2-with-column-projections (fn2-env-ek)
(defthm fn2-commit-release-pools-fn2-env-ek
  (implies (fn2-env-ek fn2-core fn2-rel-c0)
           (fn2-env-ek (fn2-commit-release-pools left id owner-gen fn2-core) fn2-rel-c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek) clause world)))))
(fn2-with-column-projections (fn2-env-io-view)
(defthm fn2-env-reserve-extent-io
  ; the extent reservation writes commit-io's extent column only at its row's
  ; three units, and only when it answers :ok
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (let ((out (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (r (* 3 (fn2-commit-row id fn2-core))))
    (and (equal (nth *fn2-commit-io-rows* (nth 30 out)) (nth *fn2-commit-io-rows* (nth 30 fn2-core)))
         (implies (not (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
                  (equal (nth 30 out) (nth 30 fn2-core)))
         (implies (and (natp j) (not (equal j r)) (not (equal j (+ 1 r))) (not (equal j (+ 2 r))))
                  (equal (nth j (nth *fn2-commit-io-extent$ai* (nth 30 out)))
                         (nth j (nth *fn2-commit-io-extent$ai* (nth 30 fn2-core))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)) (e/d (fn2-commit-reserve-extent fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   update-nth-array )
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop update-nth))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-io-view) clause world)))))
(fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-reserve-extent-role-extent
  ; the reservation keeps the role extents of every row but its own
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp role) (< role 3)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (equal (fn2-env-role-extent i role (mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))
                  (fn2-env-role-extent i role fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (e/d (fn2-env-role-extent fn2-commit-resource fn2-core-commit-io fn2-commit-io-extent
                                   fn2-commit-io-rows fn2-commit-row)
                                  (fn2-commit-reserve-extent fn2-commit-idp fn2-machine-slot nth update-nth)))
           :do-not-induct t
           :use (
                 (:instance fn2-env-read-codes-of-tk (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core) (id i))
                 (:instance fn2-env-reserve-extent-io (j (+ (* 3 (fn2-machine-slot i fn2-core)) role)))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 0))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 1))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 2))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
(defthm fn2-env-alloc-reserve-ranges
  ; an accepted reservation names a 32-bit extent and 60-bit epoch and counter
  (implies (and (fn2-extentsp x) (eq (mv-nth 0 (fn2-alloc-reserve x)) :ok))
           (and (unsigned-byte-p 32 (mv-nth 2 (fn2-alloc-reserve x)))
                (unsigned-byte-p 60 (mv-nth 3 (fn2-alloc-reserve x)))
                (unsigned-byte-p 60 (mv-nth 4 (fn2-alloc-reserve x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-alloc-reserve fn2-alloc-current-epoch fn2-alloc-next-counter)
           :use ((:instance fn2-alloc-free-head-range (fn2-extents x))))))
(defthm fn2-env-core-extentsp
  (implies (fn2-corep fn2-core) (fn2-extentsp (fn2-core-extents fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-corep fn2-core-extents))))
(fn2-with-column-projections (fn2-env-io-view)
(defthm fn2-env-reserve-extent-io-shared
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
           (let ((x (nth *fn2-commit-io-extent$ai* (nth 30 (mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))))
                 (r (* 3 (fn2-commit-row id fn2-core))))
             (and (natp (nth r x)) (equal (nth (+ 1 r) x) (nth r x)) (equal (nth (+ 2 r) x) (nth r x))
                  (< (+ 2 r) (nth *fn2-commit-io-rows* (nth 30 fn2-core))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)) (e/d (fn2-commit-reserve-extent fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   update-nth-array  fn2-commit-io-rows)
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop update-nth)))
           :use ((:instance fn2-env-alloc-reserve-ranges (x (fn2-core-extents fn2-core)))
                 (:instance fn2-env-core-extentsp)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-io-view) clause world)))))
(fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-reserve-extent-shared
  ; an accepted reservation gives its row's three roles one extent
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core)
                (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
           (let ((c (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
             (and (natp (fn2-env-role-extent id 0 c))
                  (equal (fn2-env-role-extent id 1 c) (fn2-env-role-extent id 0 c))
                  (equal (fn2-env-role-extent id 2 c) (fn2-env-role-extent id 0 c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (e/d (fn2-env-role-extent fn2-commit-resource fn2-core-commit-io fn2-commit-io-extent
                                   fn2-commit-io-rows)
                                  (fn2-commit-reserve-extent fn2-commit-row fn2-commit-idp nth)))
           :do-not-induct t
           :use ((:instance fn2-env-reserve-extent-io-shared)
                 (:instance fn2-env-reserve-extent-io (j 0))

                 (:instance fn2-env-read-codes-of-tk (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
(fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-j3-reserve-extent
  ; the extent reservation keeps J3 at every id but its own row's
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (and (equal (fn2-env-j3-row i log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (fn2-env-j3-row i log fn2-core))
                (equal (fn2-env-j3e-row i (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (fn2-env-j3e-row i fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-j-same-evidence fn2-env-tk-refl (:e natp) (:e <)) (theory 'minimal-theory))))
           :cases ((fn2-commit-idp i fn2-core))
           :do-not-induct t)
          ("Subgoal 2" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-j3-off-commit fn2-env-tk-refl) (theory 'minimal-theory))))
           :use (
                 (:instance fn2-env-read-codes-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))))
          ("Subgoal 1"
           :use (
                 (:instance fn2-env-read-codes-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-env-commit-idp-kind (id i))
                 (:instance fn2-machine-phase-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-batch-no-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-mode-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-fence-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-deps-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-log-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-done-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-env-reserve-extent-role-extent (role 0))
                 (:instance fn2-env-reserve-extent-role-extent (role 1))
                 (:instance fn2-env-reserve-extent-role-extent (role 2))
                 (:instance fn2-env-j3-congruence (id i) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
(defthm fn2-env-j-row-of-row-frame-other-slot
  ; a commit-table frame at ROW keeps J at an id at another slot, whatever its columns
  (implies (and (fn2-env-j-row i log a) (fn2-env-j-frontier log b)
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (fn2-corep b) (fn2-core-wfp b)
                (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (fn2-env-ek b a)
                (not (member-equal 33 cs)) (fn2-ctf-dir b a)
                (not (equal (fn2-machine-slot i a) row)))
           (fn2-env-j-row i log b))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence) (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind i a) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers (id i))
                 (:instance fn2-env-j-row-off-kind (id i) (fn2-core b))
                 (:instance fn2-env-read-codes-of-row-frame (id i))
                 (:instance fn2-machine-phase-of-row-frame (id i))
                 (:instance fn2-machine-batch-no-of-row-frame (id i))
                 (:instance fn2-machine-cb-mode-of-row-frame (id i))
                 (:instance fn2-machine-cb-fence-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-deps-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-log-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-acks-of-row-frame (id i))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 0))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 1))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 2))
                 (:instance fn2-env-j-row-transfer (id i))))))
(fn2-with-column-projections (fn2-env-rk fn2-env-tk)
(defthm fn2-env-j-row-reserve-extent
  ; the extent reservation keeps J at every id but its own row's
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (fn2-env-j-row i log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-j-same-evidence fn2-env-j-row-not-idp fn2-env-tk-refl fn2-env-rk-refl (:e natp) (:e <))
                                             (theory 'minimal-theory))))
           :cases ((equal (fn2-machine-kind i fn2-core) *fn2-commit-kind*))
           :do-not-induct t
           :use (

                 (:instance fn2-env-j-frontier-of-rk (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-commit-reserve-extent-preserves-type)
                 (:instance fn2-commit-reserve-extent-preserves-wfp)
                 (:instance fn2-env-read-codes-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-env-j-row-off-kind (id i) (fn2-core (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-machine-phase-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-batch-no-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-mode-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-fence-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-deps-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-log-ok-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-machine-cb-acks-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-env-reserve-extent-role-extent (role 0))
                 (:instance fn2-env-reserve-extent-role-extent (role 1))
                 (:instance fn2-env-reserve-extent-role-extent (role 2))
                 (:instance fn2-env-j-row-transfer (id i) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-rk fn2-env-tk) clause world)))))
(defthm fn2-env-j-row-of-collect
  ; J asks nothing of a row at :collect with a positive batch, no reply and no flag
  (implies (and (fn2-commit-idp i c) (fn2-commit-idp id c)
                (equal (fn2-machine-slot i c) (fn2-machine-slot id c))
                (equal (fn2-machine-phase id c) *fn2-commit-state-collect*)
                (posp (fn2-machine-batch-no id c))
                (equal (fn2-machine-cb-deps-ok id c) 0) (equal (fn2-machine-cb-log-ok id c) 0)
                (equal (nth (fn2-machine-slot id c) (nth *fn2-env-acks* (nth *fn2-env-tk* c))) 0))
           (fn2-env-j-row i log c))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row fn2-env-j1-row fn2-env-j2-row member-equal
                                               (:e member-equal) (:e posp))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-same-slot-reads (fn2-core c))
                 (:instance fn2-env-commit-idp-kind (id i) (fn2-core c))
                 (:instance fn2-env-commit-row-unfolds (id i) (fn2-core c))))))
;; J AS ONE PREDICATE OF THE CORE (FN2-ENV-JR), each admission step's rule.
(defun-nx fn2-env-jr (ids log fn2-core)
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-rows ids log fn2-core)
       (fn2-env-j-frontier log fn2-core)))
(defthm fn2-env-jr-of-tk
  (implies (and (fn2-env-jr ids log a) (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a) (fn2-corep b) (fn2-core-wfp b))
           (fn2-env-jr ids log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-jr) :use (fn2-env-j-rows-of-tk fn2-env-j3-rows-of-tk))))
(defthm fn2-env-commit-idp-cell
  ; a readable commit row's cell: the write guard's first four conjuncts
  (implies (fn2-commit-idp id fn2-core)
           (and (fn2-machine-idp id fn2-core) (equal (fn2-machine-kind id fn2-core) *fn2-commit-kind*)
                (natp (fn2-machine-slot id fn2-core))
                (< (fn2-machine-slot id fn2-core) (fn2-commit-rows (fn2-commit-table fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code)
                                  (fn2-machine-idp fn2-machine-kind fn2-machine-slot)))))
(defthm fn2-env-same-slot-mode
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp id fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
           (equal (fn2-machine-cb-mode i fn2-core) (fn2-machine-cb-mode id fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                   fn2-machine-cb-mode fn2-machine-cb-mode-read-code)
                                  (fn2-machine-kind fn2-machine-slot)))))
(defthm fn2-env-same-slot-done
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp id fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
           (equal (fn2-machine-cb-done i fn2-core) (fn2-machine-cb-done id fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                   fn2-machine-cb-done fn2-machine-cb-done-read-code)
                                  (fn2-machine-kind fn2-machine-slot)))))
(defthm fn2-env-same-slot-evidence
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp j fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot j fn2-core)))
           (and (equal (fn2-machine-cb-acks i fn2-core) (fn2-machine-cb-acks j fn2-core))
                (equal (fn2-machine-cb-acks-read-code i fn2-core) (fn2-machine-cb-acks-read-code j fn2-core))
                (equal (fn2-machine-batch-no-read-code i fn2-core) (fn2-machine-batch-no-read-code j fn2-core))
                (equal (fn2-env-role-extent i role fn2-core) (fn2-env-role-extent j role fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-role-extent fn2-commit-resource fn2-commit-row fn2-env-cell-code)
                                  (fn2-commit-idp fn2-machine-slot fn2-machine-idp fn2-machine-kind))
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-kind (id i))
                 (:instance fn2-env-commit-idp-kind (id j))
                 (:instance fn2-env-commit-idp-cell (id i))
                 (:instance fn2-env-commit-idp-cell (id j))
                 (:instance fn2-env-commit-row-unfolds (id i))
                 (:instance fn2-env-commit-row-unfolds (id j))))))
(defthm fn2-env-j-row-same-slot
  ; two readable commit ids at one slot carry the same J
  (implies (and (fn2-env-j-row j log fn2-core) (fn2-commit-idp i fn2-core) (fn2-commit-idp j fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot j fn2-core)))
           (fn2-env-j-row i log fn2-core))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j-row fn2-env-j1-row fn2-env-j2-row fn2-env-role-offset-of-extent)
           :do-not-induct t
           :use ((:instance fn2-env-same-slot-reads (i i) (id j))
                 (:instance fn2-env-same-slot-mode (i i) (id j))
                 (:instance fn2-env-same-slot-evidence (role 0))
                 (:instance fn2-env-same-slot-evidence (role 1))
                 (:instance fn2-env-same-slot-evidence (role 2))))))
(defthm fn2-env-j3-same-slot
  ; two readable commit ids at one slot carry the same J3
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp j fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot j fn2-core)))
           (and (equal (fn2-env-j3-row i log fn2-core) (fn2-env-j3-row j log fn2-core))
                (equal (fn2-env-j3e-row i fn2-core) (fn2-env-j3e-row j fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-role-offset-of-extent)
           :do-not-induct t
           :use ((:instance fn2-env-same-slot-reads (i i) (id j))
                 (:instance fn2-env-same-slot-mode (i i) (id j))
                 (:instance fn2-env-same-slot-done (i i) (id j))
                 (:instance fn2-env-same-slot-evidence (role 0))
                 (:instance fn2-env-same-slot-evidence (role 1))
                 (:instance fn2-env-same-slot-evidence (role 2))))))
;; THE STARTED ROW. fn2-commit-start's row write, accepted with phase
;; :collect, a positive batch, no reply and no durability flag, leaves J
;; true of every id at its row (J asks nothing of such a row but the
;; batch); every other id keeps J by the write's row frame.
(defun fn2-env-start-j-events (world)
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (formals (formals w world))
         (wformals (butlast (cdr formals) 1))
         (call (cons w formals))
         (e (fn2-arm-frame-known w kind world))
         (cs (fn2-arm-frame-entry-j e))
         (ch (fn2-arm-frame-entry-s e))
         (row '(fn2-machine-slot id fn2-core))
         (c2 '(mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))
         (call2 (cons w (append (butlast formals 1) (list c2))))
         (fits (nthcdr 5 (fn2-arm-frame-write-guards kind ord wformals world)))
         (written `((equal ,(nth (position-eq 'phase ord) wformals) ,*fn2-commit-state-collect*)
                    (equal ,(nth (position-eq 'cb-deps-ok ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-log-ok ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-acks ord) wformals) 0)
                    (posp ,(nth (position-eq 'batch-no ord) wformals))
                    (equal ,(nth (position-eq 'cb-done ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-fence-ok ord) wformals) 0)))
         (ok-ext '(eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
         (frame-uses `((:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 30) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 31) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-ctf-dir-readers (id i) (b ,call) (a fn2-core))
                       (:instance fn2-ctf-dir-readers (id id) (b ,call) (a fn2-core))
                       (:instance fn2-env-read-codes-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-env-read-codes-of-row-frame (id id) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call)))))
    `((defthm fn2-env-start-write-keeps-ids
        ; the write keeps every id's readability and slot
        (and (equal (fn2-commit-idp x ,call) (fn2-commit-idp x fn2-core))
             (equal (fn2-machine-slot x ,call) (fn2-machine-slot x fn2-core)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir-refl (:type-prescription fn2-machine-slot-natp))
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-ctf-dir-readers (id x) (b ,call) (a fn2-core))
                       (:instance fn2-env-read-codes-of-row-frame (id x) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))))))
      (defthm fn2-env-start-write-row
        ; what the accepted write leaves at its row
        (implies (and (fn2-env-start-write-accepted ,@formals) ,@written (fn2-commit-idp id fn2-core))
                 (and (equal (fn2-machine-phase id ,call) ,*fn2-commit-state-collect*)
                      (equal (fn2-machine-batch-no id ,call) ,(nth (position-eq 'batch-no ord) wformals))
                      (equal (fn2-machine-cb-deps-ok id ,call) 0) (equal (fn2-machine-cb-log-ok id ,call) 0)
                      (equal (fn2-machine-cb-fence-ok id ,call) 0) (equal (fn2-machine-cb-done id ,call) 0)
                      (equal (nth (fn2-machine-slot id fn2-core) (nth *fn2-env-acks* (nth *fn2-env-tk* ,call))) 0)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-start-write-accepted) (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-READS"))
                       (:instance fn2-env-start-write-acks)
                       (:instance fn2-env-start-write-keeps-ids (x id))
                       (:instance fn2-commit-idp (fn2-core ,call))
                       (:instance fn2-env-commit-row-flag-reads (fn2-core ,call))
                       (:instance fn2-env-commit-row-count-reads (fn2-core ,call))))))
      (defthm fn2-env-start-write-same-slot
        ; the started row: every id there reads :collect, the batch, no reply, no flag
        (implies (and (fn2-env-start-write-accepted ,@formals) ,@written
                      (fn2-commit-idp id fn2-core) (fn2-commit-idp i fn2-core)
                      (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
                 (fn2-env-j-row i log ,call))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(posp) (theory 'minimal-theory))
                 :do-not-induct t
                 :use (fn2-env-start-write-row
                       (:instance fn2-env-start-write-keeps-ids (x id))
                       (:instance fn2-env-start-write-keeps-ids (x i))
                       (:instance fn2-env-j-row-of-collect (c ,call))))))
      (defthm fn2-env-start-write-other
        ; every other id keeps J by the write's row frame
        (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-corep ,call) (fn2-core-wfp ,call)
                      (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
                 (fn2-env-j-row i log ,call))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row-not-idp fn2-env-ek-refl fn2-ctf-dir-refl
                                                     (:type-prescription fn2-machine-slot-natp))
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use (,@frame-uses
                       (:instance fn2-env-ek-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-j-frontier-of-root (b ,call) (a fn2-core))
                       (:instance fn2-env-j-row-of-row-frame-other-slot (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))))))
      (fn2-with-column-projections (fn2-env-rk fn2-env-tk)
(defthm fn2-env-start-tail-j-row
        ; the extent reservation and the row write, from the row's free core
        (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core)
                      ,@fits ,@written)
                 (fn2-env-j-row i log ,call2))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-tk-refl fn2-env-rk-refl) (theory 'minimal-theory))))
                 :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance ,(fn2-columns-sym w "-PRESERVES-TYPE") (fn2-core ,c2))
                       (:instance ,(fn2-columns-sym w "-PRESERVES-WFP") (fn2-core ,c2))


                       (:instance fn2-env-j-frontier-of-rk (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-commit-idp-cell (fn2-core ,c2))
                       (:instance fn2-env-start-write-accepted-suff (fn2-core ,c2))
                       (:instance fn2-env-start-write-same-slot (fn2-core ,c2))
                       (:instance fn2-env-j-row-reserve-extent)
                       (:instance fn2-env-start-write-other (fn2-core ,c2))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-rk fn2-env-tk) clause world)))))
      (defthm fn2-env-start-tail-j-rows
        (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j-frontier log fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core)
                      ,@fits ,@written)
                 (fn2-env-j-rows ids log ,call2))
        :rule-classes nil
        :hints (("Goal" :induct (len ids) :in-theory '(fn2-env-j-rows len atom))
                ("Subgoal *1/1" :use ((:instance fn2-env-start-tail-j-row (i (car ids)))))))
      (defthm fn2-env-start-write-extents
        ; the write keeps every id's role extents
        (equal (fn2-env-role-extent x role ,call) (fn2-env-role-extent x role fn2-core))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-ek-refl fn2-ctf-dir-refl (:type-prescription fn2-machine-slot-natp))
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 30) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-env-ek-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-start-write-keeps-ids)
                       (:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-read-codes-of-row-frame (id x) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-env-role-extent-of-ek (id x) (b ,call) (a fn2-core))))))
      (defthm fn2-env-start-write-j3-row
        ; the started row: :collect with its extents shared, nothing counted, no fence
        (implies (and (fn2-env-start-write-accepted ,@formals) ,@written (fn2-commit-idp id fn2-core)
                      (natp (fn2-env-role-extent id 0 fn2-core))
                      (equal (fn2-env-role-extent id 1 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                      (equal (fn2-env-role-extent id 2 fn2-core) (fn2-env-role-extent id 0 fn2-core)))
                 (and (fn2-env-j3-row id log ,call) (fn2-env-j3e-row id ,call)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-j3-row fn2-env-j3e-row member-equal (:e member-equal))
                                                   (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance fn2-env-start-write-row)
                       (:instance fn2-env-start-write-extents (x id) (role 0))
                       (:instance fn2-env-start-write-extents (x id) (role 1))
                       (:instance fn2-env-start-write-extents (x id) (role 2))))))
      (defthm fn2-env-start-write-j3-other
        ; every other id keeps J3 by the write's row frame
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
                 (and (equal (fn2-env-j3-row i log ,call) (fn2-env-j3-row i log fn2-core))
                      (equal (fn2-env-j3e-row i ,call) (fn2-env-j3e-row i fn2-core))))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-j3-off-commit fn2-ctf-dir-refl
                                                     (:type-prescription fn2-machine-slot-natp))
                                                   (theory 'fn2-arm-frame-base))
                 :cases ((fn2-commit-idp i fn2-core))
                 :do-not-induct t
                 :use ((:instance fn2-env-start-write-keeps-ids (x i))
                       (:instance fn2-env-commit-idp-kind (id i))
                       (:instance fn2-env-start-write-extents (x i) (role 0))
                       (:instance fn2-env-start-write-extents (x i) (role 1))
                       (:instance fn2-env-start-write-extents (x i) (role 2))
                       (:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-ctf-dir-refl (a fn2-core))
                       (:instance fn2-env-read-codes-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-phase-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-batch-no-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-cb-mode-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-cb-fence-ok-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-cb-deps-ok-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-cb-log-ok-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-machine-cb-done-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       (:instance fn2-env-j3-congruence (id i) (a fn2-core) (b ,call))))))
      (fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-start-tail-j3-same
        ; at the started slot: the row write's J3
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext
                      ,@fits ,@written
                      (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
                 (and (fn2-env-j3-row i log ,call2) (fn2-env-j3e-row i ,call2)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-tk-refl) (theory 'minimal-theory))))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)

                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-commit-idp-cell (fn2-core ,c2))
                       (:instance fn2-env-start-write-accepted-suff (fn2-core ,c2))
                       (:instance fn2-env-reserve-extent-shared)
                       (:instance fn2-env-start-write-j3-row (fn2-core ,c2))
                       (:instance fn2-env-start-write-keeps-ids (x i) (fn2-core ,c2))
                       (:instance fn2-env-start-write-keeps-ids (x id) (fn2-core ,c2))
                       (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core ,call2))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
      (fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-start-tail-j3-other
        ; elsewhere: the reservation and the write keep J3
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
                 (and (equal (fn2-env-j3-row i log ,call2) (fn2-env-j3-row i log fn2-core))
                      (equal (fn2-env-j3e-row i ,call2) (fn2-env-j3e-row i fn2-core))))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-tk-refl) (theory 'minimal-theory))))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)

                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-j3-reserve-extent)
                       (:instance fn2-env-start-write-j3-other (fn2-core ,c2))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
      (defthm fn2-env-start-tail-j3-row
        ; the extent reservation and the row write keep J3 at every id
        (implies (and (fn2-env-j3-row i log fn2-core) (fn2-env-j3e-row i fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext
                      ,@fits ,@written)
                 (and (fn2-env-j3-row i log ,call2) (fn2-env-j3e-row i ,call2)))
        :rule-classes nil
        :hints (("Goal" :in-theory (theory 'minimal-theory)
                 :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                 :do-not-induct t
                 :use (fn2-env-start-tail-j3-same fn2-env-start-tail-j3-other))))
      (defthm fn2-env-start-tail-j3-rows
        (implies (and (fn2-env-j3-rows ids log fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext
                      ,@fits ,@written)
                 (fn2-env-j3-rows ids log ,call2))
        :rule-classes nil
        :hints (("Goal" :induct (len ids) :in-theory '(fn2-env-j3-rows len atom))
                ("Subgoal *1/1" :use ((:instance fn2-env-start-tail-j3-row (i (car ids)))))))
      (defthm fn2-env-start-write-frontier
        (and (equal (fn2-env-j-frontier log ,call) (fn2-env-j-frontier log fn2-core))
             (equal (fn2-env-rk ,call fn2-core) t))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-rk-refl) (theory 'fn2-arm-frame-base))
                 :use ((:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 31) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-env-rk-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-j-frontier-of-root (b ,call) (a fn2-core))))))
      (fn2-with-column-projections (fn2-env-rk)
(defthm fn2-env-start-tail-jr
        (implies (and (fn2-env-jr ids log fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext ,@fits ,@written)
                 (fn2-env-jr ids log ,call2))
        :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-env-jr fn2-env-rk-refl) (theory 'minimal-theory)))
                 :do-not-induct t
                 :use (fn2-env-start-tail-j-rows fn2-env-start-tail-j3-rows
                       (:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance ,(fn2-columns-sym w "-PRESERVES-TYPE") (fn2-core ,c2))
                       (:instance ,(fn2-columns-sym w "-PRESERVES-WFP") (fn2-core ,c2))

                       (:instance fn2-env-j-frontier-of-rk (b ,c2) (a fn2-core))
                       (:instance fn2-env-start-write-frontier (fn2-core ,c2))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-rk) clause world))))))))
(make-event (value (cons 'progn (fn2-env-start-j-events (w state)))))
(make-event (value (cons 'progn (fn2-env-jr-events '((fn2-core-stop (unsigned-byte-p 8 reason)) fn2-commit-reserve-pools fn2-commit-release-pools
  fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake) (w state)))))
(fn2-with-column-projections (fn2-env-rk fn2-env-tk)
(defthm fn2-commit-reserve-extent-fn2-env-jr
  ; a refused reservation writes no extent
  (implies (and (fn2-env-jr ids log fn2-core) (not (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok)))
           (fn2-env-jr ids log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-jr fn2-env-tk-refl fn2-env-rk-refl fn2-env-ek-refl
                                               fn2-commit-reserve-extent-preserves-type fn2-commit-reserve-extent-preserves-wfp)
                                             (theory 'minimal-theory))))
           :do-not-induct t
           :use ((:instance fn2-env-jr-of-tk (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))


                 (:instance fn2-env-reserve-extent-io (j 0))
                 (:instance fn2-env-ek-of-nth (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (x fn2-core) (a fn2-core))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-rk fn2-env-tk) clause world)))))
(fn2-with-column-projections (fn2-env-tk)
(defthm fn2-env-reserve-pools-idp
  (equal (fn2-commit-idp x (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core))) (fn2-commit-idp x fn2-core))
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-tk-refl)))
           :use (
                 (:instance fn2-env-read-codes-of-tk (id x) (b (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)))
                            (a fn2-core))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-tk) clause world)))))
(defthm fn2-env-commit-idp-u32
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp x c)) (unsigned-byte-p 32 x))
  :hints (("Goal" :in-theory (enable fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-machine-idp))))
(defthm fn2-env-generation-u60
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp id c)) (unsigned-byte-p 60 (fn2-machine-generation id c))))
(defthm fn2-env-generation-natp
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp id c)) (natp (fn2-machine-generation id c)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn2-env-generation-u60 :in-theory (disable fn2-env-generation-u60))))
(defthm fn2-env-gen-limit-natp
  (implies (fn2-corep c) (natp (fn2-machine-gen-limit c)))
  :rule-classes :type-prescription)
(defthm fn2-env-gen-limit-bound
  (implies (and (fn2-corep c) (fn2-core-wfp c)) (< (fn2-machine-gen-limit c) 1152921504606846976))
  :rule-classes :linear)
(defthm fn2-env-jr-forward
  (implies (fn2-env-jr ids log fn2-core) (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn2-env-jr))))
(defthm fn2-env-commit-start-jr
  (implies (fn2-env-jr ids log fn2-core)
           (fn2-env-jr ids log (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core))))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-env-start-tail-jr fn2-commit-reserve-extent-fn2-env-jr
                                               fn2-commit-reserve-pools-fn2-env-jr fn2-commit-release-pools-fn2-env-jr
                                               fn2-commit-prepare-root-fn2-env-jr fn2-commit-ready-fn2-env-jr
                                               fn2-core-stop-fn2-env-jr fn2-env-reserve-pools-idp fn2-env-commit-idp-u32
                                               fn2-env-generation-u60 fn2-env-generation-natp fn2-env-gen-limit-natp fn2-env-gen-limit-bound fn2-env-jr-forward unsigned-byte-p integer-range-p posp)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-commit-admit-keyed-jr
  (implies (fn2-env-jr ids log fn2-core)
           (fn2-env-jr ids log (mv-nth 4 (fn2-commit-admit-keyed n mode okind oslot ogen fn2-core))))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-admit-keyed fn2-env-commit-start-jr fn2-commit-put-members-fn2-env-jr
                                               fn2-core-stop-fn2-env-jr fn2-env-jr-forward)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-admit-jr
  (implies (fn2-env-jr ids log fn2-core)
           (fn2-env-jr ids log (fn2-env-admit members mode fn2-core)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-env-commit-admit-keyed-jr fn2-exec-wake-fn2-env-jr)
                                             (theory 'fn2-arm-frame-base)))))
;; THE ADMISSION KEEPS J: every id's J1/J2 and the frontier J4.
(defthm fn2-env-j-admit-step
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-rows ids log fn2-core) (fn2-env-j-frontier log fn2-core))
           (and (fn2-env-j-rows ids log (fn2-env-admit members mode fn2-core))
                (fn2-env-j3-rows ids log (fn2-env-admit members mode fn2-core))
                (fn2-env-j-frontier log (fn2-env-admit members mode fn2-core))))
  :hints (("Goal" :in-theory '(fn2-env-jr) :use fn2-env-admit-jr)))
(defthm fn2-env-step-admit-unfolds
  (implies (equal (fn2-env-tag action) :admit)
           (equal (fn2-env-step action nil image rlog fn2-core)
                  (mv nil (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-step))))
(defthm fn2-env-dur-inv-admit-step
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-env-dur-inv ids acked log fn2-core)
                (equal (fn2-env-tag action) :admit))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-dur-inv ids (fn2-env-observe ids acked after)
                              (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-dur-inv) (theory 'minimal-theory))
           :use ((:instance fn2-env-step-admit-unfolds)
                 (:instance fn2-env-inv-admit-step)
                 (:instance fn2-env-j-admit-step (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))
                 (:instance fn2-env-j-rows-extends (more nil)
                            (fn2-core (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core)))
                 (:instance fn2-env-j3-rows-extends (more nil)
                            (fn2-core (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core)))
                 (:instance fn2-env-j-frontier-extends (more nil)
                            (fn2-core (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core)))))))
; Every step kind but :turn preserves the durability invariant.
(defthm fn2-env-dur-inv-step-but-turn
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-env-dur-inv ids acked log fn2-core)
                (not (equal (fn2-env-tag action) :turn)))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-dur-inv ids (fn2-env-observe ids acked after)
                              (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (union-theories '(member-equal) (theory 'minimal-theory))
           :use (fn2-env-dur-inv-admit-step fn2-env-dur-inv-host-step))))
;; ---------------------------------------------------------------------------
;; THE VISITED ID. A visit of a commit id that is not a readable row only
;; stops the core, which keeps J; a readable one reads the row at its slot,
;; so J at it is J at the ghost id at that slot: the ghost ids
;; (FN2-ENV-COMMIT-IDS) cover every readable commit row once the directory
;; holds them at slots 0 and 1 and the commit table has two rows
;; (FN2-ENV-COMMIT-SLOTS-P).
(defthm fn2-env-commit-run-non-row-jr
  (implies (and (fn2-env-jr ids log fn2-core) (not (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)))
           (fn2-env-jr ids log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-core-stop-fn2-env-jr) (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-j-rows-non-row-visit
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-rows ids log fn2-core) (fn2-env-j-frontier log fn2-core)
                (not (fn2-commit-idp id fn2-core)))
           (and (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j3-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j-frontier log (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
  :hints (("Goal" :in-theory '(fn2-env-jr fn2-commit-idp) :use fn2-env-commit-run-non-row-jr)))
(defun-nx fn2-env-commit-slots-p (profile fn2-core)
  ; the directory holds the ghost ids at slots 0 and 1 of a two-row commit table
  (let ((a (fn2-machine-global-id *fn2-commit-kind* 0 profile)) (b (fn2-machine-global-id *fn2-commit-kind* 1 profile)))
    (and (<= (fn2-commit-rows (fn2-commit-table fn2-core)) 2)
         (fn2-commit-idp a fn2-core) (equal (fn2-machine-slot a fn2-core) 0)
         (fn2-commit-idp b fn2-core) (equal (fn2-machine-slot b fn2-core) 1))))
(defthm fn2-env-commit-ids-cover
  ; every readable commit row is at the slot of a ghost id
  (implies (and (fn2-commit-idp id fn2-core) (fn2-env-commit-slots-p profile fn2-core))
           (let ((j (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id fn2-core) profile)))
             (and (member-equal j (fn2-env-commit-ids profile))
                  (fn2-commit-idp j fn2-core)
                  (equal (fn2-machine-slot j fn2-core) (fn2-machine-slot id fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-commit-slots-p fn2-env-commit-ids natp member-equal car-cons cdr-cons) (theory 'minimal-theory))
           :cases ((equal (fn2-machine-slot id fn2-core) 0) (equal (fn2-machine-slot id fn2-core) 1))
           :use ((:instance fn2-env-commit-idp-cell)))))
(defthm fn2-env-j-row-of-commit-ids
  ; J at every readable commit row from J at the ghost ids
  (implies (and (fn2-commit-idp id fn2-core) (fn2-env-commit-slots-p profile fn2-core)
                (fn2-env-j-rows (fn2-env-commit-ids profile) log fn2-core))
           (fn2-env-j-row id log fn2-core))
  :rule-classes nil
  :hints (("Goal" :in-theory nil
           :use ((:instance fn2-env-commit-ids-cover)
                 (:instance fn2-env-j-rows-member (ids (fn2-env-commit-ids profile))
                            (id (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id fn2-core) profile)))
                 (:instance fn2-env-j-row-same-slot (i id)
                            (j (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id fn2-core) profile)))))))
;; THE SLOTS STAY. FN2-ENV-COMMIT-SLOTS-P reads the directory's kinds and
;; slots and the commit table's rows field (FN2-ENV-SK); every step but
;; :turn keeps them (the host steps touch neither child, and every admission
;; sub-operation writes the table only below its rows field), and so does
;; every commit visit (each arm's frame keeps the directory and leaves the
;; rows field).
(fn2-defview fn2-env-sk :carrier fn2-core
  :select ((fn2-machines :columns (kind slot) :rows t :scalars (rows))
             (fn2-commit :scalars (rows))))
(defthm fn2-env-sk-view-equivalence
  (equal (fn2-env-sk b a) (and (fn2-ctf-dir b a) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-sk fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-sk))
(defthm fn2-env-sk-refl (fn2-env-sk a a))
(defthm fn2-env-sk-of-nth
  (implies (and (equal (nth 3 b) (nth 3 x)) (equal (nth 9 b) (nth 9 x)) (fn2-env-sk x a)) (fn2-env-sk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-sk)) :use ((:instance fn2-ctf-dir-of-nth)))))
(defthm fn2-env-sk-trans
  (implies (and (fn2-env-sk c b) (fn2-env-sk b a)) (fn2-env-sk c a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-sk)) :use ((:instance fn2-ctf-dir-trans)))))
(defthm fn2-env-sk-of-row-frame
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch)) (not (member-equal 3 ch))
                (not (intersectp-equal cs '(33))) (fn2-env-sk x a))
           (fn2-env-sk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-sk member-equal car-cons cdr-cons (:e member-equal) (:e natp) (:e binary-+)) (theory 'minimal-theory)))
           :do-not-induct t
           :use ((:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-row-frame (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-kids-nth (i 0) (k 3) (free (cons 9 ch)) (a x))
                 (:instance fn2-ctf-dir-of-nth (x x) (a x))
                 (:instance fn2-ctf-dir-trans (c b) (b x))
                 (:instance fn2-ctf-dir-refl (a x))
                 (:instance fn2-arm-cols-nth (k 0) (j 33) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-env-not-intersectp-member (j 33) (x cs) (y '(33)))))))
(defthm fn2-env-sk-of-tk
  (implies (fn2-env-tk b a) (fn2-env-sk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) '(fn2-env-tk fn2-env-sk)))))
(in-theory (disable fn2-env-sk))

(defthm fn2-env-sk-projections
  (implies (fn2-env-sk b a)
           (and (fn2-ctf-dir b a)
                (equal (fn2-commit-rows (fn2-commit-table b))
                       (fn2-commit-rows (fn2-commit-table a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-rows fn2-commit-table)
           :use fn2-env-sk-view-equivalence)))

(defthm fn2-env-commit-slots-p-of-sk
  (implies (fn2-env-sk b a)
           (equal (fn2-env-commit-slots-p profile b) (fn2-env-commit-slots-p profile a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-commit-slots-p fn2-commit-idp fn2-commit-snapshot-read-code
                                   fn2-machine-phase-read-code fn2-commit-table fn2-commit-rows)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
           :do-not-induct t
           :use ((:instance fn2-env-sk-projections)
                 (:instance fn2-ctf-dir-readers (id (fn2-machine-global-id *fn2-commit-kind* 0 profile)))
                 (:instance fn2-ctf-dir-readers (id (fn2-machine-global-id *fn2-commit-kind* 1 profile)))))))
;; the host steps: neither child
(defthm fn2-env-commit-rows-child-frame
  (and (equal (fn2-commit-rows (fn2-commit-table (update-fn2-core-ops x c))) (fn2-commit-rows (fn2-commit-table c)))
       (equal (fn2-commit-rows (fn2-commit-table (update-fn2-core-pool x c))) (fn2-commit-rows (fn2-commit-table c)))
       (equal (fn2-commit-rows (fn2-commit-table (update-fn2-core-extents x c))) (fn2-commit-rows (fn2-commit-table c))))
  :hints (("Goal" :in-theory (enable fn2-commit-table update-fn2-core-ops update-fn2-core-pool update-fn2-core-extents))))
(defthm fn2-env-commit-slots-p-child-frame
  (and (equal (fn2-env-commit-slots-p p (update-fn2-core-ops x fn2-core)) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (update-fn2-core-pool x fn2-core)) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (update-fn2-core-extents x fn2-core)) (fn2-env-commit-slots-p p fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-commit-slots-p fn2-env-commit-rows-child-frame
                                fn2-commit-idp-of-update-fn2-core-ops fn2-commit-idp-of-update-fn2-core-pool fn2-commit-idp-of-update-fn2-core-extents
                                fn2-machine-slot-of-update-fn2-core-ops fn2-machine-slot-of-update-fn2-core-pool fn2-machine-slot-of-update-fn2-core-extents))))
(defthm fn2-env-commit-slots-p-host-frame
  (and (equal (fn2-env-commit-slots-p p (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (fn2-host-post-signal bits fn2-core)) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-commit-slots-p p fn2-core))
       (equal (fn2-env-commit-slots-p p (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-commit-slots-p p fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                   fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                   fn2-env-fill fn2-env-begin-epoch)
                                  (fn2-env-commit-slots-p)))))
(defthm fn2-env-commit-slots-p-take-frame
  (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-env-take nil image fn2-core))) (fn2-env-commit-slots-p p fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-env-take) (fn2-env-commit-slots-p)))))
(defthm fn2-env-commit-slots-p-host-step
  (implies (not (member-eq (fn2-env-tag action) '(:turn :admit)))
           (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                  (fn2-env-commit-slots-p p fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post)
                                  (fn2-env-commit-slots-p fn2-env-take)))))
;; the admission: each sub-operation keeps SK (the started row's write below its rows field)

(fn2-with-column-projections (fn2-env-sk)
(defthm fn2-commit-reserve-pools-fn2-env-sk
  (implies (fn2-env-sk fn2-core fn2-rel-c0)
           (fn2-env-sk (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-sk) clause world)))))
(fn2-with-column-projections (fn2-env-sk)
(defthm fn2-env-commit-start-sk
  (implies (fn2-env-sk fn2-core c0)
           (fn2-env-sk (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)) c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-sk) clause world)))))
(fn2-with-column-projections (fn2-env-sk)
(defthm fn2-env-admit-sk
  (implies (fn2-env-sk fn2-core c0)
           (fn2-env-sk (fn2-env-admit members mode fn2-core) c0))
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-sk
                                                 )
                                             (theory 'fn2-arm-frame-base)))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-sk) clause world)))))
(defthm fn2-env-commit-slots-p-step-but-turn
  ; every step but :turn keeps FN2-ENV-COMMIT-SLOTS-P
  (implies (not (equal (fn2-env-tag action) :turn))
           (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                  (fn2-env-commit-slots-p p fn2-core)))
  :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-commit-slots-p-host-step member-eq (:e member-eq) fn2-env-sk-refl) (theory 'minimal-theory)))
           :cases ((equal (fn2-env-tag action) :admit))
           :use ((:instance fn2-env-step-admit-unfolds)
                 (:instance fn2-env-admit-sk (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)) (c0 fn2-core))
                 (:instance fn2-env-commit-slots-p-of-sk (profile p) (a fn2-core)
                            (b (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core)))))))
(defthm fn2-env-arm-decls-miss-rows
  (and (not (member-equal 9 (fn2-commit-arm-children p))) (not (member-equal 33 (fn2-commit-arm-columns p))))
  :hints (("Goal" :in-theory '(fn2-commit-arm-children fn2-commit-arm-columns assoc-equal (:e assoc-equal) car-cons cdr-cons
                               (:e member-equal))
           :cases ((member-equal p (strip-cars *fn2-commit-arm-decls*))))))
(make-event
 (let ((ctl (fn2-arm-frame-ctl (w state))))
   (value
    `(defthm fn2-env-commit-run-sk
       (fn2-env-sk (mv-nth 4 (fn2-commit-run id budget fn2-core)) fn2-core)
       :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir fn2-machines-directory-keeps) (union-theories '(fn2-env-sk fn2-env-arm-decls-miss-rows member-equal car-cons cdr-cons
                                                    fn2-ctf-subsetp-refl fn2-env-subsetp-cons (:e natp) (:type-prescription fn2-machine-slot-natp))
                                                  (theory 'minimal-theory)))
                :do-not-induct t
                :use ((:instance fn2-commit-run-arm-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id fn2-core))
                                 (fn2-arm-cs (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)))
                                 (fn2-arm-ch (cons ,ctl (fn2-commit-arm-children (fn2-commit-row-phase id fn2-core))))
                                 (fn2-arm-c0 fn2-core))
                      (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id fn2-core))
                                 (columns (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)))
                                 (children (cons ,ctl (fn2-commit-arm-children (fn2-commit-row-phase id fn2-core))))
                                 (a fn2-core))
                      (:instance fn2-arm-row-frame-cols (table 9) (row (fn2-machine-slot id fn2-core))
                                 (columns (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)))
                                 (children (cons ,ctl (fn2-commit-arm-children (fn2-commit-row-phase id fn2-core))))
                                 (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                      (:instance fn2-arm-cols-nth (k 0) (j 33) (row (fn2-machine-slot id fn2-core))
                                 (columns (fn2-commit-arm-columns (fn2-commit-row-phase id fn2-core)))
                                 (a (nth 9 fn2-core)) (b (nth 9 (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
                      (:instance fn2-commit-run-ctf-dir (fn2-ctf-c0 fn2-core))
                      (:instance fn2-ctf-dir-refl (a fn2-core)))))))))
(defthm fn2-env-commit-slots-p-commit-run
  ; every commit visit keeps FN2-ENV-COMMIT-SLOTS-P
  (equal (fn2-env-commit-slots-p p (mv-nth 4 (fn2-commit-run id budget fn2-core))) (fn2-env-commit-slots-p p fn2-core))
  :hints (("Goal" :in-theory nil
           :use (fn2-env-commit-run-sk
                 (:instance fn2-env-commit-slots-p-of-sk (profile p) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
;; THE DIRECTORY IS CANONICAL. Every directory id of the commit kind is the
;; global id of its slot (FN2-ENV-COMMIT-DIR-CANONICAL-P), so a readable
;; commit row's id is the ghost id at its slot (FN2-ENV-COMMIT-ID-CANONICAL)
;; and J at the ghost ids is J at the id a harvested op names as its owner.
;; It reads the directory's kinds, slots and rows alone: FN2-CTF-DIR keeps
;; it (FN2-ENV-COMMIT-DIR-CANONICAL-P-OF-DIR), so every step but :turn keeps
;; it (the host steps write no directory; admission keeps SK) and so does
;; every commit visit (FN2-COMMIT-RUN-CTF-DIR).
(defun-sk fn2-env-commit-dir-canonical-p (profile c)
  (forall id (implies (and (fn2-machine-idp id c) (equal (fn2-machine-kind id c) *fn2-commit-kind*))
                      (equal (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id c) profile) id))))
(in-theory (disable fn2-env-commit-dir-canonical-p))
(defthm fn2-env-commit-id-canonical
  ; a readable commit row's id is the global id of its slot
  (implies (and (fn2-env-commit-dir-canonical-p profile c) (fn2-commit-idp id c))
           (equal (fn2-machine-global-id *fn2-commit-kind* (fn2-machine-slot id c) profile) id))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn2-env-commit-idp-cell (fn2-core c))
                 (:instance fn2-env-commit-dir-canonical-p-necc)))))
(defthm fn2-env-commit-dir-canonical-p-of-dir
  (implies (fn2-ctf-dir b a)
           (equal (fn2-env-commit-dir-canonical-p profile b) (fn2-env-commit-dir-canonical-p profile a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-commit-dir-canonical-p)
           :use ((:instance fn2-env-commit-dir-canonical-p-necc (c a)
                            (id (fn2-env-commit-dir-canonical-p-witness profile b)))
                 (:instance fn2-env-commit-dir-canonical-p-necc (c b)
                            (id (fn2-env-commit-dir-canonical-p-witness profile a)))
                 (:instance fn2-ctf-dir-readers (id (fn2-env-commit-dir-canonical-p-witness profile b)))
                 (:instance fn2-ctf-dir-readers (id (fn2-env-commit-dir-canonical-p-witness profile a)))))))
;; the host steps write no directory
(defthm fn2-env-ctf-dir-host-frame
  (implies (fn2-ctf-dir c c0)
           (and (fn2-ctf-dir (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 c) c0)
                (fn2-ctf-dir (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 c) c0)
                (fn2-ctf-dir (fn2-host-post-clock mono real flags c) c0)
                (fn2-ctf-dir (fn2-host-post-signal bits c) c0)
                (fn2-ctf-dir (mv-nth 1 (fn2-host-outbox-ack n c)) c0)
                (fn2-ctf-dir (mv-nth 1 (fn2-host-op-finish slot gen c)) c0)
                (fn2-ctf-dir (fn2-env-fill rslot rgen slot gen idx octets c) c0)
                (fn2-ctf-dir (fn2-env-begin-epoch epoch c) c0)))
  :hints (("Goal" :in-theory (e/d (fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                   fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                   fn2-env-fill fn2-env-begin-epoch)
                                  (fn2-ctf-dir)))))
(defthm fn2-env-ctf-dir-take-frame
  (implies (fn2-ctf-dir c c0) (fn2-ctf-dir (mv-nth 1 (fn2-env-take nil image c)) c0))
  :hints (("Goal" :in-theory (e/d (fn2-env-take)
                                  (fn2-ctf-dir fn2-env-octets fn2-dev-image-octets fn2-host-action fn2-host-op-span
                                   fn2-host-outbox-peek fn2-op-output-kindp fn2-action-completionp
                                   fn2-host-outbox-ack fn2-host-op-finish fn2-env-fill)))))
(defthm fn2-env-ctf-dir-host-step
  (implies (not (member-eq (fn2-env-tag action) '(:turn :admit)))
           (fn2-ctf-dir (mv-nth 1 (fn2-env-step action nil image rlog c)) c))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post)
                                  (fn2-ctf-dir fn2-env-take)))))
(defthm fn2-env-commit-dir-canonical-p-step-but-turn
  ; every step but :turn keeps the canonical directory
  (implies (not (equal (fn2-env-tag action) :turn))
           (equal (fn2-env-commit-dir-canonical-p p (mv-nth 1 (fn2-env-step action nil image rlog c)))
                  (fn2-env-commit-dir-canonical-p p c)))
  :hints (("Goal" :in-theory (union-theories '(member-eq (:e member-eq) fn2-env-sk-refl) (theory 'minimal-theory))
           :cases ((equal (fn2-env-tag action) :admit))
           :use ((:instance fn2-env-step-admit-unfolds (fn2-core c))
                 (:instance fn2-env-ctf-dir-host-step)
                 (:instance fn2-env-admit-sk (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action))
                            (fn2-core c) (c0 c))
                 (:instance fn2-env-sk-projections (a c) (b (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) c)))
                 (:instance fn2-env-commit-dir-canonical-p-of-dir (profile p) (a c)
                            (b (mv-nth 1 (fn2-env-step action nil image rlog c))))))))
(defthm fn2-env-commit-dir-canonical-p-commit-run
  ; every commit visit keeps the canonical directory
  (equal (fn2-env-commit-dir-canonical-p p (mv-nth 4 (fn2-commit-run id budget c))) (fn2-env-commit-dir-canonical-p p c))
  :hints (("Goal" :in-theory '(fn2-ctf-dir-refl)
           :use ((:instance fn2-commit-run-ctf-dir (fn2-core c) (fn2-ctf-c0 c))
                 (:instance fn2-env-commit-dir-canonical-p-of-dir (profile p) (a c)
                            (b (mv-nth 4 (fn2-commit-run id budget c))))))))
;; THE ENTRY. fn2-core-init builds the directory canonical: row I holds the
;; kind and slot fn2-machine-local-id gives I (FN2-ENV-INIT-ROWS-DIR), and a
;; commit-kind row's local slot is the slot whose global id is I
;; (FN2-ENV-LOCAL-ID-COMMIT-INVERSE); every later init step keeps the
;; directory (FN2-ENV-INIT-EXECUTOR-CTF-DIR), so fn2-init-executor's core is
;; canonical (FN2-ENV-COMMIT-DIR-CANONICAL-P-INIT).
(defthm fn2-env-local-id-commit-inverse
  (implies (equal (mv-nth 0 (fn2-machine-local-id id profile)) *fn2-commit-kind*)
           (equal (fn2-machine-global-id *fn2-commit-kind* (mv-nth 1 (fn2-machine-local-id id profile)) profile) id))
  :hints (("Goal" :in-theory (enable fn2-machine-local-id fn2-machine-global-id))))
(defthm fn2-env-local-id-commit-slot
  (implies (and (natp id) (equal (mv-nth 0 (fn2-machine-local-id id profile)) *fn2-commit-kind*))
           (and (natp (mv-nth 1 (fn2-machine-local-id id profile)))
                (<= (mv-nth 1 (fn2-machine-local-id id profile)) id)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-local-id))))
(defun fn2-env-local-kind-fit (i profile)
  (declare (xargs :verify-guards nil))
  (mv-let (k s) (fn2-machine-local-id i profile) (declare (ignore s)) (if (unsigned-byte-p 8 k) k 255)))
(defun fn2-env-local-slot-fit (i profile)
  (declare (xargs :verify-guards nil))
  (mv-let (k s) (fn2-machine-local-id i profile) (declare (ignore k)) (if (unsigned-byte-p 32 s) s 0)))
(make-event
 (value (cons 'progn (fn2-ctf-dir-forms
                      (fn2-ctf-postorder-new '(fn2-init-engine fn2-listener-set-mode-all fn2-listener-set-target-all
                                               fn2-listener-set-principals fn2-exec-genesis-row) (w state))
                      'fn2-commit))))
(defthm fn2-exec-genesis-ctf-dir
  (implies (fn2-ctf-dir fn2-core fn2-ctf-c0)
           (fn2-ctf-dir (fn2-exec-genesis left id fn2-core) fn2-ctf-c0))
  :hints (("Goal" :induct (fn2-exec-genesis left id fn2-core)
           :in-theory (union-theories '(fn2-exec-genesis fn2-exec-genesis-row-ctf-dir) (theory 'minimal-theory)))))
(make-event
 (value (cons 'progn (fn2-ctf-dir-forms
                      (fn2-ctf-postorder-new '(fn2-scribe-start fn2-machine-take-wake fn2-exec-wake) (w state))
                      'fn2-commit))))
(defthm fn2-env-init-rows-unfold
  (equal (fn2-machines-init-rows left profile m)
         (if (or (zp left) (> left (fn2-machines-rows m))) m
           (fn2-machines-init-rows (- left 1) profile
            (fn2-machines-set-wait-reason (- left 1) *fn2-wait-none*
             (fn2-machines-set-ready-next (- left 1) *fn2-none*
              (fn2-machines-set-ready-prev (- left 1) *fn2-none*
               (fn2-machines-set-slot (- left 1) (fn2-env-local-slot-fit (- left 1) profile)
                (fn2-machines-set-kind (- left 1) (fn2-env-local-kind-fit (- left 1) profile) m))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-machines-init-rows fn2-env-local-slot-fit fn2-env-local-kind-fit))))
(defun-nx fn2-env-init-rows-ind (left profile m)
  ; fn2-machines-init-rows's recursion, with the fitted directory values
  (declare (xargs :measure (nfix left)
                  :hints (("Goal" :in-theory (disable fn2-machines-set-wait-reason fn2-machines-set-ready-next
                                                      fn2-machines-set-ready-prev fn2-machines-set-slot fn2-machines-set-kind)))))
  (if (or (zp left) (> left (fn2-machines-rows m))) m
    (fn2-env-init-rows-ind (- left 1) profile
     (fn2-machines-set-wait-reason (- left 1) *fn2-wait-none*
      (fn2-machines-set-ready-next (- left 1) *fn2-none*
       (fn2-machines-set-ready-prev (- left 1) *fn2-none*
        (fn2-machines-set-slot (- left 1) (fn2-env-local-slot-fit (- left 1) profile)
         (fn2-machines-set-kind (- left 1) (fn2-env-local-kind-fit (- left 1) profile) m))))))))
(defthm fn2-env-init-rows-frame
  (implies (and (natp j) (<= (nfix left) j))
           (and (equal (fn2-machines-kind j (fn2-machines-init-rows left profile m)) (fn2-machines-kind j m))
                (equal (fn2-machines-slot j (fn2-machines-init-rows left profile m)) (fn2-machines-slot j m))))
  :hints (("Goal" :induct (fn2-env-init-rows-ind left profile m)
           :in-theory (union-theories '((:induction fn2-env-init-rows-ind) fn2-machines-init-rows-rows fn2-env-machines-setters-dir nfix natp (:e zp) zp (:e nfix)) (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-init-rows-unfold)))
          ("Subgoal *1/1" :use ((:instance fn2-env-init-rows-unfold)))))
(defthm fn2-env-init-rows-dir
  (implies (and (natp i) (< i (nfix left)) (<= (nfix left) (fn2-machines-rows m)))
           (and (equal (fn2-machines-kind i (fn2-machines-init-rows left profile m)) (fn2-env-local-kind-fit i profile))
                (equal (fn2-machines-slot i (fn2-machines-init-rows left profile m)) (fn2-env-local-slot-fit i profile))))
  :hints (("Goal" :induct (fn2-env-init-rows-ind left profile m)
           :in-theory (union-theories '((:induction fn2-env-init-rows-ind) fn2-machines-init-rows-rows fn2-env-machines-setters-dir fn2-env-init-rows-frame nfix natp (:e zp) zp (:e nfix))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-init-rows-unfold)))
          ("Subgoal *1/1" :use ((:instance fn2-env-init-rows-unfold)))))
(defthm fn2-env-machines-init-rows
  (implies (< (fn2-machine-index-count profile) 4294967296)
           (equal (fn2-machines-rows (fn2-machines-init profile m)) (fn2-machine-index-count profile)))
  :hints (("Goal" :in-theory (e/d (fn2-machines-init fn2-machines-columns-init fn2-machines-rows)
                                  (fn2-machines-init-rows fn2-machines-init-bases fn2-machines-init-partitions
                                   fn2-machine-index-count)))))
(defthm fn2-env-machines-init-dir
  (implies (and (natp i) (< i (fn2-machine-index-count profile)) (< (fn2-machine-index-count profile) 4294967296))
           (and (equal (fn2-machines-kind i (fn2-machines-init profile m)) (fn2-env-local-kind-fit i profile))
                (equal (fn2-machines-slot i (fn2-machines-init profile m)) (fn2-env-local-slot-fit i profile))))
  :hints (("Goal" :in-theory (e/d (fn2-machines-init fn2-machines-columns-init fn2-machines-rows)
                                  (fn2-machines-init-rows fn2-machines-init-bases fn2-machines-init-partitions
                                   fn2-machine-index-count fn2-env-local-kind-fit fn2-env-local-slot-fit)))))
(make-event
 `(defthm fn2-env-core-init-machines
    (equal (fn2-core-machines (fn2-core-init profile c)) (fn2-machines-init profile (fn2-core-machines c)))
    :hints (("Goal" :in-theory (e/d (fn2-core-init ,@(fn2-core-init-child-names *fn2-core-children*))
                                    (fn2-machines-init))))))
(defthm fn2-env-core-profilep-index-count
  (implies (fn2-core-profilep profile) (< (fn2-machine-index-count profile) 4294967296))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-core-profilep unsigned-byte-p integer-range-p (:e expt)))))
(defthm fn2-env-commit-dir-canonical-p-core-init
  ; the core's directory is built canonical: row I holds fn2-machine-local-id of I
  (implies (fn2-core-profilep profile)
           (fn2-env-commit-dir-canonical-p profile (fn2-core-init profile c)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn2-env-commit-dir-canonical-p fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                fn2-machine-slot fn2-machine-slot-read-code fn2-env-core-init-machines fn2-env-machines-init-dir fn2-env-machines-init-rows
                                fn2-env-local-kind-fit fn2-env-local-slot-fit fn2-env-local-id-commit-inverse
                                unsigned-byte-p integer-range-p natp (:e expt) (:e unsigned-byte-p) (:e equal) (:e <))
                              (theory 'minimal-theory))
           :use ((:instance fn2-env-core-profilep-index-count)
                 (:instance fn2-env-local-id-commit-slot
                            (id (fn2-env-commit-dir-canonical-p-witness profile (fn2-core-init profile c))))))))
(defthm fn2-env-init-executor-ctf-dir
  ; after the core's init no init step writes the directory
  (fn2-ctf-dir (fn2-init-executor profile mode scribe-p c) (fn2-core-init profile c))
  :hints (("Goal" :in-theory (union-theories
                              '(fn2-init-executor fn2-ctf-dir-refl fn2-init-engine-ctf-dir fn2-listener-set-mode-all-ctf-dir
                                fn2-listener-set-target-all-ctf-dir fn2-listener-set-principals-ctf-dir fn2-exec-genesis-ctf-dir
                                fn2-scribe-start-ctf-dir fn2-machine-take-wake-ctf-dir fn2-exec-wake-ctf-dir
                                mv-nth car-cons cdr-cons (:e zp) zp)
                              (theory 'minimal-theory)))))
(defthm fn2-env-commit-dir-canonical-p-init
  ; the entry: the executor starts with a canonical directory
  (implies (fn2-core-profilep profile)
           (fn2-env-commit-dir-canonical-p profile (fn2-init-executor profile mode scribe-p c)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn2-env-commit-dir-canonical-p-core-init)
                 (:instance fn2-env-init-executor-ctf-dir)
                 (:instance fn2-env-commit-dir-canonical-p-of-dir (a (fn2-core-init profile c))
                            (b (fn2-init-executor profile mode scribe-p c)))))))
;; ---------------------------------------------------------------------------
;; :DEPENDENCIES AND :LOG-WRITE. J3, the counted-completion link: a row in a
;; write phase has its three role extents shared, and each completion it
;; counted (cb-done) is a write of one of the phase's roles answered done in
;; full in the log at the role's offset (role 2 carrying the seal of its
;; batch), fenced as J2 asks once the fence flag is set (or FUA in barrier
;; mode 1). The phase's flag rise (cb-deps-ok, cb-log-ok) happens only when
;; every issued write is counted, so J3 at the visited row gives J2 after.
;; FN2-ENV-FK: the commit table's two flag columns.
(fn2-defview fn2-env-fk :carrier fn2-core
  :select ((fn2-commit :columns (cb-deps-ok cb-log-ok) :rows t)))
(defthm fn2-env-fk-view-equivalence
  (equal (fn2-env-fk b a) (and (equal (nth 24 (nth 9 b)) (nth 24 (nth 9 a))) (equal (nth 25 (nth 9 b)) (nth 25 (nth 9 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-fk fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-fk))
(defthm fn2-env-fk-refl (fn2-env-fk a a))
(defthm fn2-env-fk-of-nth
  (implies (and (equal (nth 9 b) (nth 9 x)) (fn2-env-fk x a)) (fn2-env-fk b a))
  :rule-classes nil)
(defthm fn2-env-fk-of-row-frame
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch))
                (not (intersectp-equal cs '(24 25))) (fn2-env-fk x a))
           (fn2-env-fk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-fk fn2-arm-row-frame-cols (:e member-equal) (:e natp) (:e binary-+))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-cols-nth (k 0) (j 24) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-arm-cols-nth (k 0) (j 25) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-env-not-intersectp-member (j 24) (x cs) (y '(24 25)))
                 (:instance fn2-env-not-intersectp-member (j 25) (x cs) (y '(24 25)))))))
(in-theory (disable fn2-env-fk))

(defthm fn2-env-flags-of-fk
  (implies (and (fn2-env-fk b a) (fn2-ctf-dir b a) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))
                (equal (fn2-machine-kind id a) *fn2-commit-kind*))
           (and (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
                (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-fk fn2-machine-cb-deps-ok fn2-machine-cb-log-ok fn2-commit-table fn2-commit-rows
                                   fn2-commit-cb-deps-ok fn2-commit-cb-deps-ok$ai fn2-commit-cb-log-ok fn2-commit-cb-log-ok$ai)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)))))





(defthm fn2-env-flags-congruence
  (implies (and (equal (nth 3 b) (nth 3 a)) (equal (nth 9 b) (nth 9 a)))
           (and (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
                (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-cb-deps-ok fn2-machine-cb-log-ok fn2-machine-cb-deps-ok-read-code
                                     fn2-machine-cb-log-ok-read-code fn2-machine-idp fn2-core-machines fn2-commit-table)
           :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
(make-event (value (fn2-env-write-keeps-ids-event 'fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok (w state))))
(defthm fn2-env-deps-advance-reads
  (implies (and (fn2-commit-idp id fn2-core) (natp p) (< p 13))
           (let ((b (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok id p 0 0 0 1 0 fn2-core)))
             (and (equal (fn2-machine-cb-deps-ok id b) 1) (equal (fn2-machine-cb-log-ok id b) 0))))
  :hints (("Goal" :in-theory (union-theories '(unsigned-byte-p integer-range-p (:e expt) fn2-commit-idp) (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok-reads
                            (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0)
                            (fn2-arms-w-cb-deps-ok 1) (fn2-arms-w-cb-log-ok 0))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok-keeps-ids (x id)
                            (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0)
                            (fn2-arms-w-cb-deps-ok 1) (fn2-arms-w-cb-log-ok 0))
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-env-commit-row-flag-reads
                            (fn2-core (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok id p 0 0 0 1 0 fn2-core)))))))
(fn2-with-column-projections (fn2-env-fk)
(defthm fn2-env-dependencies-arm-flags
  ; the :dependencies visit leaves both flags, or raises cb-deps-ok (and
  ; clears cb-log-ok) only once its one write is issued and counted
  (let ((b (mv-nth 4 (fn2-commit-run-dependencies id budget fn2-core))))
    (or (fn2-env-fk b fn2-core)
        (and (equal (fn2-machine-cb-deps-ok id b) 1) (equal (fn2-machine-cb-log-ok id b) 0)
             (fn2-commit-idp id fn2-core)
             (equal (fn2-commit-row-cb-issued id fn2-core) 1)
             (not (< (fn2-commit-row-cb-done id fn2-core) 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run-dependencies fn2-env-fk-refl fn2-env-deps-advance-reads
                                               fn2-commit-idp





                                               )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-fk) clause world)))))
(fn2-with-column-projections (fn2-env-commit-table-view fn2-env-directory-view)
(defthm fn2-env-contract-check-flags
  (let ((b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core))))
    (and (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id fn2-core))
         (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id fn2-core))))
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-commit-table-view fn2-env-directory-view) (theory 'fn2-column-projection-base)) nil)
           :use (
                 (:instance fn2-env-flags-congruence
                            (b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
                            (a fn2-core))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-commit-table-view fn2-env-directory-view) clause world)))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :dependencies 3))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :dependencies nil (w state)))))
(fn2-with-column-projections (fn2-env-ek fn2-env-fk fn2-env-rk)
(defthm fn2-env-commit-run-dependencies-facts
  ; the visit keeps J2's extents and the root, and leaves both flags or
  ; raises cb-deps-ok once its write is counted
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (and (fn2-env-ek b fn2-core) (fn2-env-rk b fn2-core)
                  (or (fn2-env-fk b fn2-core)
                      (and (equal (fn2-machine-cb-deps-ok id b) 1) (equal (fn2-machine-cb-log-ok id b) 0)
                           (fn2-commit-idp id fn2-core)
                           (equal (fn2-commit-row-cb-issued id fn2-core) 1)
                           (not (< (fn2-commit-row-cb-done id fn2-core) 1)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run fn2-env-ek-refl fn2-env-rk-refl fn2-env-fk-refl


                                                fn2-env-contract-check-flags)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-dependencies-arm-flags) (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek fn2-env-fk fn2-env-rk) clause world)))))
(defthm fn2-env-cb-done-natp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (natp (fn2-machine-cb-done id fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-cb-done))))
(defthm fn2-env-j1-row-flag-transfer
  ; J1 reads no flag: a step that keeps the batch, the reply count and their
  ; readability, does not lower the installed root, and moves the phase only
  ; among phases whose J1 obligations it meets keeps J1
  (implies (and (fn2-env-j1-row id log a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
                (equal (fn2-machine-batch-no-read-code id b) (fn2-machine-batch-no-read-code id a))
                (equal (fn2-machine-cb-acks id b) (fn2-machine-cb-acks id a))
                (equal (fn2-machine-cb-acks-read-code id b) (fn2-machine-cb-acks-read-code id a))
                (<= (fn2-env-installed a) (fn2-env-installed b))
                (fn2-commit-idp id a)
                (not (equal (fn2-machine-phase id a) *fn2-commit-state-free*))
                (not (member-equal (fn2-machine-phase id b)
                                   (list *fn2-commit-state-install* *fn2-commit-state-publish* *fn2-commit-state-notify*))))
           (fn2-env-j1-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j1-row posp natp nfix (:type-prescription fn2-env-installed-natp) member-equal (:e member-equal)))))
(defthm fn2-env-j-row-dependencies-visited
  (implies (and (fn2-env-j-row id log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*))
           (fn2-env-j-row id log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row fn2-env-j2-row fn2-env-j3-row fn2-env-role-written
                                               fn2-env-role-offset-of-extent fn2-env-j-same-evidence nfix
                                               fn2-commit-idp fn2-commit-arm-row-phase member-equal (:e member-equal)
                                               natp (:type-prescription fn2-machine-slot-natp) (:e natp))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-dependencies-arm-frame)
                 (:instance fn2-env-cb-done-natp)
                 (:instance fn2-env-commit-run-dependencies-facts)
                 (:instance fn2-env-commit-run-dependencies-next)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-row-count-reads)
                 (:instance fn2-env-commit-idp-kind)
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-arm-row-frame-cols (table 9) (row (fn2-machine-slot id fn2-core))
                            (columns '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (children '(30 20 21 1 0 31 5))
                            (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-arm-cols-nth (k 0) (j 33) (columns '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30))
                            (row (fn2-machine-slot id fn2-core))
                            (a (nth 9 fn2-core)) (b (nth 9 (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
                 (:instance fn2-env-flags-of-fk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-batch-no-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-mode-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-fence-ok-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-acks-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 0) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 1) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 2) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j1-row-flag-transfer (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j2-row-congruence (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(defthm fn2-env-j-row-dependencies-arm
  ; the :dependencies visit keeps J at every id, given J3 at the visited row
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row-not-idp fn2-commit-idp natp (:e natp) (:e member-equal)
                                               (:type-prescription fn2-machine-slot-natp))
                                             (theory 'minimal-theory))
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :do-not-induct t
           :use ((:instance fn2-env-dependencies-arm-frame)
                 (:instance fn2-env-commit-run-dependencies-facts)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-commit-run-preserves-type)
                 (:instance fn2-commit-run-preserves-wfp)
                 (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (id i) (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (id id) (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (id i) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (id id) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-row-same-slot (i id) (j i))
                 (:instance fn2-env-j-row-dependencies-visited)
                 (:instance fn2-env-j-row-same-slot (i i) (j id) (fn2-core (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-row-of-row-frame-other-slot (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 24 25 16 17 18 19 21 6 20 15 14 30)) (ch '(30 20 21 1 0 31 5))  (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(make-event (value `(defthm fn2-env-j-rows-dependencies-arm
  (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*))
           (and (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j-frontier log (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
  :hints ,(fn2-env-pw-arm-hints 'fn2-env-j-row 'fn2-env-j-rows 'fn2-env-j-row-dependencies-arm
               '((fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                 (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*)) nil
               '((:instance fn2-env-commit-run-dependencies-facts)
                 (:instance fn2-env-j-frontier-of-rk
                   (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))))))))
(make-event (value (fn2-env-write-keeps-ids-event 'fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok (w state))))
(defthm fn2-env-log-advance-reads
  (implies (and (fn2-commit-idp id fn2-core) (natp p) (< p 13))
           (let ((b (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)))
             (and (equal (fn2-machine-cb-log-ok id b) 1)
                  (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id fn2-core)))))
  :hints (("Goal" :in-theory (union-theories '(unsigned-byte-p integer-range-p (:e expt) fn2-commit-idp fn2-ctf-dir-refl
                                               (:e member-equal) (:type-prescription fn2-machine-slot-natp))
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-reads (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-keeps-ids (x id) (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-env-commit-row-flag-reads (fn2-core (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-arm-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id fn2-core))
                            (fn2-arm-cs '(0 16 17 18 25)) (fn2-arm-ch '(5)) (fn2-arm-c0 fn2-core) (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id fn2-core)) (columns '(0 16 17 18 25))
                            (children '(5)) (a fn2-core))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-arm-kids (fn2-arm-free '(9 5)) (fn2-arm-c0 fn2-core) (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-arm-kids-nth (i 0) (k 3) (free '(9 5)) (a fn2-core) (b (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)))
                 (:instance fn2-ctf-dir-of-nth (b (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)) (x fn2-core) (a fn2-core))
                 (:instance fn2-machine-cb-deps-ok-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 16 17 18 25))
                            (ch '(5)) (a fn2-core) (b (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)))))))
(fn2-with-column-projections (fn2-env-fk)
(defthm fn2-env-log-write-arm-flags
  ; the :log-write visit leaves both flags, or raises cb-log-ok only once its
  ; two writes are issued and counted
  (let ((b (mv-nth 4 (fn2-commit-run-log-write id budget fn2-core))))
    (or (fn2-env-fk b fn2-core)
        (and (equal (fn2-machine-cb-log-ok id b) 1)
             (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id fn2-core))
             (fn2-commit-idp id fn2-core)
             (equal (fn2-commit-row-cb-issued id fn2-core) 2)
             (not (< (fn2-commit-row-cb-done id fn2-core) 2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run-log-write fn2-env-fk-refl fn2-env-log-advance-reads
                                               fn2-commit-idp




                                               )
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-fk) clause world)))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :log-write 4))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :log-write nil (w state)))))
(fn2-with-column-projections (fn2-env-ek fn2-env-fk fn2-env-rk)
(defthm fn2-env-commit-run-log-write-facts
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (and (fn2-env-ek b fn2-core) (fn2-env-rk b fn2-core)
                  (or (fn2-env-fk b fn2-core)
                      (and (equal (fn2-machine-cb-log-ok id b) 1)
                           (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id fn2-core))
                           (fn2-commit-idp id fn2-core)
                           (equal (fn2-commit-row-cb-issued id fn2-core) 2)
                           (not (< (fn2-commit-row-cb-done id fn2-core) 2)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run fn2-env-ek-refl fn2-env-rk-refl fn2-env-fk-refl


                                                fn2-env-contract-check-flags)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-log-write-arm-flags) (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek fn2-env-fk fn2-env-rk) clause world)))))
(defthm fn2-env-j-row-log-write-visited
  (implies (and (fn2-env-j-row id log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*))
           (fn2-env-j-row id log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row fn2-env-j2-row fn2-env-j3-row fn2-env-role-written
                                               fn2-env-role-offset-of-extent fn2-env-j-same-evidence nfix
                                               fn2-commit-idp fn2-commit-arm-row-phase member-equal (:e member-equal)
                                               natp (:type-prescription fn2-machine-slot-natp) (:e natp))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-log-write-arm-frame)
                 (:instance fn2-env-cb-done-natp)
                 (:instance fn2-env-commit-run-log-write-facts)
                 (:instance fn2-env-commit-run-log-write-next)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-row-count-reads)
                 (:instance fn2-env-commit-idp-kind)
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-arm-row-frame-cols (table 9) (row (fn2-machine-slot id fn2-core))
                            (columns '(0 5 29 25 16 17 18 15 19 21 6)) (children '(30 20 21 1 0 5))
                            (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-arm-cols-nth (k 0) (j 33) (columns '(0 5 29 25 16 17 18 15 19 21 6))
                            (row (fn2-machine-slot id fn2-core))
                            (a (nth 9 fn2-core)) (b (nth 9 (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
                 (:instance fn2-env-flags-of-fk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-batch-no-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-mode-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-fence-ok-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-machine-cb-acks-of-row-frame (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 0) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 1) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-role-extent-of-ek (role 2) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j1-row-flag-transfer (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j2-row-congruence (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(defthm fn2-env-j-row-log-write-arm
  ; the :log-write visit keeps J at every id, given J3 at the visited row
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*))
           (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-row-not-idp fn2-commit-idp natp (:e natp) (:e member-equal)
                                               (:type-prescription fn2-machine-slot-natp))
                                             (theory 'minimal-theory))
           :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           :do-not-induct t
           :use ((:instance fn2-env-log-write-arm-frame)
                 (:instance fn2-env-commit-run-log-write-facts)
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-commit-run-preserves-type)
                 (:instance fn2-commit-run-preserves-wfp)
                 (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (id i) (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-read-codes-of-row-frame (id id) (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5)) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (id i) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-ctf-dir-readers (id id) (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-row-same-slot (i id) (j i))
                 (:instance fn2-env-j-row-log-write-visited)
                 (:instance fn2-env-j-row-same-slot (i i) (j id) (fn2-core (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-j-row-of-row-frame-other-slot (row (fn2-machine-slot id fn2-core)) (cs '(0 5 29 25 16 17 18 15 19 21 6)) (ch '(30 20 21 1 0 5))  (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
(make-event (value `(defthm fn2-env-j-rows-log-write-arm
  (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*))
           (and (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j-frontier log (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
  :hints ,(fn2-env-pw-arm-hints 'fn2-env-j-row 'fn2-env-j-rows 'fn2-env-j-row-log-write-arm
               '((fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                 (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*)) nil
               '((:instance fn2-env-commit-run-log-write-facts)
                 (:instance fn2-env-j-frontier-of-rk
                   (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core)))))))))
;; ---------------------------------------------------------------------------
;; THE COMMIT ARMS' J3 LIFTS. Every visit keeps J3 at every id: off the
;; visited row by its frame (FN2-ENV-J3-OF-ROW-FRAME-OFF-ROW), at it by the
;; phase move (FN2-ENV-J3-MOVE-OK): a stay, :collect -> :seal ->
;; :dependencies, :fence -> :log-write only in barrier mode 1
;; (FN2-ENV-COMMIT-RUN-FENCE-MODE), any move out of :collect .. :fence, and
;; the write arms' advance with the count reset (FN2-ENV-COMMIT-RUN-
;; <PHASE>-DONE: their visit keeps the count, FN2-ENV-DK, with a stay or a
;; failure, or leaves it 0). No arm writes the batch, the barrier mode or
;; the fence flag.
(defthm fn2-env-j3-of-row-frame-off-row
  ; a commit-table frame at ROW keeps J3 at an id that is not a readable row there
  (implies (and (fn2-arm-row-frame 9 row cs ch a b) (natp row) (not (member-equal 9 ch)) (not (member-equal 33 cs))
                (fn2-ctf-dir b a) (fn2-env-ek b a)
                (or (not (fn2-commit-idp i a)) (not (equal (fn2-machine-slot i a) row))))
           (and (equal (fn2-env-j3-row i log b) (fn2-env-j3-row i log a))
                (equal (fn2-env-j3e-row i b) (fn2-env-j3e-row i a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence) (theory 'minimal-theory))
           :cases ((fn2-commit-idp i a))
           :do-not-induct t)
          ("Subgoal 2" :in-theory (union-theories '(fn2-env-j3-off-commit) (theory 'minimal-theory))
           :use ((:instance fn2-env-read-codes-of-row-frame (id i))))
          ("Subgoal 1"
           :use ((:instance fn2-env-read-codes-of-row-frame (id i))
                 (:instance fn2-env-commit-idp-kind (id i) (fn2-core a))
                 (:instance fn2-machine-phase-of-row-frame (id i))
                 (:instance fn2-machine-batch-no-of-row-frame (id i))
                 (:instance fn2-machine-cb-mode-of-row-frame (id i))
                 (:instance fn2-machine-cb-fence-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-deps-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-log-ok-of-row-frame (id i))
                 (:instance fn2-machine-cb-done-of-row-frame (id i))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 0))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 1))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 2))
                 (:instance fn2-env-j3-congruence (id i))))))
(defthm fn2-env-j3-move
  (implies (and (fn2-env-j3-row id log a) (fn2-env-j3e-row id a) (fn2-commit-idp id a)
                (fn2-env-j-same-evidence id a b)
                (fn2-env-j3-move-ok (fn2-machine-phase id a) (fn2-machine-phase id b) (fn2-machine-cb-mode id a)
                                    (fn2-machine-cb-done id a) (fn2-machine-cb-done id b)))
           (and (fn2-env-j3-row id log b) (fn2-env-j3e-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-j-same-evidence fn2-env-j3-move-ok
                               fn2-env-role-offset-of-extent member-equal (:e member-equal) nfix (:e nfix) (:e <) (:e equal)))))
(defun fn2-env-j3-arm-events (state-name code extra kids)
  ; FN2-ENV-J3-ROW-<STATE>-ARM and -J3-ROWS-: the visit at STATE (an arm
  ; writing no count, batch, mode or flag) keeps J3: off its row by the
  ; frame (FN2-ENV-J3-OF-ROW-FRAME-OFF-ROW), at its row by the phase move
  ; (FN2-ENV-J3-MOVE) over its declared successors. KIDS: :use instances
  ; giving (fn2-env-ek b fn2-core) and further facts.
  (declare (xargs :mode :program))
  (let* ((e (assoc code *fn2-commit-arm-decls*)) (ch (cadr e)) (cs (caddr e))
         (const (fn2-env-arm-state-const state-name))
         (b '(mv-nth 4 (fn2-commit-run id budget fn2-core)))
         (row '(fn2-machine-slot id fn2-core))
         (frame (fn2-columns-sym (fn2-columns-col-name 'fn2-env state-name) "-ARM-FRAME"))
         (next (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-NEXT"))
         (one (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j3-row state-name) "-ARM"))
         (rows (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j3-rows state-name) "-ARM")))
    (if (intersectp cs '(9 13 17 23 24 25 33))
        (er hard 'fn2-env-j3-arm-events "~x0 writes a column J3 reads: ~x1." state-name e)
      `((defthm ,one
          (implies (and (fn2-env-j3-row i log fn2-core) (fn2-env-j3e-row i fn2-core) ,@extra
                        (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (equal (fn2-commit-row-phase id fn2-core) ,const))
                   (and (fn2-env-j3-row i log ,b) (fn2-env-j3e-row i ,b)))
          :rule-classes nil
          :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                                       fn2-commit-idp fn2-commit-arm-row-phase fn2-env-j-same-evidence fn2-env-j3-move-ok
                                       (:e equal) (:e fn2-commit-arm-children) (:e fn2-commit-arm-columns))
                   :do-not-induct t
                   :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) ,row)))
                   :use ((:instance ,frame) (:instance ,next) (:instance fn2-env-row-phase-snapshot)
                         ,@kids
                         (:instance fn2-env-j3-of-row-frame-off-row (a fn2-core) (b ,b) (row ,row) (cs ',cs) (ch ',ch))
                         (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core fn2-core))
                         (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core ,b))
                         (:instance fn2-env-read-codes-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
                         (:instance fn2-env-read-codes-of-row-frame (id id) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
                         (:instance fn2-ctf-dir-readers (id i) (a fn2-core) (b ,b))
                         (:instance fn2-ctf-dir-readers (id id) (a fn2-core) (b ,b))
                         (:instance fn2-env-commit-idp-kind (id id))
                         ,@(fn2-env-row-frame-uses '(fn2-machine-batch-no-of-row-frame fn2-machine-cb-mode-of-row-frame
                                                     fn2-machine-cb-fence-ok-of-row-frame fn2-machine-cb-deps-ok-of-row-frame
                                                     fn2-machine-cb-log-ok-of-row-frame fn2-machine-cb-done-of-row-frame)
                                                   row cs ch b)
                         (:instance fn2-env-role-extent-of-ek (id id) (role 0) (a fn2-core) (b ,b))
                         (:instance fn2-env-role-extent-of-ek (id id) (role 1) (a fn2-core) (b ,b))
                         (:instance fn2-env-role-extent-of-ek (id id) (role 2) (a fn2-core) (b ,b))
                         (:instance fn2-env-j3-move (id id) (a fn2-core) (b ,b))))))
        (defthm ,rows
          (implies (and (fn2-env-j3-rows ids log fn2-core) ,@extra (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (equal (fn2-commit-row-phase id fn2-core) ,const))
                   (fn2-env-j3-rows ids log ,b))
          :hints ,(fn2-env-pw-arm-hints 'fn2-env-j3-point 'fn2-env-j3-rows one
                    `(,@extra (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (equal (fn2-commit-row-phase id fn2-core) ,const)) '(fn2-env-j3-point) nil))))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :collect 1 nil nil))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :seal 2 nil '((:instance fn2-env-commit-run-seal-ek))))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :free 0 '((fn2-commit-idp id fn2-core)) nil))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :draining 10 nil '((:instance fn2-env-commit-run-draining-ek))))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :uncertain 11 nil '((:instance fn2-env-commit-run-uncertain-ek))))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :dropping 12 nil nil))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :notify nil (w state)))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :durable nil (w state)))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :install nil (w state)))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :publish nil (w state)))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :notify 9 nil nil))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :install 7 nil nil))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :durable 6 nil
  '((:instance fn2-env-commit-run-durable-keeps-commit-io)
    (:instance fn2-env-ek-of-nth (b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (x fn2-core) (a fn2-core))
    (:instance fn2-env-ek-refl (a fn2-core)))))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :publish 8 nil
  '((:instance fn2-env-commit-run-publish-keeps-commit-io)
    (:instance fn2-env-ek-of-nth (b (mv-nth 4 (fn2-commit-run id budget fn2-core))) (x fn2-core) (a fn2-core))
    (:instance fn2-env-ek-refl (a fn2-core)))))))
(make-event
 `(defthm fn2-env-fence-arm-mode-phase
    ; the :fence arm reaches :log-write only in barrier mode 1
    (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                  (subsetp-equal '(11 6) fn2-arm-pset)
                  (or (member-equal 4 fn2-arm-pset) (not (equal (fn2-commit-row-cb-mode id fn2-core) 1))))
             (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run-fence id budget fn2-core))) fn2-arm-pset))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-fence ,@(fn2-env-arm-phase-runes :fence (w state)))
                                               (theory 'fn2-arm-frame-base))
             :do-not-induct t))))
(defthm fn2-env-commit-row-mode-read
  (implies (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
           (equal (fn2-commit-row-cb-mode id fn2-core) (fn2-machine-cb-mode id fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-row-cb-mode fn2-machine-cb-mode fn2-machine-cb-mode-read-code
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp)))))
(defthm fn2-env-commit-run-fence-mode
  (implies (and (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-fence*)
                (equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run id budget fn2-core))) *fn2-commit-state-log-write*))
           (equal (fn2-machine-cb-mode id fn2-core) 1))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-fence-arm-mode-phase (fn2-arm-pset '(5 11 6)))
                 (:instance fn2-env-row-phase-snapshot)
                 (:instance fn2-env-commit-row-mode-read)))))
(make-event (value (cons 'progn (fn2-env-j3-arm-events :fence 5 nil '((:instance fn2-env-commit-run-fence-mode))))))
(fn2-defview fn2-env-dk :carrier fn2-core
  :select ((fn2-commit :columns (cb-done) :rows t)))
(defthm fn2-env-dk-view-equivalence
  (equal (fn2-env-dk b a) (equal (nth 17 (nth 9 b)) (nth 17 (nth 9 a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-dk fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-dk))
(defthm fn2-env-dk-refl (fn2-env-dk a a))
(defthm fn2-env-dk-of-nth
  (implies (and (equal (nth 9 b) (nth 9 x)) (fn2-env-dk x a)) (fn2-env-dk b a))
  :rule-classes nil)
(defthm fn2-env-dk-of-row-frame
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch))
                (not (intersectp-equal cs '(17))) (fn2-env-dk x a))
           (fn2-env-dk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-dk (:e member-equal) (:e natp) (:e binary-+)) (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch) (a x))
                 (:instance fn2-arm-cols-nth (k 0) (j 17) (columns cs) (a (nth 9 x)) (b (nth 9 b)))
                 (:instance fn2-env-not-intersectp-member (j 17) (x cs) (y '(17)))))))
(in-theory (disable fn2-env-dk))

(defthm fn2-env-done-of-dk
  (implies (and (fn2-env-dk b a) (fn2-ctf-dir b a) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))
                (equal (fn2-machine-kind id a) *fn2-commit-kind*))
           (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-dk fn2-machine-cb-done fn2-commit-table fn2-commit-rows
                                   fn2-commit-cb-done fn2-commit-cb-done$ai)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)))))

(defthm fn2-env-deps-advance-done
  (implies (and (fn2-commit-idp id fn2-core) (natp p) (< p 13))
           (equal (fn2-machine-cb-done id (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok id p 0 0 0 1 0 fn2-core)) 0))
  :hints (("Goal" :in-theory (union-theories '(unsigned-byte-p integer-range-p (:e expt) fn2-commit-idp) (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok-reads
                            (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0)
                            (fn2-arms-w-cb-deps-ok 1) (fn2-arms-w-cb-log-ok 0))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok-keeps-ids (x id)
                            (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0)
                            (fn2-arms-w-cb-deps-ok 1) (fn2-arms-w-cb-log-ok 0))
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-env-commit-row-count-reads
                            (fn2-core (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-deps-ok+cb-log-ok id p 0 0 0 1 0 fn2-core)))))))
(defthm fn2-env-log-advance-done
  (implies (and (fn2-commit-idp id fn2-core) (natp p) (< p 13))
           (equal (fn2-machine-cb-done id (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)) 0))
  :hints (("Goal" :in-theory (union-theories '(unsigned-byte-p integer-range-p (:e expt) fn2-commit-idp) (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-reads (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok-keeps-ids (x id) (fn2-arms-w-phase p) (fn2-arms-w-cb-issued 0) (fn2-arms-w-cb-done 0) (fn2-arms-w-cb-bytes 0) (fn2-arms-w-cb-log-ok 1))
                 (:instance fn2-env-commit-idp-cell)
                 (:instance fn2-env-commit-row-count-reads (fn2-core (fn2-commit-write+phase+cb-issued+cb-done+cb-bytes+cb-log-ok id p 0 0 0 1 fn2-core)))))))
(make-event
 `(fn2-with-column-projections (fn2-env-dk)
(defthm fn2-env-deps-arm-done
    ; the :dependencies arm keeps the count and moves the phase as a stay or a failure, or resets the count
    (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal '(11 12) fn2-arm-pset))
             (let ((b (mv-nth 4 (fn2-commit-run-dependencies id budget fn2-core))))
               (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) fn2-arm-pset))
                   (equal (fn2-machine-cb-done id b) 0))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run-dependencies fn2-env-dk-refl fn2-env-deps-advance-done fn2-commit-idp

                                                 ,@(fn2-env-arm-phase-runes :dependencies (w state)))
                                               (theory 'fn2-arm-frame-base)))
             :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-dk) clause world))))))
(make-event
 `(fn2-with-column-projections (fn2-env-dk)
(defthm fn2-env-log-arm-done
    (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal '(11 12) fn2-arm-pset))
             (let ((b (mv-nth 4 (fn2-commit-run-log-write id budget fn2-core))))
               (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) fn2-arm-pset))
                   (equal (fn2-machine-cb-done id b) 0))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run-log-write fn2-env-dk-refl fn2-env-log-advance-done fn2-commit-idp

                                                 ,@(fn2-env-arm-phase-runes :log-write (w state)))
                                               (theory 'fn2-arm-frame-base)))
             :do-not-induct t)
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-dk) clause world))))))
(defthm fn2-env-done-congruence
  (implies (and (equal (nth 3 b) (nth 3 a)) (equal (nth 9 b) (nth 9 a)))
           (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-cb-done fn2-machine-cb-done-read-code fn2-machine-idp fn2-core-machines fn2-commit-table)
           :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
(fn2-with-column-projections (fn2-env-commit-table-view fn2-env-directory-view)
(defthm fn2-env-contract-check-done
  (equal (fn2-machine-cb-done id (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
         (fn2-machine-cb-done id fn2-core))
  :hints (("Goal" :in-theory (union-theories (union-theories '(fn2-env-commit-table-view fn2-env-directory-view) (theory 'fn2-column-projection-base)) nil)
           :use (
                 (:instance fn2-env-done-congruence
                            (b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
                            (a fn2-core))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-commit-table-view fn2-env-directory-view) clause world)))))
(fn2-with-column-projections (fn2-env-dk)
(defthm fn2-env-commit-run-dependencies-done
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) '(3 11 12)))
                 (equal (fn2-machine-cb-done id b) 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run fn2-env-dk-refl  fn2-env-contract-check-done
                                               fn2-commit~fn2-machine-contract-check-arm-phase fn2-arm-member-of-subsetp-free
                                               fn2-commit-arm-row-phase fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-deps-arm-done (fn2-arm-pset '(3 11 12))) (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-dk) clause world)))))
(fn2-with-column-projections (fn2-env-dk)
(defthm fn2-env-commit-run-log-write-done
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) '(4 11 12)))
                 (equal (fn2-machine-cb-done id b) 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-commit-run fn2-env-dk-refl  fn2-env-contract-check-done
                                               fn2-commit~fn2-machine-contract-check-arm-phase fn2-arm-member-of-subsetp-free
                                               fn2-commit-arm-row-phase fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base)))
           :do-not-induct t
           :use ((:instance fn2-env-log-arm-done (fn2-arm-pset '(4 11 12))) (:instance fn2-env-row-phase-snapshot)))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-dk) clause world)))))
(defthm fn2-env-j3-move-reads
  ; FN2-ENV-J3-MOVE over the reads J3 makes (not the durability flags)
  (implies (and (fn2-env-j3-row id log a) (fn2-env-j3e-row id a) (fn2-commit-idp id a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
                (equal (fn2-env-role-extent id 0 b) (fn2-env-role-extent id 0 a))
                (equal (fn2-env-role-extent id 1 b) (fn2-env-role-extent id 1 a))
                (equal (fn2-env-role-extent id 2 b) (fn2-env-role-extent id 2 a))
                (fn2-env-j3-move-ok (fn2-machine-phase id a) (fn2-machine-phase id b) (fn2-machine-cb-mode id a)
                                    (fn2-machine-cb-done id a) (fn2-machine-cb-done id b)))
           (and (fn2-env-j3-row id log b) (fn2-env-j3e-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-j3-move-ok
                               fn2-env-role-offset-of-extent member-equal (:e member-equal) nfix (:e nfix) (:e <) (:e equal)))))
(defun fn2-env-j3-write-arm-events (state-name code)
  ; the write arms (:dependencies, :log-write): FN2-ENV-COMMIT-RUN-<STATE>-DONE
  ; keeps the count with a stay or a failure, or resets it
  (declare (xargs :mode :program))
  (let* ((e (assoc code *fn2-commit-arm-decls*)) (ch (cadr e)) (cs (caddr e))
         (const (fn2-env-arm-state-const state-name))
         (b '(mv-nth 4 (fn2-commit-run id budget fn2-core)))
         (row '(fn2-machine-slot id fn2-core))
         (frame (fn2-columns-sym (fn2-columns-col-name 'fn2-env state-name) "-ARM-FRAME"))
         (next (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-NEXT"))
         (facts (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-FACTS"))
         (done (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-DONE"))
         (one (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j3-row state-name) "-ARM"))
         (rows (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j3-rows state-name) "-ARM")))
    (if (intersectp cs '(9 13 23 33))
        (er hard 'fn2-env-j3-write-arm-events "~x0 writes a column J3 reads: ~x1." state-name e)
      `((defthm ,one
          (implies (and (fn2-env-j3-row i log fn2-core) (fn2-env-j3e-row i fn2-core)
                        (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (equal (fn2-commit-row-phase id fn2-core) ,const))
                   (and (fn2-env-j3-row i log ,b) (fn2-env-j3e-row i ,b)))
          :rule-classes nil
          :hints (("Goal" :in-theory '(natp (:type-prescription fn2-machine-slot-natp) (:e member-equal) member-equal (:e tau-system)
                                       fn2-commit-idp fn2-commit-arm-row-phase fn2-env-j3-move-ok fn2-commit-rows fn2-commit-table
                                       (:e equal) (:e fn2-commit-arm-children) (:e fn2-commit-arm-columns))
                   :do-not-induct t
                   :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) ,row)))
                   :use ((:instance ,frame) (:instance ,next) (:instance fn2-env-row-phase-snapshot)
                         (:instance ,facts) (:instance ,done) (:instance fn2-env-commit-run-sk)
                         (:instance fn2-env-sk-projections (a fn2-core) (b ,b))
                         (:instance fn2-env-done-of-dk (a fn2-core) (b ,b))
                         (:instance fn2-env-j3-of-row-frame-off-row (a fn2-core) (b ,b) (row ,row) (cs ',cs) (ch ',ch))
                         (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core fn2-core))
                         (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core ,b))
                         (:instance fn2-env-read-codes-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
                         (:instance fn2-env-read-codes-of-row-frame (id id) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
                         (:instance fn2-ctf-dir-readers (id i) (a fn2-core) (b ,b))
                         (:instance fn2-ctf-dir-readers (id id) (a fn2-core) (b ,b))
                         (:instance fn2-env-commit-idp-kind (id id))
                         ,@(fn2-env-row-frame-uses '(fn2-machine-batch-no-of-row-frame fn2-machine-cb-mode-of-row-frame
                                                     fn2-machine-cb-fence-ok-of-row-frame)
                                                   row cs ch b)
                         (:instance fn2-env-role-extent-of-ek (id id) (role 0) (a fn2-core) (b ,b))
                         (:instance fn2-env-role-extent-of-ek (id id) (role 1) (a fn2-core) (b ,b))
                         (:instance fn2-env-role-extent-of-ek (id id) (role 2) (a fn2-core) (b ,b))
                         (:instance fn2-env-j3-move-reads (id id) (a fn2-core) (b ,b))))))
        (defthm ,rows
          (implies (and (fn2-env-j3-rows ids log fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (equal (fn2-commit-row-phase id fn2-core) ,const))
                   (fn2-env-j3-rows ids log ,b))
          :hints ,(fn2-env-pw-arm-hints 'fn2-env-j3-point 'fn2-env-j3-rows one
                    `((fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (equal (fn2-commit-row-phase id fn2-core) ,const)) '(fn2-env-j3-point) nil))))))
(make-event (value (cons 'progn (fn2-env-j3-write-arm-events :dependencies 3))))
(make-event (value (cons 'progn (fn2-env-j3-write-arm-events :log-write 4))))
(defthm fn2-env-j3-rows-commit-run
  ; every commit visit keeps J3 (a visit of an id that is not a readable row only stops the core)
  (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-rows ids log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp id fn2-core))
                    (member-equal (fn2-commit-row-phase id fn2-core) '(0 1 2 3 4 5 6 7 8 9 10 11 12))))
           (fn2-env-j3-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :hints (("Goal" :in-theory '(member-equal (:e member-equal) car-cons cdr-cons
                               fn2-env-j3-rows-free-arm fn2-env-j3-rows-collect-arm fn2-env-j3-rows-seal-arm
                               fn2-env-j3-rows-dependencies-arm fn2-env-j3-rows-log-write-arm fn2-env-j3-rows-fence-arm
                               fn2-env-j3-rows-durable-arm fn2-env-j3-rows-install-arm fn2-env-j3-rows-publish-arm
                               fn2-env-j3-rows-notify-arm fn2-env-j3-rows-draining-arm fn2-env-j3-rows-uncertain-arm
                               fn2-env-j3-rows-dropping-arm)
           :use ((:instance fn2-env-j-rows-non-row-visit)))))
;; ---------------------------------------------------------------------------
;; Executor instance interface.  A turn logs nothing, but may expose new
;; replies.  Therefore the fixed ghost ACKED is re-observed at the current
;; core in the lifted predicate; holding ACKED fixed in FN2-ENV-INV itself
;; would incorrectly forbid a legitimate notify step.
;; This is the evidence projection of the required phase/history invariant.
;; It is NOT inductive by itself: executor-contracts-unit's companion
;; commit test exhibits an unfenced :notify row satisfying the old invariant.
;; The notify-invariant lane supplies J1-J4; the run/observe/grant frame
;; obligations also remain necessary.  Do not admit FN2-ENV-TURN-INSTANCE
;; until those semantic obligations are discharged.
(defun-nx fn2-env-turn-inv (g c)
  (fn2-env-inv (nth 0 g) (fn2-env-observe (nth 0 g) (nth 1 g) c) (nth 2 g) c))
(defun-nx fn2-env-turn-rel (tag args g before after)
  (declare (ignorable tag args))
  (implies (fn2-env-turn-inv g before) (fn2-env-turn-inv g after)))
(defthm fn2-env-turn-inv-entry
  (implies (fn2-env-inv ids acked log fn2-core)
           (fn2-env-turn-inv (list ids acked log) fn2-core))
  :hints (("Goal" :in-theory (disable fn2-env-rows fn2-env-observed-p
                                      fn2-env-observe-rows fn2-env-acked-durable-p))))
(defun-nx fn2-env-dur-turn-inv (g c)
  ; the turn's predicate: J's rows and frontier at the fixed log (nth 2 g),
  ; the ghost acknowledged set (nth 1 g) durable in it
  (and (fn2-env-j-rows (nth 0 g) (nth 2 g) c)
       (fn2-env-j3-rows (nth 0 g) (nth 2 g) c)
       (fn2-env-j-frontier (nth 2 g) c)
       (fn2-env-acked-durable-p (nth 1 g) (nth 2 g))))
(defthm fn2-env-dur-turn-inv-projection
  (implies (fn2-env-dur-turn-inv g c) (fn2-env-turn-inv g c))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-turn-inv fn2-env-inv)
                                  (fn2-env-j-rows fn2-env-j3-rows fn2-env-j-frontier fn2-env-installed fn2-env-rows
                                   fn2-env-observe-rows fn2-env-acked-durable-p fn2-env-prefix-durable-p
                                   fn2-env-observed-p))
           :use ((:instance fn2-env-observe-rows-durable (rows (fn2-env-rows (nth 0 g) c))
                            (n (fn2-env-installed c)) (acked (nth 1 g)) (log (nth 2 g)))
                 (:instance fn2-env-observe-rows-covers (rows (fn2-env-rows (nth 0 g) c)) (acked (nth 1 g)))
                 (:instance fn2-env-j-rows-acks-bounded (ids (nth 0 g)) (log (nth 2 g)) (fn2-core c))
                 (:instance fn2-env-j-frontier-installed (log (nth 2 g)) (fn2-core c))))))
(defthm fn2-env-dur-inv-entry
  (implies (fn2-env-dur-inv ids acked log fn2-core)
           (fn2-env-dur-turn-inv (list ids acked log) fn2-core))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn2-env-j-rows fn2-env-j3-rows fn2-env-j-frontier fn2-env-rows fn2-env-observed-p
                                      fn2-env-acked-durable-p))))
; The turn's half, to be proved by FN2-EXECUTOR-INSTANTIATE with predicate
; FN2-ENV-DUR-TURN-INV and relation "every cut preserves it" (not a new turn
; induction). With FN2-ENV-DUR-TURN-INV-PROJECTION it gives the :turn step of
; FN2-ENV-DUR-INV, and with FN2-ENV-DUR-INV-STEP-BUT-TURN (the host steps and
; :admit) the run's invariant.
(defthm-owed fn2-env-dur-turn-preserves (g fn2-core)
  (implies (and (fn2-env-dur-turn-inv g fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-env-dur-turn-inv g (mv-nth 4 (fn2-turn fn2-core))))
  :schema :invariant :from (:machine fn2-commit)
  :teeth (fn2-dur-turn-positive fn2-dur-turn-j-removal)
  :doc "fn2-turn preserves J1-J4 (FN2-ENV-J-ROWS, FN2-ENV-J-FRONTIER) at a fixed device log, so that every batch a commit row shows acknowledged stays durable (FN2-ENV-DUR-TURN-INV-PROJECTION). The executor-level lift FN2-EXECUTOR-INV-TURN reduces it to one obligation per cut in *FN2-EXECUTOR-CONTRACT-CUTS*. Proved for the commit visit fn2-commit-run, per phase: :notify, :durable, :fence, :collect, :seal, :draining, :uncertain, :dropping (FN2-ENV-J-ROWS-<PHASE>-ARM), :free (with the visited id a readable row), :install and :publish (with J at the visited id), each with its frontier lemma FN2-ENV-J-FRONTIER-<PHASE>-ARM. Owed, by owner: (1) cross-kind: every non-commit cut (the other kinds' -RUN / -RUN-STUB, fn2-exec-harvest of their completions, the wait-source grants, fn2-member-replay; *FN2-COMMIT-TURN-FRAME-BLOCKERS*) must leave the directory's kinds and slots, the commit table, the commit root and the commit-io table, which needs their KIDS/DIR constraints (dispatch-contracts, handler-frames); (2) commit-internal: :dependencies and :log-write keep J given J3 at the visited row (FN2-ENV-J-ROWS-DEPENDENCIES-ARM, FN2-ENV-J-ROWS-LOG-WRITE-ARM; J3 is FN2-ENV-J3-ROW: shared role extents and each counted completion a done write of the phase's roles at its offset in the log, role 2 with its batch's seal); J3 is in FN2-ENV-DUR-INV and this predicate (FN2-ENV-J3-ROWS: FN2-ENV-J3-ROW and its entry clauses FN2-ENV-J3E-ROW), kept by every step but :turn (FN2-ENV-DUR-INV-STEP-BUT-TURN); every commit visit keeps J3 (FN2-ENV-J3-ROWS-COMMIT-RUN, from FN2-ENV-J3-ROWS-<PHASE>-ARM for all thirteen phases); owed: J3 kept by the write/fence handler, whose count rise needs the delivered result to be the first done answer to a take of an uncounted role write of the row (the mailbox/operations-table link to the log, J5) and whose fence-ok rise needs the fence result to answer a fence taken after the row's writes were answered; (3) the visited commit id carries J: a visit of an id that is not a readable row only stops the core (FN2-ENV-J-ROWS-NON-ROW-VISIT), and a readable one is at the slot of a ghost id once FN2-ENV-COMMIT-SLOTS-P holds (FN2-ENV-COMMIT-IDS-COVER, FN2-ENV-J-ROW-OF-COMMIT-IDS); every step but :turn keeps FN2-ENV-COMMIT-SLOTS-P (FN2-ENV-COMMIT-SLOTS-P-STEP-BUT-TURN) and so does every commit visit (FN2-ENV-COMMIT-SLOTS-P-COMMIT-RUN); owed: the other cuts of the turn, with (1).")
(defthm fn2-env-turn-inv-exit-by-definition
  (implies (and (fn2-env-turn-inv (list ids acked log) (mv-nth 4 (fn2-turn fn2-core)))
                (equal (fn2-env-tag action) :turn))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (declare (ignore entry))
             (fn2-env-inv ids (fn2-env-observe ids acked after) log after)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-turn-inv)
                      (fn2-env-inv fn2-env-observe fn2-env-observe-is-rows fn2-turn)))))

; The turn's accounting, reset and service-bit changes really do preserve
; the full evidence projection.  These are discharged obligations, not
; extra premises added to the final durability claim.
(defthm fn2-env-rows-executor-children
  (and (equal (fn2-env-rows ids (update-fn2-core-control x fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (update-fn2-core-sched x fn2-core)) (fn2-env-rows ids fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-machine-cb-acks fn2-machine-batch-no fn2-machine-idp
                                     fn2-machine-kind fn2-machine-slot))))
(defthm fn2-env-rows-executor-accounting
  (and (equal (fn2-env-rows ids (fn2-exec-account-work bytes steps fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-exec-set-turn-bytes value fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-exec-set-turn-steps value fn2-core)) (fn2-env-rows ids fn2-core))
       (equal (fn2-env-rows ids (fn2-exec-clear-service service fn2-core)) (fn2-env-rows ids fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-exec-account-work fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
                                   fn2-core-stop fn2-exec-clear-service) (fn2-env-rows)))))
(defthm fn2-env-turn-inv-accounting
  (implies (fn2-env-turn-inv g fn2-core)
           (and (fn2-env-turn-inv g (fn2-exec-account-work bytes steps fn2-core))
                (fn2-env-turn-inv g (fn2-exec-set-turn-bytes value fn2-core))
                (fn2-env-turn-inv g (fn2-exec-set-turn-steps value fn2-core))
                (fn2-env-turn-inv g (fn2-exec-clear-service service fn2-core))))
  :hints (("Goal" :in-theory (e/d (fn2-env-turn-inv fn2-env-inv)
                     (fn2-env-rows fn2-env-observed-p fn2-env-observe-rows fn2-env-acked-durable-p
                      fn2-exec-account-work fn2-exec-set-turn-bytes fn2-exec-set-turn-steps fn2-exec-clear-service)))))

;; ---------------------------------------------------------------------------
;; RECOVERY COMPLETENESS, the statement's recovery half: an image that holds
;; batches 1..N of a run's log as the run wrote them (A-FENCE-PERSISTS keeps
;; a fenced write's bytes unless a write that may land after it replaced
;; them) makes recovery, once at :done, report a chain of at least N.

; Entry W is batch B's durable seal write, and IMAGE holds it and a fenced
; write of its extent's page and records units.
(defun fn2-env-batch-held-at (w b log image)
  (declare (xargs :verify-guards nil))
  (let* ((e (nth w log)) (base (- (nfix (nth 4 e)) (* 2 *fn2-commit-unit-bytes*))))
    (and (fn2-env-seal-durable-at w b log)
         (fn2-env-image-holds-write-p e image)
         (fn2-env-held-offset-from 0 base log image)
         (fn2-env-held-offset-from 0 (+ base *fn2-commit-unit-bytes*) log image))))
(defun fn2-env-batch-held-from (w b log image)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-env-batch-held-at)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((fn2-env-batch-held-at w b log image) t)
        (t (fn2-env-batch-held-from (+ 1 w) b log image))))
(defun fn2-env-image-holds-prefix-p (n log image)
  (declare (xargs :verify-guards nil))
  (if (zp n) t
    (and (fn2-env-batch-held-from 0 n log image) (fn2-env-image-holds-prefix-p (- n 1) log image))))

(defthm-owed fn2-recovery-chain-complete (profile actions image n recovery-actions)
 (let* ((log (fn2-env-device-log (fn2-env-run profile actions)))
        (rec (fn2-env-recover profile image recovery-actions)))
  (implies (and (fn2-profile-supportedp profile)
                (fn2-env-image-holds-prefix-p n log image)
                (fn2-env-recovery-done-p rec))
           (subsetp-equal (fn2-env-iota (nfix n)) (fn2-env-recovered-batches rec))))
 :teeth (fn2-recovery-complete-positive fn2-recovery-complete-held-removal)
 :schema :crash
 :doc "Recovery completeness: when an image holds batches 1..N of a run's device log as the run wrote them (each batch's fenced seal write and fenced page and records writes of its extent, byte for byte), the real recovery row, run by fn2-turn over a fresh core reading that image under any recovery action list, reports at :done a chain containing 1..N. With FN2-ENV-INV (acknowledged implies durable in the log) and A-FENCE-PERSISTS it gives FN2-COMMIT-ACK-IMPLIES-RECOVERABLE.")

; Per recovery step kind: every step but :turn leaves the recovery row's
; phase and chain as they were, so the result is decided at :turn steps
; (the recovery kind's arm FRAMEs); the host steps carry no obligation.
(make-event
 (let ((world (w state)))
   `(defthm fn2-env-recovery-done-congruence
      (implies (and ,@(fn2-arm-frame-nth-equalities (fn2-arm-frame-phase-indices world)))
               (equal (fn2-env-recovery-done id a) (fn2-env-recovery-done id b)))
      :rule-classes nil
      :hints (("Goal" :in-theory (e/d (fn2-env-recovery-done fn2-machine-rc-chain fn2-machine-rc-chain-read-code
                                       fn2-machine-phase-read-code fn2-machine-idp fn2-core-machines
                                       ,@(fn2-machine-machine-tables world))
                                      (fn2-machine-phase fn2-machine-slot fn2-machine-kind))
               :use ((:instance fn2-arm-phase-congruence)
                     (:instance fn2-arm-slot-congruence)
                     (:instance fn2-arm-kind-congruence)))))))
(defthm fn2-env-recovery-done-child-frame
  (and (equal (fn2-env-recovery-done id (update-fn2-core-pool x fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (update-fn2-core-ops x fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (update-fn2-core-sched x fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (update-fn2-core-trace x fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (update-fn2-core-control x fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (update-fn2-core-extents x fn2-core)) (fn2-env-recovery-done id fn2-core)))
  :hints (("Goal" :in-theory (union-theories '(update-fn2-core-pool update-fn2-core-ops update-fn2-core-sched
                                               update-fn2-core-trace update-fn2-core-control update-fn2-core-extents
                                               nth-update-nth)
                                             (theory 'fn2-arm-frame-base))
           :use ((:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-pool x fn2-core)))
                 (:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-ops x fn2-core)))
                 (:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-sched x fn2-core)))
                 (:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-trace x fn2-core)))
                 (:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-control x fn2-core)))
                 (:instance fn2-env-recovery-done-congruence (a fn2-core) (b (update-fn2-core-extents x fn2-core)))))))
(in-theory (disable fn2-env-recovery-done))
(defthm fn2-env-recovery-done-host-frame
  (and (equal (fn2-env-recovery-done id (fn2-host-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-core))
              (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (fn2-host-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 fn2-core))
              (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (fn2-host-post-clock mono real flags fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (fn2-host-post-signal bits fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (mv-nth 1 (fn2-host-outbox-ack n fn2-core))) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (mv-nth 1 (fn2-host-op-finish slot gen fn2-core))) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (fn2-env-fill rslot rgen slot gen idx octets fn2-core)) (fn2-env-recovery-done id fn2-core))
       (equal (fn2-env-recovery-done id (fn2-env-begin-epoch epoch fn2-core)) (fn2-env-recovery-done id fn2-core)))
  :hints (("Goal" :in-theory (enable fn2-host-post-result fn2-host-post-accept-result fn2-host-post-clock
                                     fn2-host-post-signal fn2-host-outbox-ack fn2-host-op-finish
                                     fn2-env-fill fn2-env-begin-epoch))))
(defthm fn2-env-recovery-done-take-frame
  (equal (fn2-env-recovery-done id (mv-nth 1 (fn2-env-take recoveryp image fn2-core))) (fn2-env-recovery-done id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-env-take))))
(defthm fn2-env-recovery-done-host-step-frame
  (implies (not (equal (fn2-env-tag action) :turn))
           (equal (fn2-env-recovery-done id (mv-nth 1 (fn2-env-step action t image rlog fn2-core)))
                  (fn2-env-recovery-done id fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-env-step fn2-env-loan-write fn2-env-post) (fn2-env-take fn2-env-admit)))))
(defthm fn2-env-recovery-done-needs-turn
  (implies (and (not (equal (fn2-env-tag action) :turn))
                (not (fn2-env-recovery-done id fn2-core)))
           (not (fn2-env-recovery-done id (mv-nth 1 (fn2-env-step action t image rlog fn2-core))))))

;; ---------------------------------------------------------------------------
;; WHAT J5 CARRIES. J3 follows from J5's count and per-role clause
;; (FN2-ENV-J3-ROW-OF-J5): a counted write is a role whose write left the live
;; set, hence written. The fence flag's rise keeps J2 by J5's fence clause
;; (FN2-ENV-J2-RISE-OF-J5-FENCE): the row's flagged writes were answered before
;; its fence was taken, and the fence's first answer is the successful result
;; the handler counts. A take reads its loan range in full
;; (FN2-ENV-TAKE-OUTPUT-ENTRY, fact 1: with J5's range, 4096 octets).
(defthm fn2-env-role-live-booleanp
  (booleanp (fn2-env-role-live id role fn2-core))
  :rule-classes :type-prescription)
(in-theory (disable fn2-env-role-live))
; J3 VIA J5. The exact count (cb-done plus the live roles is cb-issued) and
; the per-role clause (an issued role no longer live is written) give J3's
; counted-completion clause: whatever the handler counted is a role whose
; write left the live set, so it is written. J3's shared extents are the
; row's own (kept by every step that keeps J3).
(defthm fn2-env-j3-row-of-j5
  (implies (and (fn2-env-j5-roles id log fn2-core)
                (implies (and (fn2-commit-idp id fn2-core)
                              (member-equal (fn2-machine-phase id fn2-core)
                                            (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*)))
                         (and (natp (fn2-env-role-extent id 0 fn2-core))
                              (equal (fn2-env-role-extent id 1 fn2-core) (fn2-env-role-extent id 0 fn2-core))
                              (equal (fn2-env-role-extent id 2 fn2-core) (fn2-env-role-extent id 0 fn2-core)))))
           (fn2-env-j3-row id log fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j5-roles fn2-env-j5-role fn2-env-b2n
                               member-equal (:e member-equal) nfix (:e nfix) natp (:e <) (:e equal) (:e binary-+)
                               fn2-env-role-live-booleanp)
           :do-not-induct t)))
(defthm fn2-env-written-fenced-by-later-fence
  (implies (and (fn2-env-written-from w offset b nil x) (fn2-dev-fence-after-p y) (true-listp y))
           (fn2-env-written-from w offset b t (append x y)))
  :hints (("Goal" :induct (fn2-env-written-from w offset b nil x)
           :in-theory '(fn2-env-written-from fn2-env-done-write-extends fn2-env-fenced-by-later-fence
                        fn2-env-nth-append-low fn2-env-len-append (:type-prescription true-listp-append)
                        true-listp-append natp nfix fix (:type-prescription len)))))
(local (defthm fn2-env-nthcdr-at
  (implies (and (natp n) (< n (len l)))
           (and (consp (nthcdr n l)) (equal (car (nthcdr n l)) (nth n l))
                (equal (cdr (nthcdr n l)) (nthcdr (+ 1 n) l))))
  :rule-classes nil))
(local (defthm fn2-env-append-take-nthcdr
  (implies (<= (nfix n) (len l)) (equal (append (take n l) (nthcdr n l)) l))))
(defthm fn2-env-written-fenced-by-fence-take
  (let ((f (nth wf log)))
    (implies (and (fn2-env-written-from 0 offset b nil (take wf log))
                  (natp wf) (< wf (len log)) (true-listp log)
                  (fn2-dev-takep f) (equal (nth 3 f) *fn2-dev-fence-kind*)
                  (fn2-dev-done-answer-p (fn2-dev-answer (nth 1 f) (nth 2 f) (nthcdr (+ 1 wf) log))
                                         *fn2-dev-fence-result* nil))
             (fn2-env-written-from 0 offset b t log)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-append-take-nthcdr) (fn2-env-written-from fn2-dev-answer fn2-dev-done-answer-p fn2-dev-takep
                                                                 fn2-env-written-fenced-by-later-fence take nthcdr))
           :use ((:instance fn2-env-written-fenced-by-later-fence (w 0) (x (take wf log)) (y (nthcdr wf log)))
                 (:instance fn2-dev-fence-after-p (log (nthcdr wf log)))
                 (:instance fn2-env-nthcdr-at (n wf) (l log))))))

; The fence flag's rise keeps J2: a fence J5 accounts for, whose first answer
; is the successful fence result the handler counts, fences every write the
; row's flags name.
(defthm fn2-env-j2-rise-of-j5-fence
  (progn$
    (implies (and (fn2-env-j5-fence id op slot log fn2-core) (true-listp log)
                  (equal (nth 2 op) *fn2-op-phase-submitted*) (equal (nth 13 op) 1)
                  (equal (nth 15 op) *fn2-event-fence-result*) (equal (nth 16 op) *fn2-outcome-done*))
             (and (implies (equal (fn2-machine-cb-deps-ok id fn2-core) 1)
                           (fn2-env-role-written id 0 t log fn2-core))
                  (implies (equal (fn2-machine-cb-log-ok id fn2-core) 1)
                           (and (fn2-env-role-written id 1 t log fn2-core)
                                (fn2-env-role-written id 2 t log fn2-core))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-fence fn2-env-j5-taken fn2-env-role-written fn2-dev-done-answer-p
                               natp nfix (:e nfix) unicity-of-0 (:e equal) (:e member-equal) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-take-index-bound (gen (nth 1 op)))
                 (:instance fn2-env-answer-resultp (gen (nth 1 op))
                            (l (nthcdr (+ 1 (fn2-env-take-index slot (nth 1 op) log)) log)))
                 (:instance fn2-env-written-fenced-by-fence-take (wf (fn2-env-take-index slot (nth 1 op) log))
                            (offset (fn2-env-role-offset id 0 fn2-core)) (b nil))
                 (:instance fn2-env-written-fenced-by-fence-take (wf (fn2-env-take-index slot (nth 1 op) log))
                            (offset (fn2-env-role-offset id 1 fn2-core)) (b nil))
                 (:instance fn2-env-written-fenced-by-fence-take (wf (fn2-env-take-index slot (nth 1 op) log))
                            (offset (fn2-env-role-offset id 2 fn2-core)) (b (fn2-machine-batch-no id fn2-core)))))))

;; FACT 1.
(defun fn2-env-pool-base (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (b)
    (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (fn2-pool-base slot fn2-pool) 0) b))
(defun fn2-env-pool-length (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-pool-data-length fn2-pool) n))
(defthm fn2-env-op-span-output
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (eq (mv-nth 0 (fn2-host-op-span op gen fn2-core)) :ok)
                (fn2-op-output-kindp (nth 3 (fn2-env-op op fn2-core))))
           (let ((o (fn2-env-op op fn2-core)))
             (and (nth 0 o) (equal (nth 1 o) gen) (natp (nth 9 o)) (natp (nth 10 o))
                  (equal (mv-nth 1 (fn2-host-op-span op gen fn2-core))
                         (+ (fn2-env-pool-base (nth 7 o) fn2-core) (nth 9 o)))
                  (equal (mv-nth 2 (fn2-host-op-span op gen fn2-core)) (nth 10 o))
                  (natp (fn2-env-pool-base (nth 7 o) fn2-core))
                  (<= (+ (fn2-env-pool-base (nth 7 o) fn2-core) (nth 9 o) (nth 10 o)) (fn2-env-pool-length fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize) :do-not-induct t
           :in-theory (e/d (fn2-host-op-span fn2-env-op fn2-env-pool-base fn2-env-pool-length fn2-op-output-kindp)
                           (fn2-ops-rows fn2-ops-gen fn2-ops-phase fn2-ops-kind
                            fn2-ops-range-slot fn2-ops-range-gen fn2-ops-range-off fn2-ops-range-len
                            fn2-ops-owner-kind fn2-ops-owner-slot fn2-ops-owner-gen
                            fn2-ops-storage-offset fn2-ops-fua fn2-ops-c0-posted fn2-ops-c0-harvested
                            fn2-ops-c0-event fn2-ops-c0-outcome fn2-ops-c0-count
                            fn2-pool-rows fn2-pool-gen fn2-pool-cap fn2-pool-base
                            fn2-pool-data-length fn2-pool-lease-off fn2-pool-lease-len
                            fn2-pool-state fn2-pool-out-count fn2-pool-fill
                            fn2-pool-ownerp fn2-pool-input-code))
           :use ((:instance fn2-core-pool-type) (:instance fn2-core-ops-type)
                 (:instance fn2-ops-range-off-natp (i op) (fn2-ops (fn2-core-ops fn2-core)))
                 (:instance fn2-ops-range-len-natp (i op) (fn2-ops (fn2-core-ops fn2-core)))
                 (:instance fn2-pool-base-natp (i (fn2-ops-range-slot op (fn2-core-ops fn2-core))) (fn2-pool (fn2-core-pool fn2-core)))))))
(defun fn2-env-pool-span (slot off len fn2-core)
  ; the octets of pool slot SLOT's range (OFF, LEN)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-env-octets (+ (fn2-env-pool-base slot fn2-core) (nfix off)) (nfix len) fn2-core))
(defthm fn2-env-octets-len
  (implies (and (natp addr) (natp n) (<= (+ addr n) (fn2-env-pool-length fn2-core)))
           (equal (len (fn2-env-octets addr n fn2-core)) n))
  :hints (("Goal" :in-theory '(fn2-env-octets fn2-env-pool-length fn2-env-pool-octets-len))))
(defthm fn2-env-host-action-fields
  (implies (eq (mv-nth 0 (fn2-host-action slot fn2-core)) :ok)
           (let ((o (fn2-env-op slot fn2-core)))
             (and (nth 0 o) (equal (mv-nth 1 (fn2-host-action slot fn2-core)) (nth 3 o))
                  (equal (mv-nth 8 (fn2-host-action slot fn2-core)) (nth 11 o))
                  (equal (mv-nth 9 (fn2-host-action slot fn2-core)) (nth 12 o)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-host-action fn2-env-op fn2-op-slotp fn2-op-kind fn2-op-storage fn2-op-range
                                   fn2-op-capability fn2-op-cancel-target fn2-op-wake fn2-op-may-release)
                                  (fn2-ops-rows fn2-ops-gen fn2-ops-phase fn2-ops-kind
                                   fn2-ops-range-slot fn2-ops-range-gen fn2-ops-range-off fn2-ops-range-len
                                   fn2-ops-owner-kind fn2-ops-owner-slot fn2-ops-owner-gen
                                   fn2-ops-storage-offset fn2-ops-fua fn2-ops-c0-posted fn2-ops-c0-harvested
                                   fn2-ops-c0-event fn2-ops-c0-outcome fn2-ops-c0-count)))))
; FACT 1. A taken output's octets are its loan range's octets, as many as the
; range's length: the span check the take passes bounds the range in the
; pool. (J5 puts a role write's range at the role's pool slot, offset 0,
; 4096 octets.)
(defthm fn2-env-take-output-entry
  (let ((e (mv-nth 0 (fn2-env-take recoveryp image fn2-core))))
    (implies (and e (fn2-op-output-kindp (nth 3 e)) (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
             (let ((o (fn2-env-op (nth 1 e) fn2-core)))
               (and (nth 0 o) (equal (nth 1 o) (nth 2 e)) (equal (nth 3 o) (nth 3 e))
                    (equal (nth 11 o) (nth 4 e)) (equal (nth 12 o) (nth 5 e))
                    (equal (nth 6 e) (fn2-env-pool-span (nth 7 o) (nth 9 o) (nth 10 o) fn2-core))
                    (equal (len (nth 6 e)) (nth 10 o))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not (quote (generalize eliminate-destructors fertilize))
           :in-theory (e/d (fn2-env-take fn2-env-pool-span)
                           (fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-host-outbox-ack fn2-host-op-finish
                            fn2-env-fill fn2-env-octets fn2-env-op fn2-env-pool-base fn2-env-pool-length
                            fn2-action-completionp fn2-op-output-kindp fn2-dev-image-octets))
           :use ((:instance fn2-env-host-action-fields (slot (mv-nth 1 (fn2-host-outbox-peek 0 fn2-core))))
                 (:instance fn2-env-op-span-output (op (mv-nth 1 (fn2-host-outbox-peek 0 fn2-core)))
                            (gen (mv-nth 2 (fn2-host-outbox-peek 0 fn2-core))))))))

;; ---------------------------------------------------------------------------
;; J5 ACROSS :POST-RESULT, the pieces. The step leaves every child but the ops
;; table and appends the result iff fn2-post-result accepted it on cell 0
;; (FN2-ENV-POST-STEP); it changes exactly the posted op's terminal cell
;; (FN2-ENV-OP-OF-POST); the logged result keeps every other op's take and
;; answer (FN2-ENV-J5-TAKEN-OTHER-RESULT) and is the posted op's first answer,
;; since J5 had none for it (FN2-ENV-J5-TAKEN-POSTED-RESULT). The ops-level
;; reader facts are proved with the column readers closed.

(in-theory (disable fn2-env-op-c1-posted))
(in-theory (disable fn2-env-ops-op-of-post-refused fn2-env-ops-op-of-post-cell0 fn2-env-ops-op-of-post-cell1))
(defthm fn2-env-op-is-ops-op
  (equal (fn2-env-op s fn2-core) (fn2-env-ops-op s (fn2-core-ops fn2-core)))
  :hints (("Goal" :in-theory '(fn2-env-op fn2-env-ops-op))))
; The :post-result step: the core's ops become fn2-post-result's, and the
; device log gains the result iff the post was accepted on cell 0.
(defthm fn2-env-post-step
  (let ((cell (fn2-env-arg 1 action)) (slot (fn2-env-arg 2 action)) (gen (fn2-env-arg 3 action))
        (evkind (fn2-env-arg 4 action)) (outcome (fn2-env-arg 5 action)) (reason (fn2-env-arg 6 action))
        (count (fn2-env-arg 7 action)) (aux0 (fn2-env-arg 8 action)) (aux1 (fn2-env-arg 9 action)))
    (and (equal (mv-nth 1 (fn2-env-post action nil rlog fn2-core))
                (update-fn2-core-ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1
                                                      (fn2-core-ops fn2-core))
                                     fn2-core))
         (equal (mv-nth 0 (fn2-env-post action nil rlog fn2-core))
                (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops fn2-core))
                     (equal cell 0)
                     (list :result slot gen evkind outcome count)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-env-post fn2-host-post-result fn2-env-post-count fn2-env-post-count-of-post-result)
                           (fn2-post-result fn2-env-post-accepted-p fn2-env-arg fn2-env-taken fn2-ops-post-count)))))
(defthm fn2-env-op-of-post
  (equal (fn2-env-op s (mv-nth 1 (fn2-env-post action nil rlog fn2-core)))
         (if (and (equal s (fn2-env-arg 2 action))
                  (fn2-env-post-accepted-p (fn2-env-arg 1 action) (fn2-env-arg 2 action) (fn2-env-arg 3 action)
                                           (fn2-env-arg 4 action) (fn2-env-arg 5 action) (fn2-env-arg 6 action)
                                           (fn2-env-arg 7 action) (fn2-env-arg 8 action) (fn2-env-arg 9 action)
                                           (fn2-core-ops fn2-core)))
             (if (equal (fn2-env-arg 1 action) 0)
                 (fn2-env-op-posted (fn2-env-op s fn2-core) (fn2-env-arg 4 action) (fn2-env-arg 5 action) (fn2-env-arg 7 action))
               (fn2-env-op-c1-posted (fn2-env-op s fn2-core)))
           (fn2-env-op s fn2-core)))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn2-env-post-step fn2-env-op-is-ops-op fn2-env-ops-op-of-post-result
                        fn2-core-ops-of-update-fn2-core-ops (:e equal)))))
(in-theory (disable fn2-env-op-is-ops-op))
;; J5 ACROSS :POST-RESULT. The readers of every child but the ops table
;; are framed (FN2-ENV-OPS-FRAME); op S after the post is op S, or the posted
;; op with its terminal cell set (FN2-ENV-OP-OF-POST-RESULT-CORE), whose
;; fields 0..12 are unchanged (FN2-ENV-NTH-OP-POSTED). So each J5 clause holds
;; op by op (FN2-ENV-J5-OP-POST, -J5-ROLE-POST), the owned fences and J6 are
;; unchanged, and the step keeps J5-ROWS (FN2-ENV-J5-ROWS-POST-STEP).
(defthm fn2-env-ops-frame
  (and (equal (fn2-env-io u (update-fn2-core-ops x c)) (fn2-env-io u c))
       (equal (fn2-env-role-octets id role (update-fn2-core-ops x c)) (fn2-env-role-octets id role c))
       (equal (fn2-env-ops-rows (update-fn2-core-ops x c)) (fn2-ops-rows x))
       (equal (fn2-env-role-offset id role (update-fn2-core-ops x c)) (fn2-env-role-offset id role c))
       (equal (fn2-env-role-written id role f log (update-fn2-core-ops x c)) (fn2-env-role-written id role f log c))
       (equal (fn2-env-role-io id role (update-fn2-core-ops x c)) (fn2-env-role-io id role c)))
  :hints (("Goal" :in-theory (e/d (fn2-env-io fn2-env-role-octets fn2-env-ops-rows
                                   fn2-env-role-offset fn2-env-role-written fn2-env-role-io)
                                  (fn2-env-ops-op fn2-env-written-from fn2-env-pool-octets)))))
(defthm fn2-env-op-of-update-ops
  (equal (fn2-env-op s (update-fn2-core-ops x c)) (fn2-env-ops-op s x))
  :hints (("Goal" :in-theory (e/d (fn2-env-op-is-ops-op) (fn2-env-ops-op)))))
(in-theory (disable fn2-env-op-of-update-ops))
(defthm fn2-env-j5-fence-ops-frame
  (equal (fn2-env-j5-fence id op s log (update-fn2-core-ops x c)) (fn2-env-j5-fence id op s log c))
  :hints (("Goal" :in-theory (e/d (fn2-env-j5-fence) (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take)))))
(defthm fn2-env-j5-fence-other-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-fence id op s log c) (true-listp log)
                  (not (and (equal s slot) (equal (nth 1 op) gen))))
             (fn2-env-j5-fence id op s (append log (list r)) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-fence fn2-env-take-index-append-result fn2-env-take-append-low
                            fn2-env-j5-taken-other-result fn2-env-nth-append-low)
                           (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take binary-append nth))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-j5-fence-posted-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-fence id op slot log c) (true-listp log)
                  (equal (nth 1 op) gen) (equal (nth 2 op) *fn2-op-phase-submitted*) (equal (nth 13 op) 0))
             (fn2-env-j5-fence id (fn2-env-op-posted op evkind outcome count) slot (append log (list r)) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-fence fn2-env-take-index-append-result fn2-env-take-append-low
                            fn2-env-j5-taken-posted-result fn2-env-nth-append-low fn2-env-nth-op-posted)
                           (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take binary-append nth fn2-env-op-posted))
           :use ((:instance fn2-env-take-index-bound (gen (nth 1 op)))))))
(in-theory (disable fn2-env-op-posted))
(defthm fn2-env-post-accepted-op
  (implies (fn2-env-post-accepted-p 0 slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))
           (let ((op (fn2-env-op slot c)))
             (and (nth 0 op) (equal (nth 1 op) gen) (equal (nth 2 op) *fn2-op-phase-submitted*)
                  (equal (nth 13 op) 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-post-accepted-p fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp
                                   fn2-env-op-is-ops-op fn2-env-ops-op)
                                  (fn2-post-payloadp)))))
(defthm fn2-env-post-accepted-event
  ; an accepted terminal post carries the op kind's terminal event
  (implies (fn2-env-post-accepted-p 0 slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))
           (equal evkind (fn2-terminal-event (nth 3 (fn2-env-op slot c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-post-accepted-p fn2-post-payloadp fn2-env-op-is-ops-op fn2-env-ops-op)
                                  (fn2-post-eligiblep fn2-terminal-event)))))
(defthm fn2-env-post-accepted-count
  ; an accepted terminal write result counts at most the write's range
  (implies (and (fn2-env-post-accepted-p 0 slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))
                (equal evkind *fn2-event-write-result*))
           (<= count (nth 10 (fn2-env-op slot c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-post-accepted-p fn2-post-payloadp fn2-env-op-is-ops-op fn2-env-ops-op)
                                  (fn2-post-eligiblep fn2-terminal-event)))))
(defthm fn2-env-post-accepted-release-cell
  ; a post accepted on the release cell needs an op that may release
  (implies (and (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))
                (not (equal cell 0)))
           (equal (nth 18 (fn2-env-op slot c)) 1))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-post-accepted-p fn2-post-eligiblep fn2-op-handle-code fn2-op-slotp
                                   fn2-env-op-is-ops-op fn2-env-ops-op)
                                  (fn2-post-payloadp)))))
(defthm fn2-env-op-of-post-result-core
  (equal (fn2-env-op s (update-fn2-core-ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1
                                                             (fn2-core-ops c))
                                            c))
         (if (and (equal s slot)
                  (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
             (if (equal cell 0)
                 (fn2-env-op-posted (fn2-env-op s c) evkind outcome count)
               (fn2-env-op-c1-posted (fn2-env-op s c)))
           (fn2-env-op s c)))
  :hints (("Goal" :in-theory (quote (fn2-env-op-of-update-ops fn2-env-ops-op-of-post-result fn2-env-op-is-ops-op)))))
(in-theory (disable fn2-env-post-ok fn2-env-post-log))
; D26: J5 across a post, one lemma per cell (6.8 s -> 0.3 s): a post that
; leaves op S, a release cell on S, and a logged terminal cell
(defthm fn2-env-j5-op-post-same
  ; a post that leaves op S (refused, or another op's) keeps its J5
  (implies (and (not (and (equal s slot)
                          (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))))
                (not (fn2-env-pr-p)) (fn2-env-j5-op s id log c))
           (fn2-env-j5-op s id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-post-log fn2-env-op-of-post-result-core fn2-env-ops-frame
                         fn2-env-j5-fence-ops-frame
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-fence-live-of-update-fn2-core-ops fn2-commit-row-of-update-fn2-core-ops)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j5-op-post-release
  ; a release cell posted on op S: an op owned at the row's generation may
  ; not release, so S is not one, and its J5 reads no release field
  (implies (and (equal s slot) (not (equal cell 0))
                (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c))
                (fn2-env-j5-op s id log c))
           (fn2-env-j5-op s id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-post-log fn2-env-post-ok fn2-env-op-of-post-result-core fn2-env-ops-frame
                         fn2-env-nth-op-c1-posted fn2-env-j5-fence-ops-frame
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-fence-live-of-update-fn2-core-ops fn2-commit-row-of-update-fn2-core-ops
                         (:e natp) (:e <) (:e equal))
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-post-accepted-release-cell)))))
(defthm fn2-env-j5-op-post-logged
  (implies (and (fn2-env-pr-p) (fn2-env-j5-op s id log c) (true-listp log))
           (fn2-env-j5-op s id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((equal s slot))
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-post-log fn2-env-post-ok fn2-env-op-of-post-result-core fn2-env-ops-frame fn2-env-nth-op-posted
                         fn2-env-j5-fence-ops-frame fn2-env-j5-fence-other-result fn2-env-j5-fence-posted-result
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-fence-live-of-update-fn2-core-ops fn2-commit-row-of-update-fn2-core-ops
                         member-equal (:e member-equal) (:e natp) (:e <) (:e equal) natp)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-post-accepted-op)))))
(defthm fn2-env-j5-op-post
  (implies (and (fn2-env-j5-op s id log c) (true-listp log))
           (fn2-env-j5-op s id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :in-theory '(fn2-env-post-ok) :do-not-induct t
           :use ((:instance fn2-env-j5-op-post-same) (:instance fn2-env-j5-op-post-release)
                 (:instance fn2-env-j5-op-post-logged)))))
(in-theory (disable fn2-env-j5-op-post-same fn2-env-j5-op-post-release fn2-env-j5-op-post-logged))
(defthm fn2-env-j5-ops-post
  (implies (and (fn2-env-j5-ops s k id log c) (true-listp log))
           (fn2-env-j5-ops s k id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log c)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-j5-op-post) (theory 'minimal-theory)))))
(defthm fn2-env-owned-fences-post
  (equal (fn2-env-owned-fences s k id (update-fn2-core-ops (fn2-env-pr-ops) c))
         (fn2-env-owned-fences s k id c))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id c)
           :in-theory (union-theories
                       '(fn2-env-owned-fences fn2-env-owned-fence-at fn2-env-op-of-post-result-core fn2-env-nth-op-posted fn2-env-nth-op-c1-posted
                         fn2-machine-generation-of-update-fn2-core-ops (:e natp) (:e <) natp)
                       (theory 'minimal-theory)))))
(defthm fn2-env-ops-rows-post
  (equal (fn2-env-ops-rows (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-ops-rows c))
  :hints (("Goal" :in-theory '(fn2-env-ops-frame fn2-post-result-preserves-rows fn2-env-ops-rows))))
(defthm fn2-env-role-live-post
  (equal (fn2-env-role-live id role (update-fn2-core-ops (fn2-env-pr-ops) c))
         (fn2-env-role-live id role c))
  :hints (("Goal" :in-theory (union-theories
                       '(fn2-env-role-live fn2-env-op-of-post-result-core fn2-env-nth-op-posted fn2-env-nth-op-c1-posted fn2-env-ops-frame
                         (:e natp) (:e <) natp)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j5-role-post
  (implies (and (fn2-env-j5-role id role log c) (true-listp log))
           (fn2-env-j5-role id role (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (fn2-env-pr-p))
                   (and (fn2-env-pr-p) (not (equal (nth 1 (fn2-env-role-io id role c)) slot)))
                   (and (fn2-env-pr-p) (equal (nth 1 (fn2-env-role-io id role c)) slot)))
           :in-theory (union-theories
                       '(fn2-env-j5-role fn2-env-post-log fn2-env-post-ok fn2-env-op-of-post-result-core fn2-env-ops-frame fn2-env-nth-op-posted fn2-env-nth-op-c1-posted
                         fn2-env-role-live-post fn2-env-role-live-booleanp
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-ops
                         fn2-machine-cb-fence-ok-of-update-fn2-core-ops
                         fn2-env-j5-taken-other-result fn2-env-j5-taken-posted-result fn2-env-j5-taken-op-c1-posted
                         fn2-env-take-index-append-result fn2-env-not-takep-result fn2-env-nth-append-low
                         fn2-env-role-written fn2-env-written-extends (:type-prescription fn2-env-role-written)
                         fn2-env-j5-event-ok-of-posted fn2-env-j5-event-ok-of-c1-posted
                         (:e member-equal) (:e natp) (:e <) (:e equal) natp nfix (:e nfix) (:e fn2-terminal-event))
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-post-accepted-op) (:instance fn2-env-post-accepted-event) (:instance fn2-env-post-accepted-count)
                 (:instance fn2-env-take-index-bound (slot (nth 1 (fn2-env-role-io id role c)))
                            (gen (nth 1 (fn2-env-op (nth 1 (fn2-env-role-io id role c)) c))))))))
(defthm fn2-env-j5-roles-post
  (implies (and (fn2-env-j5-roles id log c) (true-listp log))
           (fn2-env-j5-roles id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn2-env-j5-roles fn2-env-j5-role-post fn2-env-role-live-post fn2-env-j5-apart fn2-env-ops-frame
                         fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-issued-of-update-fn2-core-ops
                         fn2-machine-cb-done-of-update-fn2-core-ops)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j6-row-post
  (equal (fn2-env-j6-row id (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-j6-row id c))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn2-env-j6-row fn2-env-role-live-post fn2-env-ops-frame fn2-env-op-of-post-result-core
                         fn2-env-nth-op-posted fn2-env-nth-op-c1-posted fn2-commit-idp-of-update-fn2-core-ops
                         fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-issued-of-update-fn2-core-ops
                         fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-ops
                         (:e natp) (:e <) natp)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j5-row-post
  (implies (and (fn2-env-j5-row id log c) (true-listp log))
           (fn2-env-j5-row id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn2-env-j5-row fn2-env-j5-ops-post fn2-env-ops-rows-post fn2-env-j5-roles-post
                         fn2-env-owned-fences-post fn2-commit-idp-of-update-fn2-core-ops
                         fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-fence-live-of-update-fn2-core-ops)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j5-rows-post
  (implies (and (fn2-env-j5-rows ids log c) (true-listp log))
           (fn2-env-j5-rows ids (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :induct (fn2-env-j5-rows ids log c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j5-row-post fn2-env-j6-row-post)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-step-post-unfolds
  (implies (equal (fn2-env-tag action) :post-result)
           (equal (fn2-env-step action nil image rlog c) (fn2-env-post action nil rlog c)))
  :hints (("Goal" :in-theory '(fn2-env-step))))
(defthm fn2-env-j5-rows-post-step
  ; :post-result keeps J5 and J6
  (implies (and (fn2-env-j5-rows ids log c) (true-listp log) (equal (fn2-env-tag action) :post-result))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-j5-rows ids (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn2-env-step-post-unfolds fn2-env-post-step fn2-env-post-log fn2-env-post-ok
                        append-to-nil (:e append))
           :use ((:instance fn2-env-j5-rows-post
                            (cell (fn2-env-arg 1 action)) (slot (fn2-env-arg 2 action)) (gen (fn2-env-arg 3 action))
                            (evkind (fn2-env-arg 4 action)) (outcome (fn2-env-arg 5 action))
                            (reason (fn2-env-arg 6 action)) (count (fn2-env-arg 7 action))
                            (aux0 (fn2-env-arg 8 action)) (aux1 (fn2-env-arg 9 action)))))))
(defthm fn2-env-take-frames
  (let ((c2 (mv-nth 1 (fn2-env-take nil image c))))
    (and (equal (fn2-machine-phase id c2) (fn2-machine-phase id c))
         (equal (fn2-machine-generation id c2) (fn2-machine-generation id c))
         (equal (fn2-machine-cb-fence-live id c2) (fn2-machine-cb-fence-live id c))
         (equal (fn2-machine-cb-issued id c2) (fn2-machine-cb-issued id c))
         (equal (fn2-machine-cb-done id c2) (fn2-machine-cb-done id c))
         (equal (fn2-machine-cb-mode id c2) (fn2-machine-cb-mode id c))
         (equal (fn2-machine-batch-no id c2) (fn2-machine-batch-no id c))
         (equal (fn2-machine-cb-fence-ok id c2) (fn2-machine-cb-fence-ok id c))
         (equal (fn2-machine-cb-deps-ok id c2) (fn2-machine-cb-deps-ok id c))
         (equal (fn2-machine-cb-log-ok id c2) (fn2-machine-cb-log-ok id c))
         (equal (fn2-commit-idp id c2) (fn2-commit-idp id c))
         (equal (fn2-commit-row id c2) (fn2-commit-row id c))
         (equal (fn2-env-io u c2) (fn2-env-io u c))
         (equal (fn2-env-role-io id role c2) (fn2-env-role-io id role c))
         (equal (fn2-env-role-octets id role c2) (fn2-env-role-octets id role c))
         (equal (fn2-env-role-offset id role c2) (fn2-env-role-offset id role c))
         (equal (fn2-env-role-written id role f log c2) (fn2-env-role-written id role f log c))
         (equal (fn2-env-j5-fence id op s log c2) (fn2-env-j5-fence id op s log c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish)
                           (fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-env-octets
                            fn2-outbox-ack fn2-op-finish fn2-env-io fn2-env-role-io fn2-env-role-octets
                            fn2-env-role-offset fn2-env-role-written fn2-env-j5-fence fn2-env-fill)))))
(defthm fn2-env-take-op
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (let* ((tk (fn2-env-take nil image c)) (e (mv-nth 0 tk)) (c2 (mv-nth 1 tk)))
             (and (implies (not (and e (equal s (nth 1 e)))) (equal (fn2-env-op s c2) (fn2-env-op s c)))
                  (implies e
                           (let ((o (fn2-env-op (nth 1 e) c)) (o2 (fn2-env-op (nth 1 e) c2)))
                             (and (nth 0 o) (equal (nth 1 o) (nth 2 e)) (equal (nth 2 o) *fn2-op-phase-queued*)
                                  (equal (nth 3 o) (nth 3 e))
                                  (equal (nth 11 o) (nth 4 e)) (equal (nth 12 o) (nth 5 e))
                                  (if (fn2-action-completionp (nth 3 o))
                                      (equal o2 (update-nth 2 *fn2-op-phase-submitted* o))
                                    (or (equal o2 (update-nth 2 *fn2-op-phase-done* o))
                                        (member-equal (nth 2 o2) (list *fn2-op-phase-free* *fn2-op-phase-retired*))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish fn2-host-outbox-peek
                            fn2-env-op-of-update-ops fn2-env-op-is-ops-op fn2-env-ops-op-of-outbox-ack-1
                            fn2-env-ops-op-of-op-finish-other fn2-op-ack-phase fn2-env-outbox-ack-refused)
                           (fn2-host-action fn2-host-op-span fn2-env-octets fn2-env-ops-op
                            fn2-outbox-ack fn2-op-finish fn2-outbox-peek fn2-env-fill fn2-opsp fn2-action-completionp))
           :use ((:instance fn2-core-ops-type (fn2-core c))
                 (:instance fn2-env-outbox-ack-1-head-op (fn2-ops (fn2-core-ops c)))
                 (:instance fn2-env-outbox-peek-0 (fn2-ops (fn2-core-ops c)))
                 (:instance fn2-env-host-action-fields (fn2-core c)
                            (slot (mv-nth 1 (fn2-outbox-peek 0 (fn2-core-ops c)))))
                 (:instance fn2-env-ops-op-of-op-finish-self
                            (h (mv-nth 1 (fn2-outbox-peek 0 (fn2-core-ops c))))
                            (g (mv-nth 2 (fn2-outbox-peek 0 (fn2-core-ops c))))
                            (fn2-ops (mv-nth 1 (fn2-outbox-ack 1 (fn2-core-ops c)))))))))
(defthm fn2-env-j5-fence-other-take
  (implies (and (fn2-env-j5-fence id op s log c) (true-listp log) (fn2-dev-takep e) (not (equal s (nth 1 e))))
           (fn2-env-j5-fence id op s (append log (list e)) c))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-fence fn2-env-take-index-append fn2-env-take-append-low
                            fn2-env-j5-taken-other-take fn2-env-nth-append-low)
                           (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take binary-append nth fn2-dev-takep))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-j5-fence-take
  (implies (and (fn2-env-j5-taken o slot log) (true-listp log) (equal (nth 2 o) *fn2-op-phase-queued*)
                (fn2-dev-takep e) (equal (nth 1 e) slot) (equal (nth 2 e) (nth 1 o))
                (equal (nth 3 e) *fn2-action-fence*)
                (implies (equal (fn2-machine-cb-deps-ok id c) 1) (fn2-env-role-written id 0 nil log c))
                (implies (equal (fn2-machine-cb-log-ok id c) 1)
                         (and (fn2-env-role-written id 1 nil log c) (fn2-env-role-written id 2 nil log c))))
           (fn2-env-j5-fence id (update-nth 2 *fn2-op-phase-submitted* o) slot (append log (list e)) c))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-fence fn2-env-take-append-low fn2-env-nth-len-append fn2-env-take-len-true-list)
                           (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take binary-append fn2-dev-takep
                            fn2-env-take-index-append))
           :use ((:instance fn2-env-j5-taken-take)))))
(defthm fn2-env-take-entry-shape
  (let ((e (mv-nth 0 (fn2-env-take recoveryp image c))))
    (implies e (and (fn2-dev-takep e) (true-listp (nth 6 e)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-take fn2-env-octets) (fn2-host-outbox-peek fn2-host-action fn2-host-op-span
                                   fn2-host-outbox-ack fn2-host-op-finish fn2-env-fill fn2-dev-image-octets)))))
(defthm fn2-env-written-unfenced
  (implies (fn2-env-written-from w offset b fenced log)
           (fn2-env-written-from w offset b nil log))
  :hints (("Goal" :induct (fn2-env-written-from w offset b fenced log)
           :in-theory (e/d (fn2-env-written-from) (fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-seal-commit)))))
(defthm fn2-env-fence-prefix-of-j2
  (implies (and (fn2-env-j2-row id log c) (fn2-commit-idp id c))
           (and (implies (equal (fn2-machine-cb-deps-ok id c) 1) (fn2-env-role-written id 0 nil log c))
                (implies (equal (fn2-machine-cb-log-ok id c) 1)
                         (and (fn2-env-role-written id 1 nil log c) (fn2-env-role-written id 2 nil log c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j2-row fn2-env-role-written fn2-env-written-unfenced (:e equal))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-fence-taken
  (implies (fn2-env-j5-fence id op s log c) (fn2-env-j5-taken op s log))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn2-env-j5-fence))))
(defthm fn2-env-j5-op-take-same
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log) (fn2-env-j5-op s id log c)
                (not (and (fn2-env-tk-e) (equal s (nth 1 (fn2-env-tk-e))))))
           (fn2-env-j5-op s id (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-log+ fn2-env-take-frames fn2-env-j5-fence-other-take append-to-nil)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op)
                 (:instance fn2-env-take-entry-shape (recoveryp nil))))))
(defthm fn2-env-j5-op-take-slot
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-op s id log c) (fn2-env-j2-row id log c) (fn2-commit-idp id c)
                (fn2-env-tk-e) (equal s (nth 1 (fn2-env-tk-e))))
           (fn2-env-j5-op s id (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-log+ fn2-env-take-frames fn2-env-j5-fence-take fn2-env-j5-fence-taken
                         fn2-action-completionp (:e fn2-action-completionp)
                         nth-update-nth (:e nfix) (:e equal) (:e member-equal) member-equal (:e natp) (:e <) natp)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op)
                 (:instance fn2-env-take-entry-shape (recoveryp nil))
                 (:instance fn2-env-fence-prefix-of-j2)))))
(defthm fn2-env-j5-op-take
  (let* ((tk (fn2-env-take nil image c)) (e (mv-nth 0 tk)))
    (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                  (fn2-env-j5-op s id log c) (fn2-env-j2-row id log c) (fn2-commit-idp id c))
             (fn2-env-j5-op s id (fn2-env-log+ log e) (mv-nth 1 tk))))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use (fn2-env-j5-op-take-same fn2-env-j5-op-take-slot))))
(in-theory (disable fn2-env-log+))
(defthm fn2-env-j5-ops-take
  (let* ((tk (fn2-env-take nil image c)) (e (mv-nth 0 tk)))
    (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                  (fn2-env-j5-ops s k id log c) (fn2-env-j2-row id log c) (fn2-commit-idp id c))
             (fn2-env-j5-ops s k id (fn2-env-log+ log e) (mv-nth 1 tk))))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log c)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-j5-op-take) (theory 'minimal-theory)))))
(defthm fn2-env-owned-fence-at-take
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (equal (fn2-env-owned-fence-at s id (mv-nth 1 (fn2-env-take nil image c)))
                  (fn2-env-owned-fence-at s id c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (mv-nth 0 (fn2-env-take nil image c)))
                   (and (mv-nth 0 (fn2-env-take nil image c)) (not (equal s (nth 1 (mv-nth 0 (fn2-env-take nil image c))))))
                   (and (mv-nth 0 (fn2-env-take nil image c)) (equal s (nth 1 (mv-nth 0 (fn2-env-take nil image c))))))
           :in-theory (union-theories
                       '(fn2-env-owned-fence-at fn2-env-take-frames fn2-action-completionp (:e fn2-action-completionp)
                         nth-update-nth (:e nfix) (:e equal) (:e member-equal) member-equal (:e natp) (:e <) natp)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op)))))
(defthm fn2-env-owned-fences-take
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (equal (fn2-env-owned-fences s k id (mv-nth 1 (fn2-env-take nil image c)))
                  (fn2-env-owned-fences s k id c)))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id c)
           :in-theory (union-theories '(fn2-env-owned-fences fn2-env-owned-fence-at-take) (theory 'minimal-theory)))))
(defthm fn2-env-ops-rows-take
  (equal (fn2-env-ops-rows (mv-nth 1 (fn2-env-take nil image c))) (fn2-env-ops-rows c))
  :hints (("Goal" :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish fn2-env-ops-rows)
                                  (fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-env-octets
                                   fn2-outbox-ack fn2-op-finish fn2-env-fill)))))
(defthm fn2-env-role-live-take
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (and (implies (fn2-env-role-live id role (mv-nth 1 (fn2-env-take nil image c)))
                         (fn2-env-role-live id role c))
                (implies (and (fn2-env-role-live id role c)
                              (equal (nth 3 (fn2-env-op (nth 1 (fn2-env-role-io id role c)) c)) *fn2-action-write*))
                         (fn2-env-role-live id role (mv-nth 1 (fn2-env-take nil image c))))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (mv-nth 0 (fn2-env-take nil image c)))
                   (and (mv-nth 0 (fn2-env-take nil image c))
                        (not (equal (nth 1 (fn2-env-role-io id role c)) (nth 1 (mv-nth 0 (fn2-env-take nil image c))))))
                   (and (mv-nth 0 (fn2-env-take nil image c))
                        (equal (nth 1 (fn2-env-role-io id role c)) (nth 1 (mv-nth 0 (fn2-env-take nil image c))))))
           :in-theory (union-theories
                       '(fn2-env-role-live fn2-env-take-frames fn2-action-completionp (:e fn2-action-completionp)
                         nth-update-nth (:e nfix) (:e equal) (:e member-equal) member-equal (:e natp) (:e <) natp)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op (s (nth 1 (fn2-env-role-io id role c))))))))
(defthm fn2-env-role-octets-span
  (implies (equal (len (fn2-env-role-octets id role c)) *fn2-commit-unit-bytes*)
           (equal (fn2-env-pool-span (nth 4 (fn2-env-role-io id role c)) 0 *fn2-commit-unit-bytes* c)
                  (fn2-env-role-octets id role c)))
  :hints (("Goal" :in-theory (e/d (fn2-env-role-octets fn2-env-pool-span fn2-env-octets fn2-env-pool-base)
                                  (fn2-env-role-io fn2-env-pool-octets))
           :cases ((consp (fn2-env-role-octets id role c))))))
(defthm fn2-env-role-offset-natp
  (implies (natp role) (natp (fn2-env-role-offset id role c)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-env-role-offset))))
(defthm fn2-env-take-ok-of-role
  (let ((o (fn2-env-op (nth 1 (fn2-env-tk-e)) c)))
    (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-tk-e)
                  (equal (nth 3 o) *fn2-action-write*) (equal (nth 7 o) rs) (equal (nth 9 o) 0)
                  (equal (nth 10 o) *fn2-commit-unit-bytes*) (equal (nth 11 o) offset) (equal (nth 12 o) fua)
                  (natp offset)
                  (implies b (equal (fn2-env-seal-commit (fn2-env-pool-span rs 0 *fn2-commit-unit-bytes* c)) b)))
             (fn2-env-j5-take-ok (fn2-env-tk-e) offset fua b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-take-ok fn2-dev-take-writep fn2-op-output-kindp (:e equal) (:e fn2-op-output-kindp))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op (s 0))
                 (:instance fn2-env-take-entry-shape (recoveryp nil))
                 (:instance fn2-env-take-output-entry (recoveryp nil) (fn2-core c))))))
(defthm fn2-env-j5-role-take-dead
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-role id role log c) (not (fn2-env-role-live id role c)))
           (fn2-env-j5-role id role (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-role fn2-env-log+ fn2-env-role-live-take fn2-env-take-frames
                                        fn2-env-role-written fn2-env-written-extends (:type-prescription true-listp))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5-role-take-other
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-role id role log c) (fn2-env-role-live id role c)
                (not (and (fn2-env-tk-e) (equal (nth 1 (fn2-env-role-io id role c)) (nth 1 (fn2-env-tk-e))))))
           (fn2-env-j5-role id role (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories '(fn2-env-j5-role fn2-env-log+ fn2-env-role-live-take fn2-env-take-frames
                                        fn2-env-j5-taken-other-take fn2-env-take-index-append fn2-env-nth-append-low
                                        append-to-nil natp nfix (:e equal) (:e nfix))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op (s (nth 1 (fn2-env-role-io id role c))))
                 (:instance fn2-env-take-entry-shape (recoveryp nil))
                 (:instance fn2-env-take-index-bound (slot (nth 1 (fn2-env-role-io id role c)))
                            (gen (nth 1 (fn2-env-op (nth 1 (fn2-env-role-io id role c)) c))))))))
(defthm fn2-env-j5-role-take-taken
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log) (natp role)
                (fn2-env-j5-role id role log c) (fn2-env-role-live id role c)
                (fn2-env-tk-e) (equal (nth 1 (fn2-env-role-io id role c)) (nth 1 (fn2-env-tk-e)))
                (implies (equal role 2)
                         (and (equal (len (fn2-env-role-octets id 2 c)) *fn2-commit-unit-bytes*)
                              (equal (fn2-env-seal-commit (fn2-env-role-octets id 2 c)) (fn2-machine-batch-no id c)))))
           (fn2-env-j5-role id role (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories '(fn2-env-j5-role fn2-env-log+ fn2-env-role-live-take fn2-env-take-frames
                                        fn2-env-j5-taken-take fn2-env-j5-taken-queued-untaken fn2-env-take-index-append fn2-env-nth-len-append fn2-env-role-octets-span
                                        fn2-env-role-offset-natp fn2-action-completionp (:e fn2-action-completionp)
                                        fn2-env-j5-event-ok-of-update-phase nth-update-nth append-to-nil natp nfix (:e equal) (:e nfix) (:e natp) (:e <))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op (s (nth 1 (fn2-env-role-io id role c))))
                 (:instance fn2-env-take-entry-shape (recoveryp nil))
                 (:instance fn2-env-role-offset-natp)
                 (:instance fn2-env-take-ok-of-role (rs (nth 4 (fn2-env-role-io id role c)))
                            (offset (fn2-env-role-offset id role c))
                            (fua (if (equal (fn2-machine-phase id c) *fn2-commit-state-log-write*) (fn2-machine-cb-mode id c) 0))
                            (b (and (equal role 2) (fn2-machine-batch-no id c))))))))
(defthm fn2-env-j6-role2-seal
  (implies (and (fn2-env-j6-row id c) (fn2-commit-idp id c)
                (equal (fn2-machine-phase id c) *fn2-commit-state-log-write*)
                (fn2-env-role-live id 2 c)
                (equal (nth 2 (fn2-env-op (nth 1 (fn2-env-role-io id 2 c)) c)) *fn2-op-phase-queued*))
           (and (equal (len (fn2-env-role-octets id 2 c)) *fn2-commit-unit-bytes*)
                (equal (fn2-env-seal-commit (fn2-env-role-octets id 2 c)) (fn2-machine-batch-no id c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6-row member-equal (:e member-equal) (:e equal))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-role-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log) (natp role)
                (fn2-env-j5-role id role log c) (fn2-env-j6-row id c) (fn2-commit-idp id c)
                (implies (equal role 2) (equal (fn2-machine-phase id c) *fn2-commit-state-log-write*)))
           (fn2-env-j5-role id role (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn2-env-j6-role2-seal)
                 (:instance fn2-env-take-op (s (nth 1 (fn2-env-role-io id role c))))
                 (:instance fn2-env-j5-role-take-dead) (:instance fn2-env-j5-role-take-other)
                 (:instance fn2-env-j5-role-take-taken)))))
(defthm fn2-env-role-live-take-of-j5-role
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-role id role log c))
           (equal (fn2-env-role-live id role (fn2-env-tk-c)) (fn2-env-role-live id role c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-role fn2-env-role-live-booleanp) (theory 'minimal-theory))
           :use ((:instance fn2-env-role-live-take)))))
(defthm fn2-env-j5-apart-take
  ; a role live after the take was live before, at the same unit
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-apart id c))
           (fn2-env-j5-apart id (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-apart fn2-env-take-frames) (theory 'minimal-theory))
           :use ((:instance fn2-env-role-live-take (role 1)) (:instance fn2-env-role-live-take (role 2))))))
(defthm fn2-env-j5-roles-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-roles id log c) (fn2-env-j6-row id c) (fn2-commit-idp id c))
           (fn2-env-j5-roles id (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-roles fn2-env-take-frames fn2-env-role-live-take-of-j5-role
                                        fn2-env-j5-role-take (:e natp) (:e equal) fn2-env-j5-apart-take)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-role-live-take (role 0))))))
(defthm fn2-env-j6-row-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j6-row id c))
           (fn2-env-j6-row id (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (fn2-env-tk-e))
                   (and (fn2-env-tk-e) (not (equal (nth 1 (fn2-env-role-io id 2 c)) (nth 1 (fn2-env-tk-e)))))
                   (and (fn2-env-tk-e) (equal (nth 1 (fn2-env-role-io id 2 c)) (nth 1 (fn2-env-tk-e)))))
           :in-theory (union-theories '(fn2-env-j6-row fn2-env-take-frames fn2-env-role-live-take
                                        fn2-action-completionp (:e fn2-action-completionp)
                                        nth-update-nth (:e nfix) (:e equal) (:e member-equal) member-equal (:e natp) (:e <) natp)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-take-op (s (nth 1 (fn2-env-role-io id 2 c))))
                 (:instance fn2-env-role-live-take (role 2))))))
(defthm fn2-env-j5-row-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-row id log c) (fn2-env-j6-row id c) (fn2-env-j2-row id log c))
           (fn2-env-j5-row id (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-row fn2-env-j5-ops-take fn2-env-ops-rows-take fn2-env-j5-roles-take
                                        fn2-env-owned-fences-take fn2-env-take-frames)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5-rows-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-rows ids log c) (fn2-env-j-rows ids log c))
           (fn2-env-j5-rows ids (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :induct (fn2-env-j5-rows ids log c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j-rows fn2-env-j-row fn2-env-j5-row-take fn2-env-j6-row-take)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-step-take-unfolds
  (implies (equal (fn2-env-tag action) :take)
           (equal (fn2-env-step action nil image rlog c) (fn2-env-take nil image c)))
  :hints (("Goal" :in-theory '(fn2-env-step))))
(defthm fn2-env-j5-rows-take-step
  ; :take keeps J5 and J6 (J2 gives a taken fence its prefix)
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-rows ids log c) (fn2-env-j-rows ids log c) (equal (fn2-env-tag action) :take))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-j5-rows ids (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn2-env-step-take-unfolds fn2-env-log+)
           :use ((:instance fn2-env-j5-rows-take)))))
(defun-nx fn2-env-ops-kept-from (s k x fn2-core)
  (declare (xargs :measure (acl2-count k) :hints (("Goal" :in-theory (disable fn2-env-op-kept)))))
  (if (zp k) t
    (and (fn2-env-op-kept (fn2-env-ops-op s x) (fn2-env-op s fn2-core))
         (fn2-env-ops-kept-from (+ 1 (nfix s)) (- k 1) x fn2-core))))
(defun-nx fn2-env-ops-kept (x fn2-core)
  ; every op of X is kept from the core's
  (and (equal (fn2-ops-rows x) (fn2-env-ops-rows fn2-core)) (natp (fn2-env-ops-rows fn2-core))
       (fn2-env-ops-kept-from 0 (fn2-env-ops-rows fn2-core) x fn2-core)))
(defthm fn2-env-ops-kept-from-at
  (implies (and (fn2-env-ops-kept-from s0 k x c) (natp k) (natp s0) (natp s) (<= s0 s) (< s (+ s0 k)))
           (fn2-env-op-kept (fn2-env-ops-op s x) (fn2-env-op s c)))
  :hints (("Goal" :induct (fn2-env-ops-kept-from s0 k x c) :in-theory (disable fn2-env-op-kept fn2-env-ops-op fn2-env-op))))
(defthm fn2-env-ops-kept-at
  (implies (fn2-env-ops-kept x c)
           (fn2-env-op-kept (fn2-env-ops-op s x) (fn2-env-op s c)))
  :hints (("Goal" :cases ((and (natp s) (< s (fn2-env-ops-rows c))))
           :in-theory (e/d (fn2-env-op-is-ops-op fn2-env-ops-rows) (fn2-env-op-kept fn2-env-ops-kept-from))
           :use ((:instance fn2-env-ops-kept-from-at (s0 0) (k (fn2-env-ops-rows c)))))
          ("Subgoal 2" :in-theory (enable fn2-env-op-kept fn2-env-ops-op fn2-env-op-is-ops-op fn2-env-ops-rows))))
(in-theory (disable fn2-env-op-kept fn2-env-ops-kept))
(defthm fn2-env-j5-op-kept
  (implies (and (fn2-env-j5-op s id log c) (fn2-env-ops-kept x c))
           (fn2-env-j5-op s id log (update-fn2-core-ops x c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-op fn2-env-op-kept fn2-env-op-of-update-ops fn2-env-ops-frame
                                        fn2-env-j5-fence-ops-frame
                                        fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                                        fn2-machine-cb-fence-live-of-update-fn2-core-ops fn2-commit-row-of-update-fn2-core-ops
                                        member-equal (:e member-equal) (:e equal))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-ops-kept-at)))))
(defthm fn2-env-j5-ops-kept
  (implies (and (fn2-env-j5-ops s k id log c) (fn2-env-ops-kept x c))
           (fn2-env-j5-ops s k id log (update-fn2-core-ops x c)))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log c)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-j5-op-kept) (theory 'minimal-theory)))))
(defthm fn2-env-owned-fence-at-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-owned-fence-at s id (update-fn2-core-ops x c)) (fn2-env-owned-fence-at s id c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-owned-fence-at fn2-env-op-kept fn2-env-op-of-update-ops
                                        fn2-machine-generation-of-update-fn2-core-ops
                                        member-equal (:e member-equal) (:e equal))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-ops-kept-at)))))
(defthm fn2-env-owned-fences-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-owned-fences s k id (update-fn2-core-ops x c)) (fn2-env-owned-fences s k id c)))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id c)
           :in-theory (union-theories '(fn2-env-owned-fences fn2-env-owned-fence-at-kept) (theory 'minimal-theory)))))
(defthm fn2-env-role-live-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-role-live id role (update-fn2-core-ops x c)) (fn2-env-role-live id role c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-role-live fn2-env-op-kept fn2-env-op-of-update-ops fn2-env-ops-frame)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-ops-kept-at (s (nth 1 (fn2-env-role-io id role c))))))))
(defthm fn2-env-j5-role-kept
  (implies (and (fn2-env-j5-role id role log c) (fn2-env-ops-kept x c))
           (fn2-env-j5-role id role log (update-fn2-core-ops x c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-role fn2-env-op-kept fn2-env-op-of-update-ops fn2-env-ops-frame
                                        fn2-env-role-live-kept
                                        fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                                        fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-ops
                                        fn2-machine-cb-fence-ok-of-update-fn2-core-ops (:e equal))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-ops-kept-at (s (nth 1 (fn2-env-role-io id role c))))))))
(defthm fn2-env-j5-roles-kept
  (implies (and (fn2-env-j5-roles id log c) (fn2-env-ops-kept x c))
           (fn2-env-j5-roles id log (update-fn2-core-ops x c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-roles fn2-env-j5-role-kept fn2-env-role-live-kept fn2-env-j5-apart fn2-env-ops-frame
                                        fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-issued-of-update-fn2-core-ops
                                        fn2-machine-cb-done-of-update-fn2-core-ops)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6-row-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-j6-row id (update-fn2-core-ops x c)) (fn2-env-j6-row id c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6-row fn2-env-op-kept fn2-env-op-of-update-ops fn2-env-ops-frame
                                        fn2-env-role-live-kept fn2-commit-idp-of-update-fn2-core-ops
                                        fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-issued-of-update-fn2-core-ops
                                        fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-ops)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-ops-kept-at (s (nth 1 (fn2-env-role-io id 2 c))))))))
(defthm fn2-env-j5-rows-kept
  (implies (and (fn2-env-j5-rows ids log c) (fn2-env-ops-kept x c))
           (fn2-env-j5-rows ids log (update-fn2-core-ops x c)))
  :hints (("Goal" :induct (fn2-env-j5-rows ids log c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j5-row fn2-env-j5-ops-kept fn2-env-j5-roles-kept
                                        fn2-env-owned-fences-kept fn2-env-j6-row-kept fn2-env-ops-frame
                                        fn2-commit-idp-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                                        fn2-machine-cb-fence-live-of-update-fn2-core-ops)
                                      (theory 'minimal-theory))
           :expand ((fn2-env-ops-kept x c)))))
(fn2-env-ops-kept-events fn2-env-post-accept
  (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 (fn2-core-ops c)))
(fn2-env-ops-kept-events fn2-env-post-clock (fn2-post-clock mono real flags (fn2-core-ops c)))
(fn2-env-ops-kept-events fn2-env-post-signal (fn2-post-signal bits (fn2-core-ops c)))
(fn2-env-j5-child-frame-events update-fn2-core-extents)
(fn2-env-j5-child-frame-events update-fn2-core-pool)
(defthm fn2-env-j6-readers-of-update-fn2-core-extents
  (and (equal (fn2-env-role-octets id role (update-fn2-core-extents x c)) (fn2-env-role-octets id role c))
       (equal (fn2-env-role-live id role (update-fn2-core-extents x c)) (fn2-env-role-live id role c)))
  :hints (("Goal" :in-theory (e/d (fn2-env-role-octets fn2-env-role-live)
                                  (fn2-env-op fn2-env-role-io fn2-env-pool-octets)))))
(defthm fn2-env-j6-row-of-update-fn2-core-extents
  (equal (fn2-env-j6-row id (update-fn2-core-extents x c)) (fn2-env-j6-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6-row fn2-env-j6-readers-of-update-fn2-core-extents
                                               fn2-env-j5-readers-of-update-fn2-core-extents
                                               fn2-commit-idp-of-update-fn2-core-extents
                                               fn2-machine-phase-of-update-fn2-core-extents
                                               fn2-machine-cb-issued-of-update-fn2-core-extents
                                               fn2-machine-cb-mode-of-update-fn2-core-extents
                                               fn2-machine-batch-no-of-update-fn2-core-extents)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-rows-of-update-fn2-core-extents
  (equal (fn2-env-j5-rows ids log (update-fn2-core-extents x c)) (fn2-env-j5-rows ids log c))
  :hints (("Goal" :induct (fn2-env-j5-rows ids log c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j5-row-of-update-fn2-core-extents
                                        fn2-env-j6-row-of-update-fn2-core-extents)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5-rows-frame-step
  ; :accept-result, :clock, :signal and :epoch keep J5 and J6
  (implies (and (fn2-corep c) (true-listp log) (fn2-env-j5-rows ids log c)
                (member-equal (fn2-env-tag action) '(:accept-result :clock :signal :epoch)))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (fn2-env-j5-rows ids (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                        fn2-env-begin-epoch fn2-env-j5-rows-kept fn2-env-post-accept-kept
                                        fn2-env-post-clock-kept fn2-env-post-signal-kept
                                        fn2-env-j5-rows-of-update-fn2-core-extents append-to-nil
                                        member-equal (:e member-equal) (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons
                                        (:e mv-nth))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5-row-loan-write
  ; :loan-write writes the pool only, which J5 does not read (J6 across it is
  ; FN2-POOL-CONSERVATION's: the loan's range is disjoint from the roles')
  (implies (equal (fn2-env-tag action) :loan-write)
           (equal (fn2-env-j5-row id log (mv-nth 1 (fn2-env-step action nil image rlog c)))
                  (fn2-env-j5-row id log c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-env-loan-write fn2-env-fill fn2-env-j5-row-of-update-fn2-core-pool
                                        (:e equal) (:e zp) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
(local (in-theory (enable fn2-env-pool-octets-is-logical fn2-env-logical-octets-prefix)))
(defun fn2-env-pool-row (s fn2-core)
  ; (VALID STATE OWNER-SLOT CAP) of pool row S
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (r)
    (if (and (natp s) (< s (fn2-pool-rows fn2-pool)))
        (list t (fn2-pool-state s fn2-pool) (fn2-pool-owner-slot s fn2-pool) (fn2-pool-cap s fn2-pool))
      (list nil))
    r))
(defun fn2-env-role-pool-ok (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((r (fn2-env-pool-row (nth 4 (fn2-env-role-io id role fn2-core)) fn2-core)))
    (and (nth 0 r)
         (member-equal (nth 1 r) (list *fn2-pool-state-workspace* *fn2-pool-state-leased-out*))
         (equal (nth 2 r) id) (natp (nth 3 r)) (<= *fn2-commit-unit-bytes* (nth 3 r)))))
(defun fn2-env-j6p-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (and (fn2-commit-idp id fn2-core)
                (member-equal (fn2-machine-phase id fn2-core)
                              (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*
                                    *fn2-commit-state-fence*)))
           (and (fn2-env-role-pool-ok id 0 fn2-core) (fn2-env-role-pool-ok id 1 fn2-core)
                (fn2-env-role-pool-ok id 2 fn2-core))))
(defthm fn2-env-role-octets-of-extent
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-role-pool-ok id role c))
           (equal (fn2-env-role-octets id role c)
                  (take *fn2-commit-unit-bytes* (fn2-core-pool-extent (nth 4 (fn2-env-role-io id role c)) c))))
  :hints (("Goal" :in-theory (e/d (fn2-env-role-octets fn2-env-role-pool-ok fn2-env-pool-row fn2-core-pool-semanticp
                                   fn2-core-pool-extent)
                                  (fn2-env-role-io fn2-env-pool-octets fn2-pool-logical-octets fn2-pool-semanticp))
           :use ((:instance fn2-env-pool-octets-in-extent (fn2-pool (fn2-core-pool c))
                            (s (nth 4 (fn2-env-role-io id role c))) (k *fn2-commit-unit-bytes*))))))
(defthm fn2-env-pool-fill-keeps-row
  ; a loan's fill never touches a row that is not leased in: its extent, state,
  ; owner, place and size stay, and the pool stays semantic
  (implies (and (fn2-pool-semanticp p) (natp r) (< r (fn2-pool-rows p))
                (not (equal (fn2-pool-state r p) *fn2-pool-state-leased-in*)))
           (let ((q (fn2-env-pool-fill rslot rgen slot gen idx octets p)))
             (and (fn2-pool-semanticp q)
                  (equal (fn2-pool-rows q) (fn2-pool-rows p))
                  (equal (fn2-pool-cap r q) (fn2-pool-cap r p))
                  (equal (fn2-pool-base r q) (fn2-pool-base r p))
                  (equal (fn2-pool-state r q) (fn2-pool-state r p))
                  (equal (fn2-pool-gen r q) (fn2-pool-gen r p))
                  (equal (fn2-pool-owner-slot r q) (fn2-pool-owner-slot r p))
                  (equal (fn2-pool-logical-octets (fn2-pool-cap r p) (fn2-pool-base r p) q)
                         (fn2-pool-logical-octets (fn2-pool-cap r p) (fn2-pool-base r p) p)))))
  :hints (("Goal" :induct (fn2-env-pool-fill rslot rgen slot gen idx octets p)
           :in-theory (disable fn2-pool-semanticp fn2-pool-logical-octets fn2-pool-adapter-write
                               fn2-pool-base fn2-pool-cap fn2-pool-state fn2-pool-gen fn2-pool-owner-slot fn2-pool-rows))))
(defthm fn2-env-pool-fill-semanticp
  (implies (fn2-pool-semanticp p)
           (fn2-pool-semanticp (fn2-env-pool-fill rslot rgen slot gen idx octets p)))
  :hints (("Goal" :induct (fn2-env-pool-fill rslot rgen slot gen idx octets p)
           :in-theory (disable fn2-pool-semanticp fn2-pool-adapter-write))))
(defthm fn2-env-fill-semanticp
  (implies (fn2-core-pool-semanticp c)
           (fn2-core-pool-semanticp (fn2-env-fill rslot rgen slot gen idx octets c)))
  :hints (("Goal" :in-theory (e/d (fn2-env-fill fn2-core-pool-semanticp) (fn2-pool-semanticp fn2-env-pool-fill)))))
(defthm fn2-env-fill-is-pool-update
  (equal (fn2-env-fill rslot rgen slot gen idx octets c)
         (update-fn2-core-pool (fn2-env-pool-fill rslot rgen slot gen idx octets (fn2-core-pool c)) c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-fill))))
(defthm fn2-env-core-pool-of-update-pool
  (equal (fn2-core-pool (update-fn2-core-pool x c)) x)
  :hints (("Goal" :in-theory (enable fn2-core-pool update-fn2-core-pool))))
(defthm fn2-env-fill-keeps-role
  ; a loan's fill keeps a role's pool row and its octets
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-role-pool-ok id role c))
           (let ((c2 (fn2-env-fill rslot rgen slot gen idx octets c)))
             (and (fn2-env-role-pool-ok id role c2)
                  (equal (fn2-env-role-octets id role c2) (fn2-env-role-octets id role c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-core-pool-extent fn2-env-role-pool-ok fn2-env-pool-row fn2-core-pool-semanticp
                                        fn2-env-core-pool-of-update-pool fn2-env-j5-readers-of-update-fn2-core-pool
                                        (:e member-equal) member-equal car-cons cdr-cons (:e nth) nth-0-cons nth-add1)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-fill-is-pool-update)
                 (:instance fn2-env-role-octets-of-extent)
                 (:instance fn2-env-role-octets-of-extent (c (fn2-env-fill rslot rgen slot gen idx octets c)))
                 (:instance fn2-env-fill-semanticp)
                 (:instance fn2-env-pool-fill-keeps-row (p (fn2-core-pool c))
                            (r (nth 4 (fn2-env-role-io id role c))))))))
(defthm fn2-env-fill-machine-frame
  (let ((c2 (fn2-env-fill rslot rgen slot gen idx octets c)))
    (and (equal (fn2-commit-idp id c2) (fn2-commit-idp id c))
         (equal (fn2-machine-phase id c2) (fn2-machine-phase id c))
         (equal (fn2-machine-cb-issued id c2) (fn2-machine-cb-issued id c))
         (equal (fn2-machine-cb-mode id c2) (fn2-machine-cb-mode id c))
         (equal (fn2-machine-batch-no id c2) (fn2-machine-batch-no id c))
         (equal (fn2-env-role-io id role c2) (fn2-env-role-io id role c))
         (equal (fn2-env-op s c2) (fn2-env-op s c))
         (equal (fn2-env-role-live id role c2) (fn2-env-role-live id role c))))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-role-live fn2-commit-idp-of-update-fn2-core-pool
                                               fn2-machine-phase-of-update-fn2-core-pool fn2-machine-cb-issued-of-update-fn2-core-pool
                                               fn2-machine-cb-mode-of-update-fn2-core-pool fn2-machine-batch-no-of-update-fn2-core-pool
                                               fn2-env-j5-readers-of-update-fn2-core-pool)
                                             (theory 'minimal-theory))
           :use ((:instance fn2-env-fill-is-pool-update)))))
(defthm fn2-env-j6-fill
  ; J6 and its pool rows survive a loan's fill
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-j6-row id c) (fn2-env-j6p-row id c))
           (let ((c2 (fn2-env-fill rslot rgen slot gen idx octets c)))
             (and (fn2-env-j6-row id c2) (fn2-env-j6p-row id c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6-row fn2-env-j6p-row fn2-env-fill-machine-frame fn2-env-fill-keeps-role)
                                      (theory 'minimal-theory)))))
(defun fn2-env-j6p-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j6p-row (car ids) fn2-core) (fn2-env-j6p-rows (cdr ids) fn2-core))))
;; J6L, THE ROLES' LEASES. Through the write phases the three roles' pool
;; rows are three rows, each at the generation its unit records, and a role
;; whose write is live holds its row's lease (leased-out): the harvest's
;; release of that write's range is accepted. Kept by every host step and
;; by :admit (FN2-ENV-J5-ROWS-ADMIT-STEP); owed: J6L across :turn, and a
;; foreign operation's release-out (no owner check, pool.lisp's A2) never
;; hits a live role's row.
(defun fn2-env-role-lease (id role fn2-core)
  ; (STATE GEN) of the role's pool row
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((s (nth 4 (fn2-env-role-io id role fn2-core))))
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (r)
      (if (and (natp s) (< s (fn2-pool-rows fn2-pool)))
          (list (fn2-pool-state s fn2-pool) (fn2-pool-gen s fn2-pool))
        nil)
      r)))
(defun fn2-env-role-lease-ok (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((r (fn2-env-role-lease id role fn2-core)))
    (and (equal (nth 1 r) (nth 5 (fn2-env-role-io id role fn2-core)))
         (implies (fn2-env-role-live id role fn2-core)
                  (equal (nth 0 r) *fn2-pool-state-leased-out*)))))
(defun fn2-env-j6l-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (and (fn2-commit-idp id fn2-core)
                (member-equal (fn2-machine-phase id fn2-core)
                              (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*
                                    *fn2-commit-state-fence*)))
           (let ((s0 (nth 4 (fn2-env-role-io id 0 fn2-core))) (s1 (nth 4 (fn2-env-role-io id 1 fn2-core)))
                 (s2 (nth 4 (fn2-env-role-io id 2 fn2-core))))
             (and (not (equal s0 s1)) (not (equal s0 s2)) (not (equal s1 s2))
                  (fn2-env-role-lease-ok id 0 fn2-core) (fn2-env-role-lease-ok id 1 fn2-core)
                  (fn2-env-role-lease-ok id 2 fn2-core)))))
(defun fn2-env-j6l-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j6l-row (car ids) fn2-core) (fn2-env-j6l-rows (cdr ids) fn2-core))))
;; J6P AND J6L ACROSS THE HOST STEPS. Both read the roles' units, their pool
;; rows and (J6L) whether each role's write is live. A post, an accept, a
;; clock and a signal write the ops table only, keeping every role's
;; liveness (FN2-ENV-ROLE-LIVE-POST, -KEPT); a take writes the ops table only,
;; and a role live after it was live before (FN2-ENV-ROLE-LIVE-TAKE); an
;; epoch writes the extents; a loan's fill writes a leased-in row's octets
;; only, which no role's row is (J6P), keeping each role row's state and
;; generation (FN2-ENV-POOL-FILL-KEEPS-ROW).
(defthm fn2-env-core-pool-child-frames
  (and (equal (fn2-core-pool (update-fn2-core-ops x c)) (fn2-core-pool c))
       (equal (fn2-core-pool (update-fn2-core-extents x c)) (fn2-core-pool c)))
  :hints (("Goal" :in-theory (enable fn2-core-pool update-fn2-core-ops update-fn2-core-extents))))
(defthm fn2-env-pool-readers-of-update-ops
  (and (equal (fn2-env-pool-row s (update-fn2-core-ops x c)) (fn2-env-pool-row s c))
       (equal (fn2-env-role-lease id role (update-fn2-core-ops x c)) (fn2-env-role-lease id role c)))
  :hints (("Goal" :in-theory '(fn2-env-pool-row fn2-env-role-lease fn2-env-core-pool-child-frames fn2-env-ops-frame))))
(defthm fn2-env-j6p-row-of-update-ops
  (equal (fn2-env-j6p-row id (update-fn2-core-ops x c)) (fn2-env-j6p-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6p-row fn2-env-role-pool-ok fn2-env-pool-readers-of-update-ops
                                               fn2-env-ops-frame fn2-commit-idp-of-update-fn2-core-ops
                                               fn2-machine-phase-of-update-fn2-core-ops)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j6l-row-of-update-ops
  ; an ops-table write that keeps every role's liveness keeps J6L
  (implies (and (equal (fn2-env-role-live id 0 (update-fn2-core-ops x c)) (fn2-env-role-live id 0 c))
                (equal (fn2-env-role-live id 1 (update-fn2-core-ops x c)) (fn2-env-role-live id 1 c))
                (equal (fn2-env-role-live id 2 (update-fn2-core-ops x c)) (fn2-env-role-live id 2 c)))
           (equal (fn2-env-j6l-row id (update-fn2-core-ops x c)) (fn2-env-j6l-row id c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6l-row fn2-env-role-lease-ok fn2-env-pool-readers-of-update-ops
                                               fn2-env-ops-frame fn2-commit-idp-of-update-fn2-core-ops
                                               fn2-machine-phase-of-update-fn2-core-ops)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j6l-row-post
  (equal (fn2-env-j6l-row id (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-j6l-row id c))
  :hints (("Goal" :in-theory '(fn2-env-role-live-post)
           :use ((:instance fn2-env-j6l-row-of-update-ops (x (fn2-env-pr-ops)))))))
(defthm fn2-env-j6l-row-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-j6l-row id (update-fn2-core-ops x c)) (fn2-env-j6l-row id c)))
  :hints (("Goal" :in-theory '(fn2-env-role-live-kept)
           :use ((:instance fn2-env-j6l-row-of-update-ops)))))
(defthm fn2-env-take-core-pool
  (equal (fn2-core-pool (mv-nth 1 (fn2-env-take nil image c))) (fn2-core-pool c))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish fn2-env-core-pool-child-frames)
                           (fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-env-octets
                            fn2-outbox-ack fn2-op-finish fn2-env-fill)))))
(defthm fn2-env-take-pool-frame
  (let ((c2 (mv-nth 1 (fn2-env-take nil image c))))
    (and (equal (fn2-env-pool-row s c2) (fn2-env-pool-row s c))
         (equal (fn2-env-role-lease id role c2) (fn2-env-role-lease id role c))))
  :hints (("Goal" :in-theory '(fn2-env-pool-row fn2-env-role-lease fn2-env-take-core-pool fn2-env-take-frames))))
(defthm fn2-env-j6p-j6l-row-take
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (and (equal (fn2-env-j6p-row id (fn2-env-tk-c)) (fn2-env-j6p-row id c))
                (implies (fn2-env-j6l-row id c) (fn2-env-j6l-row id (fn2-env-tk-c)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6p-row fn2-env-role-pool-ok fn2-env-j6l-row fn2-env-role-lease-ok
                                        fn2-env-take-pool-frame fn2-env-take-frames)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-role-live-take (role 0)) (:instance fn2-env-role-live-take (role 1))
                 (:instance fn2-env-role-live-take (role 2))))))
(defthm fn2-env-pool-readers-of-update-extents
  (and (equal (fn2-env-pool-row s (update-fn2-core-extents x c)) (fn2-env-pool-row s c))
       (equal (fn2-env-role-lease id role (update-fn2-core-extents x c)) (fn2-env-role-lease id role c)))
  :hints (("Goal" :in-theory '(fn2-env-pool-row fn2-env-role-lease fn2-env-core-pool-child-frames
                               fn2-env-j5-readers-of-update-fn2-core-extents))))
(defthm fn2-env-j6p-j6l-row-of-update-extents
  (and (equal (fn2-env-j6p-row id (update-fn2-core-extents x c)) (fn2-env-j6p-row id c))
       (equal (fn2-env-j6l-row id (update-fn2-core-extents x c)) (fn2-env-j6l-row id c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6p-row fn2-env-role-pool-ok fn2-env-j6l-row fn2-env-role-lease-ok
                                               fn2-env-pool-readers-of-update-extents fn2-env-j5-readers-of-update-fn2-core-extents
                                               fn2-env-j6-readers-of-update-fn2-core-extents
                                               fn2-commit-idp-of-update-fn2-core-extents fn2-machine-phase-of-update-fn2-core-extents)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-fill-keeps-lease
  ; a loan's fill keeps the state and generation of a role's pool row J6P holds
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-role-pool-ok id role c))
           (equal (fn2-env-role-lease id role (fn2-env-fill rslot rgen slot gen idx octets c))
                  (fn2-env-role-lease id role c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-role-lease fn2-env-role-pool-ok fn2-env-pool-row fn2-core-pool-semanticp
                                        fn2-env-core-pool-of-update-pool fn2-env-j5-readers-of-update-fn2-core-pool
                                        (:e member-equal) member-equal car-cons cdr-cons (:e nth) nth-0-cons nth-add1)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-fill-is-pool-update)
                 (:instance fn2-env-pool-fill-keeps-row (p (fn2-core-pool c))
                            (r (nth 4 (fn2-env-role-io id role c))))))))
(defthm fn2-env-j6l-fill
  ; J6L survives a loan's fill
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-j6p-row id c) (fn2-env-j6l-row id c))
           (fn2-env-j6l-row id (fn2-env-fill rslot rgen slot gen idx octets c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6p-row fn2-env-j6l-row fn2-env-role-lease-ok fn2-env-fill-machine-frame
                                        fn2-env-fill-keeps-lease)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6p-fill
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-j6p-row id c))
           (fn2-env-j6p-row id (fn2-env-fill rslot rgen slot gen idx octets c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6p-row fn2-env-fill-machine-frame fn2-env-fill-keeps-role)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6p-j6l-row-host-step
  ; every step but :turn and :admit keeps J6P and J6L at a commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-core-pool-semanticp c)
                (fn2-env-j6p-row id c) (fn2-env-j6l-row id c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (let ((after (mv-nth 1 (fn2-env-step action nil image rlog c))))
             (and (fn2-env-j6p-row id after) (fn2-env-j6l-row id after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                        fn2-env-begin-epoch fn2-env-loan-write fn2-env-post-step
                                        fn2-env-post-accept-kept fn2-env-post-clock-kept fn2-env-post-signal-kept
                                        fn2-env-j6l-row-kept fn2-env-j6l-row-post fn2-env-j6p-row-of-update-ops
                                        fn2-env-j6p-j6l-row-of-update-extents fn2-env-j6p-j6l-row-take
                                        fn2-env-j6p-fill fn2-env-j6l-fill
                                        member-eq (:e member-eq) (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6p-j6l-rows-host-step
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-core-pool-semanticp c)
                (fn2-env-j6p-rows ids c) (fn2-env-j6l-rows ids c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (let ((after (mv-nth 1 (fn2-env-step action nil image rlog c))))
             (and (fn2-env-j6p-rows ids after) (fn2-env-j6l-rows ids after))))
  :hints (("Goal" :induct (fn2-env-j6p-rows ids c)
           :in-theory (union-theories '(fn2-env-j6p-rows fn2-env-j6l-rows fn2-env-j6p-j6l-row-host-step)
                                      (theory 'minimal-theory)))))
;; THE HARVEST'S RELEASE IS ACCEPTED. A role write's harvest releases its
;; range's pool row (fn2-harvest-one's release-out branch: a write result,
;; FN2-ENV-J5-EVENT-OK). At a write phase J6P names the role's row (valid, a
;; unit long) and J6L its lease (the unit's generation, leased out while the
;; write is live); a semantic pool's leased-out row has a lease out
;; (FN2-ENV-POOL-LEASED-OUT-COUNT), so the release is accepted
;; (FN2-ENV-ROLE-RELEASE-ACCEPTED). The harvest-one delivery theorem built on
;; it is the next statement (lanedumps/proof-floor-continue.md).
;; J6S, THE SETTLING ROLES. In :draining, :uncertain and :dropping a role
;; write may still be live (the row waits for pending writes before it
;; releases its pool rows); while it is, its pool row is J6P's and its lease
;; J6L's, so its harvest's release is accepted (FN2-ENV-ROLE-RELEASE-ACCEPTED).
(defun fn2-env-role-settle-ok (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (fn2-env-role-live id role fn2-core)
           (and (fn2-env-role-pool-ok id role fn2-core) (fn2-env-role-lease-ok id role fn2-core))))
(defun fn2-env-j6s-row (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (and (fn2-commit-idp id fn2-core)
                (member-equal (fn2-machine-phase id fn2-core)
                              (list *fn2-commit-state-draining* *fn2-commit-state-uncertain*
                                    *fn2-commit-state-dropping*)))
           (and (fn2-env-role-settle-ok id 0 fn2-core) (fn2-env-role-settle-ok id 1 fn2-core)
                (fn2-env-role-settle-ok id 2 fn2-core))))
(defun fn2-env-j6s-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) t
    (and (fn2-env-j6s-row (car ids) fn2-core) (fn2-env-j6s-rows (cdr ids) fn2-core))))
(defthm fn2-env-j6s-row-post
  (equal (fn2-env-j6s-row id (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-j6s-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-role-pool-ok fn2-env-role-lease-ok
                                               fn2-env-pool-readers-of-update-ops fn2-env-ops-frame fn2-env-role-live-post
                                               fn2-commit-idp-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j6s-row-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-j6s-row id (update-fn2-core-ops x c)) (fn2-env-j6s-row id c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-role-pool-ok fn2-env-role-lease-ok
                                               fn2-env-pool-readers-of-update-ops fn2-env-ops-frame fn2-env-role-live-kept
                                               fn2-commit-idp-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j6s-row-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j6s-row id c))
           (fn2-env-j6s-row id (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-role-pool-ok fn2-env-role-lease-ok
                                        fn2-env-take-pool-frame fn2-env-take-frames)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-role-live-take (role 0)) (:instance fn2-env-role-live-take (role 1))
                 (:instance fn2-env-role-live-take (role 2))))))
(defthm fn2-env-j6s-row-of-update-extents
  (equal (fn2-env-j6s-row id (update-fn2-core-extents x c)) (fn2-env-j6s-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-role-pool-ok fn2-env-role-lease-ok
                                               fn2-env-pool-readers-of-update-extents fn2-env-j5-readers-of-update-fn2-core-extents
                                               fn2-env-j6-readers-of-update-fn2-core-extents
                                               fn2-commit-idp-of-update-fn2-core-extents fn2-machine-phase-of-update-fn2-core-extents)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j6s-fill
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-j6s-row id c))
           (fn2-env-j6s-row id (fn2-env-fill rslot rgen slot gen idx octets c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-role-lease-ok fn2-env-fill-machine-frame
                                        fn2-env-fill-keeps-role fn2-env-fill-keeps-lease)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6s-row-host-step
  ; every step but :turn and :admit keeps J6S at a commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-core-pool-semanticp c) (fn2-env-j6s-row id c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (fn2-env-j6s-row id (mv-nth 1 (fn2-env-step action nil image rlog c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                        fn2-env-begin-epoch fn2-env-loan-write fn2-env-post-step
                                        fn2-env-post-accept-kept fn2-env-post-clock-kept fn2-env-post-signal-kept
                                        fn2-env-j6s-row-kept fn2-env-j6s-row-post fn2-env-j6s-row-of-update-extents
                                        fn2-env-j6s-row-take fn2-env-j6s-fill
                                        member-eq (:e member-eq) (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j6s-rows-host-step
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-core-pool-semanticp c) (fn2-env-j6s-rows ids c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (fn2-env-j6s-rows ids (mv-nth 1 (fn2-env-step action nil image rlog c))))
  :hints (("Goal" :induct (fn2-env-j6s-rows ids c)
           :in-theory (union-theories '(fn2-env-j6s-rows fn2-env-j6s-row-host-step) (theory 'minimal-theory)))))
;; J5E ACROSS THE HOST STEPS. A post, an accept, a clock and a signal keep
;; every role's liveness, every owned fence and the machine table; a take
;; keeps the owned fences and the machine table, and a role live after it
;; was live before (FN2-ENV-ROLE-LIVE-TAKE); an epoch and a loan's fill
;; write the extents or the pool, which J5E does not read.
(make-event (value (cons 'progn (fn2-env-j-reader-frame-events
  '((fn2-machine-pending id) (fn2-machine-cb-bytes id)) '(update-fn2-core-ops update-fn2-core-pool update-fn2-core-extents)))))
(defthm fn2-env-j5e-row-of-weaker
  ; J5E survives a step that keeps the row's phase, makes no role live and
  ; no owned fence, and takes nothing from its pending count
  (implies (and (fn2-env-j5e-row id a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-bytes id b) (fn2-machine-cb-bytes id a))
                (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a))
                (implies (fn2-env-role-live id 0 b) (fn2-env-role-live id 0 a))
                (implies (fn2-env-role-live id 1 b) (fn2-env-role-live id 1 a))
                (implies (fn2-env-role-live id 2 b) (fn2-env-role-live id 2 a))
                (<= (fn2-env-owned-fences 0 (fn2-env-ops-rows b) id b) (fn2-env-owned-fences 0 (fn2-env-ops-rows a) id a))
                (<= (nfix (fn2-machine-pending id a)) (nfix (fn2-machine-pending id b))))
           (fn2-env-j5e-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live fn2-env-b2n nfix
                               (:type-prescription fn2-env-owned-fences)))))
(defthm fn2-env-j5e-row-post
  (equal (fn2-env-j5e-row id (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-j5e-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live
                                               fn2-machine-cb-bytes-of-update-fn2-core-ops fn2-machine-cb-done-of-update-fn2-core-ops
                                               fn2-env-role-live-post fn2-env-owned-fences-post fn2-env-ops-rows-post
                                               fn2-commit-idp-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                                               fn2-machine-pending-of-update-fn2-core-ops)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5e-row-kept
  (implies (fn2-env-ops-kept x c)
           (equal (fn2-env-j5e-row id (update-fn2-core-ops x c)) (fn2-env-j5e-row id c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live
                                               fn2-machine-cb-bytes-of-update-fn2-core-ops fn2-machine-cb-done-of-update-fn2-core-ops
                                               fn2-env-role-live-kept fn2-env-owned-fences-kept fn2-env-ops-frame
                                               fn2-commit-idp-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                                               fn2-machine-pending-of-update-fn2-core-ops)
                                             (theory 'minimal-theory))
           :expand ((fn2-env-ops-kept x c)))))
(defthm fn2-env-pending-take
  (and (equal (fn2-machine-pending id (mv-nth 1 (fn2-env-take nil image c))) (fn2-machine-pending id c))
       (equal (fn2-machine-cb-bytes id (mv-nth 1 (fn2-env-take nil image c))) (fn2-machine-cb-bytes id c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish fn2-env-fill)
                           (fn2-host-outbox-peek fn2-host-action fn2-host-op-span fn2-env-octets
                            fn2-outbox-ack fn2-op-finish fn2-env-pool-fill)))))
(defthm fn2-env-j5e-row-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5e-row id c))
           (fn2-env-j5e-row id (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-take-frames fn2-env-owned-fences-take fn2-env-ops-rows-take fn2-env-pending-take)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-j5e-row-of-weaker (a c) (b (fn2-env-tk-c)))
                 (:instance fn2-env-role-live-take (role 0)) (:instance fn2-env-role-live-take (role 1))
                 (:instance fn2-env-role-live-take (role 2))))))
(defthm fn2-env-j5e-row-of-update-fn2-core-extents
  (equal (fn2-env-j5e-row id (update-fn2-core-extents x c)) (fn2-env-j5e-row id c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live
                                               fn2-machine-cb-bytes-of-update-fn2-core-extents fn2-machine-cb-done-of-update-fn2-core-extents
                                               fn2-env-j6-readers-of-update-fn2-core-extents fn2-env-j5-readers-of-update-fn2-core-extents
                                               fn2-env-owned-fences-of-update-fn2-core-extents
                                               fn2-commit-idp-of-update-fn2-core-extents fn2-machine-phase-of-update-fn2-core-extents
                                               fn2-machine-pending-of-update-fn2-core-extents)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5e-row-of-update-fn2-core-pool
  (equal (fn2-env-j5e-row id (update-fn2-core-pool x c)) (fn2-env-j5e-row id c))
  :hints (("Goal" :in-theory (e/d (fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live fn2-env-role-live)
                                  (fn2-env-owned-fences fn2-env-op fn2-env-role-io fn2-env-ops-rows)))))
(defthm fn2-env-j5e-fill
  (equal (fn2-env-j5e-row id (fn2-env-fill rslot rgen slot gen idx octets c)) (fn2-env-j5e-row id c))
  :hints (("Goal" :in-theory '(fn2-env-j5e-row-of-update-fn2-core-pool) :use ((:instance fn2-env-fill-is-pool-update)))))
(defthm fn2-env-j5e-row-host-step
  ; every step but :turn and :admit keeps J5E at a commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5e-row id c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (fn2-env-j5e-row id (mv-nth 1 (fn2-env-step action nil image rlog c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                        fn2-env-begin-epoch fn2-env-loan-write fn2-env-post-step
                                        fn2-env-post-accept-kept fn2-env-post-clock-kept fn2-env-post-signal-kept
                                        fn2-env-j5e-row-kept fn2-env-j5e-row-post fn2-env-j5e-row-of-update-fn2-core-extents
                                        fn2-env-j5e-row-take fn2-env-j5e-fill
                                        member-eq (:e member-eq) (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5e-rows-host-step
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5e-rows ids c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (fn2-env-j5e-rows ids (mv-nth 1 (fn2-env-step action nil image rlog c))))
  :hints (("Goal" :induct (fn2-env-j5e-rows ids c)
           :in-theory (union-theories '(fn2-env-j5e-rows fn2-env-j5e-row-host-step) (theory 'minimal-theory)))))
(defthm fn2-env-j6-role-oks
  ; J6P and J6L at a write phase name each role's pool row and lease
  (implies (and (fn2-commit-idp id c)
                (member-equal (fn2-machine-phase id c)
                              (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write* *fn2-commit-state-fence*))
                (fn2-env-j6p-row id c) (fn2-env-j6l-row id c) (natp role) (< role 3))
           (and (fn2-env-role-pool-ok id role c) (fn2-env-role-lease-ok id role c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((equal role 0) (equal role 1) (equal role 2))
           :in-theory (union-theories '(fn2-env-j6p-row fn2-env-j6l-row natp (:e natp) (:e <)) (theory 'minimal-theory)))))
(defthm fn2-env-role-release-accepted
  ; a live role's pool row, J6P's and J6L's, may be released
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-role-pool-ok id role c) (fn2-env-role-lease-ok id role c)
                (fn2-env-role-live id role c))
           (equal (mv-nth 0 (fn2-pool-release-out (nth 4 (fn2-env-role-io id role c)) (nth 5 (fn2-env-role-io id role c))
                                                  (fn2-core-pool c)))
                  :ok))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-role-pool-ok fn2-env-role-lease-ok
                                        fn2-env-pool-row fn2-env-role-lease fn2-core-pool-semanticp
                                        car-cons cdr-cons nth-0-cons nth-add1 (:e zp) (:e nth) (:e equal) (:e member-equal)
                                        member-equal natp)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-release-out-accepted (p (fn2-core-pool c)) (i (nth 4 (fn2-env-role-io id role c)))
                            (g (nth 5 (fn2-env-role-io id role c))))))))
(defthm fn2-env-j5-rows-loan-write-fill
  (implies (and (fn2-core-pool-semanticp c) (fn2-env-j5-rows ids log c) (fn2-env-j6p-rows ids c))
           (let ((c2 (fn2-env-fill rslot rgen slot gen idx octets c)))
             (and (fn2-env-j5-rows ids log c2) (fn2-env-j6p-rows ids c2))))
  :hints (("Goal" :induct (fn2-env-j6p-rows ids c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j6p-rows fn2-env-j6-fill)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-fill-is-pool-update)
                                (:instance fn2-env-j5-row-of-update-fn2-core-pool (id (car ids))
                                           (x (fn2-env-pool-fill rslot rgen slot gen idx octets (fn2-core-pool c))))
                                (:instance fn2-env-j6-fill (id (car ids)))))))
(defthm fn2-env-j5-rows-loan-write-step
  ; :loan-write keeps J5, J6 and their pool rows, and the pool stays semantic
  (implies (and (equal (fn2-env-tag action) :loan-write)
                (fn2-core-pool-semanticp c) (true-listp log) (fn2-env-j5-rows ids log c) (fn2-env-j6p-rows ids c))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (and (fn2-env-j5-rows ids (append log (if entry (list entry) nil)) after)
                  (fn2-env-j6p-rows ids after)
                  (fn2-core-pool-semanticp after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-rows-loan-write-fill fn2-env-fill-semanticp append-to-nil
                                        fn2-env-step fn2-env-loan-write (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
;; J5 ACROSS :ADMIT, the ops table. Admission's callees write the pool,
;; sched, control, commit table, extents, members, settled, commit-io and
;; root children, never the ops table (FN2-ENV-OK carried by each callee):
;; every op and the ops rows are unchanged (FN2-ENV-OP-OF-ADMIT,
;; FN2-ENV-OPS-ROWS-OF-ADMIT).
(fn2-defview fn2-env-ok :carrier fn2-core
  :select ((fn2-ops :whole t)))
(defthm fn2-env-ok-view-equivalence
  (equal (fn2-env-ok b a) (equal (nth 1 b) (nth 1 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-ok fn2-ctf-dir fn2-machines-directory-keeps))))
(in-theory (enable fn2-env-ok))
(defthm fn2-env-ok-refl (fn2-env-ok a a))
(defthm fn2-env-ok-of-nth
  (implies (and (equal (nth 1 b) (nth 1 x)) (fn2-env-ok x a)) (fn2-env-ok b a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-ok))))
(in-theory (disable fn2-env-ok))

(fn2-with-column-projections (fn2-env-ok)
(defthm fn2-commit-reserve-pools-fn2-env-ok
  (implies (fn2-env-ok fn2-core fn2-rel-c0)
           (fn2-env-ok (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ok) clause world)))))
(fn2-with-column-projections (fn2-env-ok)
(defthm fn2-env-commit-start-ok
  (implies (fn2-env-ok fn2-core c0)
           (fn2-env-ok (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)) c0))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'fn2-column-projection-base))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ok) clause world)))))
(fn2-with-column-projections (fn2-env-ok)
(defthm fn2-env-admit-ok
  ; admission never writes the ops table
  (implies (fn2-env-ok fn2-core c0)
           (fn2-env-ok (fn2-env-admit members mode fn2-core) c0))
  :hints (("Goal" :in-theory (union-theories (theory 'fn2-column-projection-base) (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-ok
                                                 )
                                             (theory 'fn2-arm-frame-base))))
         (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ok) clause world)))))
(defthm fn2-env-op-of-admit
  (equal (fn2-env-op s (fn2-env-admit members mode c)) (fn2-env-op s c))
  :hints (("Goal" :in-theory (e/d (fn2-env-ok fn2-env-op fn2-core-ops) (fn2-env-admit))
           :use ((:instance fn2-env-admit-ok (fn2-core c) (c0 c))))))
(defthm fn2-env-ops-rows-of-admit
  (equal (fn2-env-ops-rows (fn2-env-admit members mode c)) (fn2-env-ops-rows c))
  :hints (("Goal" :in-theory (e/d (fn2-env-ok fn2-env-ops-rows fn2-core-ops) (fn2-env-admit))
           :use ((:instance fn2-env-admit-ok (fn2-core c) (c0 c))))))
;; J5 AND J6 ACROSS :ADMIT, THE OTHER ROW. J5, J6 and J6P at a commit row
;; read its evidence alone (FN2-ENV-J5-POINT-CONGRUENCE, FN2-ENV-J5-KEPT-TRANSFER):
;; the ops table (OK), the directory and its commit columns (TK, MK), its
;; three units (commit-io), their extents (EK) and their pool rows. Every
;; admission callee keeps them for every row but the admitted one: by its
;; producer footprint for the views; a pool reservation leaves every row that
;; is not free and every octet (FN2-ENV-CORE-RESERVE-UNIT-KEPT); a release by
;; another owner leaves J6P's rows (FN2-ENV-CORE-RELEASE-UNIT-KEPT); the
;; extent reservation and a saved pool row write only the admitted row's
;; units (FN2-ENV-RESERVE-EXTENT-UNIT-KEPT, FN2-ENV-SAVE-POOL-UNIT-KEPT).
(defun-nx fn2-env-j5-same-evidence (id a b)
  ; the ops table and the columns, units and octets J5 and J6 read of
  ; row ID agree in cores A and B
  (and (fn2-env-ok b a)
       (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
       (equal (fn2-commit-row id b) (fn2-commit-row id a))
       (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
       (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
       (equal (fn2-machine-cb-issued id b) (fn2-machine-cb-issued id a))
       (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a))
       (equal (fn2-machine-cb-bytes id b) (fn2-machine-cb-bytes id a))
       (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
       (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
       (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
       (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
       (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))
       (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
       (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
       (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
       (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a))
       (equal (fn2-env-role-extent id 0 b) (fn2-env-role-extent id 0 a))
       (equal (fn2-env-role-extent id 1 b) (fn2-env-role-extent id 1 a))
       (equal (fn2-env-role-extent id 2 b) (fn2-env-role-extent id 2 a))
       (equal (fn2-env-role-octets id 0 b) (fn2-env-role-octets id 0 a))
       (equal (fn2-env-role-octets id 1 b) (fn2-env-role-octets id 1 a))
       (equal (fn2-env-role-octets id 2 b) (fn2-env-role-octets id 2 a))))
(defthm fn2-env-op-of-ok
  (implies (fn2-env-ok b a)
           (and (equal (fn2-env-op s b) (fn2-env-op s a))
                (equal (fn2-env-ops-rows b) (fn2-env-ops-rows a))))
  :hints (("Goal" :in-theory (enable fn2-env-ok fn2-env-op fn2-env-ops-rows fn2-core-ops))))
(defthm fn2-env-owned-fence-at-of-ok
  (implies (and (fn2-env-ok b a) (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (equal (fn2-env-owned-fence-at s id b) (fn2-env-owned-fence-at s id a)))
  :hints (("Goal" :in-theory '(fn2-env-owned-fence-at fn2-env-op-of-ok))))
(defthm fn2-env-owned-fences-of-ok
  (implies (and (fn2-env-ok b a) (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (equal (fn2-env-owned-fences s k id b) (fn2-env-owned-fences s k id a)))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id a)
           :in-theory (union-theories '(fn2-env-owned-fences fn2-env-owned-fence-at-of-ok) (theory 'minimal-theory)))))
(defthm fn2-env-j5-evidence-reads
  (implies (fn2-env-j5-same-evidence id a b)
           (and (fn2-env-ok b a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
                (equal (fn2-machine-cb-issued id b) (fn2-machine-cb-issued id a))
                (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a))
                (equal (fn2-machine-cb-bytes id b) (fn2-machine-cb-bytes id a))
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
                (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))
                (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))))
  :hints (("Goal" :in-theory '(fn2-env-j5-same-evidence))))
(defthm fn2-env-j5-evidence-role-reads
  (implies (and (fn2-env-j5-same-evidence id a b) (natp role) (< role 3))
           (and (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a))
                (equal (fn2-env-role-extent id role b) (fn2-env-role-extent id role a))
                (equal (fn2-env-role-octets id role b) (fn2-env-role-octets id role a))))
  :hints (("Goal" :in-theory '(fn2-env-j5-same-evidence natp) :cases ((equal role 0) (equal role 1) (equal role 2)))))
(defthm fn2-env-j5-evidence-io
  (implies (and (fn2-env-j5-same-evidence id a b) (natp k) (< k 3))
           (equal (fn2-env-io (+ (* 3 (fn2-commit-row id a)) k) b) (fn2-env-io (+ (* 3 (fn2-commit-row id a)) k) a)))
  :hints (("Goal" :in-theory '(fn2-env-role-io fn2-env-j5-evidence-reads)
           :use ((:instance fn2-env-j5-evidence-role-reads (role k))))))
(defthm fn2-env-j5-evidence-op
  (implies (fn2-env-j5-same-evidence id a b)
           (and (equal (fn2-env-op s b) (fn2-env-op s a))
                (equal (fn2-env-ops-rows b) (fn2-env-ops-rows a))))
  :hints (("Goal" :in-theory nil :use ((:instance fn2-env-j5-evidence-reads) (:instance fn2-env-op-of-ok)))))
(defthm fn2-env-role-written-congruence
  (implies (and (fn2-env-j5-same-evidence id a b) (natp role) (< role 3))
           (equal (fn2-env-role-written id role f log b) (fn2-env-role-written id role f log a)))
  :hints (("Goal" :in-theory '(fn2-env-role-written fn2-env-role-offset-of-extent fn2-env-j5-evidence-reads
                               fn2-env-j5-evidence-role-reads))))
(defthm fn2-env-j5-fence-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-j5-fence id op s log b) (fn2-env-j5-fence id op s log a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-fence fn2-env-role-written-congruence fn2-env-j5-evidence-reads
                                               (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-op-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-j5-op s id log b) (fn2-env-j5-op s id log a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-op fn2-env-j5-fence-congruence fn2-env-j5-evidence-reads
                                               fn2-env-j5-evidence-op fn2-env-j5-evidence-io (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-ops-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-j5-ops s k id log b) (fn2-env-j5-ops s k id log a)))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-j5-op-congruence) (theory 'minimal-theory)))))
(defthm fn2-env-owned-fence-at-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-owned-fence-at s id b) (fn2-env-owned-fence-at s id a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-owned-fence-at fn2-env-j5-evidence-reads fn2-env-j5-evidence-op)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-owned-fences-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-owned-fences s k id b) (fn2-env-owned-fences s k id a)))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id a)
           :in-theory (union-theories '(fn2-env-owned-fences fn2-env-owned-fence-at-congruence) (theory 'minimal-theory)))))
(defthm fn2-env-role-live-congruence
  (implies (and (fn2-env-j5-same-evidence id a b) (natp role) (< role 3))
           (equal (fn2-env-role-live id role b) (fn2-env-role-live id role a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-role-live fn2-env-j5-evidence-role-reads fn2-env-j5-evidence-op)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-role-congruence
  (implies (and (fn2-env-j5-same-evidence id a b) (natp role) (< role 3))
           (equal (fn2-env-j5-role id role log b) (fn2-env-j5-role id role log a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-role fn2-env-role-live-congruence fn2-env-j5-evidence-reads
                                               fn2-env-j5-evidence-role-reads fn2-env-j5-evidence-op
                                               fn2-env-role-written-congruence fn2-env-role-offset-of-extent)
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-roles-congruence
  (implies (fn2-env-j5-same-evidence id a b)
           (equal (fn2-env-j5-roles id log b) (fn2-env-j5-roles id log a)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-roles fn2-env-j5-role-congruence fn2-env-role-live-congruence
                                               fn2-env-j5-apart fn2-env-j5-evidence-role-reads
                                               fn2-env-j5-evidence-reads (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-j5-point-congruence
  ; J5 and J6 at ID read only ID's evidence
  (implies (fn2-env-j5-same-evidence id a b)
           (and (equal (fn2-env-j5-row id log b) (fn2-env-j5-row id log a))
                (equal (fn2-env-j6-row id b) (fn2-env-j6-row id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-row fn2-env-j6-row
                                               fn2-env-j5-ops-congruence fn2-env-owned-fences-congruence
                                               fn2-env-j5-roles-congruence fn2-env-role-live-congruence
                                               fn2-env-j5-evidence-reads fn2-env-j5-evidence-role-reads fn2-env-j5-evidence-op
                                               (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defun-nx fn2-env-j5-kept (id a b)
  ; B keeps A's J5/J6 evidence of row ID and each role's pool row J6P asks for
  (and (fn2-env-j5-same-evidence id a b)
       (implies (fn2-env-role-pool-ok id 0 a) (fn2-env-role-pool-ok id 0 b))
       (implies (fn2-env-role-pool-ok id 1 a) (fn2-env-role-pool-ok id 1 b))
       (implies (fn2-env-role-pool-ok id 2 a) (fn2-env-role-pool-ok id 2 b))
       (implies (fn2-env-role-pool-ok id 0 a) (equal (fn2-env-role-lease id 0 b) (fn2-env-role-lease id 0 a)))
       (implies (fn2-env-role-pool-ok id 1 a) (equal (fn2-env-role-lease id 1 b) (fn2-env-role-lease id 1 a)))
       (implies (fn2-env-role-pool-ok id 2 a) (equal (fn2-env-role-lease id 2 b) (fn2-env-role-lease id 2 a)))))
(defthm fn2-env-j5-kept-transfer
  (implies (and (fn2-env-j5-kept id a b) (fn2-env-j5-row id log a) (fn2-env-j6-row id a) (fn2-env-j6p-row id a))
           (and (fn2-env-j5-row id log b) (fn2-env-j6-row id b) (fn2-env-j6p-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-kept fn2-env-j6p-row fn2-env-j5-evidence-reads) (theory 'minimal-theory))
           :use ((:instance fn2-env-j5-point-congruence)))))
;; J6L and J6S read a role's unit, its pool row and lease and whether its
;; write is live: the kept evidence carries them wherever J6P (or, settling,
;; the live role's own pool row) names the role's pool row.
(defthm fn2-env-role-lease-ok-kept
  (implies (and (fn2-env-j5-kept id a b) (natp role) (< role 3) (fn2-env-role-pool-ok id role a))
           (equal (fn2-env-role-lease-ok id role b) (fn2-env-role-lease-ok id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp fn2-env-role-lease-ok fn2-env-j5-kept fn2-env-role-live-congruence fn2-env-j5-evidence-role-reads)
           :cases ((equal role 0) (equal role 1) (equal role 2)))))
(defthm fn2-env-j6ls-kept-transfer
  (implies (and (fn2-env-j5-kept id a b) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j6l-row fn2-env-j6s-row fn2-env-j6p-row fn2-env-role-settle-ok
                                               fn2-env-j5-kept fn2-env-j5-evidence-reads
                                               fn2-env-j5-evidence-role-reads fn2-env-role-live-congruence (:e natp) (:e <))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-role-lease-ok-kept (role 0)) (:instance fn2-env-role-lease-ok-kept (role 1))
                 (:instance fn2-env-role-lease-ok-kept (role 2))))))
(defthm fn2-env-j5-same-evidence-refl (fn2-env-j5-same-evidence id a a)
  :hints (("Goal" :in-theory '(fn2-env-j5-same-evidence fn2-env-ok-refl))))
(defthm fn2-env-j5-kept-refl (fn2-env-j5-kept id a a)
  :hints (("Goal" :in-theory '(fn2-env-j5-kept fn2-env-j5-same-evidence-refl))))
(defthm fn2-env-j5-kept-trans
  (implies (and (fn2-env-j5-kept id a b) (fn2-env-j5-kept id b c)) (fn2-env-j5-kept id a c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-kept fn2-env-j5-same-evidence)
           :use ((:instance fn2-env-ok-transitive (c c) (b b) (a a))))))
(defthm fn2-env-io-of-io-setters
  ; a commit-io column write at unit R leaves every other unit and the row count
  (implies (and (natp u) (natp r) (not (equal u r)))
           (and (equal (fn2-env-io u (update-fn2-core-commit-io (fn2-commit-io-set-pool-slot r v io) c))
                       (fn2-env-io u (update-fn2-core-commit-io io c)))
                (equal (fn2-env-io u (update-fn2-core-commit-io (fn2-commit-io-set-pool-gen r v io) c))
                       (fn2-env-io u (update-fn2-core-commit-io io c)))
                (equal (fn2-env-io u (update-fn2-core-commit-io (fn2-commit-io-set-ready r v io) c))
                       (fn2-env-io u (update-fn2-core-commit-io io c)))))
  :hints (("Goal" :in-theory (enable fn2-env-io fn2-commit-io-set-pool-slot fn2-commit-io-set-pool-gen fn2-commit-io-set-ready
                                     update-fn2-commit-io-pool-slot$ai update-fn2-commit-io-pool-gen$ai
                                     update-fn2-commit-io-ready$ai update-nth-array
                                     fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-pool-slot
                                     fn2-commit-io-pool-gen fn2-commit-io-op-slot$ai fn2-commit-io-op-gen$ai fn2-commit-io-lent$ai
                                     fn2-commit-io-pool-slot$ai fn2-commit-io-pool-gen$ai fn2-commit-io-rows))))
(fn2-defview fn2-env-mk :carrier fn2-core
  :select ((fn2-commit :columns (cb-issued generation cb-fence-live cb-bytes) :rows t)))
(fn2-defview fn2-env-pk :carrier fn2-core :select ((fn2-pool :whole t)))
(fn2-defview fn2-env-iok :carrier fn2-core
  :select ((fn2-commit-io :columns (op-slot op-gen lent pool-slot pool-gen) :rows t :scalars (rows))))
(make-event (value (cons 'progn (fn2-env-mk-read-events '(cb-issued generation cb-fence-live cb-bytes)))))
(defun-nx fn2-env-j5-unit-kept (id a b)
  ; B keeps the units and pool rows of row ID's three roles
  (and (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
       (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
       (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a))
       (equal (fn2-env-role-extent id 0 b) (fn2-env-role-extent id 0 a))
       (equal (fn2-env-role-extent id 1 b) (fn2-env-role-extent id 1 a))
       (equal (fn2-env-role-extent id 2 b) (fn2-env-role-extent id 2 a))
       (equal (fn2-env-role-octets id 0 b) (fn2-env-role-octets id 0 a))
       (equal (fn2-env-role-octets id 1 b) (fn2-env-role-octets id 1 a))
       (equal (fn2-env-role-octets id 2 b) (fn2-env-role-octets id 2 a))
       (implies (fn2-env-role-pool-ok id 0 a) (fn2-env-role-pool-ok id 0 b))
       (implies (fn2-env-role-pool-ok id 1 a) (fn2-env-role-pool-ok id 1 b))
       (implies (fn2-env-role-pool-ok id 2 a) (fn2-env-role-pool-ok id 2 b))
       (implies (fn2-env-role-pool-ok id 0 a) (equal (fn2-env-role-lease id 0 b) (fn2-env-role-lease id 0 a)))
       (implies (fn2-env-role-pool-ok id 1 a) (equal (fn2-env-role-lease id 1 b) (fn2-env-role-lease id 1 a)))
       (implies (fn2-env-role-pool-ok id 2 a) (equal (fn2-env-role-lease id 2 b) (fn2-env-role-lease id 2 a)))))
(defthm fn2-env-j5-unit-kept-refl (fn2-env-j5-unit-kept id a a)
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept))))
(defthm fn2-env-j5-unit-kept-trans
  (implies (and (fn2-env-j5-unit-kept id a b) (fn2-env-j5-unit-kept id b c)) (fn2-env-j5-unit-kept id a c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept))))
(defthm fn2-env-j5-kept-of-parts
  ; the directory and J5's commit columns (TK, MK), the ops table (OK) and
  ; the row's units and pool rows carry J5's evidence of a commit row
  (implies (and (fn2-env-tk b a) (fn2-env-mk b a) (fn2-env-ok b a) (fn2-env-j5-unit-kept id a b)
                (equal (fn2-machine-kind id a) *fn2-commit-kind*))
           (fn2-env-j5-kept id a b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-kept fn2-env-j5-same-evidence fn2-env-j5-unit-kept)
           :use ((:instance fn2-env-read-codes-of-tk)
                 (:instance fn2-machine-phase-of-tk) (:instance fn2-machine-batch-no-of-tk)
                 (:instance fn2-machine-cb-mode-of-tk) (:instance fn2-machine-cb-fence-ok-of-tk)
                 (:instance fn2-machine-cb-deps-ok-of-tk) (:instance fn2-machine-cb-log-ok-of-tk)
                 (:instance fn2-machine-cb-done-of-tk)
                 (:instance fn2-machine-cb-issued-of-mk) (:instance fn2-machine-generation-of-mk)
                 (:instance fn2-machine-cb-fence-live-of-mk) (:instance fn2-machine-cb-bytes-of-mk)))))
(defun fn2-env-row-octets-at (s fn2-core)
  ; the unit of octets at pool row S's base
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (octets)
    (if (and (natp s) (< s (fn2-pool-rows fn2-pool)))
        (fn2-env-pool-octets *fn2-commit-unit-bytes* (fn2-pool-base s fn2-pool) fn2-pool)
      nil)
    octets))
(defthm fn2-env-role-octets-is-row-octets
  (equal (fn2-env-role-octets id role c) (fn2-env-row-octets-at (nth 4 (fn2-env-role-io id role c)) c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-octets fn2-env-row-octets-at))))
(defthm fn2-env-io-of-io-child
  (implies (equal (nth 30 b) (nth 30 a))
           (equal (fn2-env-io u b) (fn2-env-io u a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-io fn2-core-commit-io))))
(defthm fn2-env-pool-readers-of-pool-child
  (implies (equal (nth 0 b) (nth 0 a))
           (and (equal (fn2-env-pool-row s b) (fn2-env-pool-row s a))
                (equal (fn2-env-row-octets-at s b) (fn2-env-row-octets-at s a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-pool-row fn2-env-row-octets-at fn2-core-pool))))
(defthm fn2-env-role-lease-of-unit
  ; a role's lease reads its unit and the pool alone
  (implies (and (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a)) (equal (nth 0 b) (nth 0 a)))
           (equal (fn2-env-role-lease id role b) (fn2-env-role-lease id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-lease fn2-core-pool))))
(defthm fn2-env-role-readers-of-children
  ; a role's unit and extent read the directory and commit-io; its octets,
  ; pool row and lease read the unit and the pool
  (implies (and (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (equal (nth 30 b) (nth 30 a)) (equal (nth 0 b) (nth 0 a)))
           (and (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a))
                (equal (fn2-env-role-extent id role b) (fn2-env-role-extent id role a))
                (equal (fn2-env-role-octets id role b) (fn2-env-role-octets id role a))
                (equal (fn2-env-role-pool-ok id role b) (fn2-env-role-pool-ok id role a))
                (equal (fn2-env-role-lease id role b) (fn2-env-role-lease id role a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-io fn2-env-role-extent fn2-commit-resource fn2-core-commit-io fn2-env-role-pool-ok)
           :use ((:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id a)) role)))
                 (:instance fn2-env-role-lease-of-unit)
                 (:instance fn2-env-role-octets-is-row-octets (c a))
                 (:instance fn2-env-role-octets-is-row-octets (c b))
                 (:instance fn2-env-pool-readers-of-pool-child (s (nth 4 (fn2-env-io (+ (* 3 (fn2-commit-row id a)) role) a))))))))
(defthm fn2-env-j5-unit-kept-of-views
  ; the whole commit-io and pool children carry a row's units and pool rows
  (implies (and (fn2-env-tk b a) (fn2-env-io-view b a) (fn2-env-pk b a))
           (fn2-env-j5-unit-kept id a b))
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept fn2-env-io-view fn2-env-pk)
           :use ((:instance fn2-env-read-codes-of-tk)
                 (:instance fn2-env-role-readers-of-children (role 0))
                 (:instance fn2-env-role-readers-of-children (role 1))
                 (:instance fn2-env-role-readers-of-children (role 2))))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-mk fn2-env-pk fn2-env-iok fn2-env-io-view)
  '(fn2-core-stop fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-mk fn2-env-pk)
  '(fn2-commit-reserve-extent) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-mk fn2-env-ok fn2-env-tk)
  '(fn2-commit-reserve-pools fn2-commit-release-pools fn2-commit-reserve-extent fn2-core-stop fn2-commit-prepare-root
    fn2-commit-ready fn2-commit-put-members fn2-exec-wake) (w state)))))
(defthm fn2-env-core-stop-keeps-io-pool
  (and (equal (nth *fn2-core-commit-io* (fn2-core-stop r c)) (nth *fn2-core-commit-io* c))
       (equal (nth *fn2-core-pool* (fn2-core-stop r c)) (nth *fn2-core-pool* c)))
  :hints (("Goal" :in-theory (enable fn2-core-stop update-fn2-core-control))))
(defthm fn2-env-reserve-extent-io-units
  ; the extent reservation writes no unit's op, loan or pool columns
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (equal (fn2-env-io u (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (fn2-env-io u fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-reserve-extent fn2-core-commit-io update-fn2-core-commit-io fn2-env-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-pool-slot
                                   fn2-commit-io-pool-gen fn2-commit-io-rows fn2-env-core-stop-keeps-io-pool
                                   update-nth-array)
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop update-nth nth)))))
(defthm fn2-env-role-pool-readers-of-unit
  ; a role's octets and pool row read its unit and the pool alone
  (implies (and (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a)) (equal (nth 0 b) (nth 0 a)))
           (and (equal (fn2-env-role-octets id role b) (fn2-env-role-octets id role a))
                (equal (fn2-env-role-pool-ok id role b) (fn2-env-role-pool-ok id role a))
                (equal (fn2-env-role-lease id role b) (fn2-env-role-lease id role a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-pool-ok)
           :use ((:instance fn2-env-role-lease-of-unit)
                 (:instance fn2-env-role-octets-is-row-octets (c a))
                 (:instance fn2-env-role-octets-is-row-octets (c b))
                 (:instance fn2-env-pool-readers-of-pool-child (s (nth 4 (fn2-env-role-io id role a))))))))
(defthm fn2-env-role-io-of-tk-units
  (implies (and (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (equal (fn2-env-io (+ (* 3 (fn2-commit-row id a)) role) b) (fn2-env-io (+ (* 3 (fn2-commit-row id a)) role) a)))
           (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-io))))
(defthm fn2-env-reserve-extent-unit-kept
  ; the extent reservation keeps the units and pool rows of every other row
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (fn2-env-j5-unit-kept i fn2-core (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept fn2-env-reserve-extent-io-units fn2-env-pk (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-read-codes-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))
                 (:instance fn2-env-tk-refl (a fn2-core))
                 (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-commit-reserve-extent-fn2-env-pk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-pk-reflexive (a fn2-core))
                 (:instance fn2-env-reserve-extent-role-extent (role 0))
                 (:instance fn2-env-reserve-extent-role-extent (role 1))
                 (:instance fn2-env-reserve-extent-role-extent (role 2))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role 0) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role 1) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role 2) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 0) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 1) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 2) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))))))
(defthm fn2-env-commit-io-of-update-pool
  (equal (fn2-core-commit-io (update-fn2-core-pool q a)) (fn2-core-commit-io a))
  :hints (("Goal" :in-theory (enable fn2-core-commit-io update-fn2-core-pool))))
(defthm fn2-env-role-of-pool-update
  ; a pool write that keeps the octet array, the row count, the role's row
  ; base and, when J6P holds of it, its state, owner and size keeps the role
  (let ((s (nth 4 (fn2-env-role-io id role a))) (p (fn2-core-pool a)))
    (implies (and (equal (fn2-pool-rows q) (fn2-pool-rows p))
                  (equal (nth *fn2-pool-datai* q) (nth *fn2-pool-datai* p))
                  (equal (fn2-pool-base s q) (fn2-pool-base s p))
                  (implies (fn2-env-role-pool-ok id role a)
                           (and (equal (fn2-pool-state s q) (fn2-pool-state s p))
                                (equal (fn2-pool-owner-slot s q) (fn2-pool-owner-slot s p))
                                (equal (fn2-pool-cap s q) (fn2-pool-cap s p))
                                (equal (fn2-pool-gen s q) (fn2-pool-gen s p)))))
             (and (equal (fn2-env-role-io id role (update-fn2-core-pool q a)) (fn2-env-role-io id role a))
                  (equal (fn2-env-role-extent id role (update-fn2-core-pool q a)) (fn2-env-role-extent id role a))
                  (equal (fn2-env-role-octets id role (update-fn2-core-pool q a)) (fn2-env-role-octets id role a))
                  (implies (fn2-env-role-pool-ok id role a) (fn2-env-role-pool-ok id role (update-fn2-core-pool q a)))
                  (implies (fn2-env-role-pool-ok id role a)
                           (equal (fn2-env-role-lease id role (update-fn2-core-pool q a)) (fn2-env-role-lease id role a))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-role-pool-ok fn2-env-pool-row fn2-env-row-octets-at fn2-env-role-lease
                                               fn2-env-core-pool-of-update-pool fn2-env-j5-readers-of-update-fn2-core-pool
                                               fn2-env-role-extent fn2-commit-resource fn2-commit-idp-of-update-fn2-core-pool
                                               fn2-commit-row-of-update-fn2-core-pool fn2-env-commit-io-of-update-pool (:e nth) (:e car) car-cons cdr-cons (:e member-equal) member-equal)
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-role-octets-is-row-octets (c a))
                 (:instance fn2-env-role-octets-is-row-octets (c (update-fn2-core-pool q a)))
                 (:instance fn2-env-pool-octets-of-data (p (fn2-core-pool a)) (n *fn2-commit-unit-bytes*)
                            (addr (fn2-pool-base (nth 4 (fn2-env-role-io id role a)) (fn2-core-pool a))))))))
(make-event
 (value (cons 'progn
   (fn2-env-j-reader-frame-events
    '((fn2-machine-idp id) (fn2-machine-kind id) (fn2-machine-slot id) (fn2-commit-idp id) (fn2-commit-row id) (fn2-commit-resource id role) (fn2-env-io u)
      (fn2-env-pool-row s) (fn2-env-row-octets-at s) (fn2-env-role-io id role) (fn2-env-role-extent id role)
      (fn2-env-role-pool-ok id role) (fn2-env-role-lease id role))
    '(update-fn2-core-control)))))
(defthm fn2-env-role-octets-of-update-control
  (equal (fn2-env-role-octets id role (update-fn2-core-control x c)) (fn2-env-role-octets id role c))
  :hints (("Goal" :in-theory '(fn2-env-role-io-of-update-fn2-core-control fn2-env-row-octets-at-of-update-fn2-core-control)
           :use ((:instance fn2-env-role-octets-is-row-octets)
                 (:instance fn2-env-role-octets-is-row-octets (c (update-fn2-core-control x c)))))))
(defthm fn2-env-pool-ok-row-facts
  (implies (fn2-env-role-pool-ok id role c)
           (let ((s (nth 4 (fn2-env-role-io id role c))))
             (and (not (equal (fn2-pool-state s (fn2-core-pool c)) *fn2-pool-state-free*))
                  (equal (fn2-pool-owner-slot s (fn2-core-pool c)) id))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-pool-ok fn2-env-pool-row (:e nth) (:e car) car-cons cdr-cons member-equal (:e member-equal) nth-add1 nth-0-cons (:e zp) (:e equal)))))
(defthm fn2-env-core-reserve-role
  (let ((b (mv-nth 3 (fn2-core-reserve class okind oslot ogen c))))
    (and (equal (fn2-env-role-io i role b) (fn2-env-role-io i role c))
         (equal (fn2-env-role-extent i role b) (fn2-env-role-extent i role c))
         (equal (fn2-env-role-octets i role b) (fn2-env-role-octets i role c))
         (implies (fn2-env-role-pool-ok i role c) (fn2-env-role-pool-ok i role b))
         (implies (fn2-env-role-pool-ok i role c) (equal (fn2-env-role-lease i role b) (fn2-env-role-lease i role c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(mv-nth (:e mv-nth) car-cons cdr-cons (:e zp) (:e binary-+))
           :do-not-induct t
           :use ((:instance fn2-core-reserve (fn2-core c)) (:instance fn2-env-pool-ok-row-facts (id i))
                 (:instance fn2-env-role-of-pool-update (id i) (a c) (q (mv-nth 3 (fn2-pool-reserve class okind oslot ogen (fn2-core-pool c)))))
                 (:instance fn2-env-pool-reserve-keeps (p (fn2-core-pool c)) (r (nth 4 (fn2-env-role-io i role c))))))))
(defthm fn2-env-core-reserve-unit-kept
  ; a pool reservation keeps every commit row's units and J6P pool rows
  (fn2-env-j5-unit-kept i c (mv-nth 3 (fn2-core-reserve class okind oslot ogen c)))
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept)
           :use ((:instance fn2-env-core-reserve-role (role 0)) (:instance fn2-env-core-reserve-role (role 1))
                 (:instance fn2-env-core-reserve-role (role 2))))))
(defthm fn2-env-core-release-is
  (equal (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))
         (update-fn2-core-control (mv-nth 2 (fn2-core-release-children slot gen okind oslot ogen (fn2-core-pool c) (fn2-core-control c)))
                                  (update-fn2-core-pool (mv-nth 1 (fn2-core-release-children slot gen okind oslot ogen (fn2-core-pool c) (fn2-core-control c))) c)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-core-release mv-nth (:e mv-nth) car-cons cdr-cons (:e zp) (:e binary-+)))))
(defthm fn2-env-core-release-role
  (implies (not (equal i oslot))
           (let ((b (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))))
             (and (equal (fn2-env-role-io i role b) (fn2-env-role-io i role c))
                  (equal (fn2-env-role-extent i role b) (fn2-env-role-extent i role c))
                  (equal (fn2-env-role-octets i role b) (fn2-env-role-octets i role c))
                  (implies (fn2-env-role-pool-ok i role c) (fn2-env-role-pool-ok i role b))
         (implies (fn2-env-role-pool-ok i role c) (equal (fn2-env-role-lease i role b) (fn2-env-role-lease i role c))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-io-of-update-fn2-core-control fn2-env-role-extent-of-update-fn2-core-control
                               fn2-env-role-octets-of-update-control fn2-env-role-pool-ok-of-update-fn2-core-control
                               fn2-env-role-lease-of-update-fn2-core-control)
           :do-not-induct t
           :use ((:instance fn2-env-core-release-is) (:instance fn2-env-pool-ok-row-facts (id i))
                 (:instance fn2-env-release-children-pool (p (fn2-core-pool c)) (ctl (fn2-core-control c)))
                 (:instance fn2-env-role-of-pool-update (id i) (a c)
                            (q (mv-nth 1 (fn2-core-release-children slot gen okind oslot ogen (fn2-core-pool c) (fn2-core-control c)))))
                 (:instance fn2-env-pool-release-keeps (p (fn2-core-pool c)) (r (nth 4 (fn2-env-role-io i role c))))))))
(defthm fn2-env-core-release-unit-kept
  ; a release by another owner keeps every commit row's units and J6P pool rows
  (implies (not (equal i oslot))
           (fn2-env-j5-unit-kept i c (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))))
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept)
           :use ((:instance fn2-env-core-release-role (role 0)) (:instance fn2-env-core-release-role (role 1))
                 (:instance fn2-env-core-release-role (role 2))))))
(defthm fn2-env-save-pool-io-units
  ; saving a role's pool row writes that role's unit only
  (implies (and (natp u) (natp (fn2-commit-row id c)) (not (equal u (+ (* 3 (fn2-commit-row id c)) (nfix role)))))
           (equal (fn2-env-io u (fn2-commit-save-pool id role slot gen c)) (fn2-env-io u c)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-save-pool fn2-core-commit-io update-fn2-core-commit-io fn2-env-io
                                   fn2-commit-io-set-pool-slot fn2-commit-io-set-pool-gen fn2-commit-io-set-ready
                                   update-fn2-commit-io-pool-slot$ai update-fn2-commit-io-pool-gen$ai update-fn2-commit-io-ready$ai
                                   fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-pool-slot
                                   fn2-commit-io-pool-gen fn2-commit-io-rows fn2-env-core-stop-keeps-io-pool update-nth-array)
                                  (fn2-commit-row fn2-commit-idp fn2-core-stop update-nth nth)))))
(defthm fn2-env-save-pool-keeps-pool
  (equal (nth *fn2-core-pool* (fn2-commit-save-pool id role slot gen c)) (nth *fn2-core-pool* c))
  :hints (("Goal" :in-theory (e/d (fn2-commit-save-pool update-fn2-core-commit-io fn2-env-core-stop-keeps-io-pool)
                                  (fn2-commit-row fn2-commit-idp fn2-core-stop nth update-nth)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-mk fn2-env-ok fn2-env-tk fn2-env-ek)
  '(fn2-commit-save-pool fn2-commit-keep-pool fn2-commit-release-pool fn2-commit-unwind-pool fn2-core-reserve fn2-core-release) (w state)))))
(defthm fn2-env-unit-kept-of-io-units
  ; the directory (TK), the extent column (EK), the pool and the row's three
  ; units carry its units and pool rows
  (let ((r (* 3 (fn2-commit-row i a))))
    (implies (and (fn2-env-tk b a) (fn2-env-ek b a) (equal (nth 0 b) (nth 0 a))
                  (equal (fn2-env-io (+ r 0) b) (fn2-env-io (+ r 0) a))
                  (equal (fn2-env-io (+ r 1) b) (fn2-env-io (+ r 1) a))
                  (equal (fn2-env-io (+ r 2) b) (fn2-env-io (+ r 2) a)))
             (fn2-env-j5-unit-kept i a b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept)
           :do-not-induct t
           :use ((:instance fn2-env-read-codes-of-tk (id i))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role 0)) (:instance fn2-env-role-io-of-tk-units (id i) (role 1))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role 2))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 0)) (:instance fn2-env-role-extent-of-ek (id i) (role 1))
                 (:instance fn2-env-role-extent-of-ek (id i) (role 2))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 0))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 1))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role 2))))))
(defthm fn2-env-save-pool-unit-kept
  ; saving the pool row of a role of row ID keeps every other row's units and pool rows
  (implies (and (fn2-corep c) (fn2-core-wfp c) (natp role) (< role 3)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i c (fn2-commit-save-pool id role slot gen c)))
  :hints (("Goal" :in-theory '(fn2-commit-row fn2-env-tk-refl fn2-env-ek-refl (:e natp) (:e nfix) natp nfix)
           :do-not-induct t
           :use ((:instance fn2-env-unit-kept-of-io-units (a c) (b (fn2-commit-save-pool id role slot gen c)))
                 (:instance fn2-commit-save-pool-fn2-env-tk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-commit-save-pool-fn2-env-ek (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-env-save-pool-keeps-pool)
                 (:instance fn2-commit-row-natp (fn2-core c) (id i)) (:instance fn2-commit-row-natp (fn2-core c))
                 (:instance fn2-env-save-pool-io-units (u (+ (* 3 (fn2-commit-row i c)) 0)))
                 (:instance fn2-env-save-pool-io-units (u (+ (* 3 (fn2-commit-row i c)) 1)))
                 (:instance fn2-env-save-pool-io-units (u (+ (* 3 (fn2-commit-row i c)) 2)))
                 (:instance fn2-env-row-units-disjoint (a (fn2-commit-row i c)) (b (fn2-commit-row id c)) (role 0) (k role))
                 (:instance fn2-env-row-units-disjoint (a (fn2-commit-row i c)) (b (fn2-commit-row id c)) (role 1) (k role))
                 (:instance fn2-env-row-units-disjoint (a (fn2-commit-row i c)) (b (fn2-commit-row id c)) (role 2) (k role))))))
(defthm fn2-env-keep-pool-scratch-children
  ; the scratch row is the machine's own column; commit-io and the pool stay
  (implies (not (and (natp role) (< role 3)))
           (and (equal (nth 30 (fn2-commit-keep-pool id role slot gen c)) (nth 30 c))
                (equal (nth 0 (fn2-commit-keep-pool id role slot gen c)) (nth 0 c))))
  :hints (("Goal" :in-theory (e/d (fn2-commit-keep-pool fn2-env-core-stop-keeps-io-pool fn2-machine-refuse-write update-fn2-commit-table)
                                  (fn2-core-stop fn2-commit-idp fn2-machine-slot nth update-nth)))))
(defthm fn2-env-core-release-keeps-io
  (equal (nth *fn2-core-commit-io* (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))) (nth *fn2-core-commit-io* c))
  :hints (("Goal" :in-theory (union-theories '(update-fn2-core-control update-fn2-core-pool nth-update-nth (:e nfix) (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn2-env-core-release-is)))))
(defthm fn2-env-core-release-keeps-ids
  (and (equal (fn2-commit-row x (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))) (fn2-commit-row x c))
       (equal (fn2-commit-idp x (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))) (fn2-commit-idp x c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-row-of-update-fn2-core-control fn2-commit-idp-of-update-fn2-core-control
                                               fn2-commit-row-of-update-fn2-core-pool fn2-commit-idp-of-update-fn2-core-pool)
                                             (theory 'minimal-theory))
           :use ((:instance fn2-env-core-release-is)))))
(defthm fn2-env-release-pool-io-units
  ; releasing a role's pool row writes that role's unit only
  (implies (and (natp u) (natp (fn2-commit-row id c))
                (not (and (natp role) (< role 3) (equal u (+ (* 3 (fn2-commit-row id c)) role)))))
           (equal (fn2-env-io u (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))) (fn2-env-io u c)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-release-pool fn2-core-commit-io update-fn2-core-commit-io fn2-env-io
                                   fn2-commit-io-set-pool-slot fn2-commit-io-set-pool-gen fn2-commit-io-set-ready
                                   update-fn2-commit-io-pool-slot$ai update-fn2-commit-io-pool-gen$ai update-fn2-commit-io-ready$ai
                                   fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-pool-slot
                                   fn2-commit-io-pool-gen fn2-commit-io-rows fn2-env-core-stop-keeps-io-pool update-nth-array
                                   fn2-env-core-release-keeps-io fn2-env-core-release-keeps-ids fn2-machine-refuse-write update-fn2-commit-table)
                                  (fn2-commit-row fn2-commit-idp fn2-core-stop fn2-core-release fn2-commit-resource
                                   fn2-machine-slot fn2-machine-pool-slot fn2-machine-pool-gen update-nth nth)))))
(defthm fn2-env-release-pool-pool
  ; its pool is the core release's
  (implies (fn2-commit-idp id c)
           (equal (nth *fn2-core-pool* (mv-nth 1 (fn2-commit-release-pool id role owner-gen c)))
                  (nth *fn2-core-pool*
                       (mv-nth 1 (fn2-core-release
                                  (if (equal role 3) (fn2-machine-pool-slot id c) (mv-nth 3 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  (if (equal role 3) (fn2-machine-pool-gen id c) (mv-nth 4 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  *fn2-commit-kind* id owner-gen c)))))
  :hints (("Goal" :in-theory (e/d (fn2-commit-release-pool update-fn2-core-commit-io fn2-env-core-stop-keeps-io-pool
                                   fn2-machine-refuse-write update-fn2-commit-table)
                                  (fn2-commit-row fn2-commit-idp fn2-core-stop fn2-core-release fn2-commit-resource
                                   fn2-machine-slot fn2-machine-pool-slot fn2-machine-pool-gen update-nth nth)))))
(defthm fn2-env-release-pool-unchecked
  (implies (not (fn2-commit-idp id c))
           (equal (mv-nth 1 (fn2-commit-release-pool id role owner-gen c)) (fn2-core-stop *fn2-stop-reason-machine-phase* c)))
  :hints (("Goal" :in-theory '(fn2-commit-release-pool mv-nth (:e mv-nth) car-cons cdr-cons (:e zp) (:e binary-+)))))
(defthm fn2-env-release-pool-role
  (let ((b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
    (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c) (natp k) (< k 3)
                  (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
             (and (equal (fn2-env-role-io i k b) (fn2-env-role-io i k c))
                  (equal (fn2-env-role-extent i k b) (fn2-env-role-extent i k c))
                  (equal (fn2-env-role-octets i k b) (fn2-env-role-octets i k c))
                  (implies (fn2-env-role-pool-ok i k c) (fn2-env-role-pool-ok i k b))
                  (implies (fn2-env-role-pool-ok i k c) (equal (fn2-env-role-lease i k b) (fn2-env-role-lease i k c))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-row fn2-env-tk-refl fn2-env-ek-refl (:e natp) (:e nfix) natp nfix
                               fn2-env-core-stop-keeps-io-pool)
           :do-not-induct t
           :cases ((fn2-commit-idp id c))
           :use ((:instance fn2-commit-release-pool-fn2-env-tk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-commit-release-pool-fn2-env-ek (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-env-read-codes-of-tk (id i) (a c) (b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
                 (:instance fn2-commit-row-natp (fn2-core c) (id i)) (:instance fn2-commit-row-natp (fn2-core c))
                 (:instance fn2-env-release-pool-io-units (u (+ (* 3 (fn2-commit-row i c)) k)))
                 (:instance fn2-env-row-units-disjoint (a (fn2-commit-row i c)) (b (fn2-commit-row id c)) (role k) (k role))
                 (:instance fn2-env-role-io-of-tk-units (id i) (role k) (a c) (b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
                 (:instance fn2-env-role-extent-of-ek (id i) (role k) (a c) (b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
                 (:instance fn2-env-release-pool-unchecked)
                 (:instance fn2-env-release-pool-pool)
                 (:instance fn2-env-core-release-role (oslot id) (okind *fn2-commit-kind*) (ogen owner-gen) (role k)
                            (slot (if (equal role 3) (fn2-machine-pool-slot id c) (mv-nth 3 (fn2-commit-resource id (if (equal role 3) 0 role) c))))
                            (gen (if (equal role 3) (fn2-machine-pool-gen id c) (mv-nth 4 (fn2-commit-resource id (if (equal role 3) 0 role) c)))))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role k)
                            (a (mv-nth 1 (fn2-core-release
                                  (if (equal role 3) (fn2-machine-pool-slot id c) (mv-nth 3 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  (if (equal role 3) (fn2-machine-pool-gen id c) (mv-nth 4 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  *fn2-commit-kind* id owner-gen c)))
                            (b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
                 (:instance fn2-env-role-pool-readers-of-unit (id i) (role k) (a c) (b (fn2-core-stop *fn2-stop-reason-machine-phase* c)))))))
(defthm fn2-env-release-pool-unit-kept
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i c (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
  :hints (("Goal" :in-theory '(fn2-env-j5-unit-kept (:e natp) (:e <))
           :use ((:instance fn2-env-release-pool-role (k 0)) (:instance fn2-env-release-pool-role (k 1))
                 (:instance fn2-env-release-pool-role (k 2))))))
(defthm fn2-env-keep-pool-unit-kept
  (implies (and (fn2-corep c) (fn2-core-wfp c)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i c (fn2-commit-keep-pool id role slot gen c)))
  :hints (("Goal" :in-theory '(fn2-commit-keep-pool fn2-env-save-pool-unit-kept)
           :cases ((and (natp role) (< role 3))))
          ("Subgoal 2" :in-theory '(fn2-env-tk-refl fn2-env-ek-refl)
           :use ((:instance fn2-env-keep-pool-scratch-children)
                 (:instance fn2-commit-keep-pool-fn2-env-tk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-commit-keep-pool-fn2-env-ek (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-env-unit-kept-of-io-units (a c) (b (fn2-commit-keep-pool id role slot gen c)))
                 (:instance fn2-env-io-of-io-child (a c) (b (fn2-commit-keep-pool id role slot gen c)) (u (+ (* 3 (fn2-commit-row i c)) 0)))
                 (:instance fn2-env-io-of-io-child (a c) (b (fn2-commit-keep-pool id role slot gen c)) (u (+ (* 3 (fn2-commit-row i c)) 1)))
                 (:instance fn2-env-io-of-io-child (a c) (b (fn2-commit-keep-pool id role slot gen c)) (u (+ (* 3 (fn2-commit-row i c)) 2)))))))
(defthm fn2-env-core-stop-unit-kept
  (fn2-env-j5-unit-kept i c (fn2-core-stop reason c))
  :hints (("Goal" :in-theory '(fn2-env-tk-reflexive fn2-env-io-view-reflexive fn2-env-pk-reflexive)
           :use ((:instance fn2-env-j5-unit-kept-of-views (id i) (a c) (b (fn2-core-stop reason c)))
                 (:instance fn2-core-stop-fn2-env-tk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-io-view (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-pk (fn2-core c) (fn2-rel-c0 c))))))
(fn2-env-unit-chain fn2-env-core-stop-unit-chain (fn2-core-stop reason c) nil fn2-env-core-stop-unit-kept)
(fn2-env-unit-chain fn2-env-core-reserve-unit-chain (mv-nth 3 (fn2-core-reserve class okind oslot ogen c)) nil
  fn2-env-core-reserve-unit-kept)
(fn2-env-unit-chain fn2-env-keep-pool-unit-chain (fn2-commit-keep-pool id role slot gen c)
  ((fn2-corep c) (fn2-core-wfp c) (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c)))) fn2-env-keep-pool-unit-kept)
(fn2-env-unit-chain fn2-env-release-pool-unit-chain (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))
  ((fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c) (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
  fn2-env-release-pool-unit-kept)
(defthm fn2-env-unwind-pool-unit-chain
  (implies (and (fn2-env-j5-unit-kept i a c) (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i a (fn2-commit-unwind-pool id role owner-gen c)))
  :hints (("Goal" :in-theory '(fn2-commit-unwind-pool fn2-env-release-pool-unit-chain fn2-env-core-stop-unit-chain))))
(make-event (value (cons 'progn (fn2-env-keeps-ids-events
  '((fn2-env-core-reserve-keeps-ids (mv-nth 3 (fn2-core-reserve class okind oslot ogen c)) fn2-core-reserve-fn2-env-tk)
    (fn2-env-keep-pool-keeps-ids (fn2-commit-keep-pool id role slot gen c) fn2-commit-keep-pool-fn2-env-tk)
    (fn2-env-unwind-pool-keeps-ids (fn2-commit-unwind-pool id role owner-gen c) fn2-commit-unwind-pool-fn2-env-tk)
    (fn2-env-release-pool-keeps-ids (mv-nth 1 (fn2-commit-release-pool id role owner-gen c)) fn2-commit-release-pool-fn2-env-tk)
    (fn2-env-reserve-pools-keeps-ids (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen c)) fn2-commit-reserve-pools-fn2-env-tk)
    (fn2-env-release-pools-keeps-ids (fn2-commit-release-pools left id owner-gen c) fn2-commit-release-pools-fn2-env-tk)
    (fn2-env-core-stop-keeps-ids (fn2-core-stop reason c) fn2-core-stop-fn2-env-tk))))))
(defthm fn2-env-reserve-pools-unit-chain
  (implies (and (fn2-env-j5-unit-kept i a c) (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i a (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen c))))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen c)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-env-core-reserve-unit-chain fn2-env-keep-pool-unit-chain
                                        fn2-env-unwind-pool-unit-chain fn2-env-core-reserve-keeps-ids fn2-env-keep-pool-keeps-ids
                                        fn2-env-reserve-pools-keeps-ids
                                        fn2-core-reserve-preserves-type fn2-core-reserve-preserves-wfp
                                        fn2-commit-keep-pool-type fn2-commit-keep-pool-wfp fn2-commit-reserve-pools-shape)
                                      (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-release-pools-unit-chain
  (implies (and (fn2-env-j5-unit-kept i a c) (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c)
                (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
           (fn2-env-j5-unit-kept i a (fn2-commit-release-pools left id owner-gen c)))
  :hints (("Goal" :induct (fn2-commit-release-pools left id owner-gen c)
           :in-theory (union-theories '(fn2-commit-release-pools fn2-env-release-pool-unit-chain fn2-env-core-stop-unit-chain
                                        fn2-env-release-pool-keeps-ids fn2-env-release-pools-keeps-ids fn2-env-core-stop-keeps-ids
                                        fn2-commit-release-pool-preserves-type fn2-commit-release-pool-preserves-wfp
                                        fn2-core-stop-type fn2-core-stop-wfp)
                                      (theory 'fn2-arm-frame-base)))))
(make-event (value (cons 'progn (fn2-env-row-read-events '((generation . 1) (cb-fence-live . 22) (cb-bytes . 18))))))
(defun fn2-env-start-j5-events (world)
  ; the admission's row write keeps J5's evidence of every other row
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (formals (formals w world))
         (call (cons w formals))
         (e (fn2-arm-frame-known w kind world))
         (cs (fn2-arm-frame-entry-j e))
         (ch (fn2-arm-frame-entry-s e))
         (row '(fn2-machine-slot id fn2-core)))
    `((defthm fn2-env-start-write-j5-other
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp i fn2-core)
                      (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                 (fn2-env-j5-kept i fn2-core ,call))
        :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-kept fn2-env-j5-same-evidence fn2-ctf-dir-refl
                                                     (:type-prescription fn2-machine-slot-natp) fn2-commit-idp-kind-value)
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-ARM-ROW-FRAME") (fn2-arm-tb 9) (fn2-arm-row ,row)
                                  (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-row-frame-refl (table 9) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                       (:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 3) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 30) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 0) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 1) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-env-ok-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-ok-refl (a fn2-core))
                       (:instance fn2-ctf-dir-of-nth (b ,call) (x fn2-core) (a fn2-core))
                       (:instance fn2-env-read-codes-of-row-frame (id i) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))
                       ,@(fn2-env-start-j5-rf-uses '(fn2-machine-phase-of-row-frame fn2-machine-batch-no-of-row-frame
                            fn2-machine-cb-mode-of-row-frame fn2-machine-cb-fence-ok-of-row-frame fn2-machine-cb-deps-ok-of-row-frame
                            fn2-machine-cb-log-ok-of-row-frame fn2-machine-cb-done-of-row-frame fn2-machine-cb-issued-of-row-frame
                            fn2-machine-generation-of-row-frame fn2-machine-cb-fence-live-of-row-frame
                            fn2-machine-cb-bytes-of-row-frame) row cs ch call)
                       (:instance fn2-env-role-readers-of-children (id i) (role 0) (a fn2-core) (b ,call))
                       (:instance fn2-env-role-readers-of-children (id i) (role 1) (a fn2-core) (b ,call))
                       (:instance fn2-env-role-readers-of-children (id i) (role 2) (a fn2-core) (b ,call))))))
      (defthm fn2-env-start-write-keeps-ids-rewrite
        (and (equal (fn2-commit-idp x ,call) (fn2-commit-idp x fn2-core))
             (equal (fn2-machine-slot x ,call) (fn2-machine-slot x fn2-core)))
        :hints (("Goal" :in-theory nil :use ((:instance fn2-env-start-write-keeps-ids)))))
      (defthm fn2-env-start-write-kept-chain
        (implies (and (fn2-env-j5-kept i a fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp i fn2-core)
                      (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                 (fn2-env-j5-kept i a ,call))
        :hints (("Goal" :in-theory nil
                 :use ((:instance fn2-env-start-write-j5-other)
                       (:instance fn2-env-j5-kept-trans (id i) (a a) (b fn2-core) (c ,call)))))))))
(make-event (value (cons 'progn (fn2-env-start-j5-events (w state)))))
(make-event (value (cons 'progn (fn2-env-keeps-ids-events
  '((fn2-env-reserve-extent-keeps-ids (mv-nth 1 (fn2-commit-reserve-extent id c)) fn2-commit-reserve-extent-fn2-env-tk)
    (fn2-env-prepare-root-keeps-ids (fn2-commit-prepare-root id c) fn2-commit-prepare-root-fn2-env-tk)
    (fn2-env-ready-keeps-ids (fn2-commit-ready id c) fn2-commit-ready-fn2-env-tk))))))
(fn2-env-kept-chain-views fn2-env-core-stop-kept-chain (fn2-core-stop reason c))
(fn2-env-kept-chain-views fn2-env-prepare-root-kept-chain (fn2-commit-prepare-root id c))
(fn2-env-kept-chain-views fn2-env-ready-kept-chain (fn2-commit-ready id c))
(fn2-env-kept-chain-views fn2-env-put-members-kept-chain
  (mv-nth 1 (fn2-commit-put-members left m row kind okind oslot ogen event c)))
(fn2-env-kept-chain-views fn2-env-exec-wake-kept-chain (fn2-exec-wake id c))
(fn2-env-kept-chain fn2-env-reserve-extent-kept-chain (mv-nth 1 (fn2-commit-reserve-extent id c))
  ((fn2-corep c) (fn2-core-wfp c) (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
  ((:instance fn2-env-reserve-extent-unit-kept (fn2-core c))))
(fn2-env-kept-chain fn2-env-reserve-pools-kept-chain (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen c))
  ((fn2-corep c) (fn2-core-wfp c) (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
  ((:instance fn2-env-reserve-pools-unit-chain (a c))))
(fn2-env-kept-chain fn2-env-release-pools-kept-chain (fn2-commit-release-pools left id owner-gen c)
  ((fn2-corep c) (fn2-core-wfp c) (not (equal (fn2-machine-slot i c) (fn2-machine-slot id c))))
  ((:instance fn2-env-release-pools-unit-chain (a c))))
(defthm fn2-env-commit-start-j5-other
  ; admission keeps J5's evidence of every other commit row
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp i fn2-core)
                (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
           (fn2-env-j5-kept i fn2-core (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core))))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-env-j5-kept-refl fn2-env-reserve-pools-kept-chain
                                               fn2-env-reserve-extent-kept-chain fn2-env-release-pools-kept-chain
                                               fn2-env-start-write-kept-chain fn2-env-prepare-root-kept-chain
                                               fn2-env-ready-kept-chain fn2-env-core-stop-kept-chain
                                               fn2-env-reserve-pools-keeps-ids fn2-env-reserve-extent-keeps-ids fn2-env-start-write-keeps-ids-rewrite
                                               fn2-env-prepare-root-keeps-ids fn2-env-ready-keeps-ids
                                               fn2-env-release-pools-keeps-ids fn2-env-core-stop-keeps-ids
                                               fn2-commit-reserve-pools-shape fn2-commit-reserve-extent-preserves-type
                                               fn2-commit-reserve-extent-preserves-wfp fn2-commit-prepare-root-type fn2-commit-prepare-root-wfp fn2-core-stop-type fn2-core-stop-wfp
                                               fn2-env-commit-idp-u32 fn2-env-generation-u60 fn2-env-generation-natp
                                               fn2-env-gen-limit-natp fn2-env-gen-limit-bound unsigned-byte-p integer-range-p posp)
                                             (theory 'fn2-arm-frame-base)))))
;; THE ADMITTED ROW. J5 at :free says no live operation of the row is at its
;; generation; a refused admission leaves the row free with its generation,
;; fence flag and the ops table (FN2-ENV-J5-FREE-KEPT), and an accepted one
;; opens it at :collect with a generation no lower and no fence
;; (FN2-ENV-J5-FREE-TO-COLLECT); J6 and J6P ask nothing of either phase.
(defun-nx fn2-env-free-to-collect (id a b)
  ; B opens row ID, free in A, at :collect with a generation no lower and no
  ; fence, over the same ops table
  (and (fn2-env-ok b a) (fn2-commit-idp id a) (fn2-commit-idp id b)
       (equal (fn2-machine-phase id a) *fn2-commit-state-free*)
       (equal (fn2-machine-phase id b) *fn2-commit-state-collect*)
       (natp (fn2-machine-generation id a)) (natp (fn2-machine-generation id b))
       (<= (fn2-machine-generation id a) (fn2-machine-generation id b))
       (equal (fn2-machine-cb-fence-live id b) 0)))
(defthm fn2-env-j5-op-free-to-collect
  (implies (and (fn2-env-free-to-collect id a b) (fn2-env-j5-op s id log a))
           (and (fn2-env-j5-op s id log b) (equal (fn2-env-owned-fence-at s id b) 0)))
  :hints (("Goal" :in-theory (e/d (fn2-env-free-to-collect fn2-env-j5-op fn2-env-owned-fence-at)
                                  (fn2-env-op fn2-env-io fn2-env-j5-fence fn2-commit-row fn2-env-ok))
           :use ((:instance fn2-env-op-of-ok)))))
(defthm fn2-env-j5-ops-free-to-collect
  (implies (and (fn2-env-free-to-collect id a b) (fn2-env-j5-ops s k id log a))
           (and (fn2-env-j5-ops s k id log b) (equal (fn2-env-owned-fences s k id b) 0)))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-owned-fences fn2-env-j5-op-free-to-collect (:e zp) (:e binary-+) fix)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-j5-free-to-collect
  ; the phase-free argument: J5 at :free says no live operation of the row is
  ; at its generation, so a row opened at :collect with a generation no lower
  ; owns none at its new one; J6 and J6P ask nothing at :collect
  (implies (and (fn2-env-free-to-collect id a b) (fn2-env-j5-row id log a))
           (and (fn2-env-j5-row id log b) (fn2-env-j6-row id b) (fn2-env-j6p-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-row fn2-env-j6-row fn2-env-j6p-row fn2-env-j5-roles
                                               fn2-env-j5-ops-free-to-collect fn2-env-free-to-collect
                                               (:e member-equal) (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn2-env-op-of-ok (s 0))
                 (:instance fn2-env-j5-ops-free-to-collect (s 0) (k (fn2-env-ops-rows a)))))))
(defun-nx fn2-env-free-kept (id a b)
  ; row ID is free in A and B with one generation, no fence and one ops table
  (and (fn2-env-ok b a) (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
       (equal (fn2-machine-phase id a) *fn2-commit-state-free*)
       (equal (fn2-machine-phase id b) *fn2-commit-state-free*)
       (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
       (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))))
(defthm fn2-env-j5-op-free-kept
  (implies (fn2-env-free-kept id a b)
           (and (equal (fn2-env-j5-op s id log b) (fn2-env-j5-op s id log a))
                (equal (fn2-env-owned-fence-at s id b) (fn2-env-owned-fence-at s id a))))
  :hints (("Goal" :in-theory (e/d (fn2-env-free-kept fn2-env-j5-op fn2-env-owned-fence-at)
                                  (fn2-env-op fn2-env-io fn2-env-j5-fence fn2-commit-row fn2-env-ok))
           :use ((:instance fn2-env-op-of-ok)))))
(defthm fn2-env-j5-ops-free-kept
  (implies (fn2-env-free-kept id a b)
           (equal (fn2-env-j5-ops s k id log b) (fn2-env-j5-ops s k id log a)))
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-j5-op-free-kept) (theory 'minimal-theory)))))
(defthm fn2-env-owned-fences-free-kept
  (implies (fn2-env-free-kept id a b)
           (equal (fn2-env-owned-fences s k id b) (fn2-env-owned-fences s k id a)))
  :hints (("Goal" :induct (fn2-env-owned-fences s k id a)
           :in-theory (union-theories '(fn2-env-owned-fences fn2-env-j5-op-free-kept) (theory 'minimal-theory)))))
(defthm fn2-env-j5-free-kept
  ; a free row's J5 reads its generation, fence flag and the ops table; J6
  ; and J6P ask nothing of it
  (implies (and (fn2-env-free-kept id a b) (fn2-env-j5-row id log a))
           (and (fn2-env-j5-row id log b) (fn2-env-j6-row id b) (fn2-env-j6p-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j5-row fn2-env-j6-row fn2-env-j6p-row fn2-env-j5-roles
                                               fn2-env-free-kept (:e member-equal) (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn2-env-op-of-ok (s 0))
                 (:instance fn2-env-j5-ops-free-kept (s 0) (k (fn2-env-ops-rows a)))
                 (:instance fn2-env-owned-fences-free-kept (s 0) (k (fn2-env-ops-rows a)))))))
(defthm fn2-env-free-kept-base
  (implies (equal (fn2-machine-phase id c) *fn2-commit-state-free*) (fn2-env-free-kept id c c))
  :hints (("Goal" :in-theory '(fn2-env-free-kept fn2-env-ok-refl))))
(fn2-env-row-chain fn2-env-free-kept fn2-env-reserve-pools-free-kept (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen c)) nil)
(fn2-env-row-chain fn2-env-free-kept fn2-env-reserve-extent-free-kept (mv-nth 1 (fn2-commit-reserve-extent id c)) nil)
(fn2-env-row-chain fn2-env-free-kept fn2-env-release-pools-free-kept (fn2-commit-release-pools left id owner-gen c) nil)
(fn2-env-row-chain fn2-env-free-to-collect fn2-env-prepare-root-free-to-collect (fn2-commit-prepare-root id c) nil)
(fn2-env-row-chain fn2-env-free-to-collect fn2-env-ready-free-to-collect (fn2-commit-ready id c) nil)
(defthm fn2-env-commit-row-gen-reads
  (implies (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
           (and (equal (fn2-commit-row-generation id fn2-core) (fn2-machine-generation id fn2-core))
                (equal (fn2-commit-row-cb-fence-live id fn2-core) (fn2-machine-cb-fence-live id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-row-generation fn2-commit-row-cb-fence-live fn2-machine-generation
                                   fn2-machine-cb-fence-live fn2-machine-generation-read-code fn2-machine-cb-fence-live-read-code
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp)))))
(defthm fn2-env-same-slot-gen
  (implies (and (fn2-commit-idp i fn2-core) (fn2-commit-idp id fn2-core)
                (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
           (and (equal (fn2-machine-generation i fn2-core) (fn2-machine-generation id fn2-core))
                (equal (fn2-machine-cb-fence-live i fn2-core) (fn2-machine-cb-fence-live id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-idp fn2-commit-snapshot-read-code fn2-machine-phase-read-code
                                   fn2-machine-generation fn2-machine-generation-read-code
                                   fn2-machine-cb-fence-live fn2-machine-cb-fence-live-read-code)
                                  (fn2-machine-kind fn2-machine-slot)))))
(defun fn2-env-start-self-args (ord wformals owner)
  ; the admission's write arguments, by column
  (declare (xargs :mode :program))
  (if (atom ord) nil
    (cons (list (car wformals)
                (case (car ord)
                  (phase *fn2-commit-state-collect*) (generation owner) (batch-no '(mv-nth 0 (fn2-commit-frontier c)))
                  (member-count 'members) (first-key 'first-key) (partner 'partner) (cb-mode 'mode)
                  (cb-stage *fn2-commit-seal-stage-zero-dependency*) (cb-reason *fn2-commit-reason-none*) (otherwise 0)))
          (fn2-env-start-self-args (cdr ord) (cdr wformals) owner))))
(defun fn2-env-start-self-events (world)
  ; the admitted row through the accepted write: free before, :collect after
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (formals (formals w world))
         (wformals (butlast (cdr formals) 1))
         (call (cons w formals))
         (gen (nth (position-eq 'generation ord) wformals))
         (fl (nth (position-eq 'cb-fence-live ord) wformals))
         (e (fn2-arm-frame-known w kind world))
         (ch (fn2-arm-frame-entry-s e))
         (c2 '(mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))
         (call2 (cons w (append (butlast formals 1) (list c2))))
         (fits (nthcdr 5 (fn2-arm-frame-write-guards kind ord wformals world)))
         (written `((equal ,(nth (position-eq 'phase ord) wformals) ,*fn2-commit-state-collect*)
                    (equal ,(nth (position-eq 'cb-deps-ok ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-log-ok ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-acks ord) wformals) 0)
                    (posp ,(nth (position-eq 'batch-no ord) wformals))
                    (equal ,(nth (position-eq 'cb-done ord) wformals) 0)
                    (equal ,(nth (position-eq 'cb-fence-ok ord) wformals) 0)))
         (ok-ext '(eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok)))
    `((defthm fn2-env-start-write-gen
        ; what the accepted write leaves in the row's generation and fence flag
        (implies (and (fn2-env-start-write-accepted ,@formals) (fn2-commit-idp id fn2-core))
                 (and (equal (fn2-machine-generation id ,call) ,gen)
                      (equal (fn2-machine-cb-fence-live id ,call) ,fl)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-start-write-accepted) (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-READS"))
                       (:instance fn2-env-start-write-keeps-ids (x id))
                       (:instance fn2-commit-idp (fn2-core ,call))
                       (:instance fn2-env-commit-row-gen-reads (fn2-core ,call))))))
      (defthm fn2-env-start-write-ops-pool
        ; the write leaves the ops table and the pool
        (and (equal (nth 1 ,call) (nth 1 fn2-core)) (equal (nth 0 ,call) (nth 0 fn2-core)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-ctf-dir-refl) (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,(fn2-columns-sym w "-ARM-KIDS") (fn2-arm-free ',(cons 9 ch)) (fn2-arm-c0 fn2-core))
                       (:instance fn2-arm-kids-nth (i 0) (k 1) (free ',(cons 9 ch)) (a fn2-core) (b ,call))
                       (:instance fn2-arm-kids-nth (i 0) (k 0) (free ',(cons 9 ch)) (a fn2-core) (b ,call))))))
      (defthm fn2-env-start-tail-free-to-collect
        ; the extent reservation and the accepted write open a free row at
        ; :collect, at a generation no lower and with no fence
        (implies (and (fn2-env-free-kept id a fn2-core) (fn2-commit-idp id a) (fn2-corep a) (fn2-core-wfp a)
                      ,ok-ext ,@fits ,@written (equal ,fl 0) (natp ,gen) (<= (fn2-machine-generation id a) ,gen))
                 (fn2-env-free-to-collect id a ,call2))
        :hints (("Goal" :in-theory (union-theories '(fn2-env-free-to-collect fn2-env-free-kept fn2-env-start-write-accepted-suff)
                                                   (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance fn2-env-reserve-extent-free-kept (c fn2-core))
                       (:instance fn2-env-commit-idp-cell (fn2-core ,c2))
                       (:instance fn2-env-start-write-row (fn2-core ,c2))
                       (:instance fn2-env-start-write-gen (fn2-core ,c2))
                       (:instance fn2-env-start-write-keeps-ids (x id) (fn2-core ,c2))
                       (:instance fn2-env-start-write-ops-pool (fn2-core ,c2))
                       (:instance fn2-env-ok-of-nth (b ,call2) (x ,c2) (a a))
                       (:instance fn2-env-generation-natp (c a)))))))))
(make-event (value (cons 'progn (fn2-env-start-self-events (w state)))))
(defun fn2-env-start-cases-events (world)
  ; the three outcomes of admission for its own row
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (wformals (butlast (cdr (formals w world)) 1))
         (owner '(if (< 0 (fn2-machine-batch-no id c)) (+ 1 (fn2-machine-generation id c)) (fn2-machine-generation id c))))
    `((defthm fn2-env-commit-start-row-cases
        ; admission leaves every row's J5 evidence, or leaves its row ID free
        ; with one generation, or opens it at :collect
        (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-commit-idp i c))
                 (let ((b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                   (or (fn2-env-j5-kept i c b)
                       (and (fn2-commit-idp id c) (fn2-env-free-kept id c b))
                       (and (fn2-commit-idp id c) (fn2-env-free-to-collect id c b)))))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-env-j5-kept-refl fn2-env-core-stop-kept-chain
                                                     fn2-env-free-kept-base fn2-env-reserve-pools-free-kept fn2-env-reserve-extent-free-kept
                                                     fn2-env-release-pools-free-kept
                                                     fn2-env-prepare-root-free-to-collect fn2-env-ready-free-to-collect
                                                     fn2-commit-reserve-pools-shape fn2-commit-reserve-extent-preserves-type
                                                     fn2-commit-reserve-extent-preserves-wfp
                                                     fn2-env-commit-idp-u32 fn2-env-generation-u60 fn2-env-generation-natp
                                                     fn2-env-gen-limit-natp fn2-env-gen-limit-bound unsigned-byte-p integer-range-p posp natp)
                                                   (theory 'fn2-arm-frame-base))
                 :use ((:instance fn2-env-commit-idp-u32 (x partner)) (:instance fn2-env-generation-u60)
                       (:instance fn2-env-start-tail-free-to-collect (a c)
                                  (fn2-core (mv-nth 1 (fn2-commit-reserve-pools 4 id ,owner c)))
                                  ,@(fn2-env-start-self-args ord wformals owner)))))))))
(make-event (value (cons 'progn (fn2-env-start-cases-events (w state)))))
(defthm fn2-env-commit-start-keeps-ids
  (and (equal (fn2-commit-idp x (mv-nth 1 (fn2-commit-start id members first-key mode partner c))) (fn2-commit-idp x c))
       (equal (fn2-machine-slot x (mv-nth 1 (fn2-commit-start id members first-key mode partner c))) (fn2-machine-slot x c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-env-reserve-pools-keeps-ids fn2-env-reserve-extent-keeps-ids
                                               fn2-env-start-write-keeps-ids-rewrite fn2-env-prepare-root-keeps-ids
                                               fn2-env-ready-keeps-ids fn2-env-release-pools-keeps-ids fn2-env-core-stop-keeps-ids)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-free-kept-same-slot
  ; every readable id at the row's slot reads its phase, generation and fence flag
  (implies (and (fn2-env-free-kept id a b) (fn2-commit-idp id a) (fn2-commit-idp i a)
                (equal (fn2-machine-slot i a) (fn2-machine-slot id a))
                (equal (fn2-commit-idp i b) (fn2-commit-idp i a)) (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-machine-slot i b) (fn2-machine-slot i a)) (equal (fn2-machine-slot id b) (fn2-machine-slot id a)))
           (fn2-env-free-kept i a b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-free-kept)
           :use ((:instance fn2-env-same-slot-reads (fn2-core a)) (:instance fn2-env-same-slot-reads (fn2-core b))
                 (:instance fn2-env-same-slot-gen (fn2-core a)) (:instance fn2-env-same-slot-gen (fn2-core b))))))
(defthm fn2-env-free-to-collect-same-slot
  (implies (and (fn2-env-free-to-collect id a b) (fn2-commit-idp i a)
                (equal (fn2-machine-slot i a) (fn2-machine-slot id a))
                (equal (fn2-commit-idp i b) (fn2-commit-idp i a))
                (equal (fn2-machine-slot i b) (fn2-machine-slot i a)) (equal (fn2-machine-slot id b) (fn2-machine-slot id a)))
           (fn2-env-free-to-collect i a b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-free-to-collect)
           :use ((:instance fn2-env-same-slot-reads (fn2-core a)) (:instance fn2-env-same-slot-reads (fn2-core b))
                 (:instance fn2-env-same-slot-gen (fn2-core a)) (:instance fn2-env-same-slot-gen (fn2-core b))))))
(defthm fn2-env-j56-not-idp
  (implies (not (fn2-commit-idp i c))
           (and (fn2-env-j5-row i log c) (fn2-env-j6-row i c) (fn2-env-j6p-row i c)
                (fn2-env-j6l-row i c) (fn2-env-j6s-row i c)))
  :hints (("Goal" :in-theory '(fn2-env-j5-row fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row))))
(defthm fn2-env-j6ls-quiet
  ; J6L and J6S ask nothing of a free row or one at :collect
  (implies (member-equal (fn2-machine-phase i c) (list *fn2-commit-state-free* *fn2-commit-state-collect*))
           (and (fn2-env-j6l-row i c) (fn2-env-j6s-row i c)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6l-row fn2-env-j6s-row member-equal (:e member-equal) (:e car) (:e cdr) (:e consp)))))
(defthm fn2-env-commit-start-j5-row
  ; admission keeps J5, J6 and J6P of every commit row: the admitted row by
  ; the phase-free argument, every other by its kept evidence
  (implies (and (fn2-corep c) (fn2-core-wfp c)
                (fn2-env-j5-row i log c) (fn2-env-j6-row i c) (fn2-env-j6p-row i c))
           (let ((b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
             (and (fn2-env-j5-row i log b) (fn2-env-j6-row i b) (fn2-env-j6p-row i b))))
  :hints (("Goal" :in-theory nil :do-not-induct t
           :use ((:instance fn2-env-commit-start-keeps-ids (x i))
                 (:instance fn2-env-commit-start-keeps-ids (x id))
                 (:instance fn2-env-j56-not-idp (c (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-commit-start-row-cases)
                 (:instance fn2-env-commit-start-j5-other (fn2-core c))
                 (:instance fn2-env-j5-kept-transfer (id i) (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-free-kept-same-slot (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-free-to-collect-same-slot (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-j5-free-kept (id i) (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-j5-free-to-collect (id i) (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))))))
(defthm fn2-env-commit-start-j6ls-row
  ; admission keeps J6L and J6S of every commit row: the admitted row is left
  ; free or opened at :collect, every other keeps its units, pool rows and leases
  (implies (and (fn2-corep c) (fn2-core-wfp c)
                (fn2-env-j6p-row i c) (fn2-env-j6l-row i c) (fn2-env-j6s-row i c))
           (let ((b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
             (and (fn2-env-j6l-row i b) (fn2-env-j6s-row i b))))
  :hints (("Goal" :in-theory '(fn2-env-free-kept fn2-env-free-to-collect (:e member-equal) member-equal (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :use ((:instance fn2-env-commit-start-keeps-ids (x i))
                 (:instance fn2-env-commit-start-keeps-ids (x id))
                 (:instance fn2-env-j56-not-idp (c (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-j6ls-quiet (c (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-commit-start-row-cases)
                 (:instance fn2-env-commit-start-j5-other (fn2-core c))
                 (:instance fn2-env-j6ls-kept-transfer (id i) (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-free-kept-same-slot (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
                 (:instance fn2-env-free-to-collect-same-slot (a c) (b (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))))))
(make-event (value (cons 'progn (fn2-env-keeps-ids-events
  '((fn2-env-put-members-keeps-ids (mv-nth 1 (fn2-commit-put-members left m row kind okind oslot ogen event c)) fn2-commit-put-members-fn2-env-tk)
    (fn2-env-exec-wake-keeps-ids (fn2-exec-wake id c) fn2-exec-wake-fn2-env-tk))))))
(defun-nx fn2-env-j56-row (id log c)
  (and (fn2-env-j5-row id log c) (fn2-env-j6-row id c) (fn2-env-j6p-row id c)
       (fn2-env-j6l-row id c) (fn2-env-j6s-row id c)))
(defthm fn2-env-commit-start-j56
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j56-row i log c))
           (fn2-env-j56-row i log (mv-nth 1 (fn2-commit-start id members first-key mode partner c))))
  :hints (("Goal" :in-theory '(fn2-env-j56-row) :use (fn2-env-commit-start-j5-row fn2-env-commit-start-j6ls-row))))
(fn2-env-j56-step fn2-env-j56-put-members (mv-nth 1 (fn2-commit-put-members left m row kind okind oslot ogen event c))
  fn2-env-put-members-kept-chain fn2-env-put-members-keeps-ids)
(fn2-env-j56-step fn2-env-j56-core-stop (fn2-core-stop reason c) fn2-env-core-stop-kept-chain fn2-env-core-stop-keeps-ids)
(fn2-env-j56-step fn2-env-j56-exec-wake (fn2-exec-wake id c) fn2-env-exec-wake-kept-chain fn2-env-exec-wake-keeps-ids)
(defthm fn2-env-admit-j56
  ; :admit keeps J5, J6 and J6P of every commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j56-row i log c))
           (fn2-env-j56-row i log (fn2-env-admit members mode c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-j56
                                               fn2-env-j56-put-members fn2-env-j56-core-stop fn2-env-j56-exec-wake)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-j5-rows-admit
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-rows ids log c) (fn2-env-j6p-rows ids c)
                (fn2-env-j6l-rows ids c) (fn2-env-j6s-rows ids c))
           (let ((b (fn2-env-admit members mode c)))
             (and (fn2-env-j5-rows ids log b) (fn2-env-j6p-rows ids b) (fn2-env-j6l-rows ids b) (fn2-env-j6s-rows ids b))))
  :hints (("Goal" :induct (fn2-env-j6p-rows ids c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j6p-rows fn2-env-j6l-rows fn2-env-j6s-rows)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-admit-j56 (i (car ids))))
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j6p-rows fn2-env-j6l-rows fn2-env-j6s-rows fn2-env-j56-row)
                                      (theory 'minimal-theory)))))
;; THE POOL STAYS SEMANTIC ACROSS ADMISSION: its reservations and releases
;; conserve it (FN2-POOL-RESERVE-/RELEASE-CONSERVATION); every other callee
;; leaves the pool child (PK, or its own frame).
(defthm fn2-env-semanticp-of-pool-child
  (implies (and (equal (nth 0 b) (nth 0 a)) (fn2-core-pool-semanticp a)) (fn2-core-pool-semanticp b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-core-pool-semanticp fn2-core-pool))))
(fn2-env-sem-by-pk fn2-env-reserve-extent-semanticp (mv-nth 1 (fn2-commit-reserve-extent id c)))
(fn2-env-sem-by-pk fn2-env-prepare-root-semanticp (fn2-commit-prepare-root id c))
(fn2-env-sem-by-pk fn2-env-ready-semanticp (fn2-commit-ready id c))
(fn2-env-sem-by-pk fn2-env-put-members-semanticp (mv-nth 1 (fn2-commit-put-members left m row kind okind oslot ogen event c)))
(fn2-env-sem-by-pk fn2-env-exec-wake-semanticp (fn2-exec-wake id c))
(defthm fn2-env-core-stop-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (fn2-core-stop reason c)))
  :hints (("Goal" :in-theory '(fn2-env-core-stop-keeps-io-pool (:e nfix))
           :use ((:instance fn2-env-semanticp-of-pool-child (a c) (b (fn2-core-stop reason c)))))))
(defthm fn2-env-core-reserve-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (mv-nth 3 (fn2-core-reserve class okind oslot ogen c))))
  :hints (("Goal" :in-theory (e/d (fn2-core-reserve fn2-core-pool-semanticp) (fn2-pool-semanticp fn2-pool-reserve))
           :use ((:instance fn2-pool-reserve-conservation (fn2-pool (fn2-core-pool c)))))))
(defthm fn2-env-core-release-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (mv-nth 1 (fn2-core-release slot gen okind oslot ogen c))))
  :hints (("Goal" :in-theory (e/d (fn2-core-pool-semanticp) (fn2-pool-semanticp fn2-pool-release fn2-core-release-children fn2-core-release))
           :use ((:instance fn2-env-core-release-is)
                 (:instance fn2-env-release-children-pool (p (fn2-core-pool c)) (ctl (fn2-core-control c)))
                 (:instance fn2-pool-release-conservation (fn2-pool (fn2-core-pool c)))))))
(defthm fn2-env-keep-pool-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (fn2-commit-keep-pool id role slot gen c)))
  :hints (("Goal" :in-theory '(fn2-commit-keep-pool (:e nfix)) :cases ((and (natp role) (< role 3)))
           :use ((:instance fn2-env-save-pool-keeps-pool)
                 (:instance fn2-env-keep-pool-scratch-children)
                 (:instance fn2-env-semanticp-of-pool-child (a c) (b (fn2-commit-keep-pool id role slot gen c)))))))
(defthm fn2-env-release-pool-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))
  :hints (("Goal" :in-theory '(fn2-env-release-pool-unchecked fn2-env-core-stop-semanticp fn2-env-core-release-semanticp (:e nfix))
           :cases ((fn2-commit-idp id c))
           :use ((:instance fn2-env-release-pool-pool)
                 (:instance fn2-env-semanticp-of-pool-child (a (mv-nth 1 (fn2-core-release
                                  (if (equal role 3) (fn2-machine-pool-slot id c) (mv-nth 3 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  (if (equal role 3) (fn2-machine-pool-gen id c) (mv-nth 4 (fn2-commit-resource id (if (equal role 3) 0 role) c)))
                                  *fn2-commit-kind* id owner-gen c)))
                            (b (mv-nth 1 (fn2-commit-release-pool id role owner-gen c))))))))
(defthm fn2-env-unwind-pool-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (fn2-commit-unwind-pool id role owner-gen c)))
  :hints (("Goal" :in-theory '(fn2-commit-unwind-pool fn2-env-release-pool-semanticp fn2-env-core-stop-semanticp))))
(defthm fn2-env-reserve-pools-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen c))))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen c)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-env-core-reserve-semanticp fn2-env-keep-pool-semanticp
                                        fn2-env-unwind-pool-semanticp)
                                      (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-release-pools-semanticp
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (fn2-commit-release-pools left id owner-gen c)))
  :hints (("Goal" :induct (fn2-commit-release-pools left id owner-gen c)
           :in-theory (union-theories '(fn2-commit-release-pools fn2-env-release-pool-semanticp fn2-env-core-stop-semanticp)
                                      (theory 'fn2-arm-frame-base)))))
(defun fn2-env-start-write-sem-events (world)
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit)
         (fields '(phase member-count first-key cb-mode batch-no partner principal-slot stopped generation
                   cb-stage cb-cursor cb-issued cb-done cb-bytes cb-failed outcome cb-reason cb-fence-live
                   cb-fence-ok cb-deps-ok cb-log-ok cb-published cb-acks cb-seal-len deadline cb-wrote cb-open
                   dep-bytes rec-bytes))
         (ord (fn2-arms-cols-order fields (fn2-machine-property kind :columns world)))
         (w (fn2-arms-write-name kind ord))
         (call (cons w (formals w world))))
    `((defthm fn2-env-start-write-semanticp
        (implies (fn2-core-pool-semanticp fn2-core) (fn2-core-pool-semanticp ,call))
        :hints (("Goal" :in-theory nil
                 :use ((:instance fn2-env-start-write-ops-pool)
                       (:instance fn2-env-semanticp-of-pool-child (a fn2-core) (b ,call)))))))))
(make-event (value (cons 'progn (fn2-env-start-write-sem-events (w state)))))
(defthm fn2-env-admit-semanticp
  ; admission keeps the pool semantic
  (implies (fn2-core-pool-semanticp c) (fn2-core-pool-semanticp (fn2-env-admit members mode c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-commit-start
                                               fn2-env-reserve-pools-semanticp fn2-env-reserve-extent-semanticp
                                               fn2-env-release-pools-semanticp fn2-env-start-write-semanticp
                                               fn2-env-prepare-root-semanticp fn2-env-ready-semanticp fn2-env-core-stop-semanticp
                                               fn2-env-put-members-semanticp fn2-env-exec-wake-semanticp)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-j5-rows-admit-step
  ; :admit keeps J5, J6, J6P, J6L and J6S, and the pool stays semantic
  (implies (and (equal (fn2-env-tag action) :admit) (fn2-corep c) (fn2-core-wfp c)
                (fn2-core-pool-semanticp c) (true-listp log) (fn2-env-j5-rows ids log c) (fn2-env-j6p-rows ids c)
                (fn2-env-j6l-rows ids c) (fn2-env-j6s-rows ids c))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (and (fn2-env-j5-rows ids (append log (if entry (list entry) nil)) after)
                  (fn2-env-j6p-rows ids after) (fn2-env-j6l-rows ids after) (fn2-env-j6s-rows ids after)
                  (fn2-core-pool-semanticp after))))
  :hints (("Goal" :in-theory (union-theories '(append-to-nil (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-step-admit-unfolds (fn2-core c))
                 (:instance fn2-env-j5-rows-admit (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))
                 (:instance fn2-env-admit-semanticp (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))))))
;; J5E ACROSS :ADMIT. J5E reads a row's phase, its units' operation and loan
;; columns, the ops table, its generation (the owned fences) and its pending
;; count. Admission writes none of the directory, the commit table's pending
;; column (FN2-ENV-PDK), commit-io's operation and loan columns (FN2-ENV-LK)
;; or the ops table (FN2-ENV-OK), so every row's live roles and pending count stay;
;; its phase stays but for the admitted row, opened from :free (no role
;; live, J5E) at :collect (no role live asked) owning no fence at its new
;; generation (FN2-ENV-J5-OPS-FREE-TO-COLLECT).
(fn2-defview fn2-env-pdk :carrier fn2-core
  :select ((fn2-machines :columns (kind slot) :rows t :scalars (rows))
           (fn2-commit :columns (pending) :rows t :scalars (rows))))
(fn2-defview fn2-env-lk :carrier fn2-core
  :select ((fn2-commit-io :columns (op-slot op-gen lent) :rows t :scalars (rows))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-pdk)
  '(fn2-commit-start fn2-commit-put-members fn2-core-stop fn2-exec-wake) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-lk)
  '(fn2-commit-put-members fn2-core-stop fn2-exec-wake fn2-commit-save-pool fn2-commit-keep-pool fn2-commit-release-pool
    fn2-commit-unwind-pool fn2-core-reserve fn2-core-release fn2-commit-prepare-root fn2-commit-ready) (w state)))))
(defthm fn2-commit-reserve-extent-fn2-env-lk
  (implies (fn2-env-lk fn2-core fn2-rel-c0)
           (fn2-env-lk (mv-nth 1 (fn2-commit-reserve-extent id fn2-core)) fn2-rel-c0))
  :hints (("Goal" :in-theory (e/d (fn2-commit-reserve-extent fn2-env-lk fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   fn2-env-core-stop-keeps-io-pool update-nth-array nth-update-nth)
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop nth update-nth)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-lk) '(fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes) (w state)))))
(defthm fn2-commit-reserve-pools-fn2-env-lk
  (implies (fn2-env-lk fn2-core fn2-rel-c0)
           (fn2-env-lk (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-core-reserve-fn2-env-lk fn2-commit-keep-pool-fn2-env-lk
                                        fn2-commit-unwind-pool-fn2-env-lk)
                                      (theory 'fn2-arm-frame-base)))))
(defthm fn2-commit-release-pools-fn2-env-lk
  (implies (fn2-env-lk fn2-core fn2-rel-c0)
           (fn2-env-lk (fn2-commit-release-pools left id owner-gen fn2-core) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-release-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-release-pools fn2-commit-release-pool-fn2-env-lk fn2-core-stop-fn2-env-lk)
                                      (theory 'fn2-arm-frame-base)))))
(defthm fn2-commit-start-fn2-env-lk
  (implies (fn2-env-lk fn2-core fn2-rel-c0)
           (fn2-env-lk (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)) fn2-rel-c0))
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-start fn2-commit-reserve-pools-fn2-env-lk fn2-commit-reserve-extent-fn2-env-lk
                                               fn2-commit-release-pools-fn2-env-lk fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes-fn2-env-lk
                                               fn2-commit-prepare-root-fn2-env-lk fn2-commit-ready-fn2-env-lk fn2-core-stop-fn2-env-lk)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-machine-pending-of-pdk
  (implies (and (fn2-env-pdk b a) (equal (fn2-machine-kind id a) *fn2-commit-kind*))
           (equal (fn2-machine-pending id b) (fn2-machine-pending id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-pdk fn2-ctf-dir fn2-machines-directory-keeps
                                  fn2-machine-pending fn2-machine-pending-read-code fn2-commit-table fn2-commit-rows
                                  fn2-commit-pending fn2-commit-pending$ai)
                                 (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)))))
(defthm fn2-env-io-of-lk
  ; a unit's validity, operation and loan
  (implies (fn2-env-lk b a)
           (and (equal (nth 0 (fn2-env-io u b)) (nth 0 (fn2-env-io u a)))
                (equal (nth 1 (fn2-env-io u b)) (nth 1 (fn2-env-io u a)))
                (equal (nth 2 (fn2-env-io u b)) (nth 2 (fn2-env-io u a)))
                (equal (nth 3 (fn2-env-io u b)) (nth 3 (fn2-env-io u a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-lk fn2-env-io fn2-core-commit-io))))
(defthm fn2-env-role-live-of-lk
  (implies (and (fn2-env-lk b a) (fn2-env-ok b a) (equal (fn2-commit-row id b) (fn2-commit-row id a)))
           (equal (fn2-env-role-live id role b) (fn2-env-role-live id role a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-live fn2-env-role-io fn2-env-op-of-ok)
           :use ((:instance fn2-env-io-of-lk (u (+ (* 3 (fn2-commit-row id a)) role)))))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-ok) '(fn2-commit-start) (w state)))))
(defthm fn2-env-j5e-row-of-parts
  ; J5E at B from J5E at A, when B keeps the row's live roles and pending
  ; count, owns no more fences, and keeps its phase or opens it from :free
  ; at :collect
  (implies (and (fn2-env-j5e-row id a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-env-role-live id 0 b) (fn2-env-role-live id 0 a))
                (equal (fn2-env-role-live id 1 b) (fn2-env-role-live id 1 a))
                (equal (fn2-env-role-live id 2 b) (fn2-env-role-live id 2 a))
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a))
                (<= (fn2-env-owned-fences 0 (fn2-env-ops-rows b) id b) (fn2-env-owned-fences 0 (fn2-env-ops-rows a) id a))
                (implies (member-equal (fn2-machine-phase id b)
                                       (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                         (and (equal (fn2-machine-cb-bytes id b) (fn2-machine-cb-bytes id a))
                              (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a))))
                (or (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                    (and (equal (fn2-machine-phase id a) *fn2-commit-state-free*)
                         (equal (fn2-machine-phase id b) *fn2-commit-state-collect*))))
           (fn2-env-j5e-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live fn2-env-b2n nfix
                               (:type-prescription fn2-env-owned-fences) member-equal (:e member-equal)
                               car-cons cdr-cons (:e car) (:e cdr) (:e consp)))))
(defthm fn2-env-j5e-row-of-views
  ; a step keeping the directory, J5's commit columns, the ops table and
  ; J5E's columns keeps J5E
  (implies (and (fn2-env-tk b a) (fn2-env-mk b a) (fn2-env-ok b a) (fn2-env-pdk b a) (fn2-env-lk b a))
           (equal (fn2-env-j5e-row id b) (fn2-env-j5e-row id a)))
  :hints (("Goal" :in-theory '(fn2-env-j5e-row fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live fn2-env-owned-fences-of-ok
                               fn2-env-op-of-ok)
           :cases ((fn2-commit-idp id a))
           :use ((:instance fn2-env-read-codes-of-tk) (:instance fn2-machine-phase-of-tk)
                 (:instance fn2-machine-cb-done-of-tk) (:instance fn2-machine-cb-bytes-of-mk)
                 (:instance fn2-machine-generation-of-mk) (:instance fn2-machine-pending-of-pdk)
                 (:instance fn2-env-commit-idp-kind (fn2-core a))
                 (:instance fn2-env-role-live-of-lk (role 0)) (:instance fn2-env-role-live-of-lk (role 1))
                 (:instance fn2-env-role-live-of-lk (role 2))))))
(fn2-env-j5e-step fn2-env-j5e-put-members (mv-nth 1 (fn2-commit-put-members left m row kind okind oslot ogen event c)))
(fn2-env-j5e-step fn2-env-j5e-core-stop (fn2-core-stop reason c))
(fn2-env-j5e-step fn2-env-j5e-exec-wake (fn2-exec-wake id c))
(defthm fn2-env-commit-start-j5e-reads
  ; admission's row write keeps every commit row's live roles and pending count
  (implies (fn2-commit-idp i c)
           (and (equal (fn2-env-role-live i 0 (fn2-env-cs-b)) (fn2-env-role-live i 0 c))
                (equal (fn2-env-role-live i 1 (fn2-env-cs-b)) (fn2-env-role-live i 1 c))
                (equal (fn2-env-role-live i 2 (fn2-env-cs-b)) (fn2-env-role-live i 2 c))
                (equal (fn2-machine-pending i (fn2-env-cs-b)) (fn2-machine-pending i c))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-row fn2-env-pdk-reflexive fn2-env-lk-reflexive fn2-env-ok-reflexive)
           :do-not-induct t
           :use ((:instance fn2-env-commit-start-keeps-ids (x i))
                 (:instance fn2-commit-start-fn2-env-pdk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-commit-start-fn2-env-lk (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-commit-start-fn2-env-ok (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-env-commit-idp-kind (id i) (fn2-core c))
                 (:instance fn2-machine-pending-of-pdk (id i) (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-role-live-of-lk (id i) (role 0) (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-role-live-of-lk (id i) (role 1) (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-role-live-of-lk (id i) (role 2) (a c) (b (fn2-env-cs-b)))))))
(defthm fn2-env-j5e-phase-of-j5-kept
  (implies (fn2-env-j5-kept id a b)
           (and (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-bytes id b) (fn2-machine-cb-bytes id a))
                (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a))
                (equal (fn2-env-owned-fences 0 (fn2-env-ops-rows b) id b) (fn2-env-owned-fences 0 (fn2-env-ops-rows a) id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-kept fn2-env-j5-evidence-reads fn2-env-j5-evidence-op fn2-env-owned-fences-congruence))))
(defthm fn2-env-j5e-phase-of-free-kept
  (implies (fn2-env-free-kept id a b)
           (and (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-phase id b) *fn2-commit-state-free*)
                (equal (fn2-env-owned-fences 0 (fn2-env-ops-rows b) id b) (fn2-env-owned-fences 0 (fn2-env-ops-rows a) id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-owned-fences-of-ok fn2-env-free-kept fn2-env-op-of-ok))))
(defthm fn2-env-j5e-phase-of-free-to-collect
  (implies (and (fn2-env-free-to-collect id a b) (fn2-env-j5-row id log a))
           (and (equal (fn2-machine-phase id a) *fn2-commit-state-free*)
                (equal (fn2-machine-phase id b) *fn2-commit-state-collect*)
                (equal (fn2-env-owned-fences 0 (fn2-env-ops-rows b) id b) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row fn2-env-free-to-collect fn2-env-op-of-ok)
           :use (
                 (:instance fn2-env-j5-ops-free-to-collect (s 0) (k (fn2-env-ops-rows a)))))))
(defthm fn2-env-commit-start-j5e-phase
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-row i log c) (fn2-commit-idp i c))
           (and (<= (fn2-env-owned-fences 0 (fn2-env-ops-rows (fn2-env-cs-b)) i (fn2-env-cs-b))
                    (fn2-env-owned-fences 0 (fn2-env-ops-rows c) i c))
                (implies (member-equal (fn2-machine-phase i (fn2-env-cs-b))
                                       (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                         (and (equal (fn2-machine-cb-bytes i (fn2-env-cs-b)) (fn2-machine-cb-bytes i c))
                              (equal (fn2-machine-cb-done i (fn2-env-cs-b)) (fn2-machine-cb-done i c))))
                (or (equal (fn2-machine-phase i (fn2-env-cs-b)) (fn2-machine-phase i c))
                    (and (equal (fn2-machine-phase i c) *fn2-commit-state-free*)
                         (equal (fn2-machine-phase i (fn2-env-cs-b)) *fn2-commit-state-collect*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '((:type-prescription fn2-env-owned-fences) member-equal (:e member-equal)) :do-not-induct t
           :use ((:instance fn2-env-commit-start-keeps-ids (x i))
                 (:instance fn2-env-commit-start-keeps-ids (x id))
                 (:instance fn2-env-commit-start-row-cases)
                 (:instance fn2-env-commit-start-j5-other (fn2-core c))
                 (:instance fn2-env-free-kept-same-slot (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-free-to-collect-same-slot (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-j5e-phase-of-j5-kept (id i) (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-j5e-phase-of-free-kept (id i) (a c) (b (fn2-env-cs-b)))
                 (:instance fn2-env-j5e-phase-of-free-to-collect (id i) (a c) (b (fn2-env-cs-b)))))))
(defthm fn2-env-commit-start-j5e-row
  ; admission's row write keeps J5E of every commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-row i log c) (fn2-env-j5e-row i c))
           (fn2-env-j5e-row i (fn2-env-cs-b)))
  :hints (("Goal" :in-theory '(fn2-env-j5e-row) :do-not-induct t
           :cases ((fn2-commit-idp i c))
           :use ((:instance fn2-env-commit-start-keeps-ids (x i))
                 (:instance fn2-env-commit-start-j5e-reads)
                 (:instance fn2-env-commit-start-j5e-phase)
                 (:instance fn2-env-j5e-row-of-parts (id i) (a c) (b (fn2-env-cs-b)))))))
(defthm fn2-env-admit-j5e
  ; :admit keeps J5E of every commit row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-row i log c) (fn2-env-j5e-row i c))
           (fn2-env-j5e-row i (fn2-env-admit members mode c)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-j5e-row
                                               fn2-env-j5e-put-members fn2-env-j5e-core-stop fn2-env-j5e-exec-wake)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-j5e-rows-admit
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-j5-rows ids log c) (fn2-env-j5e-rows ids c))
           (fn2-env-j5e-rows ids (fn2-env-admit members mode c)))
  :hints (("Goal" :induct (fn2-env-j5e-rows ids c)
           :in-theory (union-theories '(fn2-env-j5-rows fn2-env-j5e-rows fn2-env-admit-j5e) (theory 'minimal-theory)))))
(defthm fn2-env-j5e-rows-admit-step
  (implies (and (equal (fn2-env-tag action) :admit) (fn2-corep c) (fn2-core-wfp c)
                (fn2-env-j5-rows ids log c) (fn2-env-j5e-rows ids c))
           (fn2-env-j5e-rows ids (mv-nth 1 (fn2-env-step action nil image rlog c))))
  :hints (("Goal" :in-theory (union-theories '(mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e unary--)) (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-step-admit-unfolds (fn2-core c))
                 (:instance fn2-env-j5e-rows-admit (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))))))
;; FRESHNESS AND LENT-OK, ops-wide. An issue reserves the free head at its
;; slot's generation and lends a unit that names it; the issued write's
;; J5-TAKEN (no take of it yet) and its unit's role-live need that nothing
;; of that incarnation is in the log or in a unit before it was reserved.
;; FRESHNESS: every take in the log names a valid op slot at a generation
;; no newer than the slot's, and none names a free or reserved op at its
;; current generation (a recycle raises the generation, a retire leaves the
;; slot retired). LENT-OK: every lent unit names a valid op slot at a
;; generation no newer than the slot's, and never a free or reserved op at
;; its current generation.
(defun fn2-env-incarnation-ok (s g fn2-core)
  ; (S G) names an incarnation of op slot S that has begun and been issued
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (and (nth 0 op) (natp g) (<= g (nfix (nth 1 op)))
         (implies (equal g (nth 1 op))
                  (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))))))
(defun fn2-env-freshness (log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom log) t
    (and (implies (fn2-dev-takep (car log)) (fn2-env-incarnation-ok (nth 1 (car log)) (nth 2 (car log)) fn2-core))
         (fn2-env-freshness (cdr log) fn2-core))))
(defun-sk fn2-env-lent-ok (fn2-core)
  (forall u (let ((io (fn2-env-io u fn2-core)))
              (implies (and (nth 0 io) (equal (nth 3 io) 1))
                       (fn2-env-incarnation-ok (nth 1 io) (nth 2 io) fn2-core)))))
(in-theory (disable fn2-env-incarnation-ok))
;; The host steps but :take leave every op's validity, generation and phase
;; (FN2-ENV-OP-HEADS-KEPT) and every unit (FN2-ENV-UNITS-KEPT): FRESHNESS
;; and LENT-OK read nothing else.
(defun-sk fn2-env-op-heads-kept (a b)
  (forall s (and (equal (nth 0 (fn2-env-op s b)) (nth 0 (fn2-env-op s a)))
                 (equal (nth 1 (fn2-env-op s b)) (nth 1 (fn2-env-op s a)))
                 (equal (nth 2 (fn2-env-op s b)) (nth 2 (fn2-env-op s a))))))
(defun-sk fn2-env-units-kept (a b)
  (forall u (equal (fn2-env-io u b) (fn2-env-io u a))))
(defthm fn2-env-incarnation-ok-of-heads
  (implies (and (fn2-env-incarnation-ok s g a) (fn2-env-op-heads-kept a b))
           (fn2-env-incarnation-ok s g b))
  :hints (("Goal" :in-theory '(fn2-env-incarnation-ok) :use ((:instance fn2-env-op-heads-kept-necc)))))
(defthm fn2-env-freshness-of-heads
  (implies (and (fn2-env-freshness log a) (fn2-env-op-heads-kept a b))
           (fn2-env-freshness log b))
  :hints (("Goal" :induct (fn2-env-freshness log a)
           :in-theory (union-theories '(fn2-env-freshness fn2-env-incarnation-ok-of-heads) (theory 'minimal-theory)))))
(defthm fn2-env-freshness-append
  (equal (fn2-env-freshness (append x y) c) (and (fn2-env-freshness x c) (fn2-env-freshness y c)))
  :hints (("Goal" :induct (fn2-env-freshness x c)
           :in-theory (union-theories '(fn2-env-freshness binary-append car-cons cdr-cons default-car default-cdr) (theory 'ground-zero)))))
(defthm fn2-env-lent-ok-of-kept
  (implies (and (fn2-env-lent-ok a) (fn2-env-op-heads-kept a b) (fn2-env-units-kept a b))
           (fn2-env-lent-ok b))
  :hints (("Goal" :in-theory '(fn2-env-lent-ok fn2-env-incarnation-ok-of-heads)
           :use ((:instance fn2-env-units-kept-necc (u (fn2-env-lent-ok-witness b)))
                 (:instance fn2-env-lent-ok-necc (fn2-core a) (u (fn2-env-lent-ok-witness b)))))))
(defthm fn2-env-io-of-update-ops
  (equal (fn2-env-io u (update-fn2-core-ops x c)) (fn2-env-io u c))
  :hints (("Goal" :in-theory (enable fn2-env-io))))
(defthm fn2-env-units-kept-of-io
  ; a step that leaves commit-io leaves every unit
  (implies (equal (nth *fn2-core-commit-io* b) (nth *fn2-core-commit-io* a)) (fn2-env-units-kept a b))
  :hints (("Goal" :in-theory '(fn2-env-units-kept) :use ((:instance fn2-env-io-of-io-child (u (fn2-env-units-kept-witness a b)))))))
(defthm fn2-env-heads-kept-post
  (fn2-env-op-heads-kept c (update-fn2-core-ops (fn2-env-pr-ops) c))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-op-heads-kept fn2-env-op-of-post-result-core fn2-env-nth-op-posted
                                               fn2-env-nth-op-c1-posted (:e natp) (:e <))
                                             (theory 'minimal-theory)))))
(defthm fn2-env-heads-kept-kept
  (implies (fn2-env-ops-kept x c) (fn2-env-op-heads-kept c (update-fn2-core-ops x c)))
  :hints (("Goal" :in-theory '(fn2-env-op-heads-kept fn2-env-op-kept fn2-env-op-of-update-ops)
           :use ((:instance fn2-env-ops-kept-at (s (fn2-env-op-heads-kept-witness c (update-fn2-core-ops x c))))))))
(defthm fn2-env-heads-units-kept-of-children
  ; the extents and the pool hold no op and no unit
  (and (fn2-env-op-heads-kept c (update-fn2-core-extents x c)) (fn2-env-units-kept c (update-fn2-core-extents x c))
       (fn2-env-op-heads-kept c (update-fn2-core-pool x c)) (fn2-env-units-kept c (update-fn2-core-pool x c)))
  :hints (("Goal" :in-theory '(fn2-env-op-heads-kept fn2-env-units-kept fn2-env-j5-readers-of-update-fn2-core-extents
                               fn2-env-j5-readers-of-update-fn2-core-pool))))
(defthm fn2-env-heads-units-kept-fill
  (and (fn2-env-op-heads-kept c (fn2-env-fill rslot rgen slot gen idx octets c))
       (fn2-env-units-kept c (fn2-env-fill rslot rgen slot gen idx octets c)))
  :hints (("Goal" :in-theory '(fn2-env-heads-units-kept-of-children) :use ((:instance fn2-env-fill-is-pool-update)))))
(defthm fn2-env-units-kept-update-ops
  (fn2-env-units-kept c (update-fn2-core-ops x c))
  :hints (("Goal" :in-theory '(fn2-env-units-kept fn2-env-io-of-update-ops))))
(defthm fn2-env-fresh-lent-kept
  (implies (and (fn2-env-freshness log a) (fn2-env-lent-ok a) (fn2-env-op-heads-kept a b) (fn2-env-units-kept a b))
           (and (fn2-env-freshness log b) (fn2-env-lent-ok b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-freshness-of-heads fn2-env-lent-ok-of-kept))))
(defthm fn2-env-freshness-result
  (fn2-env-freshness (list (list :result slot gen evkind outcome count)) c)
  :hints (("Goal" :in-theory '(fn2-env-freshness fn2-env-not-takep-result (:e consp) car-cons cdr-cons (:e atom) atom))))
(defthm fn2-env-freshness-nil (fn2-env-freshness nil c) :hints (("Goal" :in-theory '(fn2-env-freshness (:e atom)))))
(defthm fn2-env-fresh-lent-host-step
  ; every step but :turn, :admit and :take keeps FRESHNESS and LENT-OK
  (implies (and (fn2-corep c) (fn2-env-freshness log c) (fn2-env-lent-ok c)
                (not (member-eq (fn2-env-tag action) '(:turn :admit :take))))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (and (fn2-env-freshness (append log (if entry (list entry) nil)) after) (fn2-env-lent-ok after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step fn2-host-post-accept-result fn2-host-post-clock fn2-host-post-signal
                                        fn2-env-begin-epoch fn2-env-loan-write fn2-env-post-step
                                        fn2-env-post-accept-kept fn2-env-post-clock-kept fn2-env-post-signal-kept
                                        fn2-env-freshness-append fn2-env-freshness-result fn2-env-freshness-nil append-to-nil
                                        fn2-env-freshness-of-heads fn2-env-lent-ok-of-kept
                                        fn2-env-heads-kept-post fn2-env-heads-kept-kept fn2-env-units-kept-update-ops
                                        fn2-env-heads-units-kept-of-children fn2-env-heads-units-kept-fill
                                        member-eq (:e member-eq) (:e equal) mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-op-gen-natp
  (implies (and (fn2-corep c) (fn2-core-wfp c) (nth 0 (fn2-env-op s c))) (natp (nth 1 (fn2-env-op s c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-op fn2-ops-gen fn2-core-wfp) (fn2-corep fn2-opsp))
           :use ((:instance fn2-ops-gen-raw-nth-natp (i s) (fn2-ops (fn2-core-ops c)))
                 (:instance fn2-core-ops-type (fn2-core c))))))
(defun-sk fn2-env-op-heads-advanced (a b)
  (forall s (fn2-env-head-advanced (fn2-env-op s a) (fn2-env-op s b))))
(in-theory (disable fn2-env-head-advanced))
(defthm fn2-env-incarnation-ok-of-advanced
  (implies (and (fn2-env-incarnation-ok s g a) (fn2-env-op-heads-advanced a b))
           (fn2-env-incarnation-ok s g b))
  :hints (("Goal" :in-theory (e/d (fn2-env-incarnation-ok fn2-env-head-advanced) (fn2-env-op fn2-env-op-heads-advanced))
           :use ((:instance fn2-env-op-heads-advanced-necc)))))
(defthm fn2-env-freshness-of-advanced
  (implies (and (fn2-env-freshness log a) (fn2-env-op-heads-advanced a b))
           (fn2-env-freshness log b))
  :hints (("Goal" :induct (fn2-env-freshness log a)
           :in-theory (union-theories '(fn2-env-freshness fn2-env-incarnation-ok-of-advanced) (theory 'minimal-theory)))))
(defthm fn2-env-lent-ok-of-advanced
  (implies (and (fn2-env-lent-ok a) (fn2-env-op-heads-advanced a b) (fn2-env-units-kept a b))
           (fn2-env-lent-ok b))
  :hints (("Goal" :in-theory '(fn2-env-lent-ok fn2-env-incarnation-ok-of-advanced)
           :use ((:instance fn2-env-units-kept-necc (u (fn2-env-lent-ok-witness b)))
                 (:instance fn2-env-lent-ok-necc (fn2-core a) (u (fn2-env-lent-ok-witness b)))))))
(defthm fn2-env-core-ops-wfp
  (implies (fn2-core-wfp c) (fn2-ops-wfp (fn2-core-ops c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-core-wfp) (fn2-ops-wfp fn2-opsp)))))
(defthm fn2-env-take-ops-cases
  ; :take leaves the ops table, acks its outbox head, or acks and finishes it
  (implies (fn2-corep c)
           (let* ((o (fn2-core-ops c)) (o2 (fn2-core-ops (fn2-env-tk-c))) (a (mv-nth 1 (fn2-outbox-ack 1 o))))
             (or (equal o2 o)
                 (and (equal (mv-nth 0 (fn2-outbox-ack 1 o)) :ok) (equal (mv-nth 0 (fn2-outbox-peek 0 o)) :ok)
                      (or (equal o2 a)
                          (equal o2 (mv-nth 1 (fn2-op-finish (mv-nth 1 (fn2-outbox-peek 0 o)) (mv-nth 2 (fn2-outbox-peek 0 o)) a))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-take fn2-host-outbox-ack fn2-host-op-finish fn2-host-outbox-peek)
                           (fn2-host-action fn2-host-op-span fn2-env-octets fn2-env-ops-op fn2-action-completionp
                            fn2-outbox-ack fn2-op-finish fn2-outbox-peek fn2-env-fill fn2-opsp fn2-ops-wfp)))))
(defthm fn2-env-take-head-advanced
  ; :take advances every op's head: the taken op is submitted, done or
  ; retired at its generation, or free at the next; every other op stays
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (fn2-env-head-advanced (fn2-env-op s c) (fn2-env-op s (fn2-env-tk-c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-op-is-ops-op) (theory 'minimal-theory))
           :use ((:instance fn2-env-take-ops-cases)
                 (:instance fn2-core-ops-type (fn2-core c)) (:instance fn2-env-core-ops-wfp)
                 (:instance fn2-env-outbox-ack-1-head-op (fn2-ops (fn2-core-ops c)))
                 (:instance fn2-env-op-gen-natp (s (fn2-ops-out-sloti (fn2-ops-out-head (fn2-core-ops c)) (fn2-core-ops c))))
                 (:instance fn2-env-ops-take-cases-advanced (o (fn2-core-ops c)) (o2 (fn2-core-ops (fn2-env-tk-c))))))))
(defthm fn2-env-take-entry-incarnation
  ; the taken incarnation began and was issued
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-tk-e))
           (fn2-env-incarnation-ok (nth 1 (fn2-env-tk-e)) (nth 2 (fn2-env-tk-e)) c))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-incarnation-ok) (fn2-env-op fn2-env-take))
           :use ((:instance fn2-env-take-op (s (nth 1 (fn2-env-tk-e))))
                 (:instance fn2-env-op-gen-natp (s (nth 1 (fn2-env-tk-e))))))))
(defthm fn2-env-take-heads-advanced
  (implies (and (fn2-corep c) (fn2-core-wfp c)) (fn2-env-op-heads-advanced c (fn2-env-tk-c)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-op-heads-advanced)
           :use ((:instance fn2-env-take-head-advanced (s (fn2-env-op-heads-advanced-witness c (fn2-env-tk-c))))))))
(defthm fn2-env-take-units-kept
  (fn2-env-units-kept c (fn2-env-tk-c))
  :hints (("Goal" :in-theory '(fn2-env-units-kept fn2-env-take-frames))))
(defthm fn2-env-fresh-lent-take-step
  ; :take keeps FRESHNESS and LENT-OK: the taken incarnation began and was
  ; issued, and every op's head advances
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-freshness log c) (fn2-env-lent-ok c)
                (equal (fn2-env-tag action) :take))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (and (fn2-env-freshness (append log (if entry (list entry) nil)) after) (fn2-env-lent-ok after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-step-take-unfolds fn2-env-freshness-append fn2-env-freshness-nil append-to-nil
                                        fn2-env-freshness-of-advanced fn2-env-lent-ok-of-advanced fn2-env-take-units-kept
                                        fn2-env-incarnation-ok-of-advanced
                                        fn2-env-freshness (:e atom) atom car-cons cdr-cons mv-nth (:e car) (:e cdr) (:e mv-nth))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-take-heads-advanced)
                 (:instance fn2-env-take-entry-incarnation) (:instance fn2-env-take-entry-shape (recoveryp nil))))))
(defthm fn2-env-admit-lk
  ; admission never writes commit-io's operation and loan columns
  (implies (fn2-env-lk fn2-core c0) (fn2-env-lk (fn2-env-admit members mode fn2-core) c0))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-commit-start-fn2-env-lk
                                               fn2-commit-put-members-fn2-env-lk fn2-core-stop-fn2-env-lk fn2-exec-wake-fn2-env-lk)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-lent-ok-of-lk
  ; LENT-OK reads a unit's validity, operation and loan alone
  (implies (and (fn2-env-lent-ok a) (fn2-env-op-heads-kept a b) (fn2-env-lk b a))
           (fn2-env-lent-ok b))
  :hints (("Goal" :in-theory '(fn2-env-lent-ok fn2-env-incarnation-ok-of-heads)
           :use ((:instance fn2-env-io-of-lk (u (fn2-env-lent-ok-witness b)))
                 (:instance fn2-env-lent-ok-necc (fn2-core a) (u (fn2-env-lent-ok-witness b)))))))
(defthm fn2-env-admit-heads-kept
  (fn2-env-op-heads-kept c (fn2-env-admit members mode c))
  :hints (("Goal" :in-theory '(fn2-env-op-heads-kept fn2-env-op-of-admit))))
(defthm fn2-env-fresh-lent-admit-step
  ; :admit keeps FRESHNESS and LENT-OK: it writes neither the ops table nor a loan
  (implies (and (fn2-env-freshness log c) (fn2-env-lent-ok c) (equal (fn2-env-tag action) :admit))
           (mv-let (entry after) (fn2-env-step action nil image rlog c)
             (and (fn2-env-freshness (append log (if entry (list entry) nil)) after) (fn2-env-lent-ok after))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-freshness-of-heads fn2-env-lent-ok-of-lk
                                        fn2-env-admit-heads-kept fn2-env-freshness-append fn2-env-freshness-nil
                                        mv-nth (:e car) (:e cdr) car-cons cdr-cons (:e mv-nth))
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-step-admit-unfolds (fn2-core c))
                 (:instance fn2-env-admit-lk (fn2-core c) (c0 c) (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)))
                 (:instance fn2-env-lk-reflexive (a c))))))
(in-theory (disable fn2-env-ops-head))
(in-theory (disable fn2-env-op-reserve-ok-facts fn2-env-op-enqueue-ok-facts))
(defthm fn2-env-heads-advanced-of-ops
  (implies (fn2-env-ops-advanced (fn2-core-ops a) (fn2-core-ops b)) (fn2-env-op-heads-advanced a b))
  :hints (("Goal" :in-theory (e/d (fn2-env-op-heads-advanced fn2-env-ops-head fn2-env-op-is-ops-op fn2-env-ops-op
                                   fn2-env-head-advanced)
                                  (fn2-env-ops-advanced fn2-env-op))
           :use ((:instance fn2-env-ops-advanced-necc (a (fn2-core-ops a)) (b (fn2-core-ops b))
                            (s (fn2-env-op-heads-advanced-witness a b)))))))
(fn2-env-issue-advanced fn2-issue-receive (cap-index cap-nonce slot gen len)
  *fn2-action-receive* cap-index cap-nonce 0 0 slot gen 0 len 0 0 0)
(fn2-env-issue-advanced fn2-issue-send (cap-index cap-nonce slot gen off len may-release)
  *fn2-action-send* cap-index cap-nonce 0 0 slot gen off len may-release 0 0)
(fn2-env-issue-advanced fn2-issue-read (offset slot gen len) *fn2-action-read* 0 0 offset 0 slot gen 0 len 0 0 0)
(fn2-env-issue-advanced fn2-issue-write (offset slot gen off len fua) *fn2-action-write* 0 0 offset fua slot gen off len 0 0 0)
(fn2-env-issue-advanced fn2-issue-fence () *fn2-action-fence* 0 0 0 0 0 0 0 0 0 0 0)
(fn2-env-issue-advanced fn2-issue-accept (cap-index cap-nonce) *fn2-action-accept* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-env-issue-advanced fn2-issue-close (cap-index cap-nonce) *fn2-action-close* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-env-issue-advanced fn2-issue-cancel (target-slot target-gen) *fn2-action-cancel* 0 0 0 0 0 0 0 0 0 target-slot target-gen)
(fn2-env-issue-advanced fn2-issue-entropy (slot gen len) *fn2-action-entropy* 0 0 0 0 slot gen 0 len 0 0 0)
;; FRESHNESS AND LENT-OK ACROSS THE COMMIT ARMS (FN2-ENV-FL, both). They
;; read the op heads (FN2-ENV-HK) and the units' operation and loan
;; (FN2-ENV-LK) alone: ten arms and every callee of the three issuing arms
;; but the issue and the edge add keep both by their footprints. The
;; issuing arms (:dependencies, :log-write, :fence) issue, which advances
;; the heads, and lend a unit to the issued incarnation alone.
(fn2-defview fn2-env-hk :carrier fn2-core
  :select ((fn2-ops :columns (gen phase) :rows t :scalars (rows))))
(defthm fn2-env-op-heads-of-hk
  (implies (fn2-env-hk b a)
           (and (equal (nth 0 (fn2-env-op s b)) (nth 0 (fn2-env-op s a)))
                (equal (nth 1 (fn2-env-op s b)) (nth 1 (fn2-env-op s a)))
                (equal (nth 2 (fn2-env-op s b)) (nth 2 (fn2-env-op s a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-hk fn2-env-op fn2-core-ops))))
(defun-nx fn2-env-fl (log c) (and (fn2-env-freshness log c) (fn2-env-lent-ok c)))
(defthm fn2-env-fl-of-hk-lk
  ; FRESHNESS and LENT-OK read the op heads and the units' operation and loan alone
  (implies (and (fn2-env-fl log a) (fn2-env-hk b a) (fn2-env-lk b a)) (fn2-env-fl log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-freshness-of-heads fn2-env-lent-ok-of-lk fn2-env-op-heads-kept)
           :use ((:instance fn2-env-op-heads-of-hk (s (fn2-env-op-heads-kept-witness a b)))))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-hk)
  '(fn2-commit-run-free fn2-commit-run-collect fn2-commit-run-seal fn2-commit-run-durable fn2-commit-run-install
    fn2-commit-run-publish fn2-commit-run-notify fn2-commit-run-draining fn2-commit-run-uncertain fn2-commit-run-dropping) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-lk)
  '(fn2-commit-run-free fn2-commit-run-collect fn2-commit-run-seal fn2-commit-run-durable fn2-commit-run-install
    fn2-commit-run-publish fn2-commit-run-notify fn2-commit-run-draining fn2-commit-run-uncertain fn2-commit-run-dropping) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-hk) (cons 'fn2-core-stop *fn2-env-fl-commit-callees*) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-lk) *fn2-env-fl-commit-callees* (w state)))))
(make-event (value (cons 'progn (fn2-env-fl-keep-events (cons 'fn2-core-stop *fn2-env-fl-commit-callees*) (w state)))))
(make-event (value (cons 'progn (fn2-env-fl-keep-events
  '(fn2-commit-run-free fn2-commit-run-collect fn2-commit-run-seal fn2-commit-run-durable fn2-commit-run-install
    fn2-commit-run-publish fn2-commit-run-notify fn2-commit-run-draining fn2-commit-run-uncertain fn2-commit-run-dropping) (w state)))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-hk) '(fn2-commit-io-edge) (w state)))))
(defthm fn2-env-io-edge-add-child
  ; an edge add leaves commit-io, or lends unit R to (S G)
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (let ((io (nth *fn2-core-commit-io* c)) (io2 (nth *fn2-core-commit-io* (mv-nth 1 (fn2-commit-io-edge id role t s g c))))
                 (r (+ (* 3 (fn2-commit-row id c)) (nfix role))))
             (or (equal io2 io)
                 (equal io2 (fn2-commit-io-set-lent r 1 (fn2-commit-io-set-op-gen r g (fn2-commit-io-set-op-slot r s io)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-commit-io-edge fn2-core-commit-io update-fn2-core-commit-io fn2-env-core-stop-keeps-io-pool
                            update-fn2-core-alloc-edges update-fn2-core-extents)
                           (fn2-alloc-edge-drop fn2-alloc-edge-add fn2-commit-row fn2-commit-idp fn2-core-stop
                            fn2-commit-io-set-lent fn2-commit-io-set-op-gen fn2-commit-io-set-op-slot unsigned-byte-p)))))
(defthm fn2-env-io-set3-units
  (let ((io2 (fn2-commit-io-set-lent r 1 (fn2-commit-io-set-op-gen r g (fn2-commit-io-set-op-slot r s io)))))
    (and (equal (fn2-commit-io-rows io2) (fn2-commit-io-rows io))
         (implies (and (natp u) (< u (fn2-commit-io-rows io)))
                  (or (and (equal (fn2-commit-io-op-slot u io2) (fn2-commit-io-op-slot u io))
                           (equal (fn2-commit-io-op-gen u io2) (fn2-commit-io-op-gen u io))
                           (equal (fn2-commit-io-lent u io2) (fn2-commit-io-lent u io)))
                      (and (equal (fn2-commit-io-op-slot u io2) s) (equal (fn2-commit-io-op-gen u io2) g))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-commit-io-set-lent fn2-commit-io-set-op-gen fn2-commit-io-set-op-slot update-fn2-commit-io-lent$ai
                                     update-fn2-commit-io-op-gen$ai update-fn2-commit-io-op-slot$ai update-nth-array))))
(defthm fn2-env-io-edge-add-units
  ; an edge add keeps every unit's validity, and its operation and loan or
  ; names the added operation
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (let ((o (fn2-env-io u c)) (o2 (fn2-env-io u (mv-nth 1 (fn2-commit-io-edge id role t s g c)))))
             (and (equal (nth 0 o2) (nth 0 o))
                  (or (and (equal (nth 1 o2) (nth 1 o)) (equal (nth 2 o2) (nth 2 o)) (equal (nth 3 o2) (nth 3 o)))
                      (and (equal (nth 1 o2) s) (equal (nth 2 o2) g))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io fn2-core-commit-io nth-0-cons nth-add1 (:e zp) (:e nth) car-cons cdr-cons
                                        (:e binary-+) zp nth)
                                      (theory 'minimal-theory))
           :use ((:instance fn2-env-io-edge-add-child)
                 (:instance fn2-env-io-set3-units (io (nth *fn2-core-commit-io* c))
                            (r (+ (* 3 (fn2-commit-row id c)) (nfix role))))))))
(defthm fn2-env-io-edge-add-fl
  ; lending a unit to an issued incarnation keeps FRESHNESS and LENT-OK
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-fl log c) (fn2-env-incarnation-ok s g c))
           (fn2-env-fl log (mv-nth 1 (fn2-commit-io-edge id role t s g c))))
  :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-lent-ok fn2-env-freshness-of-heads fn2-env-incarnation-ok-of-heads
                               fn2-env-op-heads-kept)
           :use ((:instance fn2-commit-io-edge-fn2-env-hk (fn2-core c) (fn2-rel-c0 c) (add t) (opslot s) (opgen g))
                 (:instance fn2-env-hk-reflexive (a c))
                 (:instance fn2-env-op-heads-of-hk (a c) (b (mv-nth 1 (fn2-commit-io-edge id role t s g c)))
                            (s (fn2-env-op-heads-kept-witness c (mv-nth 1 (fn2-commit-io-edge id role t s g c)))))
                 (:instance fn2-env-io-edge-add-units (u (fn2-env-lent-ok-witness (mv-nth 1 (fn2-commit-io-edge id role t s g c)))))
                 (:instance fn2-env-lent-ok-necc (fn2-core c)
                            (u (fn2-env-lent-ok-witness (mv-nth 1 (fn2-commit-io-edge id role t s g c)))))))))
(fn2-env-issue-fl fn2-issue-write (offset slot gen off len fua))
(fn2-env-issue-fl fn2-issue-fence ())
(defthm fn2-env-issue-write-edge-fl
  ; an accepted write issue, then the edge add lending its op: FRESHNESS and LENT-OK stay
  (let ((w (fn2-issue-write offset slot gen off len fua okind oslot ogen principal c)))
    (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-fl log c) (equal (car w) :ok))
             (fn2-env-fl log (mv-nth 1 (fn2-commit-io-edge id role t (mv-nth 1 w) (mv-nth 2 w) (mv-nth 3 w))))))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-issue-write-issued fn2-env-issue-write-fl) (theory 'fn2-arm-frame-base))
           :use ((:instance fn2-env-io-edge-add-fl
                            (s (mv-nth 1 (fn2-issue-write offset slot gen off len fua okind oslot ogen principal c)))
                            (g (mv-nth 2 (fn2-issue-write offset slot gen off len fua okind oslot ogen principal c)))
                            (c (mv-nth 3 (fn2-issue-write offset slot gen off len fua okind oslot ogen principal c))))))))
(fn2-env-fl-issuing-arm fn2-commit-run-dependencies)
(fn2-env-fl-issuing-arm fn2-commit-run-log-write)
(fn2-env-fl-issuing-arm fn2-commit-run-fence)
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-hk fn2-env-lk) '(fn2-machine-contract-check fn2-machine-refuse-phase) (w state)))))
(make-event (value (cons 'progn (fn2-env-fl-keep-events '(fn2-machine-contract-check fn2-machine-refuse-phase) (w state)))))
(defthm fn2-commit-run-fn2-env-fl
  ; every commit arm keeps FRESHNESS and LENT-OK
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-fl log fn2-core))
           (fn2-env-fl log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-commit-run
                                        fn2-commit-run-dependencies-fn2-env-fl fn2-commit-run-log-write-fn2-env-fl
                                        fn2-commit-run-fence-fn2-env-fl fn2-commit-run-free-fn2-env-fl
                                        fn2-commit-run-collect-fn2-env-fl fn2-commit-run-seal-fn2-env-fl
                                        fn2-commit-run-durable-fn2-env-fl fn2-commit-run-install-fn2-env-fl
                                        fn2-commit-run-publish-fn2-env-fl fn2-commit-run-notify-fn2-env-fl
                                        fn2-commit-run-draining-fn2-env-fl fn2-commit-run-uncertain-fn2-env-fl
                                        fn2-commit-run-dropping-fn2-env-fl fn2-core-stop-fn2-env-fl fn2-machine-contract-check-fn2-env-fl fn2-machine-refuse-phase-fn2-env-fl)
                                      (theory 'fn2-arm-frame-base)))))
;; OWED: FRESHNESS and LENT-OK across :turn, composed: the executor's visit,
;; dispatch and wake glue, and other kinds' arms (dispatch-contracts); every
;; commit step, issue wrapper and the harvest are proved (the handlers and
;; the harvest at the end of the book, after the loan-drop lemmas).
;; ---------------------------------------------------------------------------
;; J5 AND J6 ACROSS THE WRITE/FENCE HANDLER (fn2-commit-arm-observe). The
;; harvest (fn2-harvest-one) finishes the operation it delivers before the
;; handler runs, so at the handler's entry the delivered role write (or
;; fence) is no longer live and not yet counted: FN2-ENV-J5-ROW-D is J5 with
;; that one result in flight (cb-done plus the live roles is one short of
;; cb-issued, or the owned fences one short of cb-fence-live), the dead
;; roles' written evidence asked only of a full done result. The handler
;; counts the result (cb-done, or the fence flags) or moves the row to
;; :uncertain, and drops the row's three IO loans with the phase's last
;; result (fn2-commit-drop-io). Each outcome, stated over the evidence the
;; handler keeps (FN2-ENV-ROLES-DROPPED: ops, pool, units but for cleared
;; loans; FN2-ENV-COLS-KEPT), gives J5 and J6, J6P, J6L, J6S again:
;; FN2-ENV-J5-ROW-COUNT (a full write counted), FN2-ENV-J5-ROW-FENCE-DONE (a
;; full fence counted at :fence), FN2-ENV-J5-ROW-TO-UNCERTAIN (any other
;; outcome), FN2-ENV-J6*-IN-PHASE and FN2-ENV-J6S-TO-UNCERTAIN.

(defun-nx fn2-env-roles-dropped (id a b)
  ; B keeps the ops table, the pool and row ID's units (but for cleared
  ; loans) and extents
  (and (fn2-env-ok b a) (equal (nth 0 b) (nth 0 a))
       (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
       (equal (fn2-commit-row id b) (fn2-commit-row id a))
       (fn2-env-io-drop-p (fn2-env-role-io id 0 a) (fn2-env-role-io id 0 b))
       (fn2-env-io-drop-p (fn2-env-role-io id 1 a) (fn2-env-role-io id 1 b))
       (fn2-env-io-drop-p (fn2-env-role-io id 2 a) (fn2-env-role-io id 2 b))
       (equal (fn2-env-role-extent id 0 b) (fn2-env-role-extent id 0 a))
       (equal (fn2-env-role-extent id 1 b) (fn2-env-role-extent id 1 a))
       (equal (fn2-env-role-extent id 2 b) (fn2-env-role-extent id 2 a))))
(defthm fn2-env-roles-dropped-reads
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3))
           (let ((x (fn2-env-role-io id role a)) (y (fn2-env-role-io id role b)))
             (and (equal (nth 0 y) (nth 0 x)) (equal (nth 1 y) (nth 1 x)) (equal (nth 2 y) (nth 2 x))
                  (equal (nth 4 y) (nth 4 x)) (equal (nth 5 y) (nth 5 x))
                  (implies (equal (nth 3 y) 1) (equal y x))
                  (equal (fn2-env-role-extent id role b) (fn2-env-role-extent id role a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-roles-dropped fn2-env-io-drop-p nth-update-nth (:e nfix) (:e zp) (:e equal) natp)
           :cases ((equal role 0) (equal role 1) (equal role 2)))))
(defthm fn2-env-role-live-dropped
  ; a role live after a loan drop was live before, on the same unit; a unit
  ; left as it was keeps the role's liveness
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3))
           (and (implies (fn2-env-role-live id role b)
                         (and (fn2-env-role-live id role a) (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a))))
                (implies (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a))
                         (equal (fn2-env-role-live id role b) (fn2-env-role-live id role a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-live fn2-env-roles-dropped fn2-env-op-of-ok)
           :use ((:instance fn2-env-roles-dropped-reads)))))
(defthm fn2-env-role-readers-dropped
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3))
           (and (equal (fn2-env-role-octets id role b) (fn2-env-role-octets id role a))
                (equal (fn2-env-role-pool-ok id role b) (fn2-env-role-pool-ok id role a))
                (equal (fn2-env-role-lease id role b) (fn2-env-role-lease id role a))
                (equal (fn2-env-role-offset id role b) (fn2-env-role-offset id role a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-octets fn2-env-role-pool-ok fn2-env-role-lease fn2-env-pool-row fn2-core-pool
                               fn2-env-role-offset-of-extent fn2-env-roles-dropped)
           :use ((:instance fn2-env-roles-dropped-reads)))))
(defthm fn2-env-role-written-dropped
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3)
                (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a)))
           (equal (fn2-env-role-written id role f log b) (fn2-env-role-written id role f log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-written) :use ((:instance fn2-env-role-readers-dropped)))))
(defthm fn2-env-j5-role-dropped
  ; a role keeps J5-ROLE when its liveness does
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
                (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-env-role-live id role b) (fn2-env-role-live id role a)))
           (equal (fn2-env-j5-role id role log b) (fn2-env-j5-role id role log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-role fn2-env-roles-dropped fn2-env-op-of-ok)
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped) (:instance fn2-env-role-readers-dropped)
                 (:instance fn2-env-role-written-dropped
                            (f (or (equal (fn2-machine-cb-fence-ok id a) 1)
                                   (and (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                                        (equal (fn2-machine-cb-mode id a) 1)))))))))
(defun fn2-env-j5-d-role (id role ok log fn2-core)
  ; J5-ROLE, its dead role's written evidence asked only when OK
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (or ok (fn2-env-role-live id role fn2-core)) (fn2-env-j5-role id role log fn2-core)))
(defun fn2-env-j5-roles-d (id ok log fn2-core)
  ; J5-ROLES with one issued role's result delivered and not yet counted
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)) (issued (fn2-machine-cb-issued id fn2-core))
        (done (fn2-machine-cb-done id fn2-core)))
    (cond ((equal phase *fn2-commit-state-dependencies*)
           (and (natp issued) (<= issued 1) (natp done)
                (implies (fn2-env-role-live id 0 fn2-core) (equal issued 1))
                (implies (equal issued 1) (fn2-env-j5-d-role id 0 ok log fn2-core))
                (equal (+ 1 done (if (equal issued 1) (fn2-env-b2n (fn2-env-role-live id 0 fn2-core)) 0)) issued)))
          ((equal phase *fn2-commit-state-log-write*)
           (and (natp issued) (<= issued 2) (natp done)
                (implies (<= 1 issued) (fn2-env-j5-d-role id 1 ok log fn2-core))
                (implies (<= 2 issued) (fn2-env-j5-d-role id 2 ok log fn2-core))
                (equal (+ 1 done (if (<= 1 issued) (fn2-env-b2n (fn2-env-role-live id 1 fn2-core)) 0)
                          (if (<= 2 issued) (fn2-env-b2n (fn2-env-role-live id 2 fn2-core)) 0))
                       issued)
                (fn2-env-j5-apart id fn2-core)))
          (t t))))
(defun fn2-env-j5-row-d (id event outcome count log fn2-core)
  ; J5 at the handler's entry: the harvest has finished the operation whose
  ; EVENT it delivers (a role write's or the fence's), not yet counted
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((write (equal event *fn2-event-write-result*))
         (ok (and (equal outcome *fn2-outcome-done*) (equal count (if write *fn2-commit-unit-bytes* 0))))
         (phase (fn2-machine-phase id fn2-core)) (fence-live (fn2-machine-cb-fence-live id fn2-core)))
    (implies (fn2-commit-idp id fn2-core)
             (and (fn2-env-j5-ops 0 (fn2-env-ops-rows fn2-core) id log fn2-core)
                  (if write (fn2-env-j5-roles-d id ok log fn2-core) (fn2-env-j5-roles id log fn2-core))
                  (or (member-equal phase (list *fn2-commit-state-draining* *fn2-commit-state-uncertain*
                                                *fn2-commit-state-dropping*))
                      (and (equal fence-live (if (equal phase *fn2-commit-state-fence*) fence-live 0))
                           (member-equal fence-live '(0 1))
                           (equal (+ (if write 0 1) (fn2-env-owned-fences 0 (fn2-env-ops-rows fn2-core) id fn2-core))
                                  fence-live)))))))
(defun-nx fn2-env-cols-kept (id a b)
  ; the columns J5 and J6 read of row ID but its phase, count and fence flags
  (and (equal (fn2-machine-cb-mode id b) (fn2-machine-cb-mode id a))
       (equal (fn2-machine-cb-issued id b) (fn2-machine-cb-issued id a))
       (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
       (equal (fn2-machine-batch-no id b) (fn2-machine-batch-no id a))
       (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
       (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))))
(defun-nx fn2-env-drop-all-or-none (id a b)
  ; the loans are all kept, or the last result of the phase is counted
  (or (and (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
           (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
           (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a)))
      (equal (fn2-machine-cb-issued id a) (+ 1 (fn2-machine-cb-done id a)))))
(defthm fn2-env-j5-roles-count
  ; counting a delivered full write keeps J5-ROLES
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b) (fn2-env-drop-all-or-none id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-machine-cb-done id b) (+ 1 (fn2-machine-cb-done id a)))
                (fn2-env-j5-roles-d id t log a))
           (fn2-env-j5-roles id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-roles fn2-env-j5-roles-d fn2-env-j5-d-role fn2-env-j5-apart fn2-env-b2n
                               fn2-env-cols-kept fn2-env-drop-all-or-none natp (:e natp) (:e <) (:e equal) fix)
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped (role 0)) (:instance fn2-env-role-live-dropped (role 1))
                 (:instance fn2-env-role-live-dropped (role 2))
                 (:instance fn2-env-j5-role-dropped (role 0)) (:instance fn2-env-j5-role-dropped (role 1))
                 (:instance fn2-env-j5-role-dropped (role 2))
                 (:instance fn2-env-roles-dropped-reads (role 1)) (:instance fn2-env-roles-dropped-reads (role 2))))))
(defthm fn2-env-j5-fence-dropped
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b))
           (equal (fn2-env-j5-fence id op s log b) (fn2-env-j5-fence id op s log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-fence fn2-env-cols-kept (:e natp) (:e <))
           :use ((:instance fn2-env-role-written-dropped (role 0) (f nil) (log (take (fn2-env-take-index s (nth 1 op) log) log)))
                 (:instance fn2-env-role-written-dropped (role 1) (f nil) (log (take (fn2-env-take-index s (nth 1 op) log) log)))
                 (:instance fn2-env-role-written-dropped (role 2) (f nil) (log (take (fn2-env-take-index s (nth 1 op) log) log)))))))
(defthm fn2-env-j5-op-to-uncertain
  ; a row moved to :uncertain keeps J5-OP: settling asks only of its live
  ; fences, which every phase's J5-OP already followed
  (implies (and (fn2-env-j5-op s id log a) (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
           (fn2-env-j5-op s id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-op fn2-env-roles-dropped fn2-env-cols-kept fn2-env-op-of-ok
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :use ((:instance fn2-env-j5-fence-dropped (op (fn2-env-op s a)))))))
(defthm fn2-env-j5-ops-to-uncertain
  (implies (and (fn2-env-j5-ops s k id log a) (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
           (fn2-env-j5-ops s k id log b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops) (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-j5-op-to-uncertain)))))
(defthm fn2-env-j5-op-fence-done
  ; a counted fence result at :fence: no live fence of the row is left at
  ; its generation, so none of its operations is
  (implies (and (fn2-env-j5-op s id log a) (equal (fn2-env-owned-fence-at s id a) 0) (fn2-env-ok b a)
                (equal (fn2-machine-phase id a) *fn2-commit-state-fence*)
                (equal (fn2-machine-phase id b) *fn2-commit-state-fence*)
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (fn2-env-j5-op s id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-op fn2-env-owned-fence-at fn2-env-op-of-ok
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t)))
(defthm fn2-env-owned-fence-at-bit
  (or (equal (fn2-env-owned-fence-at s id c) 0) (equal (fn2-env-owned-fence-at s id c) 1))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-owned-fence-at))))
(defthm fn2-env-owned-fence-at-natp
  (natp (fn2-env-owned-fence-at s id c))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory '(fn2-env-owned-fence-at (:e natp)))))
(defthm fn2-env-owned-fences-natp
  (natp (fn2-env-owned-fences s k id c))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn2-env-owned-fences s k id c)
           :in-theory (union-theories '(fn2-env-owned-fences natp (:e natp) (:type-prescription fn2-env-owned-fence-at-natp)) (theory 'minimal-theory)))))
(defthm fn2-env-j5-ops-fence-done
  (implies (and (fn2-env-j5-ops s k id log a) (equal (fn2-env-owned-fences s k id a) 0) (fn2-env-ok b a)
                (equal (fn2-machine-phase id a) *fn2-commit-state-fence*)
                (equal (fn2-machine-phase id b) *fn2-commit-state-fence*)
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (fn2-env-j5-ops s k id log b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops fn2-env-owned-fences natp) (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-j5-op-fence-done)
                                (:instance fn2-env-owned-fence-at-natp (c a))
                                (:instance fn2-env-owned-fences-natp (s (+ 1 (nfix s))) (k (- k 1)) (c a))))))
(defun fn2-env-op-owned-at (s id fn2-core)
  ; op S is live, owned by commit row ID, at the row's generation
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((op (fn2-env-op s fn2-core)))
    (and (nth 0 op) (not (member-equal (nth 2 op) (list *fn2-op-phase-free* *fn2-op-phase-retired*)))
         (equal (nth 4 op) *fn2-commit-kind*) (equal (nth 5 op) id)
         (equal (nth 6 op) (fn2-machine-generation id fn2-core)))))
(defthm fn2-env-j5-op-not-owned-at
  ; J5-OP of an operation the row does not own at its generation reads only
  ; the operation and the generation
  (implies (and (fn2-env-j5-op s id log a) (not (fn2-env-op-owned-at s id a)) (fn2-env-ok b a)
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (fn2-env-j5-op s id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-op fn2-env-op-owned-at fn2-env-op-of-ok) :do-not-induct t)))
(defthm fn2-env-j5-op-owned-at-live-role
  ; an operation the row owns at its generation in a write phase is a live
  ; role's write
  (implies (and (fn2-env-j5-op s id log a) (fn2-env-op-owned-at s id a))
           (and (implies (equal (fn2-machine-phase id a) *fn2-commit-state-dependencies*)
                         (fn2-env-role-live id 0 a))
                (implies (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                         (or (fn2-env-role-live id 1 a) (fn2-env-role-live id 2 a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-op fn2-env-op-owned-at fn2-env-role-live fn2-env-role-io
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t)))
(defthm fn2-env-io-of-role-io
  (implies (and (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (equal (fn2-env-role-io id k b) (fn2-env-role-io id k a)))
           (equal (fn2-env-io (+ (* 3 (fn2-commit-row id a)) k) b) (fn2-env-io (+ (* 3 (fn2-commit-row id a)) k) a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-io))))
(defthm fn2-env-j5-op-units-kept
  ; J5-OP reads the ops table, the row's phase, generation, fence flag and
  ; units, and its fence evidence
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
                (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
                (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a)))
           (equal (fn2-env-j5-op s id log b) (fn2-env-j5-op s id log a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-op fn2-env-op-of-ok fn2-env-roles-dropped fn2-env-cols-kept)
           :do-not-induct t
           :use ((:instance fn2-env-io-of-role-io (k 0)) (:instance fn2-env-io-of-role-io (k 1))
                 (:instance fn2-env-io-of-role-io (k 2))
                 (:instance fn2-env-j5-fence-dropped (op (fn2-env-op s a)))))))
(defthm fn2-env-roles-dropped-ids
  (implies (fn2-env-roles-dropped id a b)
           (fn2-env-ok b a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-roles-dropped))))
(defthm fn2-env-j5-op-count
  ; counting a role's result, and dropping the loans with the last one,
  ; keeps J5-OP: the loans drop only once no role of the phase is live
  (implies (and (fn2-env-j5-op s id log a) (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (member-equal (fn2-machine-phase id a) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                (or (and (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
                         (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
                         (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a)))
                    (and (implies (equal (fn2-machine-phase id a) *fn2-commit-state-dependencies*)
                                  (not (fn2-env-role-live id 0 a)))
                         (implies (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                                  (and (not (fn2-env-role-live id 1 a)) (not (fn2-env-role-live id 2 a)))))))
           (fn2-env-j5-op s id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-cols-kept member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :use ((:instance fn2-env-j5-op-units-kept) (:instance fn2-env-j5-op-not-owned-at)
                 (:instance fn2-env-j5-op-owned-at-live-role)
                 (:instance fn2-env-roles-dropped-ids)))))
(defthm fn2-env-j5-ops-count
  (implies (and (fn2-env-j5-ops s k id log a) (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (member-equal (fn2-machine-phase id a) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                (or (and (equal (fn2-env-role-io id 0 b) (fn2-env-role-io id 0 a))
                         (equal (fn2-env-role-io id 1 b) (fn2-env-role-io id 1 a))
                         (equal (fn2-env-role-io id 2 b) (fn2-env-role-io id 2 a)))
                    (and (implies (equal (fn2-machine-phase id a) *fn2-commit-state-dependencies*)
                                  (not (fn2-env-role-live id 0 a)))
                         (implies (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                                  (and (not (fn2-env-role-live id 1 a)) (not (fn2-env-role-live id 2 a)))))))
           (fn2-env-j5-ops s k id log b))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-j5-ops s k id log a)
           :in-theory (union-theories '(fn2-env-j5-ops) (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn2-env-j5-op-count)))))
(defthm fn2-env-roles-d-last
  ; with the phase's last result in flight no role of the phase is live
  (implies (and (fn2-env-j5-roles-d id ok log a)
                (equal (fn2-machine-cb-issued id a) (+ 1 (fn2-machine-cb-done id a))))
           (and (implies (equal (fn2-machine-phase id a) *fn2-commit-state-dependencies*)
                         (not (fn2-env-role-live id 0 a)))
                (implies (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                         (and (not (fn2-env-role-live id 1 a)) (not (fn2-env-role-live id 2 a))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-roles-d fn2-env-j5-apart fn2-env-b2n natp (:e natp) (:e <) fix) :do-not-induct t)))
(defthm fn2-env-j5-row-count
  ; a full write result of a write phase, counted, with the loans dropped
  ; at the phase's last: J5 again
  (implies (and (fn2-env-j5-row-d id *fn2-event-write-result* *fn2-outcome-done* *fn2-commit-unit-bytes* log a)
                (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b) (fn2-env-drop-all-or-none id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (member-equal (fn2-machine-phase id a) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (equal (fn2-machine-cb-done id b) (+ 1 (fn2-machine-cb-done id a))))
           (fn2-env-j5-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row fn2-env-j5-row-d fn2-env-roles-dropped fn2-env-cols-kept fn2-env-drop-all-or-none
                               fn2-env-op-of-ok fn2-env-owned-fences-of-ok unicity-of-0 fix (:type-prescription fn2-env-owned-fences-natp)
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp) (:e equal))
           :do-not-induct t
           :use ((:instance fn2-env-j5-roles-count)
                 (:instance fn2-env-roles-d-last (ok t))
                 (:instance fn2-env-j5-ops-count (s 0) (k (fn2-env-ops-rows a)))))))
(defthm fn2-env-j5-row-fence-done
  ; the fence's full result at :fence, counted: J5 again
  (implies (and (fn2-env-j5-row-d id *fn2-event-fence-result* outcome count log a) (fn2-env-ok b a)
                (equal (fn2-commit-idp id b) (fn2-commit-idp id a))
                (equal (fn2-machine-phase id a) *fn2-commit-state-fence*)
                (equal (fn2-machine-phase id b) *fn2-commit-state-fence*)
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
                (equal (fn2-machine-cb-fence-live id b) 0))
           (fn2-env-j5-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row fn2-env-j5-row-d fn2-env-j5-roles fn2-env-op-of-ok fn2-env-owned-fences-of-ok
                               (:type-prescription fn2-env-owned-fences-natp)
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp) (:e equal))
           :do-not-induct t
           :use ((:instance fn2-env-j5-ops-fence-done (s 0) (k (fn2-env-ops-rows a)))))))
(defthm fn2-env-j5-row-to-uncertain
  ; a row moved to :uncertain keeps J5 of its operations
  (implies (and (fn2-env-j5-ops 0 (fn2-env-ops-rows a) id log a) (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
           (fn2-env-j5-row id log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row fn2-env-j5-roles fn2-env-roles-dropped fn2-env-op-of-ok
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp) (:e equal))
           :do-not-induct t
           :use ((:instance fn2-env-j5-ops-to-uncertain (s 0) (k (fn2-env-ops-rows a)))))))
(defthm fn2-env-role-lease-ok-dropped
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3))
           (implies (fn2-env-role-lease-ok id role a) (fn2-env-role-lease-ok id role b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-lease-ok)
           :use ((:instance fn2-env-roles-dropped-reads) (:instance fn2-env-role-readers-dropped)
                 (:instance fn2-env-role-live-dropped)))))
(defthm fn2-env-role-settle-ok-dropped
  (implies (and (fn2-env-roles-dropped id a b) (natp role) (< role 3)
                (implies (fn2-env-role-live id role a)
                         (and (fn2-env-role-pool-ok id role a) (fn2-env-role-lease-ok id role a))))
           (fn2-env-role-settle-ok id role b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-settle-ok)
           :use ((:instance fn2-env-role-lease-ok-dropped) (:instance fn2-env-role-readers-dropped)
                 (:instance fn2-env-role-live-dropped)))))
(defthm fn2-env-j6-in-phase
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (implies (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*)
                         (equal (fn2-env-role-live id 2 b) (fn2-env-role-live id 2 a)))
                (fn2-env-j6-row id a))
           (fn2-env-j6-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6-row fn2-env-roles-dropped fn2-env-cols-kept fn2-env-op-of-ok (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-roles-dropped-reads (role 2))
                 (:instance fn2-env-role-readers-dropped (role 0)) (:instance fn2-env-role-readers-dropped (role 1))
                 (:instance fn2-env-role-readers-dropped (role 2))))))
(defthm fn2-env-j6p-in-phase
  (implies (and (fn2-env-roles-dropped id a b) (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (fn2-env-j6p-row id a))
           (fn2-env-j6p-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6p-row fn2-env-roles-dropped (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-readers-dropped (role 0)) (:instance fn2-env-role-readers-dropped (role 1))
                 (:instance fn2-env-role-readers-dropped (role 2))))))
(defthm fn2-env-j6l-in-phase
  (implies (and (fn2-env-roles-dropped id a b) (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (fn2-env-j6l-row id a))
           (fn2-env-j6l-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6l-row fn2-env-roles-dropped (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-roles-dropped-reads (role 0)) (:instance fn2-env-roles-dropped-reads (role 1))
                 (:instance fn2-env-roles-dropped-reads (role 2))
                 (:instance fn2-env-role-lease-ok-dropped (role 0)) (:instance fn2-env-role-lease-ok-dropped (role 1))
                 (:instance fn2-env-role-lease-ok-dropped (role 2))))))
(defthm fn2-env-j6s-in-phase
  (implies (and (fn2-env-roles-dropped id a b) (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (fn2-env-j6s-row id a))
           (fn2-env-j6s-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6s-row fn2-env-role-settle-ok fn2-env-roles-dropped (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-settle-ok-dropped (role 0)) (:instance fn2-env-role-settle-ok-dropped (role 1))
                 (:instance fn2-env-role-settle-ok-dropped (role 2))))))
(defthm fn2-env-j6s-to-uncertain
  ; a row moved to :uncertain from a phase that may own writes: its live
  ; roles keep J6P's pool rows and J6L's leases (J6S)
  (implies (and (fn2-env-roles-dropped id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                (member-equal (fn2-machine-phase id a)
                              (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write* *fn2-commit-state-fence*
                                    *fn2-commit-state-draining* *fn2-commit-state-uncertain* *fn2-commit-state-dropping*))
                (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row fn2-env-roles-dropped
                               fn2-env-role-settle-ok member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp)
                               (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-settle-ok-dropped (role 0)) (:instance fn2-env-role-settle-ok-dropped (role 1))
                 (:instance fn2-env-role-settle-ok-dropped (role 2))
                 (:instance fn2-env-j6-role-oks (c a) (role 0)) (:instance fn2-env-j6-role-oks (c a) (role 1))
                 (:instance fn2-env-j6-role-oks (c a) (role 2))))))
(defthm fn2-env-io-edge-drop-units
  ; an edge drop clears at most row ID's ROLE unit's loan flag; no other
  ; unit, no extent, epoch, counter or pool column changes
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (let ((b (mv-nth 1 (fn2-commit-io-edge id role nil s g c))))
             (and (fn2-env-io-drop-p (fn2-env-io u c) (fn2-env-io u b))
                  (implies (not (equal (nfix u) (+ (* 3 (fn2-commit-row id c)) (nfix role))))
                           (equal (fn2-env-io u b) (fn2-env-io u c))))))
  :hints (("Goal" :in-theory (e/d (fn2-commit-io-edge fn2-core-commit-io update-fn2-core-commit-io fn2-env-io
                                   fn2-commit-io-set-lent update-fn2-commit-io-lent$ai
                                   fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-lent fn2-commit-io-pool-slot
                                   fn2-commit-io-pool-gen fn2-commit-io-rows fn2-commit-io-op-slot$ai fn2-commit-io-op-gen$ai
                                   fn2-commit-io-lent$ai fn2-commit-io-pool-slot$ai fn2-commit-io-pool-gen$ai
                                   fn2-env-core-stop-keeps-io-pool update-nth-array fn2-env-io-drop-p
                                   update-fn2-core-alloc-edges update-fn2-core-extents nth-update-nth)
                                  (fn2-alloc-edge-drop fn2-alloc-edge-add fn2-commit-row fn2-commit-idp fn2-core-stop update-nth nth
                                   fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter)))))
(make-event
 (value (cons 'progn
   (fn2-env-j-reader-frame-events '((fn2-machine-idp id) (fn2-machine-kind id) (fn2-machine-slot id) (fn2-machine-phase id)
                                    (fn2-commit-idp id) (fn2-commit-row id))
                                  '(update-fn2-core-commit-io update-fn2-core-alloc-edges)))))
;; THE LOAN DROP (fn2-commit-drop-io, three edge drops): it clears at most
;; a unit's loan flag (commit-io field 8) and keeps every id, every row's
;; journal resources and the other children: the handler's half of
;; FN2-ENV-ROLES-DROPPED.
(defthm fn2-env-io-edge-keeps-io-fields
  ; an edge drop writes commit-io's loan column (field 8) alone
  (implies (and (fn2-corep c) (fn2-core-wfp c) (natp k) (not (equal k 8)))
           (equal (nth k (nth *fn2-core-commit-io* (mv-nth 1 (fn2-commit-io-edge id role nil s g c))))
                  (nth k (nth *fn2-core-commit-io* c))))
  :hints (("Goal" :in-theory (e/d (fn2-commit-io-edge fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-lent update-fn2-commit-io-lent$ai
                                   fn2-env-core-stop-keeps-io-pool update-nth-array
                                   update-fn2-core-alloc-edges update-fn2-core-extents nth-update-nth)
                                  (fn2-alloc-edge-drop fn2-alloc-edge-add fn2-commit-row fn2-commit-idp fn2-core-stop update-nth nth
                                   fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter fn2-commit-io-lent
                                   fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-pool-slot fn2-commit-io-pool-gen)))))
(defthm fn2-env-resource-of-io-fields
  ; a row's journal resources read the directory and commit-io's extent,
  ; epoch, counter and pool columns and its row count
  (implies (and (equal (fn2-commit-idp x b) (fn2-commit-idp x a)) (equal (fn2-commit-row x b) (fn2-commit-row x a))
                (equal (nth 0 (nth *fn2-core-commit-io* b)) (nth 0 (nth *fn2-core-commit-io* a)))
                (equal (nth 1 (nth *fn2-core-commit-io* b)) (nth 1 (nth *fn2-core-commit-io* a)))
                (equal (nth 2 (nth *fn2-core-commit-io* b)) (nth 2 (nth *fn2-core-commit-io* a)))
                (equal (nth 3 (nth *fn2-core-commit-io* b)) (nth 3 (nth *fn2-core-commit-io* a)))
                (equal (nth 4 (nth *fn2-core-commit-io* b)) (nth 4 (nth *fn2-core-commit-io* a)))
                (equal (nth 9 (nth *fn2-core-commit-io* b)) (nth 9 (nth *fn2-core-commit-io* a))))
           (equal (fn2-commit-resource x r b) (fn2-commit-resource x r a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-resource fn2-core-commit-io fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter
                               fn2-commit-io-pool-slot fn2-commit-io-pool-gen fn2-commit-io-rows fn2-commit-io-extent$ai
                               fn2-commit-io-epoch$ai fn2-commit-io-counter$ai fn2-commit-io-pool-slot$ai fn2-commit-io-pool-gen$ai))))
(make-event (value (cons 'progn (fn2-env-view-keep-events '(fn2-env-tk fn2-env-ok fn2-env-pk)
  '(fn2-commit-io-edge) (w state)))))
(make-event (value (cons 'progn (fn2-env-keeps-ids-events
  '((fn2-env-io-edge-keeps-ids (mv-nth 1 (fn2-commit-io-edge id role add opslot opgen c)) fn2-commit-io-edge-fn2-env-tk))))))
(defthm fn2-env-io-edge-drop-resource
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (equal (fn2-commit-resource x r (mv-nth 1 (fn2-commit-io-edge id role nil s g c))) (fn2-commit-resource x r c)))
  :hints (("Goal" :in-theory '((:e natp) (:e equal) fn2-env-tk-reflexive)
           :use ((:instance fn2-commit-io-edge-fn2-env-tk (fn2-core c) (fn2-rel-c0 c) (add nil) (opslot s) (opgen g))
                 (:instance fn2-env-read-codes-of-tk (id x) (a c) (b (mv-nth 1 (fn2-commit-io-edge id role nil s g c))))
                 (:instance fn2-env-resource-of-io-fields (a c) (b (mv-nth 1 (fn2-commit-io-edge id role nil s g c))))
                 (:instance fn2-env-io-edge-keeps-ids (add nil) (opslot s) (opgen g))
                 (:instance fn2-env-io-edge-keeps-io-fields (k 0)) (:instance fn2-env-io-edge-keeps-io-fields (k 1))
                 (:instance fn2-env-io-edge-keeps-io-fields (k 2)) (:instance fn2-env-io-edge-keeps-io-fields (k 3))
                 (:instance fn2-env-io-edge-keeps-io-fields (k 4)) (:instance fn2-env-io-edge-keeps-io-fields (k 9))))))
(defthm fn2-env-drop-io-is-rewrite
  (equal (fn2-commit-drop-io id c)
         (if (and (eq (mv-nth 0 (fn2-commit-io-edge id 0 nil 0 0 c)) :ok)
                  (eq (mv-nth 0 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))) :ok)
                  (eq (mv-nth 0 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))) :ok))
             (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))) (fn2-core-stop *fn2-stop-reason-commit-io* (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-drop-io))))
(defthm fn2-env-drop-io-units
  ; dropping the row's three loans clears at most a unit's loan flag
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (fn2-env-io-drop-p (fn2-env-io u c) (fn2-env-io u (fn2-commit-drop-io id c))))
  :hints (("Goal" :in-theory '(fn2-commit-io-edge-preserves-type fn2-commit-io-edge-preserves-wfp)
           :do-not-induct t
           :use ((:instance fn2-env-drop-io-is-rewrite)
                 (:instance fn2-env-io-edge-drop-units (role 0) (s 0) (g 0))
                 (:instance fn2-env-io-edge-drop-units (role 1) (s 0) (g 0) (c (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))
                 (:instance fn2-env-io-edge-drop-units (role 2) (s 0) (g 0) (c (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))
                 (:instance fn2-env-io-drop-p-trans (x (fn2-env-io u c)) (y (fn2-env-io u (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))) (z (fn2-env-io u (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))
                 (:instance fn2-env-io-drop-p-trans (x (fn2-env-io u c)) (y (fn2-env-io u (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))) (z (fn2-env-io u (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))))
                 (:instance fn2-env-io-of-io-child (a (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))) (b (fn2-core-stop *fn2-stop-reason-commit-io* (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))))
                 (:instance fn2-env-core-stop-keeps-io-pool (r *fn2-stop-reason-commit-io*) (c (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))))))))
(defthm fn2-env-drop-io-ids
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (and (equal (fn2-commit-idp x (fn2-commit-drop-io id c)) (fn2-commit-idp x c))
                (equal (fn2-commit-row x (fn2-commit-drop-io id c)) (fn2-commit-row x c))))
  :hints (("Goal" :in-theory '(fn2-commit-io-edge-preserves-type fn2-commit-io-edge-preserves-wfp
                               fn2-env-io-edge-keeps-ids fn2-env-core-stop-keeps-ids fn2-commit-row)
           :do-not-induct t
           :use ((:instance fn2-env-drop-io-is-rewrite)))))
(defthm fn2-env-drop-io-resource
  (implies (and (fn2-corep c) (fn2-core-wfp c))
           (equal (fn2-commit-resource x role (fn2-commit-drop-io id c)) (fn2-commit-resource x role c)))
  :hints (("Goal" :in-theory '(fn2-commit-io-edge-preserves-type fn2-commit-io-edge-preserves-wfp fn2-env-io-edge-drop-resource
                               fn2-env-io-edge-keeps-ids fn2-env-core-stop-keeps-ids fn2-commit-row)
           :do-not-induct t
           :use ((:instance fn2-env-drop-io-is-rewrite)
                 (:instance fn2-env-core-stop-keeps-io-pool (r *fn2-stop-reason-commit-io*) (c (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))))
                 (:instance fn2-env-core-stop-keeps-ids (reason *fn2-stop-reason-commit-io*) (x x) (c (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))))
                 (:instance fn2-env-child-congruences (id x) (a (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))) (b (fn2-core-stop *fn2-stop-reason-commit-io* (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))))))))
;; J5E ACROSS THE HANDLER. At the handler's entry the delivered operation is
;; finished and its result not yet consumed: J5E-ROW-D is J5E with that one
;; result still in the pending count. The handler keeps the row's phase or
;; moves it to :uncertain, drops loans only (FN2-ENV-ROLES-DROPPED: no role
;; becomes live), keeps the ops table and the row's generation (so its owned
;; fences), counts a write in a write phase (one more done, a unit more
;; bytes: the posted count is the unit, FN2-ENV-J5-EVENT-OK), and the
;; route's terminal takes one from the pending count.
(defun fn2-env-j5e-row-d (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (implies (fn2-commit-idp id fn2-core)
           (and (fn2-env-j5e-phases id fn2-core)
                (< (fn2-env-j5e-live id fn2-core) (nfix (fn2-machine-pending id fn2-core))))))
(defthm fn2-env-j5e-live-dropped
  ; a loan drop over the same ops table and generation makes no role live
  ; and no fence owned
  (implies (and (fn2-env-roles-dropped id a b)
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a)))
           (<= (fn2-env-j5e-live id b) (fn2-env-j5e-live id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-live fn2-env-b2n fn2-env-owned-fences-of-ok fn2-env-op-of-ok (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped (role 0)) (:instance fn2-env-role-live-dropped (role 1))
                 (:instance fn2-env-role-live-dropped (role 2)) (:instance fn2-env-roles-dropped-ids)))))
(defthm fn2-env-j5e-phases-dropped
  (implies (and (fn2-env-j5e-phases id a) (fn2-env-roles-dropped id a b)
                (or (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                    (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
                (implies (member-equal (fn2-machine-phase id b)
                                       (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                         (and (equal (fn2-machine-cb-done id b) (+ 1 (nfix (fn2-machine-cb-done id a))))
                              (equal (fn2-machine-cb-bytes id b) (+ *fn2-commit-unit-bytes* (fn2-machine-cb-bytes id a))))))
           (fn2-env-j5e-phases id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-phases fn2-env-j5e-bytes nfix (:e natp) (:e <) member-equal (:e member-equal)
                               car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped (role 0)) (:instance fn2-env-role-live-dropped (role 1))
                 (:instance fn2-env-role-live-dropped (role 2))))))
(defthm fn2-env-j5e-live-natp
  (natp (fn2-env-j5e-live id c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-live fn2-env-b2n natp (:e natp))
           :use ((:instance fn2-env-owned-fences-natp (s 0) (k (fn2-env-ops-rows c)))))))
(defthm fn2-env-roles-dropped-idp
  (implies (fn2-env-roles-dropped id a b) (equal (fn2-commit-idp id b) (fn2-commit-idp id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-roles-dropped))))
(defthm fn2-env-j5e-row-handled
  (implies (and (fn2-env-j5e-row-d id a) (fn2-env-roles-dropped id a b)
                (or (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                    (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
                (implies (member-equal (fn2-machine-phase id b)
                                       (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                         (and (equal (fn2-machine-cb-done id b) (+ 1 (nfix (fn2-machine-cb-done id a))))
                              (equal (fn2-machine-cb-bytes id b) (+ *fn2-commit-unit-bytes* (fn2-machine-cb-bytes id a)))))
                (<= (nfix (fn2-machine-pending id a)) (+ 1 (nfix (fn2-machine-pending id b)))))
           (fn2-env-j5e-row id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-row fn2-env-j5e-row-d nfix natp)
           :do-not-induct t
           :use ((:instance fn2-env-j5e-live-dropped) (:instance fn2-env-j5e-phases-dropped)
                 (:instance fn2-env-roles-dropped-idp)
                 (:instance fn2-env-j5e-live-natp (c a)) (:instance fn2-env-j5e-live-natp (c b))))))
(defthm fn2-env-handler-bytes-room
  ; the handler's byte count stays in range: at a write phase with one write
  ; delivered and uncounted, at most one write is done (J5-ROLES-D), so the
  ; row holds at most a unit of bytes (J5E), and the delivered count is at
  ; most a unit (FN2-ENV-J5-EVENT-OK: at most the write's range)
  (implies (and (fn2-commit-idp id c)
                (member-equal (fn2-machine-phase id c)
                              (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                (fn2-env-j5e-phases id c) (fn2-env-j5-roles-d id ok log c)
                (<= (nfix count) *fn2-commit-unit-bytes*))
           (unsigned-byte-p 60 (+ (fn2-machine-cb-bytes id c) (nfix count))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5-roles-d fn2-env-b2n nfix natp
                               unsigned-byte-p integer-range-p (:e expt) member-equal (:e member-equal)
                               car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t)))
;; THE WRITE HANDLER'S BRANCH. With its writers' inputs in range (outcome
;; and reason u8, the byte count's room u60; FN2-ENV-HANDLER-BYTES-ROOM gives
;; the room in a write phase), fn2-commit-on-write-result either moves the row
;; to :uncertain or counts one full write of a write phase in place.
(defthmd fn2-env-idp-snapshot-ok
  (implies (fn2-commit-idp id fn2-core) (equal (fn2-commit-snapshot-read-code id fn2-core) :ok))
  :hints (("Goal" :in-theory '(fn2-commit-idp))))
(defthmd fn2-env-write-counts-keeps-phase
  ; the counting writer leaves the row's phase
  (equal (fn2-machine-phase id (fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok id d b fl fo c))
         (fn2-machine-phase id c))
  :hints (("Goal" :in-theory '(member-equal car-cons cdr-cons (:e consp))
           :use ((:instance fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-arm-phase
                            (fn2-arm-pset (list (fn2-machine-phase id c))) (fn2-core c)
                            (fn2-arms-w-cb-done d) (fn2-arms-w-cb-bytes b) (fn2-arms-w-cb-fence-live fl)
                            (fn2-arms-w-cb-fence-ok fo))))))
(defthm fn2-env-on-write-result-branch
  ; the write handler counts a full write of a write phase (the row stays
  ; in its phase), or moves the row to :uncertain
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                (implies (member-equal (fn2-machine-phase id m) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*
                                                              *fn2-commit-state-uncertain*))
                         (unsigned-byte-p 60 (+ (fn2-commit-row-cb-bytes id m) (nfix count)))))
           (let ((b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
             (or (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                 (and (member-equal (fn2-machine-phase id m) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                      (equal (fn2-machine-phase id b) (fn2-machine-phase id m))
                      (equal (fn2-commit-row-cb-done id b) (+ 1 (fn2-commit-row-cb-done id m)))
                      (equal (fn2-commit-row-cb-bytes id b) (+ *fn2-commit-unit-bytes* (fn2-commit-row-cb-bytes id m)))
                      (equal (fn2-commit-row-cb-fence-live id b) (fn2-commit-row-cb-fence-live id m))
                      (equal (fn2-commit-row-cb-fence-ok id b) (fn2-commit-row-cb-fence-ok id m))
                      (not (equal (fn2-commit-row-cb-fence-live id m) 1))
                      (< (fn2-commit-row-cb-done id m) (fn2-commit-row-cb-issued id m))
                      (equal outcome *fn2-outcome-done*) (equal count *fn2-commit-unit-bytes*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-write-result fn2-commit-arm-row-phase fn2-env-drop-io-ids fn2-env-write-counts-keeps-phase fn2-commit~fn2-commit-drop-io-arm-phase
                                               fn2-env-idp-snapshot-ok
                                               fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-reads
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-reads
                                               fn2-commit-drop-io-type fn2-commit-drop-io-wfp
                                               fn2-commit-row-cb-acks-width fn2-commit-row-cb-done-width fn2-commit-row-cb-bytes-width
                                               fn2-commit-row-cb-issued-width fn2-commit-row-cb-failed-width
                                               fn2-commit-row-cb-fence-live-width fn2-commit-row-cb-fence-ok-width
                                               fn2-commit-row-outcome-width fn2-commit-row-cb-reason-width fn2-commit-row-cb-cursor-width fn2-commit-row-pending-width
                                               (:e unsigned-byte-p) unsigned-byte-p integer-range-p nfix natp fix)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-cell (fn2-core m)) (:instance fn2-env-commit-idp-cell (fn2-core (fn2-commit-drop-io id m)))))))
;; ---------------------------------------------------------------------------
;; THE STATEMENT. Only A-FENCE-PERSISTS is assumed.
(defthm-owed fn2-commit-ack-implies-recoverable (profile actions choice recovery-actions)
 (let* ((run (fn2-env-run profile actions))
        (image (fn2-a-crash-image (fn2-env-device-log run) choice))
        (rec (fn2-env-recover profile image recovery-actions)))
  (implies (and (fn2-profile-supportedp profile)
                (fn2-env-recovery-done-p rec))
           (subsetp-equal (fn2-env-acknowledged-batches run)
                          (fn2-env-recovered-batches rec))))
 :teeth (fn2-commit-recoverable-positive fn2-commit-recoverable-positive-fua
         fn2-commit-recoverable-fence-removal)
 :schema :crash
 :doc "Every acknowledged commit batch (a member reply on a commit row after any action of any host-boundary action list interleaved with fn2-turn, from the native host's genesis) is in the chain the real recovery row reports, run by fn2-turn over a fresh core whose storage reads see a crash image of the device log: any image A-FENCE-PERSISTS admits, CHOICE picking it. Recovery's own actions are any list; its reads are answered with the image's octets. Only A-FENCE-PERSISTS is assumed.")
;; THE HANDLERS AND THE HARVEST. The write and fence handlers write their
;; row and the control child (each writer's ARM-KIDS) and drop loans, which
;; LENT-OK never needs (FN2-ENV-IO-EDGE-DROP-UNITS). The harvest marks the
;; harvested op submitted, release-pending or done at its generation and
;; finishes it (retired there, or free at the next), and keeps commit-io.
(defthm fn2-env-io-edge-drop-fl
  ; an edge drop clears a loan at most: FRESHNESS and LENT-OK stay
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-env-fl log c))
           (fn2-env-fl log (mv-nth 1 (fn2-commit-io-edge id role nil s g c))))
  :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-lent-ok fn2-env-freshness-of-heads fn2-env-incarnation-ok-of-heads
                               fn2-env-op-heads-kept fn2-env-io-drop-p nth-update-nth (:e zp) (:e equal) (:e nth) nth-0-cons)
           :use ((:instance fn2-commit-io-edge-fn2-env-hk (fn2-core c) (fn2-rel-c0 c) (add nil) (opslot s) (opgen g))
                 (:instance fn2-env-hk-reflexive (a c))
                 (:instance fn2-env-op-heads-of-hk (a c) (b (mv-nth 1 (fn2-commit-io-edge id role nil s g c)))
                            (s (fn2-env-op-heads-kept-witness c (mv-nth 1 (fn2-commit-io-edge id role nil s g c)))))
                 (:instance fn2-env-io-edge-drop-units (u (fn2-env-lent-ok-witness (mv-nth 1 (fn2-commit-io-edge id role nil s g c)))))
                 (:instance fn2-env-lent-ok-necc (fn2-core c)
                            (u (fn2-env-lent-ok-witness (mv-nth 1 (fn2-commit-io-edge id role nil s g c)))))))))
(defthm fn2-commit-drop-io-fn2-env-fl
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-fl log fn2-core))
           (fn2-env-fl log (fn2-commit-drop-io id fn2-core)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-io-edge-drop-fl fn2-core-stop-fn2-env-fl fn2-commit-io-edge-preserves-type
                                              fn2-commit-io-edge-preserves-wfp)
                                             (theory 'fn2-arm-frame-base))
           :use ((:instance fn2-env-drop-io-is-rewrite (c fn2-core))))))
(defthm fn2-env-heads-kept-of-ops-child
  (implies (equal (nth 1 b) (nth 1 a)) (fn2-env-op-heads-kept a b))
  :hints (("Goal" :in-theory '(fn2-env-op-heads-kept fn2-env-op-is-ops-op fn2-core-ops))))
(defthm fn2-env-fl-of-children
  ; a step leaving the ops child and commit-io keeps FRESHNESS and LENT-OK
  (implies (and (fn2-env-fl log a) (equal (nth 1 b) (nth 1 a)) (equal (nth *fn2-core-commit-io* b) (nth *fn2-core-commit-io* a)))
           (fn2-env-fl log b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-units-kept-of-io fn2-env-heads-kept-of-ops-child)
           :use ((:instance fn2-env-fresh-lent-kept)))))
(fn2-env-fl-row-writer fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live)
(fn2-env-fl-row-writer fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok)
(fn2-env-fl-handler fn2-commit-on-write-result)
(fn2-env-fl-handler fn2-commit-on-fence-result)
(defthm fn2-env-core-stop-keeps-ops
  (equal (nth 1 (fn2-core-stop r c)) (nth 1 c))
  :hints (("Goal" :in-theory (enable fn2-core-stop update-fn2-core-control))))
(defthm fn2-env-harvest-one-ops-cases
  ; the harvest's ops are the harvested table, finished at the harvested op or not
  (let ((o2 (nth 1 (mv-nth 10 (fn2-harvest-one c)))) (hn (fn2-harvest-next (nth 1 c))))
    (or (equal o2 (mv-nth 4 hn))
        (equal o2 (mv-nth 1 (fn2-op-finish (mv-nth 1 hn) (mv-nth 2 hn) (mv-nth 4 hn))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories '(fn2-harvest-one update-fn2-core-ops update-fn2-core-pool fn2-core-ops fn2-core-pool
                                        fn2-env-core-stop-keeps-ops nth-update-nth mv-nth car-cons cdr-cons
                                        (:e equal) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e nth) (:e mv-nth) (:e car) (:e cdr))
                                      (theory 'minimal-theory)))))
(defthm fn2-env-harvest-one-keeps-io
  (equal (nth *fn2-core-commit-io* (mv-nth 10 (fn2-harvest-one c))) (nth *fn2-core-commit-io* c))
  :hints (("Goal" :do-not-induct t :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories '(fn2-harvest-one update-fn2-core-ops update-fn2-core-pool fn2-core-ops fn2-core-pool
                                        fn2-env-core-stop-keeps-io-pool nth-update-nth mv-nth car-cons cdr-cons
                                        (:e equal) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e nth) (:e mv-nth) (:e car) (:e cdr))
                                      (theory 'minimal-theory)))))
(defthm fn2-harvest-one-fn2-env-fl
  ; the harvest keeps FRESHNESS and LENT-OK: it advances the op heads and keeps every unit
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-env-fl log fn2-core))
           (fn2-env-fl log (mv-nth 10 (fn2-harvest-one fn2-core))))
  :hints (("Goal" :in-theory '(fn2-env-fl fn2-env-freshness-of-advanced fn2-env-lent-ok-of-advanced
                               fn2-env-heads-advanced-of-ops fn2-env-units-kept-of-io fn2-env-harvest-one-keeps-io fn2-core-ops)
           :use ((:instance fn2-env-harvest-one-ops-cases (c fn2-core))
                 (:instance fn2-core-ops-type (fn2-core fn2-core)) (:instance fn2-env-core-ops-wfp (c fn2-core))
                 (:instance fn2-env-harvest-cases-advanced (o (nth 1 fn2-core)) (o2 (nth 1 (mv-nth 10 (fn2-harvest-one fn2-core)))))))))
;; ---------------------------------------------------------------------------
;; J5 AND J6 ACROSS THE HANDLERS AND THE DISPATCHER. Each handler, from the
;; evidence at its entry (J5-ROW-D, J5E-ROW-D: the delivered result finished
;; and uncounted), keeps the handled evidence (FN2-ENV-ON-WRITE-RESULT-HANDLED:
;; loans drop with the phase's last write only; the ops table, the pool, the
;; columns J5 reads and the pending count stay) and counts the result in
;; place or moves the row to :uncertain; each outcome gives J5, J5E-ROW-D
;; (the route's terminal takes the pending result) and J6, J6P, J6L, J6S.
;; The dispatcher adds the contract check (a stop at most); every other
;; commit row keeps its evidence (FN2-MACHINE-OBSERVE-FN2-COMMIT-FN2-ENV-J-OTHER).
(fn2-env-row-is-machine (cb-done cb-bytes cb-issued cb-fence-live cb-fence-ok pending generation))
(fn2-env-writer-keeps-io fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live)
(fn2-env-writer-keeps-io fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok)
(defthmd fn2-env-phase-of-if
  (equal (fn2-machine-phase id (if c a b)) (if c (fn2-machine-phase id a) (fn2-machine-phase id b))))
(make-event (value (cons 'progn (fn2-env-row-read-events '((pending . 5) (cb-bytes . 18) (cb-fence-live . 22))))))
(defthm fn2-env-handler-frame-keeps
  ; a frame of the handlers' columns at row ID's slot (children commit-io,
  ; extents, edges and control free) keeps the ops table, the pool, the row's
  ; id and slot, the columns J5 and J6 read but phase, count and fence flags,
  ; and the pending count
  (implies (and (fn2-arm-row-frame 9 (fn2-machine-slot id a) '(0 20 15 19 21 22 17 18 23) '(30 20 21 5) a b)
                (fn2-commit-idp id a))
           (and (fn2-env-ok b a) (equal (nth 0 b) (nth 0 a))
                (fn2-commit-idp id b) (equal (fn2-commit-row id b) (fn2-commit-row id a))
                (fn2-env-cols-kept id a b)
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-cols-kept fn2-ctf-dir-refl (:e member-equal) (:e natp) natp
                               fn2-env-ok)
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-cell (fn2-core a)) (:instance fn2-env-ok-view-equivalence)
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (k 0))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (k 1))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (k 3))
                 (:instance fn2-ctf-dir-of-nth (x a))
                 (:instance fn2-env-read-codes-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-cb-mode-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-cb-issued-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-generation-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-batch-no-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-cb-deps-ok-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-cb-log-ok-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))
                 (:instance fn2-machine-pending-of-row-frame (row (fn2-machine-slot id a)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)))))))
(defthm fn2-env-on-write-result-io
  ; the write handler's commit-io is its entry's, or the loan drop's when it
  ; counts the phase's last write
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
             (or (equal (nth 30 b) (nth 30 m))
                 (and (equal (nth 30 b) (nth 30 (fn2-commit-drop-io id m)))
                      (equal (+ 1 (fn2-commit-row-cb-done id m)) (fn2-commit-row-cb-issued id m))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-write-result fn2-env-idp-snapshot-ok fn2-env-nth-of-if
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-keeps-io
                                               fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-keeps-io)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-on-write-result-phase
  ; the write handler keeps the row's phase or moves it to :uncertain
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
             (member-equal (fn2-machine-phase id b) (list (fn2-machine-phase id m) *fn2-commit-state-uncertain*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-write-result fn2-env-idp-snapshot-ok fn2-env-phase-of-if
                                               fn2-env-write-counts-keeps-phase fn2-commit~fn2-commit-drop-io-arm-phase
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-arm-phase
                                               fn2-env-member-pair (:e member-equal) (:e natp) (:e <))
                                             (set-difference-theories (theory 'fn2-arm-frame-base) '(member-equal)))
           :do-not-induct t)))
(defthm fn2-env-on-write-result-handled
  ; the write handler keeps the ops table, the pool, the row's id, slot,
  ; extents and the columns J5 and J6 read but phase, count and fence flags,
  ; and its pending count; it clears loans of the row's units only, all
  ; three with the phase's last write
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
             (and (fn2-env-roles-dropped id m b) (fn2-env-cols-kept id m b)
                  (equal (fn2-machine-pending id b) (fn2-machine-pending id m))
                  (fn2-env-drop-all-or-none id m b))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-roles-dropped fn2-env-drop-all-or-none fn2-env-role-io fn2-env-role-extent fn2-env-io-drop-p
                               fn2-env-idp-snapshot-ok fn2-commit-row-cb-done-is-machine fn2-commit-row-cb-issued-is-machine
                               fn2-commit-row (:type-prescription fn2-commit-idp) (:e subsetp-equal) (:e natp))
           :do-not-induct t
           :use ((:instance fn2-commit-on-write-result-arm-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id m)) (fn2-arm-cs '(0 20 15 19 21 22 17 18 23)) (fn2-arm-ch '(30 20 21 5)) (fn2-arm-c0 m) (fn2-core m) (event *fn2-event-write-result*))
                 (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id m)) (columns '(0 20 15 19 21 22 17 18 23)) (children '(30 20 21 5)) (a m))
                 (:instance fn2-env-handler-frame-keeps (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-on-write-result-io)
                 (:instance fn2-env-drop-io-ids (x id) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 0)) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 0)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 0)) (c m))
                 (:instance fn2-env-child-congruences (role 0) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 0) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 0) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 1)) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 1)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 1)) (c m))
                 (:instance fn2-env-child-congruences (role 1) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 1) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 1) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 2)) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 2)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 2)) (c m))
                 (:instance fn2-env-child-congruences (role 2) (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 2) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 2) (c m))))))
(defthm fn2-env-j5e-row-d-handled
  ; with the pending count kept, the handler leaves J5E-ROW-D: the delivered
  ; result is still in the count until the route's terminal takes it
  (implies (and (fn2-env-j5e-row-d id a) (fn2-env-roles-dropped id a b)
                (or (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                    (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*))
                (equal (fn2-machine-generation id b) (fn2-machine-generation id a))
                (implies (member-equal (fn2-machine-phase id b)
                                       (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                         (and (equal (fn2-machine-cb-done id b) (+ 1 (nfix (fn2-machine-cb-done id a))))
                              (equal (fn2-machine-cb-bytes id b) (+ *fn2-commit-unit-bytes* (fn2-machine-cb-bytes id a)))))
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a)))
           (fn2-env-j5e-row-d id b))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-row-d nfix natp)
           :do-not-induct t
           :use ((:instance fn2-env-j5e-live-dropped) (:instance fn2-env-j5e-phases-dropped)
                 (:instance fn2-env-roles-dropped-idp)
                 (:instance fn2-env-j5e-live-natp (c a)) (:instance fn2-env-j5e-live-natp (c b))))))
(defthm fn2-env-j6-quiet-to-uncertain
  ; with no role live, a loan drop to :uncertain leaves J6* (J6S vacuous)
  (implies (and (fn2-env-roles-dropped id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                (not (fn2-env-role-live id 0 a)) (not (fn2-env-role-live id 1 a)) (not (fn2-env-role-live id 2 a)))
           (and (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row fn2-env-role-settle-ok
                               (:e member-equal) (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped (role 0)) (:instance fn2-env-role-live-dropped (role 1))
                 (:instance fn2-env-role-live-dropped (role 2))))))
(defthm fn2-env-j6-all-to-uncertain
  ; a row moved to :uncertain by a loan drop keeps J6, J6P, J6L and J6S:
  ; from a phase that may own writes by J6S-TO-UNCERTAIN, from any other
  ; with no role live (J5E)
  (implies (and (fn2-env-roles-dropped id a b)
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                (fn2-env-j5e-phases id a) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-phases member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :use ((:instance fn2-env-j6s-to-uncertain) (:instance fn2-env-j6-quiet-to-uncertain)))))
(defthm fn2-env-handled-to-uncertain
  ; a handler step that keeps the handled evidence and moves the row to
  ; :uncertain: J5, J5E-ROW-D and J6* after
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a))
                (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                (fn2-env-j5-ops 0 (fn2-env-ops-rows a) id log a)
                (fn2-env-j5e-row-d id a) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-cols-kept member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :do-not-induct t
           :cases ((fn2-commit-idp id a))
           :use ((:instance fn2-env-j5-row-to-uncertain) (:instance fn2-env-j5e-row-d-handled)
                 (:instance fn2-env-j6-all-to-uncertain)))
          ("Subgoal 1" :in-theory '(fn2-env-j5e-row-d fn2-env-cols-kept member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp)))
          ("Subgoal 2" :in-theory '(fn2-env-j5-row fn2-env-j5e-row-d fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row)
           :use ((:instance fn2-env-roles-dropped-idp)))))
(defthm fn2-env-j5-roles-d-natp-done
  (implies (and (fn2-env-j5-roles-d id ok log c)
                (member-equal (fn2-machine-phase id c) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*)))
           (natp (fn2-machine-cb-done id c)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-roles-d member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp)))))
(defthm fn2-env-live2-kept-count
  ; at :log-write, a counted write keeps role 2's liveness: the loans stay,
  ; or the last result was in flight and no role is live
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-drop-all-or-none id a b) (fn2-env-j5-roles-d id ok log a)
                (equal (fn2-machine-phase id a) *fn2-commit-state-log-write*))
           (equal (fn2-env-role-live id 2 b) (fn2-env-role-live id 2 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-drop-all-or-none (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-role-live-dropped (role 2)) (:instance fn2-env-roles-d-last)))))
(defthm fn2-env-handled-count
  ; a handler step that counts a full write of a write phase in place,
  ; keeping the handled evidence: J5, J5E-ROW-D and J6* after
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b) (fn2-env-drop-all-or-none id a b)
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a))
                (equal (fn2-machine-phase id b) (fn2-machine-phase id a))
                (member-equal (fn2-machine-phase id a) (list *fn2-commit-state-dependencies* *fn2-commit-state-log-write*))
                (equal (fn2-machine-cb-fence-ok id b) (fn2-machine-cb-fence-ok id a))
                (equal (fn2-machine-cb-fence-live id b) (fn2-machine-cb-fence-live id a))
                (equal (fn2-machine-cb-done id b) (+ 1 (fn2-machine-cb-done id a)))
                (equal (fn2-machine-cb-bytes id b) (+ *fn2-commit-unit-bytes* (fn2-machine-cb-bytes id a)))
                (fn2-env-j5-row-d id *fn2-event-write-result* *fn2-outcome-done* *fn2-commit-unit-bytes* log a)
                (fn2-env-j5e-row-d id a)
                (fn2-env-j6-row id a) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-cols-kept)
           :do-not-induct t
           :cases ((fn2-commit-idp id a)))
          ("Subgoal 1" :in-theory '(fn2-env-cols-kept fn2-env-j5-row-d nfix natp (:e equal) (:e natp) (:e <) member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp))
           :use ((:instance fn2-env-j5-row-count) (:instance fn2-env-j5e-row-d-handled)
                 (:instance fn2-env-j6-in-phase) (:instance fn2-env-j6p-in-phase) (:instance fn2-env-j6l-in-phase)
                 (:instance fn2-env-j6s-in-phase)
                 (:instance fn2-env-live2-kept-count (ok t))
                 (:instance fn2-env-j5-roles-d-natp-done (c a) (ok t))))
          ("Subgoal 2" :in-theory '(fn2-env-j5-row fn2-env-j5e-row-d fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row)
           :use ((:instance fn2-env-roles-dropped-idp)))))
(defthm fn2-env-j5-row-d-ops
  (implies (and (fn2-env-j5-row-d id event outcome count log c) (fn2-commit-idp id c))
           (fn2-env-j5-ops 0 (fn2-env-ops-rows c) id log c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row-d))))
(defthm fn2-env-j5-row-d-roles
  (implies (and (fn2-env-j5-row-d id *fn2-event-write-result* outcome count log c) (fn2-commit-idp id c))
           (fn2-env-j5-roles-d id (and (equal outcome *fn2-outcome-done*) (equal count *fn2-commit-unit-bytes*)) log c))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-row-d (:e equal)))))
(defthm fn2-commit-on-write-result-fn2-env-j
  ; THE WRITE HANDLER. At its entry the harvest has finished the delivered
  ; role write (J5-ROW-D, J5E-ROW-D); with the result's outcome and reason
  ; bytes and its count at most a unit, the handler counts it in place or
  ; moves the row to :uncertain, and J5, J6, J6P, J6L, J6S hold after, with
  ; J5E-ROW-D (the pending count is the route's terminal's to take)
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason) (<= (nfix count) *fn2-commit-unit-bytes*)
                (fn2-env-j5-row-d id *fn2-event-write-result* outcome count log m) (fn2-env-j5e-row-d id m)
                (fn2-env-j6-row id m) (fn2-env-j6p-row id m) (fn2-env-j6l-row id m) (fn2-env-j6s-row id m))
           (let ((b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
             (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                  (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b))))
  :hints (("Goal" :in-theory '(fn2-env-idp-snapshot-ok fn2-commit-row-cb-done-is-machine fn2-commit-row-cb-bytes-is-machine
                               fn2-commit-row-cb-fence-live-is-machine fn2-commit-row-cb-fence-ok-is-machine
                               (:type-prescription fn2-commit-idp) fn2-env-j5e-row-d
                               member-equal (:e member-equal) car-cons cdr-cons (:e car) (:e cdr) (:e consp) (:e equal))
           :do-not-induct t
           :cases ((equal (fn2-machine-phase id m) *fn2-commit-state-uncertain*))
           :use ((:instance fn2-env-on-write-result-handled)
                 (:instance fn2-env-on-write-result-phase)
                 (:instance fn2-env-on-write-result-branch)
                 (:instance fn2-env-handler-bytes-room (c m) (ok (and (equal outcome *fn2-outcome-done*) (equal count *fn2-commit-unit-bytes*))))
                 (:instance fn2-env-j5-row-d-ops (event *fn2-event-write-result*) (c m))
                 (:instance fn2-env-j5-row-d-roles (c m))
                 (:instance fn2-env-roles-dropped-idp (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-handled-to-uncertain (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-handled-count (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))))))
(defthm fn2-env-on-fence-result-io
  ; the fence handler's commit-io is its entry's (it drops no loan)
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
             (or (equal (nth 30 b) (nth 30 m))
                 (and (equal (nth 30 b) (nth 30 (fn2-commit-drop-io id m)))
                      (equal (+ 1 (fn2-commit-row-cb-done id m)) (fn2-commit-row-cb-issued id m))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-fence-result fn2-env-idp-snapshot-ok fn2-env-nth-of-if
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-keeps-io
                                               fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-keeps-io)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-on-fence-result-phase
  ; the fence handler keeps the row's phase or moves it to :uncertain
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
             (member-equal (fn2-machine-phase id b) (list (fn2-machine-phase id m) *fn2-commit-state-uncertain*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-fence-result fn2-env-idp-snapshot-ok fn2-env-phase-of-if
                                               fn2-env-write-counts-keeps-phase fn2-commit~fn2-commit-drop-io-arm-phase
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-arm-phase
                                               fn2-env-member-pair (:e member-equal) (:e natp) (:e <))
                                             (set-difference-theories (theory 'fn2-arm-frame-base) '(member-equal)))
           :do-not-induct t)))
(defthm fn2-env-on-fence-result-handled
  ; the fence handler keeps the ops table, the pool, the row's id, slot,
  ; extents and the columns J5 and J6 read but phase, count and fence flags,
  ; and its pending count; it clears loans of the row's units only, all
  ; three with the phase's last write
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
             (and (fn2-env-roles-dropped id m b) (fn2-env-cols-kept id m b)
                  (equal (fn2-machine-pending id b) (fn2-machine-pending id m))
                  (fn2-env-drop-all-or-none id m b))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-roles-dropped fn2-env-drop-all-or-none fn2-env-role-io fn2-env-role-extent fn2-env-io-drop-p
                               fn2-env-idp-snapshot-ok fn2-commit-row-cb-done-is-machine fn2-commit-row-cb-issued-is-machine
                               fn2-commit-row (:type-prescription fn2-commit-idp) (:e subsetp-equal) (:e natp))
           :do-not-induct t
           :use ((:instance fn2-commit-on-fence-result-arm-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id m)) (fn2-arm-cs '(0 20 15 19 21 22 17 18 23)) (fn2-arm-ch '(30 20 21 5)) (fn2-arm-c0 m) (fn2-core m) (event *fn2-event-fence-result*))
                 (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id m)) (columns '(0 20 15 19 21 22 17 18 23)) (children '(30 20 21 5)) (a m))
                 (:instance fn2-env-handler-frame-keeps (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-on-fence-result-io)
                 (:instance fn2-env-drop-io-ids (x id) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 0)) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 0)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 0)) (c m))
                 (:instance fn2-env-child-congruences (role 0) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 0) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 0) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 1)) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 1)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 1)) (c m))
                 (:instance fn2-env-child-congruences (role 1) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 1) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 1) (c m))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 2)) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row id m)) 2)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-units (u (+ (* 3 (fn2-commit-row id m)) 2)) (c m))
                 (:instance fn2-env-child-congruences (role 2) (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (role 2) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x id) (role 2) (c m))))))
(defthm fn2-env-on-fence-result-branch
  ; the fence handler counts the fence at :fence (the row stays there with
  ; no fence live), or leaves the row at :uncertain
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason))
           (let ((b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
             (or (equal (fn2-machine-phase id b) *fn2-commit-state-uncertain*)
                 (and (equal (fn2-machine-phase id m) *fn2-commit-state-fence*)
                      (equal (fn2-machine-phase id b) *fn2-commit-state-fence*)
                      (equal (fn2-commit-row-cb-fence-live id b) 0)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-on-fence-result fn2-commit-arm-row-phase fn2-env-drop-io-ids fn2-env-write-counts-keeps-phase fn2-commit~fn2-commit-drop-io-arm-phase
                                               fn2-env-idp-snapshot-ok
                                               fn2-commit-write+cb-done+cb-bytes+cb-fence-live+cb-fence-ok-reads
                                               fn2-commit-write+phase+cb-cursor+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live-reads
                                               fn2-commit-drop-io-type fn2-commit-drop-io-wfp
                                               fn2-commit-row-cb-acks-width fn2-commit-row-cb-done-width fn2-commit-row-cb-bytes-width
                                               fn2-commit-row-cb-issued-width fn2-commit-row-cb-failed-width
                                               fn2-commit-row-cb-fence-live-width fn2-commit-row-cb-fence-ok-width
                                               fn2-commit-row-outcome-width fn2-commit-row-cb-reason-width fn2-commit-row-cb-cursor-width fn2-commit-row-pending-width
                                               (:e unsigned-byte-p) unsigned-byte-p integer-range-p nfix natp fix)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-cell (fn2-core m)) (:instance fn2-env-commit-idp-cell (fn2-core (fn2-commit-drop-io id m)))))))
(defthm fn2-env-handled-fence-done
  ; a handler step that counts the fence at :fence (none live after),
  ; keeping the handled evidence: J5, J5E-ROW-D and J6* after
  (implies (and (fn2-env-roles-dropped id a b) (fn2-env-cols-kept id a b)
                (equal (fn2-machine-pending id b) (fn2-machine-pending id a))
                (equal (fn2-machine-phase id a) *fn2-commit-state-fence*)
                (equal (fn2-machine-phase id b) *fn2-commit-state-fence*)
                (equal (fn2-machine-cb-fence-live id b) 0)
                (fn2-env-j5-row-d id *fn2-event-fence-result* outcome count log a)
                (fn2-env-j5e-row-d id a)
                (fn2-env-j6-row id a) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-cols-kept (:e member-equal) (:e equal))
           :do-not-induct t
           :use ((:instance fn2-env-j5-row-fence-done) (:instance fn2-env-j5e-row-d-handled)
                 (:instance fn2-env-roles-dropped-idp) (:instance fn2-env-roles-dropped-ids)
                 (:instance fn2-env-j6-in-phase) (:instance fn2-env-j6p-in-phase) (:instance fn2-env-j6l-in-phase)
                 (:instance fn2-env-j6s-in-phase)))))
(defthm fn2-commit-on-fence-result-fn2-env-j
  ; THE FENCE HANDLER. At its entry the harvest has finished the row's
  ; fence (J5-ROW-D: the owned fences one short of the live flag); with the
  ; result's outcome and reason bytes the handler counts it at :fence or
  ; leaves the row at :uncertain, and J5, J6, J6P, J6L, J6S hold after,
  ; with J5E-ROW-D
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                (fn2-env-j5-row-d id *fn2-event-fence-result* outcome count log m) (fn2-env-j5e-row-d id m)
                (fn2-env-j6-row id m) (fn2-env-j6p-row id m) (fn2-env-j6l-row id m) (fn2-env-j6s-row id m))
           (let ((b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
             (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                  (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b))))
  :hints (("Goal" :in-theory '(fn2-env-idp-snapshot-ok fn2-commit-row-cb-fence-live-is-machine
                               (:type-prescription fn2-commit-idp) fn2-env-j5e-row-d (:e equal))
           :do-not-induct t
           :use ((:instance fn2-env-on-fence-result-handled)
                 (:instance fn2-env-on-fence-result-branch)
                 (:instance fn2-env-j5-row-d-ops (event *fn2-event-fence-result*) (c m))
                 (:instance fn2-env-roles-dropped-idp (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-handled-to-uncertain (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-handled-fence-done (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))))))
(defthm fn2-env-j5e-row-d-of-views
  ; the same of J5E-ROW-D
  (implies (and (fn2-env-tk b a) (fn2-env-mk b a) (fn2-env-ok b a) (fn2-env-pdk b a) (fn2-env-lk b a))
           (equal (fn2-env-j5e-row-d id b) (fn2-env-j5e-row-d id a)))
  :hints (("Goal" :in-theory '(fn2-env-j5e-row-d fn2-env-j5e-phases fn2-env-j5e-bytes fn2-env-j5e-live fn2-env-owned-fences-of-ok
                               fn2-env-op-of-ok)
           :cases ((fn2-commit-idp id a))
           :use ((:instance fn2-env-read-codes-of-tk) (:instance fn2-machine-phase-of-tk)
                 (:instance fn2-machine-cb-done-of-tk) (:instance fn2-machine-cb-bytes-of-mk)
                 (:instance fn2-machine-generation-of-mk) (:instance fn2-machine-pending-of-pdk)
                 (:instance fn2-env-commit-idp-kind (fn2-core a))
                 (:instance fn2-env-role-live-of-lk (role 0)) (:instance fn2-env-role-live-of-lk (role 1))
                 (:instance fn2-env-role-live-of-lk (role 2))))))
(defthm fn2-env-j-of-views
  ; a step keeping the views J5, J5E and J6* read keeps them at a commit row
  (implies (and (fn2-env-tk b a) (fn2-env-mk b a) (fn2-env-ok b a) (fn2-env-pk b a) (fn2-env-io-view b a)
                (fn2-env-pdk b a) (fn2-env-lk b a) (fn2-commit-idp id a)
                (fn2-env-j5-row id log a) (fn2-env-j5e-row-d id a)
                (fn2-env-j6-row id a) (fn2-env-j6p-row id a) (fn2-env-j6l-row id a) (fn2-env-j6s-row id a))
           (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5e-row-d-of-views)
           :do-not-induct t
           :use ((:instance fn2-env-commit-idp-kind (fn2-core a))
                 (:instance fn2-env-j5-unit-kept-of-views)
                 (:instance fn2-env-j5-kept-of-parts)
                 (:instance fn2-env-j5-kept-transfer)
                 (:instance fn2-env-j6ls-kept-transfer)))))
(defthm fn2-core-stop-fn2-env-j
  (implies (and (fn2-commit-idp id c)
                (fn2-env-j5-row id log c) (fn2-env-j5e-row-d id c)
                (fn2-env-j6-row id c) (fn2-env-j6p-row id c) (fn2-env-j6l-row id c) (fn2-env-j6s-row id c))
           (let ((b (fn2-core-stop r c)))
             (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                  (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b))))
  :hints (("Goal" :in-theory '(fn2-env-tk-reflexive fn2-env-mk-reflexive fn2-env-ok-reflexive fn2-env-pk-reflexive fn2-env-io-view-reflexive fn2-env-pdk-reflexive fn2-env-lk-reflexive)
           :do-not-induct t
           :use ((:instance fn2-env-j-of-views (a c) (b (fn2-core-stop r c)))
                 (:instance fn2-core-stop-fn2-env-tk (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-mk (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-ok (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-pk (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-io-view (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-pdk (reason r) (fn2-core c) (fn2-rel-c0 c))
                 (:instance fn2-core-stop-fn2-env-lk (reason r) (fn2-core c) (fn2-rel-c0 c))))))
(defthm fn2-machine-observe-fn2-commit-fn2-env-j
  ; THE DISPATCHER at a commit row: a write or fence result, delivered with
  ; the row's evidence at the handler's entry, leaves J5, J5E-ROW-D and J6*
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (member-equal event (list *fn2-event-write-result* *fn2-event-fence-result*))
                (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason)
                (implies (equal event *fn2-event-write-result*) (<= (nfix count) *fn2-commit-unit-bytes*))
                (fn2-env-j5-row-d id event outcome count log m) (fn2-env-j5e-row-d id m)
                (fn2-env-j6-row id m) (fn2-env-j6p-row id m) (fn2-env-j6l-row id m) (fn2-env-j6s-row id m))
           (let ((b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
             (and (fn2-env-j5-row id log b) (fn2-env-j5e-row-d id b)
                  (fn2-env-j6-row id b) (fn2-env-j6p-row id b) (fn2-env-j6l-row id b) (fn2-env-j6s-row id b))))
  :hints (("Goal" :in-theory '(fn2-machine-observe-fn2-commit fn2-machine-observe-contract-check fn2-env-idp-snapshot-ok
                               mv-nth car-cons cdr-cons (:e zp) (:e binary-+) (:e equal) member-equal (:e member-equal) (:e consp) (:e car) (:e cdr))
           :do-not-induct t
           :use ((:instance fn2-commit-on-write-result-fn2-env-j)
                 (:instance fn2-commit-on-fence-result-fn2-env-j)
                 (:instance fn2-env-on-write-result-handled) (:instance fn2-env-on-fence-result-handled)
                 (:instance fn2-env-roles-dropped-idp (a m) (b (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-roles-dropped-idp (a m) (b (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-core-stop-fn2-env-j (r *fn2-stop-reason-machine-contract*) (c (mv-nth 1 (fn2-commit-on-write-result id *fn2-event-write-result* outcome reason count aux0 aux1 m))))
                 (:instance fn2-core-stop-fn2-env-j (r *fn2-stop-reason-machine-contract*) (c (mv-nth 1 (fn2-commit-on-fence-result id *fn2-event-fence-result* outcome reason count aux0 aux1 m))))))))
(defthm fn2-env-drop-io-other-unit
  ; the loan drop of row ID leaves every unit of another row
  (implies (and (fn2-corep c) (fn2-core-wfp c) (natp k) (< k 3)
                (not (equal (fn2-commit-row i c) (fn2-commit-row id c))))
           (equal (fn2-env-io (+ (* 3 (fn2-commit-row i c)) k) (fn2-commit-drop-io id c)) (fn2-env-io (+ (* 3 (fn2-commit-row i c)) k) c)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-commit-io-edge-preserves-type fn2-commit-io-edge-preserves-wfp fn2-env-io-edge-keeps-ids
                               fn2-commit-row nfix natp (:type-prescription fn2-machine-slot-natp) (:e nfix))
           :do-not-induct t
           :use ((:instance fn2-env-drop-io-is-rewrite)
                 (:instance fn2-env-io-edge-drop-units (role 0) (s 0) (g 0) (u (+ (* 3 (fn2-commit-row i c)) k)))
                 (:instance fn2-env-io-edge-drop-units (role 1) (s 0) (g 0) (u (+ (* 3 (fn2-commit-row i c)) k)) (c (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))
                 (:instance fn2-env-io-edge-drop-units (role 2) (s 0) (g 0) (u (+ (* 3 (fn2-commit-row i c)) k)) (c (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i c)) k)) (a (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))) (b (fn2-core-stop *fn2-stop-reason-commit-io* (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c)))))))))
                 (:instance fn2-env-core-stop-keeps-io-pool (r *fn2-stop-reason-commit-io*) (c (mv-nth 1 (fn2-commit-io-edge id 2 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 1 nil 0 0 (mv-nth 1 (fn2-commit-io-edge id 0 nil 0 0 c))))))))))))
(defthm fn2-env-role-readers-of-unit
  ; a role's octets, pool row and lease read its unit and the pool alone
  (implies (and (equal (fn2-env-role-io id role b) (fn2-env-role-io id role a)) (equal (nth 0 b) (nth 0 a)))
           (and (equal (fn2-env-role-octets id role b) (fn2-env-role-octets id role a))
                (equal (fn2-env-role-pool-ok id role b) (fn2-env-role-pool-ok id role a))
                (equal (fn2-env-role-lease id role b) (fn2-env-role-lease id role a))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-role-pool-ok)
           :use ((:instance fn2-env-role-lease-of-unit)
                 (:instance fn2-env-role-octets-is-row-octets (c a))
                 (:instance fn2-env-role-octets-is-row-octets (c b))
                 (:instance fn2-env-pool-readers-of-pool-child (s (nth 4 (fn2-env-role-io id role a))))))))
(defthm fn2-env-j-other-row-kept
  ; a step keeping a row's J5 evidence, the pool and its pending count keeps
  ; J5, J5E and J6* at the row
  (implies (and (fn2-env-j5-same-evidence i a b) (equal (nth 0 b) (nth 0 a))
                (equal (fn2-machine-pending i b) (fn2-machine-pending i a))
                (fn2-env-j5-row i log a) (fn2-env-j5e-row i a)
                (fn2-env-j6-row i a) (fn2-env-j6p-row i a) (fn2-env-j6l-row i a) (fn2-env-j6s-row i a))
           (and (fn2-env-j5-row i log b) (fn2-env-j5e-row i b)
                (fn2-env-j6-row i b) (fn2-env-j6p-row i b) (fn2-env-j6l-row i b) (fn2-env-j6s-row i b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-kept (:e natp) (:e <))
           :do-not-induct t
           :use ((:instance fn2-env-j5-evidence-role-reads (id i) (role 0)) (:instance fn2-env-j5-evidence-role-reads (id i) (role 1))
                 (:instance fn2-env-j5-evidence-role-reads (id i) (role 2))
                 (:instance fn2-env-role-readers-of-unit (id i) (role 0)) (:instance fn2-env-role-readers-of-unit (id i) (role 1))
                 (:instance fn2-env-role-readers-of-unit (id i) (role 2))
                 (:instance fn2-env-j5-kept-transfer (id i)) (:instance fn2-env-j6ls-kept-transfer (id i))
                 (:instance fn2-env-j5-evidence-reads (id i))
                 (:instance fn2-env-role-live-congruence (id i) (role 0)) (:instance fn2-env-role-live-congruence (id i) (role 1))
                 (:instance fn2-env-role-live-congruence (id i) (role 2))
                 (:instance fn2-env-owned-fences-congruence (id i) (s 0) (k (fn2-env-ops-rows a)))
                 (:instance fn2-env-j5-evidence-op (id i))
                 (:instance fn2-env-j5e-row-of-parts (id i))))))
(defthm fn2-env-dispatch-io
  ; the dispatcher's commit-io is its entry's, or the row's loan drop's
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m))
           (let ((b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
             (or (equal (nth 30 b) (nth 30 m)) (equal (nth 30 b) (nth 30 (fn2-commit-drop-io id m))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-machine-observe-fn2-commit fn2-machine-observe-contract-check fn2-machine-refuse-observation
                               fn2-env-idp-snapshot-ok fn2-env-core-stop-keeps-io-pool
                               mv-nth car-cons cdr-cons (:e zp) (:e binary-+) (:e equal) (:e consp) (:e car) (:e cdr))
           :do-not-induct t
           :cases ((equal event *fn2-event-write-result*) (equal event *fn2-event-fence-result*))
           :use ((:instance fn2-env-on-write-result-io) (:instance fn2-env-on-fence-result-io)))))
(defthm fn2-env-dispatch-other-evidence
  ; the dispatcher at row ID keeps another row's J5 evidence, the pool and
  ; that row's pending count
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m) (fn2-commit-idp i m)
                (not (equal (fn2-commit-row i m) (fn2-commit-row id m))))
           (let ((b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
             (and (fn2-env-j5-same-evidence i m b) (equal (nth 0 b) (nth 0 m))
                  (equal (fn2-machine-pending i b) (fn2-machine-pending i m)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j5-same-evidence fn2-env-role-io fn2-env-role-extent fn2-commit-row fn2-ctf-dir-refl fn2-env-ok
                               (:type-prescription fn2-commit-idp) (:e member-equal) (:e natp) natp (:e <) (:e subsetp-equal))
           :do-not-induct t
           :use ((:instance fn2-machine-observe-fn2-commit-ctf-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id m)) (fn2-arm-cs '(0 20 15 19 21 22 17 18 23)) (fn2-arm-ch '(30 20 21 5)) (fn2-arm-c0 m) (fn2-core m))
                 (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id m)) (columns '(0 20 15 19 21 22 17 18 23)) (children '(30 20 21 5)) (a m))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))) (k 0))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))) (k 1))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))) (k 3))
                 (:instance fn2-ctf-dir-of-nth (x m) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-read-codes-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-commit-idp-cell (fn2-core m))
                 (:instance fn2-env-commit-idp-cell (id i) (fn2-core m))
                 (:instance fn2-env-dispatch-io)
                 (:instance fn2-env-drop-io-ids (x i) (c m))
                 (:instance fn2-env-ok-view-equivalence (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-phase-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-mode-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-issued-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-done-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-bytes-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-generation-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-fence-live-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-fence-ok-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-deps-ok-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-cb-log-ok-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-batch-no-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-pending-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 0)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 0)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-other-unit (k 0) (c m))
                 (:instance fn2-env-child-congruences (id i) (role 0) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (id i) (role 0) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x i) (role 0) (c m))
                 (:instance fn2-env-role-readers-of-unit (id i) (role 0) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 1)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 1)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-other-unit (k 1) (c m))
                 (:instance fn2-env-child-congruences (id i) (role 1) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (id i) (role 1) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x i) (role 1) (c m))
                 (:instance fn2-env-role-readers-of-unit (id i) (role 1) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 2)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-io-of-io-child (u (+ (* 3 (fn2-commit-row i m)) 2)) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-other-unit (k 2) (c m))
                 (:instance fn2-env-child-congruences (id i) (role 2) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-child-congruences (id i) (role 2) (a (fn2-commit-drop-io id m)) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-env-drop-io-resource (x i) (role 2) (c m))
                 (:instance fn2-env-role-readers-of-unit (id i) (role 2) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))))))
(defthm fn2-machine-observe-fn2-commit-fn2-env-j-other
  ; THE DISPATCHER, OTHER ROWS: J5, J5E and J6* at another commit row stay
  (implies (and (fn2-corep m) (fn2-core-wfp m) (fn2-commit-idp id m)
                (not (equal (fn2-commit-row i m) (fn2-commit-row id m)))
                (fn2-env-j5-row i log m) (fn2-env-j5e-row i m)
                (fn2-env-j6-row i m) (fn2-env-j6p-row i m) (fn2-env-j6l-row i m) (fn2-env-j6s-row i m))
           (let ((b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
             (and (fn2-env-j5-row i log b) (fn2-env-j5e-row i b)
                  (fn2-env-j6-row i b) (fn2-env-j6p-row i b) (fn2-env-j6l-row i b) (fn2-env-j6s-row i b))))
  :hints (("Goal" :in-theory '()
           :do-not-induct t
           :cases ((fn2-commit-idp i m)))
          ("Subgoal 1" :use ((:instance fn2-env-dispatch-other-evidence)
                             (:instance fn2-env-j-other-row-kept (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))))
          ("Subgoal 2" :in-theory '(fn2-env-j5-row fn2-env-j5e-row fn2-env-j6-row fn2-env-j6p-row fn2-env-j6l-row fn2-env-j6s-row fn2-ctf-dir-refl (:type-prescription fn2-commit-idp) (:e natp) (:e subsetp-equal) (:e member-equal))
           :use ((:instance fn2-env-read-codes-of-row-frame (id i) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))
                 (:instance fn2-machine-observe-fn2-commit-ctf-row-frame (fn2-arm-tb 9) (fn2-arm-row (fn2-machine-slot id m)) (fn2-arm-cs '(0 20 15 19 21 22 17 18 23)) (fn2-arm-ch '(30 20 21 5)) (fn2-arm-c0 m) (fn2-core m))
                 (:instance fn2-arm-row-frame-refl (table 9) (row (fn2-machine-slot id m)) (columns '(0 20 15 19 21 22 17 18 23)) (children '(30 20 21 5)) (a m))
                 (:instance fn2-env-row-frame-child (tb 9) (row (fn2-machine-slot id m)) (cs '(0 20 15 19 21 22 17 18 23)) (ch '(30 20 21 5)) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))) (k 3))
                 (:instance fn2-ctf-dir-of-nth (x m) (a m) (b (mv-nth 1 (fn2-machine-observe-fn2-commit id event outcome reason count aux0 aux1 m))))))))
