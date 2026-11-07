; Commit durability over every execution and every environment (ember,
; 2026-11-07). FN2-ENV-RUN interprets any list of host-boundary actions,
; interleaved with fn2-turn, over a live core; the device is whatever
; books/assumptions-device.lisp's A-FENCE-PERSISTS admits; recovery is the
; real recovery row driven by fn2-turn over a fresh core reading a crash
; image. FN2-COMMIT-ACK-IMPLIES-DURABLE (the simulator run) is to become a
; tested instance of the statement here.
(in-package "ACL2")
(include-book "host-boundary")
(include-book "assumptions-device")
(include-book "owed")

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
(defun fn2-env-arg (i x)
  (declare (xargs :guard (natp i)))
  (if (true-listp x) (nth i x) nil))
(defun fn2-env-tag (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn2-env-pool-octets (n addr fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (natp n) (natp addr)) :measure (nfix n)))
  (if (or (zp n) (not (natp addr)) (>= addr (fn2-pool-data-length fn2-pool))) nil
    (cons (fn2-pool-datai addr fn2-pool) (fn2-env-pool-octets (- n 1) (+ 1 addr) fn2-pool))))
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

; The take entry of (SLOT GEN) in the newest-first LOG.
(defun fn2-env-taken (slot gen rlog)
  (declare (xargs :guard t))
  (cond ((atom rlog) nil)
        ((and (fn2-dev-takep (car rlog))
              (equal (nth 1 (car rlog)) slot) (equal (nth 2 (car rlog)) gen))
         (car rlog))
        (t (fn2-env-taken slot gen (cdr rlog)))))
(defthm fn2-env-taken-true-listp
  (true-listp (fn2-env-taken slot gen rlog))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn2-env-taken slot gen rlog)
           :in-theory '(fn2-env-taken fn2-dev-takep atom (:type-prescription true-listp)))))

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

; The run: (LOG ACKED). Genesis as the native host's (fn2-n-make-host).
; The wrappers' guards are not verified: their obligation is that the fresh
; core satisfies fn2-corep, which no rule of the core's defstobj states; the
; function each calls on the core is guard-verified.
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
(defun fn2-env-device-log (run)
  (declare (xargs :guard t))
  (fn2-env-arg 0 run))
(defun fn2-env-acknowledged-batches (run)
  (declare (xargs :guard t))
  (fn2-env-arg 1 run))

;; ---------------------------------------------------------------------------
;; RECOVERY: a fresh core (listeners :null, as B5's harness), the recovery
;; row started by the host (fn2-recovery-start) with the device assumption's
;; bits (crash-only, persistence fence), then RECOVERY-ACTIONS. The result
;; is (DONE CHAIN): DONE once the row has reached :done, CHAIN its chain
;; length then; the recovered batches are 1..CHAIN, the commits the chain
;; links from genesis.
(defconst *fn2-env-recovery-assume* 3)
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
(defun fn2-env-recovery-done-p (rec)
  (declare (xargs :guard t))
  (and (fn2-env-arg 0 rec) t))
(defun fn2-env-iota (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (append (fn2-env-iota (- n 1)) (list n))))
(defun fn2-env-recovered-batches (rec)
  (declare (xargs :guard t))
  (fn2-env-iota (nfix (fn2-env-arg 1 rec))))

; Every core profile is supported: a profile without commit rows acknowledges
; nothing and the statement holds of it trivially.
(defun fn2-profile-supportedp (profile)
  (declare (xargs :guard t))
  (fn2-core-profilep profile))

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
