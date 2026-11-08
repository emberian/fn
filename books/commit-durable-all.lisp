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
(include-book "commit-turn-frame")
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

; The fresh core a wrapper's with-local-stobj makes satisfies fn2-corep:
; each child's creator meets its recognizer (a column table's CREATE-<T>-TYPE,
; else the creator and recognizer opened).
(defun fn2-env-create-runes (children world)
  (declare (xargs :mode :program))
  (if (atom children) nil
    (let* ((type (cadar children)) (create (fn2-columns-pre "CREATE-" type))
           (lemma (fn2-columns-sym create "-TYPE")))
      (if (getpropc lemma 'theorem nil world)
          (cons lemma (fn2-env-create-runes (cdr children) world))
        (list* create (fn2-columns-sym type "P") (fn2-env-create-runes (cdr children) world))))))
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
(verify-guards fn2-env-recover)
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
(defun fn2-env-observe-rows (rows acked)
  (declare (xargs :verify-guards nil))
  (if (atom rows) acked
    (fn2-env-observe-rows
     (cdr rows)
     (let ((r (car rows)))
       (if (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r)))
           (add-to-set-equal (nth 3 r) acked)
         acked)))))
(defthm fn2-env-observe-is-rows
  (equal (fn2-env-observe ids acked fn2-core)
         (fn2-env-observe-rows (fn2-env-rows ids fn2-core) acked)))
(defun fn2-env-observed-p (rows acked)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (let ((r (car rows)))
      (and (or (not (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r))))
               (member-equal (nth 3 r) acked))
           (fn2-env-observed-p (cdr rows) acked)))))
(defthm fn2-env-observe-rows-observed
  (implies (fn2-env-observed-p rows acked)
           (equal (fn2-env-observe-rows rows acked) acked)))

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
;;  J1 a row whose reply count is positive, or at :publish or :notify, has a
;;     positive batch at or below the installed root; a row at :install has
;;     its batch durable in the log;
;;  J2 a row's dependency flag names a write of its role-0 unit answered done
;;     in full, its log flag the role-1 unit and the role-2 seal of its batch;
;;     each fenced once the fence flag is set (or FUA in barrier mode 1); the
;;     three roles share one extent;
;;  J4 the published root is at or below the installed one, and batches
;;     1..installed are durable in the log (publication follows predecessor
;;     publication: the root installs batch B only as published + 1).
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
; Entry W of LOG is a write the device answered done in full.
(defun fn2-env-done-write-p (w log)
  (declare (xargs :verify-guards nil))
  (and (natp w) (true-listp log) (< w (len log))
       (let ((e (nth w log)))
         (and (fn2-dev-take-writep e)
              (fn2-dev-done-answer-p (fn2-dev-answer (nth 1 e) (nth 2 e) (nthcdr (+ 1 w) log))
                                     *fn2-dev-write-result* (len (nth 6 e)))))))
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
    (and (implies (or ackedp (and rowp (member-equal phase (list *fn2-commit-state-publish*
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
         (fn2-env-prefix-durable-p (nth 1 root) log))))
(defun fn2-env-dur-inv (ids acked log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-inv ids acked log fn2-core)
       (fn2-env-j-rows ids log fn2-core)
       (fn2-env-j-frontier log fn2-core)))

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
(defun fn2-env-acks-bounded-p (rows n)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (let ((r (car rows)))
      (and (implies (and (eq (nth 0 r) :ok) (eq (nth 1 r) :ok) (posp (nth 2 r)))
                    (and (natp (nth 3 r)) (<= (nth 3 r) (nfix n))))
           (fn2-env-acks-bounded-p (cdr rows) n)))))
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
(defthm fn2-env-observed-p-mono
  (implies (and (fn2-env-observed-p rows a) (subsetp-equal a b))
           (fn2-env-observed-p rows b)))
(defthm fn2-env-subsetp-add-to-set-x
  (implies (subsetp-equal x acked) (subsetp-equal x (add-to-set-equal a acked))))
(defthm fn2-env-observe-rows-superset-gen
  (implies (subsetp-equal x acked) (subsetp-equal x (fn2-env-observe-rows rows acked)))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked) :in-theory (disable add-to-set-equal))))
(defthm fn2-env-member-observe-rows
  (implies (member-equal a acked) (member-equal a (fn2-env-observe-rows rows acked)))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked))))
(defthm fn2-env-member-add-to-set
  (member-equal a (add-to-set-equal a x)))
(defthm fn2-env-observe-rows-covers
  (fn2-env-observed-p rows (fn2-env-observe-rows rows acked))
  :hints (("Goal" :induct (fn2-env-observe-rows rows acked) :in-theory (disable add-to-set-equal))))
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

;; J ONLY GROWS WITH THE LOG, and the host steps leave every child J reads.
(local (defthm fn2-env-nthcdr-append
  (implies (<= (nfix n) (len x))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))
(local (defthm fn2-env-done-answer-append
  (implies (consp tail)
           (equal (fn2-dev-done-answer-p (append tail y) evkind count)
                  (fn2-dev-done-answer-p tail evkind count)))))
(local (defthm fn2-env-done-answer-nil (not (fn2-dev-done-answer-p nil evkind count))))
(defthm fn2-env-done-write-extends
  (implies (and (fn2-env-done-write-p w log) (true-listp more))
           (fn2-env-done-write-p w (append log more)))
  :hints (("Goal" :in-theory '(fn2-env-done-write-p fn2-env-nth-append-low fn2-env-nthcdr-append
                                fn2-env-done-answer-append fn2-dev-answer-append fn2-env-len-append
                                fn2-env-done-answer-nil natp nfix fix (:type-prescription true-listp-append) true-listp-append
                                (:type-prescription len) (:type-prescription fn2-dev-answer)
                                (:type-prescription binary-append))
           :cases ((consp (fn2-dev-answer (nth 1 (nth w log)) (nth 2 (nth w log)) (nthcdr (+ 1 w) log)))))))
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
(defthm fn2-env-j-rows-extends
  (implies (and (fn2-env-j-rows ids log fn2-core) (true-listp more))
           (fn2-env-j-rows ids (append log more) fn2-core))
  :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core)
           :in-theory '(fn2-env-j-rows fn2-env-j-row fn2-env-j1-row fn2-env-j2-row fn2-env-written-extends fn2-env-batch-durable-extends))))
(defthm fn2-env-j-frontier-extends
  (implies (and (fn2-env-j-frontier log fn2-core) (true-listp more))
           (fn2-env-j-frontier (append log more) fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-j-frontier fn2-env-prefix-durable-extends))))
;; the readers J uses, past the host steps' children (ops, pool, extents)
(defun fn2-env-j-reader-frame-1 (fn args updates)
  (declare (xargs :mode :program))
  (if (atom updates) nil
    (cons `(defthm ,(fn2-columns-sym fn (concatenate 'string "-OF-" (symbol-name (car updates))))
             (equal (,fn ,@args (,(car updates) x fn2-core)) (,fn ,@args fn2-core))
             :hints (("Goal" :in-theory (enable ,fn))))
          (fn2-env-j-reader-frame-1 fn args (cdr updates)))))
(defun fn2-env-j-reader-frame-events (readers updates)
  (declare (xargs :mode :program))
  (if (atom readers) nil
    (append (fn2-env-j-reader-frame-1 (caar readers) (cdar readers) updates)
            (fn2-env-j-reader-frame-events (cdr readers) updates))))
(make-event
 (value (cons 'progn
   (fn2-env-j-reader-frame-events
    '((fn2-machine-idp id) (fn2-machine-kind id) (fn2-machine-slot id) (fn2-machine-phase id) (fn2-machine-batch-no id) (fn2-machine-cb-acks id)
      (fn2-machine-cb-acks-read-code id) (fn2-machine-batch-no-read-code id)
      (fn2-machine-cb-fence-ok id) (fn2-machine-cb-mode id) (fn2-machine-cb-deps-ok id)
      (fn2-machine-cb-log-ok id) (fn2-commit-idp id) (fn2-commit-row id) (fn2-commit-resource id role) (fn2-env-root))
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
(defthm fn2-env-j-child-frame
  (and (equal (fn2-env-j-rows ids log (update-fn2-core-ops x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (update-fn2-core-pool x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-rows ids log (update-fn2-core-extents x fn2-core)) (fn2-env-j-rows ids log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-ops x fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-pool x fn2-core)) (fn2-env-j-frontier log fn2-core))
       (equal (fn2-env-j-frontier log (update-fn2-core-extents x fn2-core)) (fn2-env-j-frontier log fn2-core)))
  :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core)
           :in-theory '(fn2-env-j-rows fn2-env-j-frontier fn2-env-j-row-child-frame))))
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
(defthm fn2-env-dur-inv-host-step
  (implies (and (fn2-env-dur-inv ids acked log fn2-core)
                (not (member-eq (fn2-env-tag action) '(:turn :admit))))
           (mv-let (entry after) (fn2-env-step action nil image rlog fn2-core)
             (fn2-env-dur-inv ids (fn2-env-observe ids acked after)
                              (append log (if entry (list entry) nil)) after)))
  :hints (("Goal" :in-theory (e/d (fn2-env-dur-inv)
                                  (fn2-env-inv fn2-env-j-rows fn2-env-j-frontier fn2-env-observe fn2-env-step))
           :use ((:instance fn2-env-inv-host-step)
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

;; :ADMIT. The admission adds no reply a commit row did not show before:
;; fn2-env-no-new-acks-p of the rows after against the rows before, so
;; OBSERVED carries over and DURABLE is untouched (the admission logs
;; nothing). Each sub-operation's arm-frames contract (books/machines.lisp,
;; derived under the commit kind) bounds what it changes; one bridge lemma
;; turns a contract that leaves the directory, the commit table's rows and
;; its cb-acks and batch-no columns alone into the relation, and the row
;; write of fn2-commit-start, which writes both columns, leaves cb-acks 0
;; by its write contract's read-back.
(defun fn2-env-no-new-acks-p (post pre)
  (declare (xargs :verify-guards nil))
  (if (atom post) t
    (and (or (equal (car post) (car pre)) (not (posp (nth 2 (car post)))))
         (fn2-env-no-new-acks-p (cdr post) (cdr pre)))))
(defthm fn2-env-observed-no-new-acks
  (implies (and (fn2-env-observed-p pre acked) (fn2-env-no-new-acks-p post pre))
           (fn2-env-observed-p post acked)))
(defthm fn2-env-no-new-acks-refl (fn2-env-no-new-acks-p x x))
(defthm fn2-env-no-new-acks-trans
  (implies (and (fn2-env-no-new-acks-p c b) (fn2-env-no-new-acks-p b a) (equal (len c) (len b)))
           (fn2-env-no-new-acks-p c a)))
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
(defthm fn2-env-nth-off-update-nth
  (implies (and (equal (update-nth r nil x) (update-nth r nil y)) (not (equal (nfix s) (nfix r))))
           (equal (nth s x) (nth s y)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance nth-update-nth (m s) (n r) (val nil) (l x))
                        (:instance nth-update-nth (m s) (n r) (val nil) (l y)))
           :in-theory (disable nth-update-nth))))
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
(make-event
 (value (cons 'progn (fn2-arm-frame-fns-forms
                      '(fn2-commit-save-pool fn2-commit-keep-pool fn2-commit-unwind-pool fn2-core-reserve
                        fn2-commit-reserve-pools fn2-commit-reserve-extent fn2-commit-release-pools
                        fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake)
                      'fn2-commit))))
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

; The row write of fn2-commit-start writes cb-acks and batch-no at its row.
; Accepted, its contract's read-back leaves cb-acks 0 there; refused, it
; changes neither the directory nor the commit table.
(defthm fn2-env-cols-nth-in
  (implies (and (fn2-arm-cols k row columns a b) (natp k) (natp j) (member-equal (+ k j) columns))
           (equal (update-nth row nil (nth j a)) (update-nth row nil (nth j b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-arm-kids-nth-induct k j a b) :in-theory (enable nth fn2-arm-cols))))
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
(defun fn2-env-row-read-events (fields)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((f (caar fields)) (j (cdar fields))
           (r (fn2-columns-col-name 'fn2-machine f))
           (tr (fn2-columns-col-name 'fn2-commit f)) (ai (fn2-columns-sym tr "$AI")))
      (cons
       `(defthm ,(fn2-columns-sym r "-OF-ROW-FRAME")
          (implies (and (fn2-arm-row-frame 9 row cs ch a b) (not (member-equal 9 ch)) (natp row)
                        (not (member-equal 33 cs)) (fn2-ctf-dir b a)
                        (equal (fn2-machine-kind id a) *fn2-commit-kind*)
                        (or (not (member-equal ,j cs)) (not (equal (fn2-machine-slot id a) row))))
                   (equal (,r id b) (,r id a)))
          :rule-classes nil
          :hints (("Goal" :in-theory (e/d (,r fn2-commit-table fn2-commit-rows ,tr ,ai)
                                          (fn2-machine-kind fn2-machine-slot fn2-machine-idp nth update-nth
                                           fn2-arm-row-frame fn2-ctf-dir))
                   :cases ((member-equal ,j cs))
                   :do-not-induct t
                   :use ((:instance fn2-ctf-dir-readers)
                         (:instance fn2-arm-row-frame-cols (table 9) (columns cs) (children ch))
                         (:instance fn2-arm-cols-nth (k 0) (j 33) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-arm-cols-nth (k 0) (j ,j) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-env-cols-nth-in (k 0) (j ,j) (row row) (columns cs) (a (nth 9 a)) (b (nth 9 b)))
                         (:instance fn2-env-nth-off-update-nth (r row) (s (fn2-machine-slot id a))
                                    (x (nth ,j (nth 9 a))) (y (nth ,j (nth 9 b))))))))
       (fn2-env-row-read-events (cdr fields))))))
(make-event (value (cons 'progn (fn2-env-row-read-events
  '((phase . 0) (batch-no . 9) (cb-mode . 13) (cb-fence-ok . 23) (cb-deps-ok . 24) (cb-log-ok . 25) (cb-acks . 27))))))
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
(defthm fn2-env-row-frame-child
  (implies (and (fn2-arm-row-frame tb row cs ch a b) (natp k) (not (equal k tb)) (not (member-equal k ch)))
           (equal (nth k b) (nth k a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-arm-row-frame) (nth))
           :use ((:instance fn2-arm-kids-nth (i 0) (free (cons tb ch)))))))
(defthm fn2-env-j-row-of-row-frame
  (implies (and (fn2-env-j-row id log a) (fn2-env-j-frontier log a)
                (fn2-corep b) (fn2-core-wfp b)
                (fn2-arm-row-frame 9 row cs ch a b) (natp row)
                (not (member-equal 9 ch)) (not (member-equal 30 ch)) (not (member-equal 31 ch))
                (not (member-equal 33 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs))
                (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs))
                (fn2-ctf-dir b a)
                (or (not (equal (fn2-machine-slot id a) row))
                    (and (not (member-equal 0 cs)) (not (member-equal 27 cs)))
                    (and (posp (fn2-machine-batch-no id a))
                         (<= (fn2-machine-batch-no id a) (fn2-env-installed a)))))
           (and (fn2-env-j-row id log b) (fn2-env-j-frontier log b)
                (equal (fn2-env-installed b) (fn2-env-installed a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-role-extent fn2-env-installed fn2-env-j-frontier
                                               fn2-arm-row-frame natp member-equal)
                                             (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind id a) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers)
                 (:instance fn2-env-j-row-off-kind (fn2-core b))
                 (:instance fn2-env-row-frame-child (tb 9) (k 30))
                 (:instance fn2-env-row-frame-child (tb 9) (k 31))
                 (:instance fn2-env-root-congruence)
                 (:instance fn2-env-read-codes-of-row-frame)
                 (:instance fn2-env-child-congruences (role 0))
                 (:instance fn2-env-child-congruences (role 1))
                 (:instance fn2-env-child-congruences (role 2))
                 (:instance fn2-machine-phase-of-row-frame)
                 (:instance fn2-machine-batch-no-of-row-frame)
                 (:instance fn2-machine-cb-mode-of-row-frame)
                 (:instance fn2-machine-cb-fence-ok-of-row-frame)
                 (:instance fn2-machine-cb-deps-ok-of-row-frame)
                 (:instance fn2-machine-cb-log-ok-of-row-frame)
                 (:instance fn2-machine-cb-acks-of-row-frame)
                 (:instance fn2-env-j-row-transfer)))))

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
(defmacro fn2-env-turn-instance ()
  '(defthm fn2-env-turn-preserves
     (implies (and (fn2-env-turn-inv g fn2-core)
                   (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
              (fn2-env-turn-inv g (mv-nth 4 (fn2-turn fn2-core))))
     :hints (("Goal"
              :use ((:functional-instance fn2-executor-inv-turn
                      (fn2-executor-inv fn2-env-turn-inv)
                      (fn2-executor-rel fn2-env-turn-rel)))
              :in-theory (disable fn2-corep fn2-core-wfp fn2-turn
                           fn2-env-inv fn2-env-observe fn2-env-observe-is-rows fn2-env-rows
                           fn2-env-observed-p fn2-env-acked-durable-p)
              :do-not-induct t))))
(defthm fn2-env-turn-inv-entry
  (implies (fn2-env-inv ids acked log fn2-core)
           (fn2-env-turn-inv (list ids acked log) fn2-core))
  :hints (("Goal" :in-theory (disable fn2-env-rows fn2-env-observed-p
                                      fn2-env-observe-rows fn2-env-acked-durable-p))))
(defun-nx fn2-env-dur-turn-inv (g c)
  ; the turn's predicate: J's rows and frontier at the fixed log (nth 2 g),
  ; the ghost acknowledged set (nth 1 g) durable in it
  (and (fn2-env-j-rows (nth 0 g) (nth 2 g) c)
       (fn2-env-j-frontier (nth 2 g) c)
       (fn2-env-acked-durable-p (nth 1 g) (nth 2 g))))
(defthm fn2-env-dur-turn-inv-projection
  (implies (fn2-env-dur-turn-inv g c) (fn2-env-turn-inv g c))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-turn-inv fn2-env-inv)
                                  (fn2-env-j-rows fn2-env-j-frontier fn2-env-installed fn2-env-rows
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
  :hints (("Goal" :in-theory (disable fn2-env-j-rows fn2-env-j-frontier fn2-env-rows fn2-env-observed-p
                                      fn2-env-acked-durable-p))))
; The turn's half, to be proved by FN2-EXECUTOR-INSTANTIATE with predicate
; FN2-ENV-DUR-TURN-INV and relation "every cut preserves it" (not a new turn
; induction). With FN2-ENV-DUR-TURN-INV-PROJECTION it gives the :turn step of
; FN2-ENV-DUR-INV, and with FN2-ENV-DUR-INV-HOST-STEP the run's invariant.
(defthm-owed fn2-env-dur-turn-preserves (g fn2-core)
  (implies (and (fn2-env-dur-turn-inv g fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-env-dur-turn-inv g (mv-nth 4 (fn2-turn fn2-core))))
  :schema :invariant :from (:machine fn2-commit)
  :teeth (fn2-dur-turn-positive fn2-dur-turn-j-removal)
  :doc "fn2-turn preserves J1-J4 (FN2-ENV-J-ROWS, FN2-ENV-J-FRONTIER) at a fixed device log, so that every batch a commit row shows acknowledged stays durable (FN2-ENV-DUR-TURN-INV-PROJECTION). The executor-level lift FN2-EXECUTOR-INV-TURN reduces it to one obligation per cut in *FN2-EXECUTOR-CONTRACT-CUTS*. Owed, by owner: (1) cross-kind: every non-commit cut (the other kinds' -RUN / -RUN-STUB and observe routes, the wait-source grants, fn2-member-replay; *FN2-COMMIT-TURN-FRAME-BLOCKERS*) must leave the directory's kinds and slots, the commit table, the commit root and the commit-io table, which needs their KIDS/DIR constraints (dispatch-contracts, handler-frames); (2) commit-internal: the arms that raise J's flags or root fields: :dependencies/:log-write (deps-ok/log-ok from the counted write results), the write/fence handler (cb-done, fence-ok), which need J3 (each counted completion is the first done answer in the log to a take of the row's role write at its offset carrying its loan's bytes, the seal of its batch for role 2); :durable to :install (FN2-ENV-J-ROW-DURABLE-FLAGS), :install and :publish (root-swap installs only published + 1, publishes only installed), :notify (FN2-COMMIT-RUN-NOTIFY-PHASE-WRITES: a reply only at :notify, batch at or below installed by J1).")
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
(defun fn2-env-image-holds-write-p (e image)
  (declare (xargs :verify-guards nil))
  (equal (fn2-dev-image-octets image (nfix (nth 4 e)) (len (nth 6 e))) (true-list-fix (nth 6 e))))
; Some fenced write at OFFSET in LOG from W whose octets IMAGE holds.
(defun fn2-env-held-offset-from (w offset log image)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-dev-fenced-write-p fn2-env-image-holds-write-p)))))
  (cond ((not (and (natp w) (true-listp log) (< w (len log)))) nil)
        ((and (fn2-dev-fenced-write-p w log) (equal (nth 4 (nth w log)) offset)
              (fn2-env-image-holds-write-p (nth w log) image))
         t)
        (t (fn2-env-held-offset-from (+ 1 w) offset log image))))
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
