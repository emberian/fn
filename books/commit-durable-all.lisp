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
  ; (VALID GEN PHASE KIND OKIND OSLOT OGEN RSLOT RGEN ROFF RLEN OFFSET FUA C0P C0H C0E C0O C0C)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (r)
    (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
        (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
              (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
              (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
              (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
              (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
              (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
              (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops))
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
; The index of the first take of (SLOT GEN) in the oldest-first LOG.
(defun fn2-env-take-index (slot gen log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (fn2-dev-takep (car log)) (equal (nth 1 (car log)) slot) (equal (nth 2 (car log)) gen)) 0)
        (t (let ((w (fn2-env-take-index slot gen (cdr log)))) (and w (+ 1 w))))))
; The op's take is in LOG iff it left the outbox; its first answer is the
; posted terminal cell iff one is posted.
(defun fn2-env-j5-taken (op slot log)
  (declare (xargs :verify-guards nil))
  (let ((gen (nth 1 op)) (phase (nth 2 op)))
    (if (equal phase *fn2-op-phase-queued*)
        (and (not (fn2-env-take-index slot gen log)) (equal (nth 13 op) 0))
      (let ((w (fn2-env-take-index slot gen log)))
        (and (equal phase *fn2-op-phase-submitted*) (natp w)
             (let ((ans (fn2-dev-answer slot gen (nthcdr (+ 1 w) log))))
               (if (equal (nth 13 op) 1)
                   (and (equal (nth 14 op) 0) (consp ans)
                        (equal (nth 3 (car ans)) (nth 15 op)) (equal (nth 4 (car ans)) (nth 16 op))
                        (equal (nth 5 (car ans)) (nth 17 op)))
                 (not ans))))))))
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
             (fn2-env-j5-taken op slot log)
             (let ((w (fn2-env-take-index slot (nth 1 op) log)))
               (if w (fn2-env-j5-take-ok (nth w log) offset fua b) t)))
      (fn2-env-role-written id role (or (equal (fn2-machine-cb-fence-ok id fn2-core) 1)
                                         (and (equal phase *fn2-commit-state-log-write*) (equal mode 1)))
                            log fn2-core))))
(defun fn2-env-b2n (x) (declare (xargs :guard t)) (if x 1 0))
; The issued roles of a write phase: (FIRST . COUNT).
(defun fn2-env-j5-roles (id log fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((phase (fn2-machine-phase id fn2-core)) (issued (fn2-machine-cb-issued id fn2-core))
        (done (fn2-machine-cb-done id fn2-core)))
    (cond ((equal phase *fn2-commit-state-dependencies*)
           (and (natp issued) (<= issued 1) (natp done)
                (implies (equal issued 1) (fn2-env-j5-role id 0 log fn2-core))
                (equal (+ done (if (equal issued 1) (fn2-env-b2n (fn2-env-role-live id 0 fn2-core)) 0)) issued)))
          ((equal phase *fn2-commit-state-log-write*)
           (and (natp issued) (<= issued 2) (natp done)
                (implies (<= 1 issued) (fn2-env-j5-role id 1 log fn2-core))
                (implies (<= 2 issued) (fn2-env-j5-role id 2 log fn2-core))
                (equal (+ done (if (<= 1 issued) (fn2-env-b2n (fn2-env-role-live id 1 fn2-core)) 0)
                          (if (<= 2 issued) (fn2-env-b2n (fn2-env-role-live id 2 fn2-core)) 0))
                       issued)))
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
                                   (t nil))))))))
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
(local (defthm fn2-env-consp-append (implies (consp x) (consp (append x y)))))
(local (defthm fn2-env-done-answer-append
  (implies (consp tail)
           (equal (fn2-dev-done-answer-p (append tail y) evkind count)
                  (fn2-dev-done-answer-p tail evkind count)))
  :hints (("Goal" :in-theory '(fn2-dev-done-answer-p car-cons fn2-env-consp-append) :expand ((append tail y))))))
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
(defthm fn2-env-j3-rows-extends
  (implies (and (fn2-env-j3-rows ids log fn2-core) (true-listp more))
           (fn2-env-j3-rows ids (append log more) fn2-core))
  :hints (("Goal" :induct (fn2-env-j3-rows ids log fn2-core)
           :in-theory '(fn2-env-j3-rows fn2-env-j3-row fn2-env-role-written fn2-env-written-extends))))
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
(defthm fn2-env-j3-child-frame
  (and (equal (fn2-env-j3-rows ids log (update-fn2-core-ops x fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (update-fn2-core-pool x fn2-core)) (fn2-env-j3-rows ids log fn2-core))
       (equal (fn2-env-j3-rows ids log (update-fn2-core-extents x fn2-core)) (fn2-env-j3-rows ids log fn2-core)))
  :hints (("Goal" :induct (fn2-env-j3-rows ids log fn2-core)
           :in-theory '(fn2-env-j3-rows fn2-env-j3-row-child-frame))))
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
(defthm fn2-env-row-frame-child
  (implies (and (fn2-arm-row-frame tb row cs ch a b) (natp k) (not (equal k tb)) (not (member-equal k ch)))
           (equal (nth k b) (nth k a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-arm-row-frame) (nth))
           :use ((:instance fn2-arm-kids-nth (i 0) (free (cons tb ch)))))))
;; KEPT EVIDENCE. J2 reads a row's role extents (commit-io's extent column
;; and row count, FN2-ENV-EK) and J4 the root triple (FN2-ENV-RK); arms that
;; write commit-io's other columns or the root's other fields keep them.
(defun-nx fn2-env-ek (b a)
  (and (equal (nth *fn2-commit-io-extent$ai* (nth 30 b)) (nth *fn2-commit-io-extent$ai* (nth 30 a)))
       (equal (nth *fn2-commit-io-rows* (nth 30 b)) (nth *fn2-commit-io-rows* (nth 30 a)))))
(defun-nx fn2-env-rk (b a) (equal (fn2-env-root b) (fn2-env-root a)))
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
(defun fn2-env-ek-col-events (cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-io (car cols)) "$AI"))))
      (cons `(defthm ,(fn2-columns-sym (fn2-columns-pre "FN2-ENV-EK-OF-" upd) "")
               (equal (fn2-env-ek (update-fn2-core-commit-io (,upd i v io) y) a)
                      (fn2-env-ek (update-fn2-core-commit-io io y) a))
               :hints (("Goal" :in-theory (enable fn2-env-ek update-fn2-core-commit-io ,upd update-nth-array))))
            (fn2-env-ek-col-events (cdr cols))))))
(make-event (value (cons 'progn (fn2-env-ek-col-events '(epoch counter pool-slot pool-gen op-slot op-gen ready lent)))))
(defconst *fn2-env-ek-runes*
  '(fn2-env-ek-of-update-same fn2-env-ek-refl
    fn2-env-ek-of-update-fn2-commit-io-epoch$ai fn2-env-ek-of-update-fn2-commit-io-counter$ai
    fn2-env-ek-of-update-fn2-commit-io-pool-slot$ai fn2-env-ek-of-update-fn2-commit-io-pool-gen$ai
    fn2-env-ek-of-update-fn2-commit-io-op-slot$ai fn2-env-ek-of-update-fn2-commit-io-op-gen$ai
    fn2-env-ek-of-update-fn2-commit-io-ready$ai fn2-env-ek-of-update-fn2-commit-io-lent$ai
    fn2-commit-io-set-counter fn2-commit-io-set-epoch fn2-commit-io-set-lent fn2-commit-io-set-op-gen
    fn2-commit-io-set-op-slot fn2-commit-io-set-pool-gen fn2-commit-io-set-pool-slot fn2-commit-io-set-ready))
(defthm fn2-env-rk-of-update-same
  (equal (fn2-env-rk (update-fn2-core-commit-root (fn2-core-commit-root x) y) a) (fn2-env-rk x a))
  :hints (("Goal" :in-theory (enable fn2-env-rk fn2-env-root update-fn2-core-commit-root fn2-core-commit-root))))
(defun fn2-env-rk-col-events (cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let ((upd (fn2-columns-pre "UPDATE-" (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-root (car cols)) "$AI"))))
      (cons `(defthm ,(fn2-columns-sym (fn2-columns-pre "FN2-ENV-RK-OF-" upd) "")
               (equal (fn2-env-rk (update-fn2-core-commit-root (,upd i v r) y) a)
                      (fn2-env-rk (update-fn2-core-commit-root r y) a))
               :hints (("Goal" :in-theory (enable fn2-env-rk fn2-env-root update-fn2-core-commit-root fn2-core-commit-root
                                                  ,upd update-nth-array fn2-commit-root-rows fn2-commit-root-installed
                                                  fn2-commit-root-published fn2-commit-root-installed$ai fn2-commit-root-published$ai))))
            (fn2-env-rk-col-events (cdr cols))))))
(make-event (value (cons 'progn (fn2-env-rk-col-events '(parent extent first-key members proposed abort-event aborting barrier-mode seal-ready)))))
(defconst *fn2-env-rk-runes*
  '(fn2-env-rk-of-update-same fn2-env-rk-refl
    fn2-env-rk-of-update-fn2-commit-root-parent$ai fn2-env-rk-of-update-fn2-commit-root-extent$ai
    fn2-env-rk-of-update-fn2-commit-root-first-key$ai fn2-env-rk-of-update-fn2-commit-root-members$ai
    fn2-env-rk-of-update-fn2-commit-root-proposed$ai fn2-env-rk-of-update-fn2-commit-root-abort-event$ai
    fn2-env-rk-of-update-fn2-commit-root-aborting$ai fn2-env-rk-of-update-fn2-commit-root-barrier-mode$ai
    fn2-env-rk-of-update-fn2-commit-root-seal-ready$ai
    fn2-commit-root-set-abort-event fn2-commit-root-set-aborting fn2-commit-root-set-barrier-mode
    fn2-commit-root-set-extent fn2-commit-root-set-first-key fn2-commit-root-set-members fn2-commit-root-set-parent
    fn2-commit-root-set-proposed fn2-commit-root-set-seal-ready))
(defun fn2-env-rel-name (fn rel) (declare (xargs :mode :program)) (fn2-columns-sym fn (concatenate 'string "-" (symbol-name rel))))
(defun fn2-env-rel-callee-runes (callees rel world)
  (declare (xargs :mode :program))
  (cond ((atom callees) nil)
        ((getpropc (fn2-env-rel-name (car callees) rel) 'theorem nil world)
         (cons (fn2-env-rel-name (car callees) rel) (fn2-env-rel-callee-runes (cdr callees) rel world)))
        (t (fn2-env-rel-callee-runes (cdr callees) rel world))))
; FN2-ENV-REL-COLS: a relation's commit-table columns, for a relation that
; reads the table (FN2-ENV-TK); a writer of the table at one row whose
; columns miss them keeps it by its row frame and REL-OF-ROW-FRAME.
(table fn2-env-rel-cols 'fn2-env-tk '(0 9 13 17 23 24 25 27 33))
(defun fn2-env-rel-nth-uses (ks fn out tk ch row cs)
  ; for each child K of KS, the frame's equality at K
  (declare (xargs :mode :program))
  (if (atom ks) nil
    (cons (if (eq fn :arm)
              `(:instance fn2-env-row-frame-child (tb ,tk) (k ,(car ks)) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,out))
            `(:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',ch) (a fn2-core) (b ,out)))
          (fn2-env-rel-nth-uses (cdr ks) fn out tk ch row cs))))
(defun fn2-env-rel-event (fn rel k runes kind world)
  ; FN-<REL>: (REL c c0) carries over FN, REL reading the core children K
  ; (an index or a list): by its contract when its children exclude K, by
  ; its row frame when it writes REL's table (FN2-ENV-REL-COLS) at one row
  ; outside REL's columns, by the updater's rule for K's updater, else by
  ; one opening with its callees' facts and RUNES
  (declare (xargs :mode :program))
  (let* ((ks (if (integerp k) (list k) k))
         (e (fn2-arm-frame-known fn kind world))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (name (fn2-env-rel-name fn rel))
         (of-nth (fn2-columns-sym rel "-OF-NTH"))
         (tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world))
         (rcols (cdr (assoc-eq rel (table-alist 'fn2-env-rel-cols world))))
         (row '(fn2-machine-slot id fn2-core))
         (stmt `(implies (,rel fn2-core fn2-rel-c0) (,rel ,out fn2-rel-c0))))
    (cond
     ((getpropc name 'theorem nil world) nil)
     ((eq (car e) :child)
      (if (member (cadr e) ks) nil
        `((defthm ,name ,stmt :hints (("Goal" :use ((:instance ,of-nth (b ,out) (x fn2-core) (a fn2-rel-c0)))
                                       :in-theory (enable ,fn)))))))
     ((and (eq (car e) :arm) (not (intersectp ks (cons tk (cadr e)))))
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (union-theories '((:type-prescription fn2-machine-slot-natp)) (theory 'fn2-arm-frame-base))
                   :use ((:instance ,(fn2-arm-frame-name fn "-ARM-ROW-FRAME") (fn2-arm-tb ,tk) (fn2-arm-row ,row)
                                    (fn2-arm-cs ',(caddr e)) (fn2-arm-ch ',(cadr e)) (fn2-arm-c0 fn2-core))
                         (:instance fn2-arm-row-frame-refl (table ,tk) (row ,row)
                                    (columns ',(caddr e)) (children ',(cadr e)) (a fn2-core))
                         ,@(fn2-env-rel-nth-uses ks :arm out tk (cadr e) row (caddr e))
                         (:instance ,of-nth (b ,out) (x fn2-core) (a fn2-rel-c0))))))))
     ((and (member-eq (car e) '(:op :row :write)) (not (intersectp ks (fn2-arm-frame-entry-kids e world))))
      (let ((s (fn2-arm-frame-entry-kids e world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world) (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                           ,@(fn2-env-rel-nth-uses ks :kids out tk s row nil)
                           (:instance ,of-nth (b ,out) (x fn2-core) (a fn2-rel-c0)))))))))
     ((and rcols (member-eq (car e) '(:arm :row :write))
           (equal (if (eq (car e) :arm) tk (fn2-arm-frame-entry-tk e world)) tk)
           (not (intersectp-equal (if (eq (car e) :arm) (caddr e) (fn2-arm-frame-entry-j e)) rcols))
           (not (intersectp ks (if (eq (car e) :arm) (cadr e) (fn2-arm-frame-entry-s e)))))
      (let ((ch (if (eq (car e) :arm) (cadr e) (fn2-arm-frame-entry-s e)))
            (cs (if (eq (car e) :arm) (caddr e) (fn2-arm-frame-entry-j e))))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (union-theories '((:type-prescription fn2-machine-slot-natp)) (theory 'fn2-arm-frame-base))
                     :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-ROW-FRAME" kind world) (fn2-arm-tb ,tk) (fn2-arm-row ,row)
                                      (fn2-arm-cs ',cs) (fn2-arm-ch ',ch) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-row-frame-refl (table ,tk) (row ,row) (columns ',cs) (children ',ch) (a fn2-core))
                           (:instance ,(fn2-columns-sym rel "-OF-ROW-FRAME") (row ,row) (cs ',cs) (ch ',ch)
                                      (x fn2-core) (b ,out) (a fn2-rel-c0)))))))))
     (t
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (union-theories
                                      '(,fn ,@runes ,@(fn2-env-rel-callee-runes (fn2-arm-frame-body-callees fn world) rel world))
                                      (theory 'fn2-arm-frame-base))
                   :do-not-induct t))))))))
(defun fn2-env-rel-forms (fns rel k runes kind)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (cons 'progn (fn2-env-rel-event ',(car fns) ',rel ',k ',runes ',kind (w state)))))
          (fn2-env-rel-forms (cdr fns) rel k runes kind))))
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
;; The frame of the visit at PHASE, from the arm's declaration; the
;; commit-io (30) and root (31) children are kept when the arm does not
;; declare them, and then the frontier and the installed root stay.
(defun fn2-env-arm-state-const (state-name)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string "*FN2-COMMIT-STATE-" (symbol-name state-name) "*") 'fn2-core))
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
;; Each per-id lift FN2-ENV-J-ROW-<PHASE>-ARM, lifted over the id list.
(defun fn2-env-arm-rows-events (state-name extra)
  (declare (xargs :mode :program))
  (let* ((const (fn2-env-arm-state-const state-name))
         (row (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-row state-name) "-ARM"))
         (rw (fn2-columns-sym row "-REWRITE"))
         (hyps `(,@extra (fn2-env-j-frontier log fn2-core) (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (equal (fn2-commit-row-phase id fn2-core) ,const))))
    `((defthm ,rw
        (implies (and (fn2-env-j-row i log fn2-core) ,@hyps)
                 (fn2-env-j-row i log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
        :hints (("Goal" :in-theory nil :use ((:instance ,row)))))
      (defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-rows state-name) "-ARM")
        (implies (and (fn2-env-j-rows ids log fn2-core) ,@hyps)
                 (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core))))
        :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core) :in-theory '(fn2-env-j-rows ,rw))))
      (in-theory (disable ,rw)))))
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
;; so commit-io stays (FN2-ENV-COMMIT-RUN-DURABLE-KEEPS-COMMIT-IO, by the
;; generator FN2-ENV-KEEP-FORMS: a callee's contract when its children
;; exclude the child, else one opening with its callees' facts).
(defun fn2-env-keep-name (fn suffix) (declare (xargs :mode :program)) (fn2-columns-sym fn suffix))
(defun fn2-env-keep-callee-runes (callees suffix world)
  (declare (xargs :mode :program))
  (cond ((atom callees) nil)
        ((getpropc (fn2-env-keep-name (car callees) suffix) 'theorem nil world)
         (cons (fn2-env-keep-name (car callees) suffix) (fn2-env-keep-callee-runes (cdr callees) suffix world)))
        (t (fn2-env-keep-callee-runes (cdr callees) suffix world))))
(defun fn2-env-keep-event (fn k suffix kind world)
  ; FN-<SUFFIX>: FN leaves core child K: by its contract when its children
  ; exclude K, else by one opening with its callees' facts
  (declare (xargs :mode :program))
  (let* ((e (fn2-arm-frame-known fn kind world))
         (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world))
         (name (fn2-env-keep-name fn suffix))
         (stmt `(equal (nth ,k ,out) (nth ,k fn2-core))))
    (cond
     ((getpropc name 'theorem nil world) nil)
     ((eq (car e) :child)
      (if (equal (cadr e) k) (er hard 'fn2-env-keep-event "~x0 updates child ~x1." fn k)
        `((defthm ,name ,stmt :hints (("Goal" :in-theory (enable ,fn)))))))
     ((and (eq (car e) :arm) (not (member k (cadr e))))
      (let ((tk (fn2-arm-frame-child-index (fn2-columns-sym kind "-TABLE") world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (union-theories '((:type-prescription fn2-machine-slot-natp)) (theory 'fn2-arm-frame-base))
                     :use ((:instance ,(fn2-arm-frame-name fn "-ARM-ROW-FRAME") (fn2-arm-tb ,tk) (fn2-arm-row (fn2-machine-slot id fn2-core))
                                      (fn2-arm-cs ',(caddr e)) (fn2-arm-ch ',(cadr e)) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-row-frame-refl (table ,tk) (row (fn2-machine-slot id fn2-core))
                                      (columns ',(caddr e)) (children ',(cadr e)) (a fn2-core))
                           (:instance fn2-env-row-frame-child (tb ,tk) (k ,k) (row (fn2-machine-slot id fn2-core))
                                      (cs ',(caddr e)) (ch ',(cadr e)) (a fn2-core) (b ,out)))))))))
     ((and (member-eq (car e) '(:op :row :write)) (not (member k (fn2-arm-frame-entry-kids e world))))
      (let ((s (fn2-arm-frame-entry-kids e world)))
        `((defthm ,name ,stmt
            :hints (("Goal" :in-theory (theory 'fn2-arm-frame-base)
                     :use ((:instance ,(fn2-arm-frame-lemma fn e "-ARM-KIDS" kind world) (fn2-arm-free ',s) (fn2-arm-c0 fn2-core))
                           (:instance fn2-arm-kids-nth (i 0) (k ,k) (free ',s) (a fn2-core) (b ,out)))))))))
     (t
      `((defthm ,name ,stmt
          :hints (("Goal" :in-theory (union-theories
                                      '(,fn ,@(fn2-env-keep-callee-runes (fn2-arm-frame-body-callees fn world) suffix world))
                                      (theory 'fn2-arm-frame-base))
                   :do-not-induct t))))))))
(defun fn2-env-keep-forms (fns k suffix kind)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (cons 'progn (fn2-env-keep-event ',(car fns) ,k ,suffix ',kind (w state)))))
          (fn2-env-keep-forms (cdr fns) k suffix kind))))
(make-event
 (value (cons 'progn (fn2-env-keep-forms (fn2-ctf-postorder-new '(fn2-commit-run-durable fn2-machine-contract-check fn2-machine-refuse-phase) (w state))
                                         30 "-KEEPS-COMMIT-IO" 'fn2-commit))))
(defthm fn2-env-commit-run-durable-keeps-commit-io
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-durable*)
           (equal (nth 30 (mv-nth 4 (fn2-commit-run id budget fn2-core))) (nth 30 fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit-run-durable-keeps-commit-io
                                               fn2-machine-contract-check-keeps-commit-io fn2-core-stop-keeps-commit-io)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
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
;; batch; every other callee of the two arms keeps the root (generator
;; FN2-ENV-KEEP-FORMS at child 31).  So the visit at :install keeps J4 (the
;; batch is durable by J1 at :install) and does not lower the installed root,
;; and reaches :publish only by its install (FN2-ENV-COMMIT-RUN-INSTALL-FACTS);
;; the visit at :publish keeps the installed root.  Both read J at the
;; visited id itself (its batch's durability, its positive batch number).
(make-event
 (value (cons 'progn (fn2-env-keep-forms (fn2-ctf-postorder-new '(fn2-commit-root-edge fn2-core-stop fn2-commit-write+phase fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason fn2-machine-contract-check fn2-machine-refuse-phase) (w state))
                                         31 "-KEEPS-COMMIT-ROOT" 'fn2-commit))))
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
  :hints (("Goal" :in-theory (e/d (fn2-commit-root-swap fn2-env-root fn2-core-stop-keeps-commit-root update-fn2-core-commit-root fn2-core-commit-root) (fn2-machine-batch-no fn2-commit-frontier fn2-core-stop)))))
(make-event
 (value (cons 'progn (fn2-env-keep-forms (fn2-ctf-postorder-new '(fn2-successor-publish fn2-commit-stream-wake fn2-commit-write+phase+cb-published
                                                                  fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason) (w state))
                                         31 "-KEEPS-COMMIT-ROOT" 'fn2-commit))))
(defthm fn2-env-install-arm-phase
  (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset)
                (subsetp-equal '(11 7) fn2-arm-pset)
                (or (member-equal 8 fn2-arm-pset)
                    (not (and (mv-nth 0 (fn2-commit-root-swap id nil fn2-core))
                              (equal (nth 31 (mv-nth 4 (fn2-commit-run-install id budget fn2-core)))
                                     (nth 31 (mv-nth 1 (fn2-commit-root-swap id nil fn2-core))))))))
           (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run-install id budget fn2-core))) fn2-arm-pset))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-install fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase
                                               fn2-commit-root-edge-keeps-commit-root fn2-commit-write+phase-keeps-commit-root
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-keeps-commit-root
                                               fn2-core-stop-keeps-commit-root
                                               fn2-commit~fn2-commit-root-swap-arm-phase fn2-commit~fn2-commit-root-edge-arm-phase
                                               fn2-commit-write+phase-arm-phase
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-arm-phase
                                               fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
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
(defthm fn2-env-install-arm-root
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let ((b (mv-nth 4 (fn2-commit-run-install id budget fn2-core))))
             (mv-let (ok s) (fn2-commit-root-swap id nil fn2-core)
               (or (equal (nth 31 b) (nth 31 fn2-core))
                   (and ok (equal (nth 31 b) (nth 31 s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-install fn2-commit-root-edge-keeps-commit-root
                                               fn2-commit-write+phase-keeps-commit-root
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-keeps-commit-root
                                               fn2-core-stop-keeps-commit-root)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-root-swap-facts (publish nil))))))
(defthm fn2-env-publish-arm-root
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (posp (fn2-machine-batch-no id fn2-core)))
           (let ((b (mv-nth 4 (fn2-commit-run-publish id budget fn2-core))))
             (mv-let (ok s) (fn2-commit-root-swap id t fn2-core)
               (or (equal (nth 31 b) (nth 31 fn2-core))
                   (and ok (equal (nth 31 b) (nth 31 s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-publish fn2-successor-publish-keeps-commit-root
                                               fn2-commit-stream-wake-keeps-commit-root fn2-commit-write+phase+cb-published-keeps-commit-root
                                               fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason-keeps-commit-root
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-keeps-commit-root
                                               fn2-core-stop-keeps-commit-root)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-root-swap-facts (publish t))))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                               fn2-machine-contract-check-keeps-commit-root
                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-install-arm-phase (fn2-arm-pset '(8 11 7)))
                 (:instance fn2-env-install-arm-phase (fn2-arm-pset '(11 7)))
                 (:instance fn2-env-install-arm-root)
                 (:instance fn2-env-root-swap-facts (publish nil))
                 (:instance fn2-env-root-congruence (a (mv-nth 1 (fn2-commit-root-swap id nil fn2-core)))
                            (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-row-phase-snapshot)))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                               fn2-machine-contract-check-keeps-commit-root
                                               fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-publish-arm-phase (fn2-arm-pset '(9 11 8)))
                 (:instance fn2-env-publish-arm-root)
                 (:instance fn2-env-root-swap-facts (publish t))
                 (:instance fn2-env-root-congruence (a (mv-nth 1 (fn2-commit-root-swap id t fn2-core)))
                            (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
                 (:instance fn2-env-row-phase-snapshot)))))
(defthm fn2-env-root-shape
  (and (natp (nth 1 (fn2-env-root fn2-core))) (natp (nth 2 (fn2-env-root fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-root))))
(defthm fn2-env-root-fields
  (implies (equal r (list t x y)) (and (nth 0 r) (equal (nth 1 r) x) (equal (nth 2 r) y)))
  :rule-classes nil)
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
(make-event
 (value (cons 'progn (fn2-env-keep-forms (fn2-ctf-postorder-new '(fn2-commit-run-publish) (w state))
                                         30 "-KEEPS-COMMIT-IO" 'fn2-commit))))
(defthm fn2-env-commit-run-publish-keeps-commit-io
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-publish*)
           (equal (nth 30 (mv-nth 4 (fn2-commit-run id budget fn2-core))) (nth 30 fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit-run-publish-keeps-commit-io
                                               fn2-machine-contract-check-keeps-commit-io fn2-core-stop-keeps-commit-io)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
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
(defun fn2-env-arm-fn (state-name)
  (declare (xargs :mode :program))
  (fn2-columns-sym (fn2-columns-col-name 'fn2-commit-run state-name) ""))
(defun fn2-env-arm-phase-events (state-name extra world)
  ; FN2-ENV-COMMIT-RUN-<STATE>-NEXT: the visit at STATE leaves the row's
  ; phase among the arm's declared successors (any stop reason)
  (declare (xargs :mode :program))
  (let* ((arm (fn2-env-arm-fn state-name))
         (next (cadddr (cdr (assoc-eq arm (table-alist 'fn2-arm-frame-fns world)))))
         ; the theory the generator proved the arm's own -ARM-PHASE contract in
         (ev (get-event (fn2-columns-sym arm "-ARM-PHASE") world))
         (th (cadr (member :in-theory (cdr (car (cadr (member :hints ev)))))))
         (runes (if (and (consp th) (eq (car th) 'union-theories)) (unquote (cadr th))
                  (er hard 'fn2-env-arm-phase-events "No -ARM-PHASE theory for ~x0." arm)))
         (arm-phase (fn2-columns-sym (fn2-columns-col-name 'fn2-env-arm-phase state-name) "")))
    `((defthm ,arm-phase
        (implies (and (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
                      (equal (fn2-machine-phase id fn2-core) ,(fn2-env-arm-state-const state-name))
                      (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal ',next fn2-arm-pset))
                 (member-equal (fn2-machine-phase id (mv-nth 4 (,arm id budget fn2-core))) fn2-arm-pset))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(,@runes) (theory 'fn2-arm-frame-base))
                 :do-not-induct t)))
      (defthm ,(fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-NEXT")
        (implies (and ,@extra (equal (fn2-commit-row-phase id fn2-core) ,(fn2-env-arm-state-const state-name)))
                 (member-equal (fn2-machine-phase id (mv-nth 4 (fn2-commit-run id budget fn2-core))) ',next))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-commit~fn2-machine-contract-check-arm-phase
                                                     fn2-arm-member-of-subsetp-free fn2-commit-arm-row-phase fn2-core-stop-arm-phase fn2-commit-idp)
                                                   (theory 'fn2-arm-frame-base))
                 :do-not-induct t
                 :use ((:instance ,arm-phase (fn2-arm-pset ',next))
                       (:instance fn2-env-row-phase-snapshot))))))))
;; THE QUIET ARMS: an arm whose columns exclude J's flags, batch and reply
;; count, and whose declared successors exclude :install, :publish and
;; :notify, keeps J by the frame alone (FN2-ENV-J-ROW-OF-ROW-FRAME-OFF-ROW,
;; -SAME-ROW) once its children keep commit-io and the root.
(defun fn2-env-quiet-arm-events (state-name code extra world)
  (declare (xargs :mode :program))
  (let* ((e (assoc code *fn2-commit-arm-decls*)) (ch (cadr e)) (cs (caddr e))
         (const (fn2-env-arm-state-const state-name))
         (arm (fn2-env-arm-fn state-name))
         (ek (member 30 ch)) (rk (member 31 ch))
         (run-ek (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-EK"))
         (run-rk (fn2-columns-sym (fn2-columns-col-name 'fn2-env-commit-run state-name) "-RK"))
         (front (fn2-columns-sym (fn2-columns-col-name 'fn2-env-j-frontier state-name) "-ARM"))
         (b '(mv-nth 4 (fn2-commit-run id budget fn2-core)))
         (glue '(fn2-machine-contract-check fn2-machine-refuse-phase)))
    (if (intersectp cs '(9 13 23 24 25 27 33))
        (er hard 'fn2-env-quiet-arm-events "~x0 is not a quiet arm: ~x1." state-name e)
      `(,@(fn2-env-arm-frame-events state-name code)
        ,@(fn2-env-arm-phase-events state-name extra world)
        ,@(and ek
               `((make-event (value (cons 'progn (fn2-env-rel-forms (fn2-ctf-postorder-new '(,arm ,@glue) (w state))
                                                                    'fn2-env-ek 30 *fn2-env-ek-runes* 'fn2-commit))))
                 (defthm ,run-ek
                   (implies (equal (fn2-commit-row-phase id fn2-core) ,const) (fn2-env-ek ,b fn2-core))
                   :rule-classes nil
                   :hints (("Goal" :in-theory (union-theories '(fn2-commit-run ,(fn2-env-rel-name arm 'fn2-env-ek)
                                                                ,(fn2-env-rel-name 'fn2-machine-contract-check 'fn2-env-ek)
                                                                ,(fn2-env-rel-name 'fn2-core-stop 'fn2-env-ek) fn2-env-ek-refl)
                                                              (theory 'fn2-arm-frame-base))
                            :do-not-induct t)))))
        ,@(and rk
               `((make-event (value (cons 'progn (fn2-env-rel-forms (fn2-ctf-postorder-new '(,arm ,@glue) (w state))
                                                                    'fn2-env-rk 31 *fn2-env-rk-runes* 'fn2-commit))))
                 (defthm ,run-rk
                   (implies (equal (fn2-commit-row-phase id fn2-core) ,const) (fn2-env-rk ,b fn2-core))
                   :rule-classes nil
                   :hints (("Goal" :in-theory (union-theories '(fn2-commit-run ,(fn2-env-rel-name arm 'fn2-env-rk)
                                                                ,(fn2-env-rel-name 'fn2-machine-contract-check 'fn2-env-rk)
                                                                ,(fn2-env-rel-name 'fn2-core-stop 'fn2-env-rk) fn2-env-rk-refl)
                                                              (theory 'fn2-arm-frame-base))
                            :do-not-induct t)))
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
(defun-nx fn2-env-tk (b a)
  (and (fn2-ctf-dir b a)
       (equal (nth 0 (nth 9 b)) (nth 0 (nth 9 a))) (equal (nth 9 (nth 9 b)) (nth 9 (nth 9 a)))
       (equal (nth 13 (nth 9 b)) (nth 13 (nth 9 a))) (equal (nth 23 (nth 9 b)) (nth 23 (nth 9 a)))
       (equal (nth 24 (nth 9 b)) (nth 24 (nth 9 a))) (equal (nth 25 (nth 9 b)) (nth 25 (nth 9 a)))
       (equal (nth 27 (nth 9 b)) (nth 27 (nth 9 a))) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))
       (equal (nth 17 (nth 9 b)) (nth 17 (nth 9 a)))))
(defthm fn2-env-tk-refl (fn2-env-tk a a))
(defthm fn2-env-tk-trans
  (implies (and (fn2-env-tk c b) (fn2-env-tk b a)) (fn2-env-tk c a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-tk) :use ((:instance fn2-ctf-dir-trans)))))
(defthm fn2-env-tk-of-nth
  (implies (and (equal (nth 3 b) (nth 3 x)) (equal (nth 9 b) (nth 9 x)) (fn2-env-tk x a)) (fn2-env-tk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-tk) :use ((:instance fn2-ctf-dir-of-nth)))))
(defthm fn2-env-not-intersectp-member
  (implies (and (not (intersectp-equal x y)) (member-equal j y)) (not (member-equal j x)))
  :rule-classes nil)
(defthm fn2-env-tk-of-row-frame-cols
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch)) (not (member-equal 3 ch))
                (not (member-equal 0 cs)) (not (member-equal 9 cs)) (not (member-equal 13 cs)) (not (member-equal 23 cs)) (not (member-equal 24 cs)) (not (member-equal 25 cs)) (not (member-equal 27 cs)) (not (member-equal 33 cs)) (not (member-equal 17 cs)))
           (fn2-env-tk b x))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-tk fn2-ctf-dir-refl member-equal car-cons cdr-cons (:e natp) (:e binary-+) (:e equal)) (theory 'minimal-theory))
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
(defun fn2-env-tk-read-events (fields)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((f (car fields))
           (r (fn2-columns-col-name 'fn2-machine f))
           (tr (fn2-columns-col-name 'fn2-commit f)) (ai (fn2-columns-sym tr "$AI")))
      (cons
       `(defthm ,(fn2-columns-sym r "-OF-TK")
          (implies (and (fn2-env-tk b a) (equal (fn2-machine-kind id a) *fn2-commit-kind*))
                   (equal (,r id b) (,r id a)))
          :rule-classes nil
          :hints (("Goal" :in-theory (e/d (fn2-env-tk ,r fn2-commit-table fn2-commit-rows ,tr ,ai)
                                          (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
                   :do-not-induct t
                   :use ((:instance fn2-ctf-dir-readers)))))
       (fn2-env-tk-read-events (cdr fields))))))
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
  :hints (("Goal" :in-theory (e/d (fn2-env-tk fn2-machine-batch-no-read-code fn2-machine-cb-acks-read-code fn2-commit-idp
                                   fn2-commit-snapshot-read-code fn2-machine-phase-read-code fn2-commit-row
                                   fn2-commit-table fn2-commit-rows)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
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
(defthm fn2-env-j-rows-of-tk-rows
  (implies (and (fn2-env-j-rows ids log a) (fn2-env-j-frontier log a)
                (fn2-env-tk b a) (fn2-env-ek b a) (fn2-env-rk b a) (fn2-corep b) (fn2-core-wfp b))
           (fn2-env-j-rows ids log b))
  :rule-classes nil
  :hints (("Goal" :induct (len ids) :in-theory '(fn2-env-j-rows len atom))
          ("Subgoal *1/1" :use ((:instance fn2-env-j-row-of-tk (id (car ids)))))))
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
(defthm fn2-env-j3-rows-of-tk
  (implies (and (fn2-env-tk b a) (fn2-env-ek b a))
           (equal (fn2-env-j3-rows ids log b) (fn2-env-j3-rows ids log a)))
  :rule-classes nil
  :hints (("Goal" :induct (len ids) :in-theory '(fn2-env-j3-rows len atom))
          ("Subgoal *1/1" :use ((:instance fn2-env-j3-of-tk (id (car ids)))))))
;; The admission's sub-operations keep TK, EK and RK (but the extent
;; reservation, which writes its row's extents): by contract, by row frame,
;; or by one opening; the two pool loops by induction over their passes.
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool fn2-commit-release-pools
                           fn2-commit-reserve-extent fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake)
                         (w state))
  'fn2-env-tk '(3 9) nil 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool fn2-commit-reserve-pools
                           fn2-commit-reserve-extent fn2-commit-release-pools fn2-commit-prepare-root fn2-commit-ready
                           fn2-commit-put-members fn2-exec-wake)
                         (w state))
  'fn2-env-rk 31 *fn2-env-rk-runes* 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool
                           fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake)
                         (w state))
  'fn2-env-ek 30 *fn2-env-ek-runes* 'fn2-commit))))
(defthm fn2-commit-reserve-pools-fn2-env-tk
  (implies (fn2-env-tk fn2-core fn2-rel-c0)
           (fn2-env-tk (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-core-reserve-fn2-env-tk
                                        fn2-commit-keep-pool-fn2-env-tk fn2-commit-unwind-pool-fn2-env-tk)
                                      (theory 'minimal-theory)))))
(defthm fn2-commit-reserve-pools-fn2-env-ek
  (implies (fn2-env-ek fn2-core fn2-rel-c0)
           (fn2-env-ek (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-core-reserve-fn2-env-ek
                                        fn2-commit-keep-pool-fn2-env-ek fn2-commit-unwind-pool-fn2-env-ek)
                                      (theory 'minimal-theory)))))
(defthm fn2-commit-release-pools-fn2-env-ek
  (implies (fn2-env-ek fn2-core fn2-rel-c0)
           (fn2-env-ek (fn2-commit-release-pools left id owner-gen fn2-core) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-release-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-release-pools fn2-commit-release-pool-fn2-env-ek fn2-core-stop-fn2-env-ek)
                                      (theory 'minimal-theory)))))
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
  :hints (("Goal" :in-theory (e/d (fn2-commit-reserve-extent fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   update-nth-array fn2-core-stop-keeps-commit-io)
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop update-nth)))))
(defthm fn2-env-row-units-disjoint
  (implies (and (natp a) (natp b) (not (equal a b)) (natp role) (< role 3) (natp k) (< k 3))
           (not (equal (+ (* 3 a) role) (+ k (* 3 b)))))
  :rule-classes nil
  :hints (("Goal" :cases ((< a b)))))
(defthm fn2-env-reserve-extent-role-extent
  ; the reservation keeps the role extents of every row but its own
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp role) (< role 3)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (equal (fn2-env-role-extent i role (mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))
                  (fn2-env-role-extent i role fn2-core)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-role-extent fn2-commit-resource fn2-core-commit-io fn2-commit-io-extent
                                   fn2-commit-io-rows fn2-commit-row)
                                  (fn2-commit-reserve-extent fn2-commit-idp fn2-machine-slot nth update-nth))
           :do-not-induct t
           :use ((:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-read-codes-of-tk (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core) (id i))
                 (:instance fn2-env-reserve-extent-io (j (+ (* 3 (fn2-machine-slot i fn2-core)) role)))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 0))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 1))
                 (:instance fn2-env-row-units-disjoint (a (fn2-machine-slot i fn2-core)) (b (fn2-machine-slot id fn2-core)) (k 2))))))
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
(defthm fn2-env-reserve-extent-io-shared
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
           (let ((x (nth *fn2-commit-io-extent$ai* (nth 30 (mv-nth 1 (fn2-commit-reserve-extent id fn2-core)))))
                 (r (* 3 (fn2-commit-row id fn2-core))))
             (and (natp (nth r x)) (equal (nth (+ 1 r) x) (nth r x)) (equal (nth (+ 2 r) x) (nth r x))
                  (< (+ 2 r) (nth *fn2-commit-io-rows* (nth 30 fn2-core))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-commit-reserve-extent fn2-core-commit-io update-fn2-core-commit-io
                                   fn2-commit-io-set-extent fn2-commit-io-set-epoch fn2-commit-io-set-counter
                                   update-fn2-commit-io-extent$ai update-fn2-commit-io-epoch$ai update-fn2-commit-io-counter$ai
                                   update-nth-array fn2-core-stop-keeps-commit-io fn2-commit-io-rows)
                                  (fn2-alloc-reserve fn2-commit-row fn2-commit-idp fn2-core-stop update-nth))
           :use ((:instance fn2-env-alloc-reserve-ranges (x (fn2-core-extents fn2-core)))
                 (:instance fn2-env-core-extentsp)))))
(defthm fn2-env-reserve-extent-shared
  ; an accepted reservation gives its row's three roles one extent
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core)
                (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok))
           (let ((c (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
             (and (natp (fn2-env-role-extent id 0 c))
                  (equal (fn2-env-role-extent id 1 c) (fn2-env-role-extent id 0 c))
                  (equal (fn2-env-role-extent id 2 c) (fn2-env-role-extent id 0 c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-role-extent fn2-commit-resource fn2-core-commit-io fn2-commit-io-extent
                                   fn2-commit-io-rows)
                                  (fn2-commit-reserve-extent fn2-commit-row fn2-commit-idp nth))
           :do-not-induct t
           :use ((:instance fn2-env-reserve-extent-io-shared)
                 (:instance fn2-env-reserve-extent-io (j 0))
                 (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-read-codes-of-tk (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))))))
(defthm fn2-env-j3-reserve-extent
  ; the extent reservation keeps J3 at every id but its own row's
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (and (equal (fn2-env-j3-row i log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (fn2-env-j3-row i log fn2-core))
                (equal (fn2-env-j3e-row i (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (fn2-env-j3e-row i fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-tk-refl (:e natp) (:e <)) (theory 'minimal-theory))
           :cases ((fn2-commit-idp i fn2-core))
           :do-not-induct t)
          ("Subgoal 2" :in-theory (union-theories '(fn2-env-j3-off-commit fn2-env-tk-refl) (theory 'minimal-theory))
           :use ((:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-read-codes-of-tk (id i) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (a fn2-core))))
          ("Subgoal 1"
           :use ((:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
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
                 (:instance fn2-env-j3-congruence (id i) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))))))
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
(defthm fn2-env-j-row-reserve-extent
  ; the extent reservation keeps J at every id but its own row's
  (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
           (fn2-env-j-row i log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-j-same-evidence fn2-env-j-row-not-idp fn2-env-tk-refl fn2-env-rk-refl (:e natp) (:e <))
                                             (theory 'minimal-theory))
           :cases ((equal (fn2-machine-kind i fn2-core) *fn2-commit-kind*))
           :do-not-induct t
           :use ((:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-commit-reserve-extent-fn2-env-rk (fn2-rel-c0 fn2-core))
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
                 (:instance fn2-env-j-row-transfer (id i) (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))))))
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
      (defthm fn2-env-start-tail-j-row
        ; the extent reservation and the row write, from the row's free core
        (implies (and (fn2-env-j-row i log fn2-core) (fn2-env-j-frontier log fn2-core)
                      (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core)
                      ,@fits ,@written)
                 (fn2-env-j-row i log ,call2))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-tk-refl fn2-env-rk-refl) (theory 'minimal-theory))
                 :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core))))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance ,(fn2-columns-sym w "-PRESERVES-TYPE") (fn2-core ,c2))
                       (:instance ,(fn2-columns-sym w "-PRESERVES-WFP") (fn2-core ,c2))
                       (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                       (:instance fn2-commit-reserve-extent-fn2-env-rk (fn2-rel-c0 fn2-core))
                       (:instance fn2-env-j-frontier-of-rk (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-commit-idp-cell (fn2-core ,c2))
                       (:instance fn2-env-start-write-accepted-suff (fn2-core ,c2))
                       (:instance fn2-env-start-write-same-slot (fn2-core ,c2))
                       (:instance fn2-env-j-row-reserve-extent)
                       (:instance fn2-env-start-write-other (fn2-core ,c2))))))
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
      (defthm fn2-env-start-tail-j3-same
        ; at the started slot: the row write's J3
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext
                      ,@fits ,@written
                      (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))
                 (and (fn2-env-j3-row i log ,call2) (fn2-env-j3e-row i ,call2)))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-tk-refl) (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-commit-idp-cell (fn2-core ,c2))
                       (:instance fn2-env-start-write-accepted-suff (fn2-core ,c2))
                       (:instance fn2-env-reserve-extent-shared)
                       (:instance fn2-env-start-write-j3-row (fn2-core ,c2))
                       (:instance fn2-env-start-write-keeps-ids (x i) (fn2-core ,c2))
                       (:instance fn2-env-start-write-keeps-ids (x id) (fn2-core ,c2))
                       (:instance fn2-env-j3-same-slot (i i) (j id) (fn2-core ,call2))))))
      (defthm fn2-env-start-tail-j3-other
        ; elsewhere: the reservation and the write keep J3
        (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (or (not (fn2-commit-idp i fn2-core)) (not (equal (fn2-machine-slot i fn2-core) (fn2-machine-slot id fn2-core)))))
                 (and (equal (fn2-env-j3-row i log ,call2) (fn2-env-j3-row i log fn2-core))
                      (equal (fn2-env-j3e-row i ,call2) (fn2-env-j3e-row i fn2-core))))
        :rule-classes nil
        :hints (("Goal" :in-theory (union-theories '(fn2-env-tk-refl) (theory 'minimal-theory))
                 :do-not-induct t
                 :use ((:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id i) (b ,c2) (a fn2-core))
                       (:instance fn2-env-read-codes-of-tk (id id) (b ,c2) (a fn2-core))
                       (:instance fn2-env-j3-reserve-extent)
                       (:instance fn2-env-start-write-j3-other (fn2-core ,c2))))))
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
      (defthm fn2-env-start-tail-jr
        (implies (and (fn2-env-jr ids log fn2-core) (fn2-commit-idp id fn2-core) ,ok-ext ,@fits ,@written)
                 (fn2-env-jr ids log ,call2))
        :hints (("Goal" :in-theory (union-theories '(fn2-env-jr fn2-env-rk-refl) (theory 'minimal-theory))
                 :do-not-induct t
                 :use (fn2-env-start-tail-j-rows fn2-env-start-tail-j3-rows
                       (:instance fn2-commit-reserve-extent-preserves-type)
                       (:instance fn2-commit-reserve-extent-preserves-wfp)
                       (:instance ,(fn2-columns-sym w "-PRESERVES-TYPE") (fn2-core ,c2))
                       (:instance ,(fn2-columns-sym w "-PRESERVES-WFP") (fn2-core ,c2))
                       (:instance fn2-commit-reserve-extent-fn2-env-rk (fn2-rel-c0 fn2-core))
                       (:instance fn2-env-j-frontier-of-rk (b ,c2) (a fn2-core))
                       (:instance fn2-env-start-write-frontier (fn2-core ,c2)))))))))
(make-event (value (cons 'progn (fn2-env-start-j-events (w state)))))
(defun fn2-env-jr-shape-runes (fn world)
  (declare (xargs :mode :program))
  (cond ((getpropc (fn2-columns-sym fn "-PRESERVES-TYPE") 'theorem nil world)
         (list (fn2-columns-sym fn "-PRESERVES-TYPE") (fn2-columns-sym fn "-PRESERVES-WFP")))
        ((getpropc (fn2-columns-sym fn "-TYPE") 'theorem nil world)
         (list (fn2-columns-sym fn "-TYPE") (fn2-columns-sym fn "-WFP")))
        (t (list (fn2-columns-sym fn "-SHAPE")))))
(defun fn2-env-jr-events (fns world)
  ; FN-FN2-ENV-JR from FN's TK, EK and RK steps; an entry (FN . HYPS)
  ; adds its shape theorem's hypotheses
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (let* ((fn (if (consp (car fns)) (caar fns) (car fns))) (hyps (and (consp (car fns)) (cdar fns))) (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
      (cons `(defthm ,(fn2-env-rel-name fn 'fn2-env-jr)
               (implies (and (fn2-env-jr ids log fn2-core) ,@hyps) (fn2-env-jr ids log ,out))
               :hints (("Goal" :in-theory (union-theories '(fn2-env-jr fn2-env-tk-refl fn2-env-ek-refl fn2-env-rk-refl
                                                            ,(fn2-env-rel-name fn 'fn2-env-tk) ,(fn2-env-rel-name fn 'fn2-env-ek)
                                                            ,(fn2-env-rel-name fn 'fn2-env-rk) ,@(fn2-env-jr-shape-runes fn world))
                                                          (theory 'minimal-theory))
                        :do-not-induct t
                        :use ((:instance fn2-env-jr-of-tk (a fn2-core) (b ,out))))))
            (fn2-env-jr-events (cdr fns) world)))))
(make-event (value (cons 'progn (fn2-env-jr-events '((fn2-core-stop (unsigned-byte-p 8 reason)) fn2-commit-reserve-pools fn2-commit-release-pools
  fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake) (w state)))))
(defthm fn2-commit-reserve-extent-fn2-env-jr
  ; a refused reservation writes no extent
  (implies (and (fn2-env-jr ids log fn2-core) (not (eq (mv-nth 0 (fn2-commit-reserve-extent id fn2-core)) :ok)))
           (fn2-env-jr ids log (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-jr fn2-env-tk-refl fn2-env-rk-refl fn2-env-ek-refl
                                               fn2-commit-reserve-extent-preserves-type fn2-commit-reserve-extent-preserves-wfp)
                                             (theory 'minimal-theory))
           :do-not-induct t
           :use ((:instance fn2-env-jr-of-tk (a fn2-core) (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))))
                 (:instance fn2-commit-reserve-extent-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-commit-reserve-extent-fn2-env-rk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-reserve-extent-io (j 0))
                 (:instance fn2-env-ek-of-nth (b (mv-nth 1 (fn2-commit-reserve-extent id fn2-core))) (x fn2-core) (a fn2-core))))))
(defthm fn2-env-reserve-pools-idp
  (equal (fn2-commit-idp x (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core))) (fn2-commit-idp x fn2-core))
  :hints (("Goal" :in-theory '(fn2-env-tk-refl)
           :use ((:instance fn2-commit-reserve-pools-fn2-env-tk (fn2-rel-c0 fn2-core))
                 (:instance fn2-env-read-codes-of-tk (id x) (b (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)))
                            (a fn2-core))))))
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
(defun-nx fn2-env-sk (b a) (and (fn2-ctf-dir b a) (equal (nth 33 (nth 9 b)) (nth 33 (nth 9 a)))))
(defthm fn2-env-sk-refl (fn2-env-sk a a))
(defthm fn2-env-sk-of-nth
  (implies (and (equal (nth 3 b) (nth 3 x)) (equal (nth 9 b) (nth 9 x)) (fn2-env-sk x a)) (fn2-env-sk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-sk) :use ((:instance fn2-ctf-dir-of-nth)))))
(defthm fn2-env-sk-trans
  (implies (and (fn2-env-sk c b) (fn2-env-sk b a)) (fn2-env-sk c a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-sk) :use ((:instance fn2-ctf-dir-trans)))))
(defthm fn2-env-sk-of-row-frame
  (implies (and (fn2-arm-row-frame 9 row cs ch x b) (not (member-equal 9 ch)) (not (member-equal 3 ch))
                (not (intersectp-equal cs '(33))) (fn2-env-sk x a))
           (fn2-env-sk b a))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-sk member-equal car-cons cdr-cons (:e member-equal) (:e natp) (:e binary-+)) (theory 'minimal-theory))
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
  :hints (("Goal" :in-theory '(fn2-env-tk fn2-env-sk))))
(in-theory (disable fn2-env-sk))
(table fn2-env-rel-cols 'fn2-env-sk '(33))
(defthm fn2-env-commit-slots-p-of-sk
  (implies (fn2-env-sk b a)
           (equal (fn2-env-commit-slots-p profile b) (fn2-env-commit-slots-p profile a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-env-sk fn2-env-commit-slots-p fn2-commit-idp fn2-commit-snapshot-read-code
                                   fn2-machine-phase-read-code fn2-commit-table fn2-commit-rows)
                                  (fn2-machine-kind fn2-machine-slot fn2-machine-idp fn2-ctf-dir))
           :do-not-induct t
           :use ((:instance fn2-ctf-dir-readers (id (fn2-machine-global-id *fn2-commit-kind* 0 profile)))
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
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool fn2-commit-release-pools
                           fn2-commit-reserve-extent fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake
                           fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes)
                         (w state))
  'fn2-env-sk '(3 9) nil 'fn2-commit))))
(defthm fn2-commit-reserve-pools-fn2-env-sk
  (implies (fn2-env-sk fn2-core fn2-rel-c0)
           (fn2-env-sk (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-core-reserve-fn2-env-sk
                                        fn2-commit-keep-pool-fn2-env-sk fn2-commit-unwind-pool-fn2-env-sk)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-commit-start-sk
  (implies (fn2-env-sk fn2-core c0)
           (fn2-env-sk (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)) c0))
  :hints (("Goal" :in-theory (union-theories
                              '(fn2-commit-start fn2-commit-reserve-extent-fn2-env-sk fn2-commit-reserve-pools-fn2-env-sk
                                fn2-commit-release-pools-fn2-env-sk fn2-commit-prepare-root-fn2-env-sk fn2-commit-ready-fn2-env-sk
                                fn2-core-stop-fn2-env-sk
                                fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes-fn2-env-sk)
                              (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-admit-sk
  (implies (fn2-env-sk fn2-core c0)
           (fn2-env-sk (fn2-env-admit members mode fn2-core) c0))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-sk
                                               fn2-commit-put-members-fn2-env-sk fn2-core-stop-fn2-env-sk fn2-exec-wake-fn2-env-sk)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-commit-slots-p-step-but-turn
  ; every step but :turn keeps FN2-ENV-COMMIT-SLOTS-P
  (implies (not (equal (fn2-env-tag action) :turn))
           (equal (fn2-env-commit-slots-p p (mv-nth 1 (fn2-env-step action nil image rlog fn2-core)))
                  (fn2-env-commit-slots-p p fn2-core)))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-commit-slots-p-host-step member-eq (:e member-eq) fn2-env-sk-refl) (theory 'minimal-theory))
           :cases ((equal (fn2-env-tag action) :admit))
           :use ((:instance fn2-env-step-admit-unfolds)
                 (:instance fn2-env-admit-sk (members (fn2-env-arg 1 action)) (mode (fn2-env-arg 2 action)) (c0 fn2-core))
                 (:instance fn2-env-commit-slots-p-of-sk (profile p) (a fn2-core)
                            (b (fn2-env-admit (fn2-env-arg 1 action) (fn2-env-arg 2 action) fn2-core)))))))
;; every commit visit: the arm's frame keeps the directory and the rows field
(defthm fn2-env-subsetp-cons
  (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
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
       :hints (("Goal" :in-theory (union-theories '(fn2-env-sk fn2-env-arm-decls-miss-rows member-equal car-cons cdr-cons
                                                    fn2-ctf-subsetp-refl fn2-env-subsetp-cons (:e natp) (:type-prescription fn2-machine-slot-natp))
                                                  (theory 'minimal-theory))
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
;; ---------------------------------------------------------------------------
;; :DEPENDENCIES AND :LOG-WRITE. J3, the counted-completion link: a row in a
;; write phase has its three role extents shared, and each completion it
;; counted (cb-done) is a write of one of the phase's roles answered done in
;; full in the log at the role's offset (role 2 carrying the seal of its
;; batch), fenced as J2 asks once the fence flag is set (or FUA in barrier
;; mode 1). The phase's flag rise (cb-deps-ok, cb-log-ok) happens only when
;; every issued write is counted, so J3 at the visited row gives J2 after.
;; FN2-ENV-FK: the commit table's two flag columns.
(defun-nx fn2-env-fk (b a)
  (and (equal (nth 24 (nth 9 b)) (nth 24 (nth 9 a))) (equal (nth 25 (nth 9 b)) (nth 25 (nth 9 a)))))
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
(table fn2-env-rel-cols 'fn2-env-fk '(24 25))
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
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-commit-mark-abort fn2-issue-write fn2-commit-io-edge
                           fn2-commit-write+phase+cb-stage+cb-cursor+outcome+cb-open
                           fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason
                           fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason
                           fn2-commit-write+pending+cb-issued+cb-wrote
                           fn2-machine-contract-check fn2-machine-refuse-phase)
                         (w state))
  'fn2-env-fk 9 nil 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-rel-forms (fn2-ctf-postorder-new '(fn2-commit-run-dependencies fn2-commit-run-log-write
                                                                            fn2-machine-contract-check fn2-machine-refuse-phase) (w state))
                                                   'fn2-env-ek 30 *fn2-env-ek-runes* 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-rel-forms (fn2-ctf-postorder-new '(fn2-commit-run-dependencies fn2-commit-run-log-write
                                                                            fn2-machine-contract-check fn2-machine-refuse-phase) (w state))
                                                   'fn2-env-rk 31 *fn2-env-rk-runes* 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-keep-forms '(fn2-machine-contract-check) 9 "-KEEPS-COMMIT-TABLE" 'fn2-commit))))
(make-event (value (cons 'progn (fn2-env-keep-forms '(fn2-machine-contract-check) 3 "-KEEPS-DIRECTORY" 'fn2-commit))))
(defthm fn2-env-flags-congruence
  (implies (and (equal (nth 3 b) (nth 3 a)) (equal (nth 9 b) (nth 9 a)))
           (and (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id a))
                (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-cb-deps-ok fn2-machine-cb-log-ok fn2-machine-cb-deps-ok-read-code
                                     fn2-machine-cb-log-ok-read-code fn2-machine-idp fn2-core-machines fn2-commit-table)
           :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
(defun fn2-env-write-keeps-ids-event (w world)
  ; W-KEEPS-IDS: a commit-table row write keeps every id's readability and slot
  (declare (xargs :mode :program))
  (let* ((kind 'fn2-commit) (formals (formals w world)) (call (cons w formals))
         (e (fn2-arm-frame-known w kind world)) (cs (fn2-arm-frame-entry-j e)) (ch (fn2-arm-frame-entry-s e))
         (row '(fn2-machine-slot id fn2-core)))
    `(defthm ,(fn2-columns-sym w "-KEEPS-IDS")
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
                      (:instance fn2-env-read-codes-of-row-frame (id x) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,call))))))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-dependencies fn2-env-fk-refl fn2-env-deps-advance-reads
                                               fn2-commit-idp
                                               fn2-core-stop-fn2-env-fk fn2-commit-mark-abort-fn2-env-fk fn2-issue-write-fn2-env-fk
                                               fn2-commit-io-edge-fn2-env-fk
                                               fn2-commit-write+phase+cb-stage+cb-cursor+outcome+cb-open-fn2-env-fk
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-fn2-env-fk
                                               fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason-fn2-env-fk
                                               fn2-commit-write+pending+cb-issued+cb-wrote-fn2-env-fk)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-contract-check-flags
  (let ((b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core))))
    (and (equal (fn2-machine-cb-deps-ok id b) (fn2-machine-cb-deps-ok id fn2-core))
         (equal (fn2-machine-cb-log-ok id b) (fn2-machine-cb-log-ok id fn2-core))))
  :hints (("Goal" :in-theory nil
           :use (fn2-machine-contract-check-keeps-commit-table fn2-machine-contract-check-keeps-directory
                 (:instance fn2-env-flags-congruence
                            (b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
                            (a fn2-core))))))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :dependencies 3))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :dependencies nil (w state)))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-env-ek-refl fn2-env-rk-refl fn2-env-fk-refl
                                               fn2-commit-run-dependencies-fn2-env-ek fn2-commit-run-dependencies-fn2-env-rk
                                               fn2-machine-contract-check-fn2-env-ek fn2-machine-contract-check-fn2-env-rk
                                               fn2-machine-contract-check-fn2-env-fk fn2-env-contract-check-flags)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-dependencies-arm-flags) (:instance fn2-env-row-phase-snapshot)))))
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
(defthm fn2-env-j-rows-dependencies-arm
  (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*))
           (and (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j-frontier log (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
  :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core) :in-theory '(fn2-env-j-rows))
          ("Subgoal *1/2" :use ((:instance fn2-env-j-row-dependencies-arm (i (car ids)))))
          ("Subgoal *1/1" :use ((:instance fn2-env-commit-run-dependencies-facts)
                                (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-log-write fn2-env-fk-refl fn2-env-log-advance-reads
                                               fn2-commit-idp
                                               fn2-core-stop-fn2-env-fk fn2-commit-mark-abort-fn2-env-fk fn2-issue-write-fn2-env-fk
                                               fn2-commit-io-edge-fn2-env-fk
                                               fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason-fn2-env-fk
                                               fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason-fn2-env-fk
                                               fn2-commit-write+pending+cb-issued+cb-wrote-fn2-env-fk)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(make-event (value (cons 'progn (fn2-env-arm-frame-events :log-write 4))))
(make-event (value (cons 'progn (fn2-env-arm-phase-events :log-write nil (w state)))))
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
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-env-ek-refl fn2-env-rk-refl fn2-env-fk-refl
                                               fn2-commit-run-log-write-fn2-env-ek fn2-commit-run-log-write-fn2-env-rk
                                               fn2-machine-contract-check-fn2-env-ek fn2-machine-contract-check-fn2-env-rk
                                               fn2-machine-contract-check-fn2-env-fk fn2-env-contract-check-flags)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-log-write-arm-flags) (:instance fn2-env-row-phase-snapshot)))))
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
(defthm fn2-env-j-rows-log-write-arm
  (implies (and (fn2-env-j-rows ids log fn2-core) (fn2-env-j3-row id log fn2-core) (fn2-env-j-frontier log fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*))
           (and (fn2-env-j-rows ids log (mv-nth 4 (fn2-commit-run id budget fn2-core)))
                (fn2-env-j-frontier log (mv-nth 4 (fn2-commit-run id budget fn2-core)))))
  :hints (("Goal" :induct (fn2-env-j-rows ids log fn2-core) :in-theory '(fn2-env-j-rows))
          ("Subgoal *1/2" :use ((:instance fn2-env-j-row-log-write-arm (i (car ids)))))
          ("Subgoal *1/1" :use ((:instance fn2-env-commit-run-log-write-facts)
                                (:instance fn2-env-j-frontier-of-rk (a fn2-core) (b (mv-nth 4 (fn2-commit-run id budget fn2-core))))))))
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
(defun fn2-env-j3-move-ok (p q mode d d2)
  ; the phase moves a commit visit may make that keep J3 at the row: out of
  ; the write span, a stay, :collect -> :seal -> :dependencies, :fence ->
  ; :log-write in barrier mode 1, each with the count kept; or a write phase
  ; advancing with its count reset
  (declare (xargs :guard t))
  (or (not (member-equal q '(1 2 3 4 5)))
      (and (equal d2 d)
           (or (equal q p) (and (equal p 1) (equal q 2)) (and (equal p 2) (equal q 3))
               (and (equal p 5) (equal q 4) (equal mode 1))))
      (and (equal d2 0) (member-equal p '(3 4)) (member-equal q '(3 4 5)) (or (equal p 3) (not (equal q 3))))))
(defthm fn2-env-j3-move
  (implies (and (fn2-env-j3-row id log a) (fn2-env-j3e-row id a) (fn2-commit-idp id a)
                (fn2-env-j-same-evidence id a b)
                (fn2-env-j3-move-ok (fn2-machine-phase id a) (fn2-machine-phase id b) (fn2-machine-cb-mode id a)
                                    (fn2-machine-cb-done id a) (fn2-machine-cb-done id b)))
           (and (fn2-env-j3-row id log b) (fn2-env-j3e-row id b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-j3-row fn2-env-j3e-row fn2-env-role-written fn2-env-j-same-evidence fn2-env-j3-move-ok
                               fn2-env-role-offset-of-extent member-equal (:e member-equal) nfix (:e nfix) (:e <) (:e equal)))))
(defun fn2-env-row-frame-uses (rs row cs ch b)
  (declare (xargs :mode :program))
  (if (atom rs) nil
    (cons `(:instance ,(car rs) (id id) (row ,row) (cs ',cs) (ch ',ch) (a fn2-core) (b ,b))
          (fn2-env-row-frame-uses (cdr rs) row cs ch b))))
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
          :hints (("Goal" :induct (fn2-env-j3-rows ids log fn2-core) :in-theory '(fn2-env-j3-rows))
                  ("Subgoal *1/2" :use ((:instance ,one (i (car ids)))))))))))
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
(defun fn2-env-arm-phase-runes (state-name world)
  ; the theory the generator proved the arm's own -ARM-PHASE contract in
  (declare (xargs :mode :program))
  (let* ((arm (fn2-env-arm-fn state-name))
         (ev (get-event (fn2-columns-sym arm "-ARM-PHASE") world))
         (th (cadr (member :in-theory (cdr (car (cadr (member :hints ev))))))))
    (if (and (consp th) (eq (car th) 'union-theories)) (unquote (cadr th))
      (er hard 'fn2-env-arm-phase-runes "No -ARM-PHASE theory for ~x0." arm))))
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
(defun-nx fn2-env-dk (b a) (equal (nth 17 (nth 9 b)) (nth 17 (nth 9 a))))
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
(table fn2-env-rel-cols 'fn2-env-dk '(17))
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
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-commit-mark-abort fn2-issue-write fn2-commit-io-edge
                           fn2-commit-write+phase+cb-stage+cb-cursor+outcome+cb-open
                           fn2-commit-write+phase+stopped+cb-cursor+cb-failed+cb-reason
                           fn2-commit-write+phase+cb-cursor+cb-failed+cb-reason
                           fn2-commit-write+pending+cb-issued+cb-wrote
                           fn2-machine-contract-check fn2-machine-refuse-phase)
                         (w state))
  'fn2-env-dk 9 nil 'fn2-commit))))
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
 `(defthm fn2-env-deps-arm-done
    ; the :dependencies arm keeps the count and moves the phase as a stay or a failure, or resets the count
    (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal '(11 12) fn2-arm-pset))
             (let ((b (mv-nth 4 (fn2-commit-run-dependencies id budget fn2-core))))
               (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) fn2-arm-pset))
                   (equal (fn2-machine-cb-done id b) 0))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-dependencies fn2-env-dk-refl fn2-env-deps-advance-done fn2-commit-idp
                                                 ,@(fn2-env-rel-callee-runes (fn2-arm-frame-body-callees 'fn2-commit-run-dependencies (w state)) 'fn2-env-dk (w state))
                                                 ,@(fn2-env-arm-phase-runes :dependencies (w state)))
                                               (theory 'fn2-arm-frame-base))
             :do-not-induct t))))
(make-event
 `(defthm fn2-env-log-arm-done
    (implies (and (member-equal (fn2-machine-phase id fn2-core) fn2-arm-pset) (subsetp-equal '(11 12) fn2-arm-pset))
             (let ((b (mv-nth 4 (fn2-commit-run-log-write id budget fn2-core))))
               (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) fn2-arm-pset))
                   (equal (fn2-machine-cb-done id b) 0))))
    :rule-classes nil
    :hints (("Goal" :in-theory (union-theories '(fn2-commit-run-log-write fn2-env-dk-refl fn2-env-log-advance-done fn2-commit-idp
                                                 ,@(fn2-env-rel-callee-runes (fn2-arm-frame-body-callees 'fn2-commit-run-log-write (w state)) 'fn2-env-dk (w state))
                                                 ,@(fn2-env-arm-phase-runes :log-write (w state)))
                                               (theory 'fn2-arm-frame-base))
             :do-not-induct t))))
(defthm fn2-env-done-congruence
  (implies (and (equal (nth 3 b) (nth 3 a)) (equal (nth 9 b) (nth 9 a)))
           (equal (fn2-machine-cb-done id b) (fn2-machine-cb-done id a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-machine-cb-done fn2-machine-cb-done-read-code fn2-machine-idp fn2-core-machines fn2-commit-table)
           :use ((:instance fn2-arm-slot-congruence) (:instance fn2-arm-kind-congruence)))))
(defthm fn2-env-contract-check-done
  (equal (fn2-machine-cb-done id (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
         (fn2-machine-cb-done id fn2-core))
  :hints (("Goal" :in-theory nil
           :use (fn2-machine-contract-check-keeps-commit-table fn2-machine-contract-check-keeps-directory
                 (:instance fn2-env-done-congruence
                            (b (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
                            (a fn2-core))))))
(defthm fn2-env-commit-run-dependencies-done
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-dependencies*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) '(3 11 12)))
                 (equal (fn2-machine-cb-done id b) 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-env-dk-refl fn2-machine-contract-check-fn2-env-dk fn2-env-contract-check-done
                                               fn2-commit~fn2-machine-contract-check-arm-phase fn2-arm-member-of-subsetp-free
                                               fn2-commit-arm-row-phase fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-deps-arm-done (fn2-arm-pset '(3 11 12))) (:instance fn2-env-row-phase-snapshot)))))
(defthm fn2-env-commit-run-log-write-done
  (implies (equal (fn2-commit-row-phase id fn2-core) *fn2-commit-state-log-write*)
           (let ((b (mv-nth 4 (fn2-commit-run id budget fn2-core))))
             (or (and (fn2-env-dk b fn2-core) (member-equal (fn2-machine-phase id b) '(4 11 12)))
                 (equal (fn2-machine-cb-done id b) 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-commit-run fn2-env-dk-refl fn2-machine-contract-check-fn2-env-dk fn2-env-contract-check-done
                                               fn2-commit~fn2-machine-contract-check-arm-phase fn2-arm-member-of-subsetp-free
                                               fn2-commit-arm-row-phase fn2-core-stop-arm-phase)
                                             (theory 'fn2-arm-frame-base))
           :do-not-induct t
           :use ((:instance fn2-env-log-arm-done (fn2-arm-pset '(4 11 12))) (:instance fn2-env-row-phase-snapshot)))))
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
                                       fn2-commit-idp fn2-commit-arm-row-phase fn2-env-j3-move-ok fn2-env-sk
                                       (:e equal) (:e fn2-commit-arm-children) (:e fn2-commit-arm-columns))
                   :do-not-induct t
                   :cases ((and (fn2-commit-idp i fn2-core) (equal (fn2-machine-slot i fn2-core) ,row)))
                   :use ((:instance ,frame) (:instance ,next) (:instance fn2-env-row-phase-snapshot)
                         (:instance ,facts) (:instance ,done) (:instance fn2-env-commit-run-sk)
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
          :hints (("Goal" :induct (fn2-env-j3-rows ids log fn2-core) :in-theory '(fn2-env-j3-rows))
                  ("Subgoal *1/2" :use ((:instance ,one (i (car ids)))))))))))
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
  :doc "fn2-turn preserves J1-J4 (FN2-ENV-J-ROWS, FN2-ENV-J-FRONTIER) at a fixed device log, so that every batch a commit row shows acknowledged stays durable (FN2-ENV-DUR-TURN-INV-PROJECTION). The executor-level lift FN2-EXECUTOR-INV-TURN reduces it to one obligation per cut in *FN2-EXECUTOR-CONTRACT-CUTS*. Proved for the commit visit fn2-commit-run, per phase: :notify, :durable, :fence, :collect, :seal, :draining, :uncertain, :dropping (FN2-ENV-J-ROWS-<PHASE>-ARM), :free (with the visited id a readable row), :install and :publish (with J at the visited id), each with its frontier lemma FN2-ENV-J-FRONTIER-<PHASE>-ARM. Owed, by owner: (1) cross-kind: every non-commit cut (the other kinds' -RUN / -RUN-STUB and observe routes, the wait-source grants, fn2-member-replay; *FN2-COMMIT-TURN-FRAME-BLOCKERS*) must leave the directory's kinds and slots, the commit table, the commit root and the commit-io table, which needs their KIDS/DIR constraints (dispatch-contracts, handler-frames); (2) commit-internal: :dependencies and :log-write keep J given J3 at the visited row (FN2-ENV-J-ROWS-DEPENDENCIES-ARM, FN2-ENV-J-ROWS-LOG-WRITE-ARM; J3 is FN2-ENV-J3-ROW: shared role extents and each counted completion a done write of the phase's roles at its offset in the log, role 2 with its batch's seal); J3 is in FN2-ENV-DUR-INV and this predicate (FN2-ENV-J3-ROWS: FN2-ENV-J3-ROW and its entry clauses FN2-ENV-J3E-ROW), kept by every step but :turn (FN2-ENV-DUR-INV-STEP-BUT-TURN); every commit visit keeps J3 (FN2-ENV-J3-ROWS-COMMIT-RUN, from FN2-ENV-J3-ROWS-<PHASE>-ARM for all thirteen phases); owed: J3 kept by the write/fence handler, whose count rise needs the delivered result to be the first done answer to a take of an uncounted role write of the row (the mailbox/operations-table link to the log, J5) and whose fence-ok rise needs the fence result to answer a fence taken after the row's writes were answered; (3) the visited commit id carries J: a visit of an id that is not a readable row only stops the core (FN2-ENV-J-ROWS-NON-ROW-VISIT), and a readable one is at the slot of a ghost id once FN2-ENV-COMMIT-SLOTS-P holds (FN2-ENV-COMMIT-IDS-COVER, FN2-ENV-J-ROW-OF-COMMIT-IDS); every step but :turn keeps FN2-ENV-COMMIT-SLOTS-P (FN2-ENV-COMMIT-SLOTS-P-STEP-BUT-TURN) and so does every commit visit (FN2-ENV-COMMIT-SLOTS-P-COMMIT-RUN); owed: the other cuts of the turn, with (1).")
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

(local (defthm fn2-env-nth-0 (equal (nth 0 l) (car l))))
(local (defthm fn2-env-nth-1+ (implies (natp n) (equal (nth (+ 1 n) l) (nth n (cdr l))))))
(local (defthm fn2-env-len-cdr (implies (consp l) (equal (len l) (+ 1 (len (cdr l)))))))
(defthm fn2-env-take-index-bound
  (let ((w (fn2-env-take-index slot gen log)))
    (implies w (and (natp w) (< w (len log)) (fn2-dev-takep (nth w log))
                    (equal (nth 1 (nth w log)) slot) (equal (nth 2 (nth w log)) gen))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-env-take-index slot gen log)
           :in-theory '(fn2-env-take-index natp fn2-env-nth-0 fn2-env-nth-1+ fn2-env-len-cdr
                        (:type-prescription fn2-env-take-index) (:t len) atom (:e <)))))
(local (in-theory (disable fn2-env-nth-0 fn2-env-nth-1+ fn2-env-len-cdr)))
(defthm fn2-env-answer-resultp
  (implies (fn2-dev-answer slot gen l)
           (and (consp (fn2-dev-answer slot gen l)) (fn2-dev-resultp (car (fn2-dev-answer slot gen l)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dev-answer slot gen l) :in-theory '(fn2-dev-answer atom))))

;; THE FENCE'S RISE. A write answered done in full before a fence is taken
;; whose first answer is a successful fence result is fenced.
(defthm fn2-env-fence-after-of-later
  (implies (fn2-dev-fence-after-p y) (fn2-dev-fence-after-p (append x y)))
  :hints (("Goal" :induct (len x) :in-theory (disable fn2-dev-answer fn2-dev-done-answer-p))))
(local (defthm fn2-env-cdr-append
  (implies (consp x) (equal (cdr (append x y)) (append (cdr x) y)))))
(defthm fn2-env-fenced-by-later-fence
  (implies (and (fn2-env-done-write-p w x) (fn2-dev-fence-after-p y) (true-listp y))
           (fn2-dev-fenced-write-p w (append x y)))
  :hints (("Goal" :in-theory '(fn2-env-done-write-p fn2-dev-fenced-write-p fn2-env-nth-append-low fn2-env-nthcdr-append
                                fn2-env-done-answer-append fn2-dev-answer-append fn2-env-len-append fn2-env-cdr-append
                                fn2-env-fence-after-of-later fn2-env-done-answer-nil natp nfix fix
                                true-listp-append (:type-prescription true-listp-append)
                                (:type-prescription len) (:type-prescription fn2-dev-answer) (:type-prescription binary-append))
           :cases ((consp (fn2-dev-answer (nth 1 (nth w x)) (nth 2 (nth w x)) (nthcdr (+ 1 w) x)))))))
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
(defthm fn2-env-pool-octets-len
  (implies (and (natp n) (natp addr) (<= (+ addr n) (fn2-pool-data-length fn2-pool)))
           (equal (len (fn2-env-pool-octets n addr fn2-pool)) n))
  :hints (("Goal" :induct (fn2-env-pool-octets n addr fn2-pool) :in-theory (enable fn2-env-pool-octets))))
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
(defun fn2-env-ops-op (s fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (if (and (natp s) (< s (fn2-ops-rows fn2-ops)))
      (list t (fn2-ops-gen s fn2-ops) (fn2-ops-phase s fn2-ops) (fn2-ops-kind s fn2-ops)
            (fn2-ops-owner-kind s fn2-ops) (fn2-ops-owner-slot s fn2-ops) (fn2-ops-owner-gen s fn2-ops)
            (fn2-ops-range-slot s fn2-ops) (fn2-ops-range-gen s fn2-ops)
            (fn2-ops-range-off s fn2-ops) (fn2-ops-range-len s fn2-ops)
            (fn2-ops-storage-offset s fn2-ops) (fn2-ops-fua s fn2-ops)
            (fn2-ops-c0-posted s fn2-ops) (fn2-ops-c0-harvested s fn2-ops) (fn2-ops-c0-event s fn2-ops)
            (fn2-ops-c0-outcome s fn2-ops) (fn2-ops-c0-count s fn2-ops))
    (list nil)))
(defun fn2-env-post-accepted-p (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (let ((tail (fn2-ops-post-tail fn2-ops)) (n (fn2-ops-post-count fn2-ops))
        (capacity (fn2-ops-posted-fifo-length fn2-ops)))
    (and (fn2-post-eligiblep cell slot gen fn2-ops)
         (fn2-post-payloadp cell slot evkind outcome reason count aux0 aux1 fn2-ops)
         (< tail capacity) (< n capacity) (< n *fn2-u60-max*)
         (< capacity 1152921504606846976))))
(defun fn2-env-op-posted (op evkind outcome count)
  ; OP with its terminal cell posted (EVKIND OUTCOME COUNT), unharvested
  (declare (xargs :verify-guards nil))
  (update-nth 13 1 (update-nth 14 0 (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op))))))
(defthm fn2-env-take-index-append-result
  (implies (not (fn2-dev-takep r))
           (equal (fn2-env-take-index s g (append log (list r)))
                  (fn2-env-take-index s g log)))
  :hints (("Goal" :induct (fn2-env-take-index s g log)
           :in-theory '(fn2-env-take-index binary-append car-cons cdr-cons atom (:e fn2-dev-takep) (:e fn2-env-take-index))
           :expand ((append log (list r)) (fn2-env-take-index s g (append log (list r)))
                    (fn2-env-take-index s g (list r))))))
(defthm fn2-env-answer-append-result
  (equal (fn2-dev-answer s g (append l (list r)))
         (if (fn2-dev-answer s g l)
             (append (fn2-dev-answer s g l) (list r))
           (and (fn2-dev-resultp r) (equal (nth 1 r) s) (equal (nth 2 r) g) (list r))))
  :hints (("Goal" :in-theory '(fn2-dev-answer-append fn2-dev-answer atom (:e fn2-dev-answer) car-cons cdr-cons))))
(local (defthm fn2-env-nthcdr-append-list
  (implies (and (natp n) (<= n (len x)))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))
(local (defthm fn2-env-car-append (implies (consp x) (equal (car (append x y)) (car x)))))
(defthm fn2-env-j5-taken-other-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-taken op s log) (true-listp log)
                  (not (and (equal s slot) (equal (nth 1 op) gen))))
             (fn2-env-j5-taken op s (append log (list r)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append-result fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-j5-taken-posted-result
  (let ((r (list :result slot gen evkind outcome count)))
    (implies (and (fn2-env-j5-taken op slot log) (true-listp log)
                  (equal (nth 1 op) gen) (equal (nth 2 op) *fn2-op-phase-submitted*) (equal (nth 13 op) 0))
             (fn2-env-j5-taken (fn2-env-op-posted op evkind outcome count) slot (append log (list r)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append-result fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append fn2-env-op-posted)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take))
           :use ((:instance fn2-env-take-index-bound (gen (nth 1 op)))))))
(defthm fn2-env-ops-op-of-post-result
  (equal (fn2-env-ops-op s (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
         (if (and (equal s slot) (equal cell 0)
                  (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
             (fn2-env-op-posted (fn2-env-ops-op s fn2-ops) evkind outcome count)
           (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize) :do-not-induct t
           :cases ((fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
           :in-theory (e/d (fn2-post-result fn2-count-stray fn2-env-ops-op fn2-env-post-accepted-p fn2-env-op-posted
                            update-nth)
                           (fn2-post-eligiblep fn2-post-payloadp nth)))))
(defthm fn2-env-post-count-of-post-result
  (equal (fn2-ops-post-count (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
         (if (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
             (+ 1 (fn2-ops-post-count fn2-ops))
           (fn2-ops-post-count fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-post-result fn2-count-stray fn2-env-post-accepted-p fn2-ops-post-count
                            update-fn2-ops-stray update-fn2-ops-posted-fifoi update-fn2-ops-post-tail
                            update-fn2-ops-post-count update-nth-array)
                           (fn2-post-eligiblep fn2-post-payloadp nth update-nth)))))
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
         (if (and (equal s (fn2-env-arg 2 action)) (equal (fn2-env-arg 1 action) 0)
                  (mv-nth 0 (fn2-env-post action nil rlog fn2-core)))
             (fn2-env-op-posted (fn2-env-op s fn2-core) (fn2-env-arg 4 action) (fn2-env-arg 5 action) (fn2-env-arg 7 action))
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
(defthm fn2-env-take-append-low
  (implies (and (natp n) (<= n (len x))) (equal (take n (append x y)) (take n x))))
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
(defthm fn2-env-nth-op-posted
  (implies (and (natp i) (< i 13)) (equal (nth i (fn2-env-op-posted op evkind outcome count)) (nth i op)))
  :hints (("Goal" :in-theory (enable fn2-env-op-posted))))
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
(defthm fn2-env-op-of-post-result-core
  (equal (fn2-env-op s (update-fn2-core-ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1
                                                             (fn2-core-ops c))
                                            c))
         (if (and (equal s slot) (equal cell 0)
                  (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
             (fn2-env-op-posted (fn2-env-op s c) evkind outcome count)
           (fn2-env-op s c)))
  :hints (("Goal" :in-theory (quote (fn2-env-op-of-update-ops fn2-env-ops-op-of-post-result fn2-env-op-is-ops-op)))))
(defun fn2-env-post-log (p log r)
  ; the device log after a post: R appended iff the post was accepted on cell 0
  (declare (xargs :verify-guards nil))
  (if p (append log (list r)) log))
(defmacro fn2-env-pr-ops () '(fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
(defun fn2-env-post-ok (cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)
  ; the post was accepted on cell 0: the device log gains its result
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (and (equal cell 0) (fn2-env-post-accepted-p cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)))
(defmacro fn2-env-pr-p () '(fn2-env-post-ok cell slot gen evkind outcome reason count aux0 aux1 (fn2-core-ops c)))
(defmacro fn2-env-pr-log () '(fn2-env-post-log (fn2-env-pr-p) log (list :result slot gen evkind outcome count)))
(in-theory (disable fn2-env-post-ok fn2-env-post-log))
(defthm fn2-env-j5-op-post
  (implies (and (fn2-env-j5-op s id log c) (true-listp log))
           (fn2-env-j5-op s id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (fn2-env-pr-p)) (and (fn2-env-pr-p) (not (equal s slot))) (and (fn2-env-pr-p) (equal s slot)))
           :in-theory (union-theories
                       '(fn2-env-j5-op fn2-env-post-log fn2-env-post-ok fn2-env-op-of-post-result-core fn2-env-ops-frame fn2-env-nth-op-posted
                         fn2-env-j5-fence-ops-frame fn2-env-j5-fence-other-result fn2-env-j5-fence-posted-result
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-fence-live-of-update-fn2-core-ops fn2-commit-row-of-update-fn2-core-ops
                         member-equal (:e member-equal) (:e natp) (:e <) (:e equal) natp)
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-post-accepted-op)))))
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
                       '(fn2-env-owned-fences fn2-env-owned-fence-at fn2-env-op-of-post-result-core fn2-env-nth-op-posted
                         fn2-machine-generation-of-update-fn2-core-ops (:e natp) (:e <) natp)
                       (theory 'minimal-theory)))))
(defthm fn2-env-ops-rows-post
  (equal (fn2-env-ops-rows (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-ops-rows c))
  :hints (("Goal" :in-theory '(fn2-env-ops-frame fn2-post-result-preserves-rows fn2-env-ops-rows))))
(defthm fn2-env-role-live-post
  (equal (fn2-env-role-live id role (update-fn2-core-ops (fn2-env-pr-ops) c))
         (fn2-env-role-live id role c))
  :hints (("Goal" :in-theory (union-theories
                       '(fn2-env-role-live fn2-env-op-of-post-result-core fn2-env-nth-op-posted fn2-env-ops-frame
                         (:e natp) (:e <) natp)
                       (theory 'minimal-theory)))))
(defthm fn2-env-not-takep-result
  (not (fn2-dev-takep (list :result slot gen evkind outcome count)))
  :hints (("Goal" :in-theory (enable fn2-dev-takep))))
(defthm fn2-env-j5-role-post
  (implies (and (fn2-env-j5-role id role log c) (true-listp log))
           (fn2-env-j5-role id role (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :cases ((not (fn2-env-pr-p))
                   (and (fn2-env-pr-p) (not (equal (nth 1 (fn2-env-role-io id role c)) slot)))
                   (and (fn2-env-pr-p) (equal (nth 1 (fn2-env-role-io id role c)) slot)))
           :in-theory (union-theories
                       '(fn2-env-j5-role fn2-env-post-log fn2-env-post-ok fn2-env-op-of-post-result-core fn2-env-ops-frame fn2-env-nth-op-posted
                         fn2-env-role-live-post fn2-env-role-live-booleanp
                         fn2-machine-generation-of-update-fn2-core-ops fn2-machine-phase-of-update-fn2-core-ops
                         fn2-machine-cb-mode-of-update-fn2-core-ops fn2-machine-batch-no-of-update-fn2-core-ops
                         fn2-machine-cb-fence-ok-of-update-fn2-core-ops
                         fn2-env-j5-taken-other-result fn2-env-j5-taken-posted-result
                         fn2-env-take-index-append-result fn2-env-not-takep-result fn2-env-nth-append-low
                         fn2-env-role-written fn2-env-written-extends (:type-prescription fn2-env-role-written)
                         (:e member-equal) (:e natp) (:e <) (:e equal) natp nfix (:e nfix))
                       (theory 'minimal-theory))
           :use ((:instance fn2-env-post-accepted-op)
                 (:instance fn2-env-take-index-bound (slot (nth 1 (fn2-env-role-io id role c)))
                            (gen (nth 1 (fn2-env-op (nth 1 (fn2-env-role-io id role c)) c))))))))
(defthm fn2-env-j5-roles-post
  (implies (and (fn2-env-j5-roles id log c) (true-listp log))
           (fn2-env-j5-roles id (fn2-env-pr-log) (update-fn2-core-ops (fn2-env-pr-ops) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn2-env-j5-roles fn2-env-j5-role-post fn2-env-role-live-post
                         fn2-machine-phase-of-update-fn2-core-ops fn2-machine-cb-issued-of-update-fn2-core-ops
                         fn2-machine-cb-done-of-update-fn2-core-ops)
                       (theory 'minimal-theory)))))
(defthm fn2-env-j6-row-post
  (equal (fn2-env-j6-row id (update-fn2-core-ops (fn2-env-pr-ops) c)) (fn2-env-j6-row id c))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn2-env-j6-row fn2-env-role-live-post fn2-env-ops-frame fn2-env-op-of-post-result-core
                         fn2-env-nth-op-posted fn2-commit-idp-of-update-fn2-core-ops
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

;; J5 ACROSS :TAKE. The device takes the outbox head: the ack moves that op
;; from queued to its ack phase (submitted for a completion kind), and a
;; non-completion kind is finished at once (FN2-ENV-TAKE-OP); every other
;; op and every other child's reader is unchanged (FN2-ENV-TAKE-FRAMES). The
;; log gains the take, so the taken op's first take is the new last entry
;; (FN2-ENV-J5-TAKEN-TAKE) and every other op's take and answer stay
;; (FN2-ENV-J5-TAKEN-OTHER-TAKE). A taken fence follows the writes its rise
;; fences by J2 (FN2-ENV-FENCE-PREFIX-OF-J2).
(defthm fn2-env-outbox-ack-1-head
  (implies (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok)
           (let ((h (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops))
                 (g (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops)))
             (and (natp h) (< h (fn2-ops-rows fn2-ops))
                  (equal (fn2-ops-gen h fn2-ops) g)
                  (equal (fn2-ops-phase h fn2-ops) *fn2-op-phase-queued*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-outbox-ack fn2-outbox-prefixp fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
           :expand ((fn2-outbox-prefixp 1 (fn2-ops-out-head fn2-ops) fn2-ops)))))
(defthm fn2-env-ops-op-of-outbox-ack-1
  (implies (and (fn2-opsp fn2-ops) (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok))
           (equal (fn2-env-ops-op s (mv-nth 1 (fn2-outbox-ack 1 fn2-ops)))
                  (let ((h (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops)))
                    (if (equal s h)
                        (update-nth 2 (fn2-op-ack-phase (nth 3 (fn2-env-ops-op h fn2-ops))) (fn2-env-ops-op s fn2-ops))
                      (fn2-env-ops-op s fn2-ops)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-outbox-ack fn2-outbox-prefixp fn2-op-phase-code fn2-op-handle-code fn2-op-slotp
                            fn2-outbox-submit-prefix fn2-env-ops-op)
                           (fn2-op-ack-phase fn2-opsp))
           :expand ((fn2-outbox-prefixp 1 (fn2-ops-out-head fn2-ops) fn2-ops)
                    (fn2-outbox-submit-prefix 1 fn2-ops)))))
(defthm fn2-env-outbox-peek-0
  (implies (and (fn2-opsp fn2-ops) (equal (mv-nth 0 (fn2-outbox-peek 0 fn2-ops)) :ok))
           (and (equal (mv-nth 1 (fn2-outbox-peek 0 fn2-ops)) (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops))
                (equal (mv-nth 2 (fn2-outbox-peek 0 fn2-ops)) (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-outbox-peek) (fn2-opsp)))))
(defthm fn2-env-ops-op-of-op-finish-other
  (implies (and (fn2-opsp fn2-ops) (not (equal s h)))
           (equal (fn2-env-ops-op s (mv-nth 1 (fn2-op-finish h g fn2-ops))) (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
(defthm fn2-env-ops-op-of-op-finish-self
  (implies (fn2-opsp fn2-ops)
           (let ((o (fn2-env-ops-op h (mv-nth 1 (fn2-op-finish h g fn2-ops)))))
             (or (equal o (fn2-env-ops-op h fn2-ops))
                 (member-equal (nth 2 o) (list *fn2-op-phase-free* *fn2-op-phase-retired*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-op-finish fn2-op-recycle fn2-ops-clear-row fn2-op-phase-code fn2-op-handle-code
                            fn2-op-slotp fn2-env-ops-op)
                           (fn2-opsp)))))
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
(defthm fn2-env-outbox-ack-refused
  (implies (not (equal (mv-nth 0 (fn2-outbox-ack n fn2-ops)) :ok))
           (equal (mv-nth 1 (fn2-outbox-ack n fn2-ops)) fn2-ops))
  :hints (("Goal" :in-theory (enable fn2-outbox-ack))))
(defthm fn2-env-outbox-ack-1-head-op
  (implies (equal (mv-nth 0 (fn2-outbox-ack 1 fn2-ops)) :ok)
           (let ((o (fn2-env-ops-op (fn2-ops-out-sloti (fn2-ops-out-head fn2-ops) fn2-ops) fn2-ops)))
             (and (nth 0 o) (equal (nth 1 o) (fn2-ops-out-geni (fn2-ops-out-head fn2-ops) fn2-ops))
                  (equal (nth 2 o) *fn2-op-phase-queued*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn2-env-ops-op nth-0-cons nth-add1 (:e zp) (:e nth) car-cons cdr-cons
                                               (:e binary-+) (:e equal) zp nth)
                                             (theory 'minimal-theory))
           :use fn2-env-outbox-ack-1-head)))
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
(defthm fn2-env-take-index-append
  (equal (fn2-env-take-index s g (append log (list e)))
         (or (fn2-env-take-index s g log)
             (and (fn2-dev-takep e) (equal (nth 1 e) s) (equal (nth 2 e) g) (len log))))
  :hints (("Goal" :induct (fn2-env-take-index s g log)
           :in-theory '(fn2-env-take-index binary-append car-cons cdr-cons atom len (:e fn2-env-take-index) fix
                        (:type-prescription fn2-env-take-index) (:e len) (:e binary-append))
           :expand ((append log (list e)) (fn2-env-take-index s g (append log (list e)))
                    (fn2-env-take-index s g (list e))))))
(defthm fn2-env-j5-taken-other-take
  (implies (and (fn2-env-j5-taken op s log) (true-listp log) (fn2-dev-takep e) (not (equal s (nth 1 e))))
           (fn2-env-j5-taken op s (append log (list e))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append fn2-env-answer-append-result
                            fn2-env-nthcdr-append-list fn2-env-car-append fn2-env-consp-append)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take fn2-dev-takep))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-nthcdr-len-append
  (implies (true-listp log) (equal (nthcdr (+ 1 (len log)) (append log (list e))) nil)))
(defthm fn2-env-answer-of-nil (equal (fn2-dev-answer s g nil) nil))
(defthm fn2-env-j5-taken-take
  (implies (and (fn2-env-j5-taken o slot log) (true-listp log) (equal (nth 2 o) *fn2-op-phase-queued*)
                (fn2-dev-takep e) (equal (nth 1 e) slot) (equal (nth 2 e) (nth 1 o)))
           (and (fn2-env-j5-taken (update-nth 2 *fn2-op-phase-submitted* o) slot (append log (list e)))
                (equal (fn2-env-take-index slot (nth 1 o) (append log (list e))) (len log))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-taken fn2-env-take-index-append fn2-env-nthcdr-len-append fn2-env-answer-of-nil)
                           (fn2-env-take-index fn2-dev-answer nthcdr binary-append take fn2-dev-takep)))))
(defthm fn2-env-j5-fence-other-take
  (implies (and (fn2-env-j5-fence id op s log c) (true-listp log) (fn2-dev-takep e) (not (equal s (nth 1 e))))
           (fn2-env-j5-fence id op s (append log (list e)) c))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-env-j5-fence fn2-env-take-index-append fn2-env-take-append-low
                            fn2-env-j5-taken-other-take fn2-env-nth-append-low)
                           (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take binary-append nth fn2-dev-takep))
           :use ((:instance fn2-env-take-index-bound (slot s) (gen (nth 1 op)))))))
(defthm fn2-env-nth-len-append (equal (nth (len x) (append x (list e))) e))
(defthm fn2-env-take-len-true-list (implies (true-listp x) (equal (take (len x) x) x)))
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
(defun fn2-env-log+ (log e)
  ; the device log after a step whose entry is E (nil: none)
  (declare (xargs :verify-guards nil))
  (append log (if e (list e) nil)))
(defmacro fn2-env-tk-e () '(mv-nth 0 (fn2-env-take nil image c)))
(defmacro fn2-env-tk-c () '(mv-nth 1 (fn2-env-take nil image c)))
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
(defthm fn2-env-pool-octets-addr-natp
  (implies (consp (fn2-env-pool-octets n addr fn2-pool)) (natp addr))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fn2-env-pool-octets n addr fn2-pool)))))
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
(defthm fn2-env-j5-taken-queued-untaken
  (implies (and (fn2-env-j5-taken op slot log) (equal (nth 2 op) *fn2-op-phase-queued*) (equal (nth 1 op) g))
           (not (fn2-env-take-index slot g log)))
  :hints (("Goal" :in-theory '(fn2-env-j5-taken (:e equal)))))
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
                                        nth-update-nth append-to-nil natp nfix (:e equal) (:e nfix) (:e natp) (:e <))
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
(defthm fn2-env-j5-roles-take
  (implies (and (fn2-corep c) (fn2-core-wfp c) (true-listp log)
                (fn2-env-j5-roles id log c) (fn2-env-j6-row id c) (fn2-commit-idp id c))
           (fn2-env-j5-roles id (fn2-env-log+ log (fn2-env-tk-e)) (fn2-env-tk-c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-j5-roles fn2-env-take-frames fn2-env-role-live-take-of-j5-role
                                        fn2-env-j5-role-take (:e natp) (:e equal))
                                      (theory 'minimal-theory)))))
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
;; J5 ACROSS THE FRAME STEPS. :accept-result, :clock and :signal update the
;; ops table keeping every op (FN2-ENV-OPS-KEPT: an op is unchanged, or an
;; accept keeps its head fields), and an op the row could account for is
;; never an accept, so J5 and J6 hold over the kept table
;; (FN2-ENV-J5-ROWS-KEPT). :epoch writes the extents child and :loan-write
;; the pool, which J5 does not read; J6 reads the pool, so J6 across
;; :loan-write is FN2-POOL-CONSERVATION's (the loan's range is disjoint from
;; the roles').
(defun fn2-env-op-kept (o2 o)
  ; O2 is O, or O is an accept whose head fields (validity .. owner-gen) O2 keeps
  (declare (xargs :verify-guards nil))
  (or (equal o2 o)
      (and (equal (nth 3 o) *fn2-action-accept*)
           (equal (nth 0 o2) (nth 0 o)) (equal (nth 1 o2) (nth 1 o)) (equal (nth 2 o2) (nth 2 o))
           (equal (nth 3 o2) (nth 3 o)) (equal (nth 4 o2) (nth 4 o)) (equal (nth 5 o2) (nth 5 o))
           (equal (nth 6 o2) (nth 6 o)))))
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
           :in-theory (union-theories '(fn2-env-j5-roles fn2-env-j5-role-kept fn2-env-role-live-kept
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
(defthm fn2-env-ops-op-accept-kind
  (implies (and (fn2-op-slotp slot fn2-ops) (equal (fn2-ops-kind slot fn2-ops) *fn2-action-accept*))
           (equal (nth 3 (fn2-env-ops-op slot fn2-ops)) *fn2-action-accept*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-env-ops-op fn2-op-slotp))))
(defthm fn2-env-ops-op-of-peer-sets
  (and (equal (fn2-env-ops-op s (fn2-ops-set-peer-family i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-port i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w0 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w1 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w2 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-ops-set-peer-w3 i v y)) (fn2-env-ops-op s y))
       (equal (fn2-env-ops-op s (fn2-count-stray y)) (fn2-env-ops-op s y)))
  :hints (("Goal" :in-theory (enable fn2-env-ops-op fn2-ops-set-peer-family fn2-ops-set-peer-port fn2-ops-set-peer-w0
                                     fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3 fn2-count-stray
                                     update-fn2-ops-peer-family$ai update-fn2-ops-peer-port$ai update-fn2-ops-peer-w0$ai
                                     update-fn2-ops-peer-w1$ai update-fn2-ops-peer-w2$ai update-fn2-ops-peer-w3$ai
                                     update-fn2-ops-stray update-nth-array))))
(defthm fn2-env-car-update-nth
  (equal (car (update-nth n v l)) (if (zp n) v (car l)))
  :rule-classes nil
  :hints (("Goal" :expand ((update-nth n v l)))))
(defthm fn2-env-car-op-posted
  (equal (car (fn2-env-op-posted op evkind outcome count)) (car op))
  :hints (("Goal" :in-theory (enable fn2-env-op-posted)
           :use ((:instance fn2-env-car-update-nth (n 13) (v 1)
                            (l (update-nth 14 0 (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op))))))
                 (:instance fn2-env-car-update-nth (n 14) (v 0)
                            (l (update-nth 15 evkind (update-nth 16 outcome (update-nth 17 count op)))))
                 (:instance fn2-env-car-update-nth (n 15) (v evkind) (l (update-nth 16 outcome (update-nth 17 count op))))
                 (:instance fn2-env-car-update-nth (n 16) (v outcome) (l (update-nth 17 count op)))
                 (:instance fn2-env-car-update-nth (n 17) (v count) (l op))))))
(defthm fn2-env-ops-op-of-post-accept-result
  (fn2-env-op-kept (fn2-env-ops-op s (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce family port
                                                             w0 w1 w2 w3 fn2-ops))
                   (fn2-env-ops-op s fn2-ops))
  :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (e/d (fn2-post-accept-result fn2-env-op-kept fn2-env-ops-op-of-peer-sets
                            fn2-env-ops-op-of-post-result fn2-env-nth-op-posted fn2-env-car-op-posted)
                           (fn2-post-result fn2-peer-recordp fn2-env-ops-op fn2-env-op-posted fn2-count-stray
                            fn2-ops-set-peer-family fn2-ops-set-peer-port fn2-ops-set-peer-w0
                            fn2-ops-set-peer-w1 fn2-ops-set-peer-w2 fn2-ops-set-peer-w3))
           :use ((:instance fn2-env-ops-op-accept-kind)))))
(defthm fn2-env-ops-op-of-post-clock-signal
  (and (equal (fn2-env-ops-op s (fn2-post-clock mono real flags fn2-ops)) (fn2-env-ops-op s fn2-ops))
       (equal (fn2-env-ops-op s (fn2-post-signal bits fn2-ops)) (fn2-env-ops-op s fn2-ops)))
  :hints (("Goal" :in-theory (e/d (fn2-env-ops-op fn2-post-clock fn2-post-signal)
                                  (binary-logior binary-logand fn2-saturating-inc60 unsigned-byte-p)))))
(defthm fn2-env-op-kept-refl (fn2-env-op-kept o o) :hints (("Goal" :in-theory (enable fn2-env-op-kept))))
; An ops update X(fn2-ops) that keeps every op: the core's ops become X's.
(defmacro fn2-env-ops-kept-events (name call)
  ; CALL: the update applied to (fn2-core-ops c), e.g. (fn2-post-signal bits (fn2-core-ops c))
  (let ((from (fn2-columns-sym name "-KEPT-FROM")) (all (fn2-columns-sym name "-KEPT")))
    `(progn
       (defthm ,from
         (fn2-env-ops-kept-from s k ,call c)
         :hints (("Goal" :induct (fn2-env-ops-kept-from s k ,call c)
                  :in-theory '(fn2-env-ops-kept-from fn2-env-op-is-ops-op fn2-env-op-kept-refl
                               fn2-env-ops-op-of-post-accept-result fn2-env-ops-op-of-post-clock-signal))))
       (defthm ,all
         (implies (fn2-corep c) (fn2-env-ops-kept ,call c))
         :hints (("Goal" :in-theory (e/d (fn2-env-ops-kept fn2-env-ops-rows ,from) (fn2-env-ops-kept-from fn2-ops-rows))
                  :use ((:instance fn2-core-ops-type (fn2-core c)))))))))
(fn2-env-ops-kept-events fn2-env-post-accept
  (fn2-post-accept-result slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3 (fn2-core-ops c)))
(fn2-env-ops-kept-events fn2-env-post-clock (fn2-post-clock mono real flags (fn2-core-ops c)))
(fn2-env-ops-kept-events fn2-env-post-signal (fn2-post-signal bits (fn2-core-ops c)))
; J5 reads no child but the machine table, commit-io, ops and (J6) pool: the
; extents and the pool frames.
(defmacro fn2-env-j5-child-frame-events (upd)
  (progn$
    `(progn
       (defthm ,(fn2-columns-sym 'fn2-env-j5-readers (concatenate 'string "-OF-" (symbol-name upd)))
         (and (equal (fn2-env-io u (,upd x c)) (fn2-env-io u c))
              (equal (fn2-env-op s (,upd x c)) (fn2-env-op s c))
              (equal (fn2-env-ops-rows (,upd x c)) (fn2-env-ops-rows c))
              (equal (fn2-env-role-io id role (,upd x c)) (fn2-env-role-io id role c))
              (equal (fn2-env-role-offset id role (,upd x c)) (fn2-env-role-offset id role c))
              (equal (fn2-env-role-written id role f log (,upd x c)) (fn2-env-role-written id role f log c)))
         :hints (("Goal" :in-theory (e/d (fn2-env-io fn2-env-op fn2-env-ops-rows fn2-env-role-io fn2-env-role-offset
                                          fn2-env-role-written)
                                         (fn2-env-written-from)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-fence (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-fence id op s log (,upd x c)) (fn2-env-j5-fence id op s log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-fence) (fn2-env-role-written fn2-env-j5-taken fn2-env-take-index take)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-op (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-op s id log (,upd x c)) (fn2-env-j5-op s id log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-op) (fn2-env-op fn2-env-io fn2-env-j5-fence)))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-ops (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-ops s k id log (,upd x c)) (fn2-env-j5-ops s k id log c))
         :hints (("Goal" :induct (fn2-env-j5-ops s k id log c) :in-theory (disable fn2-env-j5-op))))
       (defthm ,(fn2-columns-sym 'fn2-env-owned-fences (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-owned-fences s k id (,upd x c)) (fn2-env-owned-fences s k id c))
         :hints (("Goal" :induct (fn2-env-owned-fences s k id c) :in-theory (disable fn2-env-op))))
       (defthm ,(fn2-columns-sym 'fn2-env-j5-row (concatenate 'string "-OF-" (symbol-name upd)))
         (equal (fn2-env-j5-row id log (,upd x c)) (fn2-env-j5-row id log c))
         :hints (("Goal" :in-theory (e/d (fn2-env-j5-row fn2-env-j5-roles fn2-env-j5-role fn2-env-role-live)
                                         (fn2-env-j5-ops fn2-env-owned-fences fn2-env-op fn2-env-role-io
                                          fn2-env-role-offset fn2-env-role-written fn2-env-j5-taken fn2-env-take-index
                                          fn2-env-j5-take-ok))))))))
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
;; J5 ACROSS :ADMIT, the ops table. Admission's callees write the pool,
;; sched, control, commit table, extents, members, settled, commit-io and
;; root children, never the ops table (FN2-ENV-OK carried by each callee):
;; every op and the ops rows are unchanged (FN2-ENV-OP-OF-ADMIT,
;; FN2-ENV-OPS-ROWS-OF-ADMIT).
(defun-nx fn2-env-ok (b a) (equal (nth 1 b) (nth 1 a)))
(defthm fn2-env-ok-refl (fn2-env-ok a a))
(defthm fn2-env-ok-of-nth
  (implies (and (equal (nth 1 b) (nth 1 x)) (fn2-env-ok x a)) (fn2-env-ok b a))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-env-ok))))
(in-theory (disable fn2-env-ok))
(make-event (value (cons 'progn (fn2-env-rel-forms
  (fn2-ctf-postorder-new '(fn2-core-stop fn2-core-reserve fn2-commit-keep-pool fn2-commit-unwind-pool fn2-commit-release-pools
                           fn2-commit-reserve-extent fn2-commit-prepare-root fn2-commit-ready fn2-commit-put-members fn2-exec-wake
                           fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes)
                         (w state))
  'fn2-env-ok 1 nil 'fn2-commit))))
(defthm fn2-commit-reserve-pools-fn2-env-ok
  (implies (fn2-env-ok fn2-core fn2-rel-c0)
           (fn2-env-ok (mv-nth 1 (fn2-commit-reserve-pools left id owner-gen fn2-core)) fn2-rel-c0))
  :hints (("Goal" :induct (fn2-commit-reserve-pools left id owner-gen fn2-core)
           :in-theory (union-theories '(fn2-commit-reserve-pools fn2-core-reserve-fn2-env-ok
                                        fn2-commit-keep-pool-fn2-env-ok fn2-commit-unwind-pool-fn2-env-ok)
                                      (theory 'minimal-theory)))))
(defthm fn2-env-commit-start-ok
  (implies (fn2-env-ok fn2-core c0)
           (fn2-env-ok (mv-nth 1 (fn2-commit-start id members first-key mode partner fn2-core)) c0))
  :hints (("Goal" :in-theory (union-theories
                              '(fn2-commit-start fn2-commit-reserve-extent-fn2-env-ok fn2-commit-reserve-pools-fn2-env-ok
                                fn2-commit-release-pools-fn2-env-ok fn2-commit-prepare-root-fn2-env-ok fn2-commit-ready-fn2-env-ok
                                fn2-core-stop-fn2-env-ok
                                fn2-commit-write+phase+generation+principal-slot+deadline+stopped+batch-no+member-count+first-key+partner+cb-mode+cb-stage+cb-cursor+cb-issued+cb-done+cb-bytes+cb-failed+outcome+cb-reason+cb-fence-live+cb-fence-ok+cb-deps-ok+cb-log-ok+cb-published+cb-acks+cb-seal-len+cb-wrote+cb-open+dep-bytes+rec-bytes-fn2-env-ok)
                              (theory 'fn2-arm-frame-base))
           :do-not-induct t)))
(defthm fn2-env-admit-ok
  ; admission never writes the ops table
  (implies (fn2-env-ok fn2-core c0)
           (fn2-env-ok (fn2-env-admit members mode fn2-core) c0))
  :hints (("Goal" :in-theory (union-theories '(fn2-env-admit fn2-commit-admit-keyed fn2-env-commit-start-ok
                                               fn2-commit-put-members-fn2-env-ok fn2-core-stop-fn2-env-ok fn2-exec-wake-fn2-env-ok)
                                             (theory 'fn2-arm-frame-base)))))
(defthm fn2-env-op-of-admit
  (equal (fn2-env-op s (fn2-env-admit members mode c)) (fn2-env-op s c))
  :hints (("Goal" :in-theory (e/d (fn2-env-ok fn2-env-op fn2-core-ops) (fn2-env-admit))
           :use ((:instance fn2-env-admit-ok (fn2-core c) (c0 c))))))
(defthm fn2-env-ops-rows-of-admit
  (equal (fn2-env-ops-rows (fn2-env-admit members mode c)) (fn2-env-ops-rows c))
  :hints (("Goal" :in-theory (e/d (fn2-env-ok fn2-env-ops-rows fn2-core-ops) (fn2-env-admit))
           :use ((:instance fn2-env-admit-ok (fn2-core c) (c0 c))))))
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
