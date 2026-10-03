; Typed owner syncer custody (HST-046/PRF-1252).  This slice partitions a
; qualified thread allowance; it does not claim user-bank or full work,
; disk/descriptor/identity accounting.  Resident here is thread stack plus
; runtime only; captured batch buffers remain in the served memory credits.
(in-package "ACL2")
(include-book "resource-vector-exec")
(include-book "profile-limits")

(defun fn-ros-worker-vector (workers resident-each)
  (declare (xargs :guard (and (natp workers) (natp resident-each))))
  (list (* workers resident-each) 0 0 workers 0 0 0 0 0))

; The caller supplies the qualified THREADS allowance and an ACL2-selected
; baseline/rescue partition.  Their sum plus the syncer must fit BEFORE
; any store.  Installation allocates the three fixed ledger roles once.
; No interpretation of "spare threads" is made by host code.
(defun fn-ros-install (threads baseline-workers rescue-workers resident-each fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (if (not (and (natp threads) (natp baseline-workers) (natp rescue-workers)
                (natp resident-each)
                (<= (+ baseline-workers rescue-workers 1) threads)
                (<= resident-each *fn-rl-word-max*)))
      (mv :invalid-worker-partition fn-resource-ledger)
    (mv-let (word fn-resource-ledger)
      (fn-rl-install (fn-ros-worker-vector threads resident-each)
                     (fn-ros-worker-vector baseline-workers resident-each)
                     (fn-ros-worker-vector rescue-workers resident-each)
                     3 fn-resource-ledger)
      (if (eq word :installed)
          (let ((fn-resource-ledger
                 (update-fn-rl-worker-resident resident-each fn-resource-ledger)))
            (mv word fn-resource-ledger))
        (mv word fn-resource-ledger)))))

; The parent's :hold producer already reserves the fixed thread allowance,
; including this syncer.  A child projection names its ONE syncer role,
; never fabricates historical "spare" threads or rescue capability.  The
; parent still owns baseline/recovery reservations; this child is not a new
; claim R >= W.  Ledger setup/refusal work belongs to that parent's funded
; startup/runtime baseline, not to the worker's eventual draw.
(defun fn-ros-install-syncer (qualified-threads observed-stack fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (if (not (and (posp qualified-threads) (natp observed-stack)))
      (mv :invalid-worker-grant fn-resource-ledger)
    (fn-ros-install 1 0 0
                    (+ observed-stack (* 1048576 (fn-profile-limit :thread-runtime-mib)))
                    fn-resource-ledger)))

(defun fn-ros-token (gen)
  (declare (xargs :guard t))
  (list :resource :owner 2 gen))

(defun fn-ros-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 4)
       (eq (car token) :resource) (eq (cadr token) :owner)
       (equal (nth 2 token) 2) (natp (nth 3 token))))

(defun fn-ros-livep (token fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-ros-tokenp token) (fn-rl-wfp fn-resource-ledger)
       (< 2 (fn-rl-count fn-resource-ledger))
       (equal (fn-rl-phasesi 2 fn-resource-ledger) 1)
       (equal (fn-rl-gensi 2 fn-resource-ledger) (nth 3 token))))

; Called in the owner section BEFORE actor construction/spawn.  A spawn
; refusal needs an affirmative no-actor-created physical receipt to release;
; an unwind after creation must join the actor, not synthesize that receipt.
(defun fn-ros-issue (operation-gen fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond ((not (and (natp operation-gen) (<= operation-gen *fn-rl-word-max*)))
         (mv :unrepresentable-operation-generation nil fn-resource-ledger))
        ((not (and (fn-rl-wfp fn-resource-ledger)
                    (equal (fn-rl-count fn-resource-ledger) 3)))
         (mv :not-installed nil fn-resource-ledger))
        (t (mv-let (word gen fn-resource-ledger)
             (fn-rl-draw 2 (fn-ros-worker-vector 1 (fn-rl-worker-resident fn-resource-ledger))
                          fn-resource-ledger)
             (if (not (eq word :drawn)) (mv word nil fn-resource-ledger)
               (let* ((fn-resource-ledger
                       (update-fn-rl-worker-operation operation-gen fn-resource-ledger))
                      (fn-resource-ledger (update-fn-rl-worker-physical 0 fn-resource-ledger))
                      (fn-resource-ledger (update-fn-rl-worker-outcome 0 fn-resource-ledger)))
                 (mv :drawn (fn-ros-token gen) fn-resource-ledger)))))))

(defun fn-ros-settle-ready (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger)
                              (< 2 (fn-rl-count fn-resource-ledger)))))
  (if (and (equal (fn-rl-worker-physical fn-resource-ledger) 1)
           (equal (fn-rl-worker-outcome fn-resource-ledger) 1))
      (fn-rl-settle 2 (fn-rl-gensi 2 fn-resource-ledger) fn-resource-ledger)
    (mv :pending fn-resource-ledger)))

; Receipt is the actor controller's observed physical TERMINAL or observed
; NO-ACTOR-CREATED; timeout, failed join and application result refuse here.
(defun fn-ros-physical (token receipt fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond ((not (fn-ros-livep token fn-resource-ledger)) (mv :stale fn-resource-ledger))
        ((not (member-eq receipt '(:terminal :no-actor-created)))
         (mv :pending fn-resource-ledger))
        (t (let ((fn-resource-ledger (update-fn-rl-worker-physical 1 fn-resource-ledger)))
             (fn-ros-settle-ready fn-resource-ledger)))))

(defun fn-ros-outcome (token operation-gen fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond ((not (and (fn-ros-livep token fn-resource-ledger)
                   (equal operation-gen (fn-rl-worker-operation fn-resource-ledger))))
         (mv :stale fn-resource-ledger))
        (t (let ((fn-resource-ledger (update-fn-rl-worker-outcome 1 fn-resource-ledger)))
             (fn-ros-settle-ready fn-resource-ledger)))))

; Startup/shutdown observation is bounded: one fixed syncer draw; never the
; abstraction FN-RL-BANK's whole table walk on a served path.
(defun fn-ros-drainedp (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-rl-wfp fn-resource-ledger)
       (equal (fn-rl-count fn-resource-ledger) 3)
       (equal (fn-rl-phasesi 2 fn-resource-ledger) 0)))

; The real owner issue/receipt entries have bounded stobj guards. Bootstrap
; install guards and the native physical-receipt boundary remain separate.
(verify-guards fn-ros-livep
 :hints (("Goal" :in-theory (enable fn-ros-tokenp fn-rl-wfp))))
(verify-guards fn-ros-issue
 :hints (("Goal" :in-theory (disable fn-rl-draw fn-rl-wfp))))
(verify-guards fn-ros-settle-ready
 :hints (("Goal" :in-theory (enable fn-rl-wfp))))
(verify-guards fn-ros-physical
 :hints (("Goal" :in-theory (enable fn-ros-livep fn-rl-wfp))))
(verify-guards fn-ros-outcome
 :hints (("Goal" :in-theory (enable fn-ros-livep fn-rl-wfp))))
(verify-guards fn-ros-drainedp
 :hints (("Goal" :in-theory (enable fn-rl-wfp))))

(encapsulate ()
(local
 (defthm fn-ros-operation-update-keeps-wfp
  (equal (fn-rl-wfp (update-fn-rl-worker-operation v ledger)) (fn-rl-wfp ledger))
  :hints (("Goal" :in-theory (enable fn-rl-wfp)))))
(local
 (defthm fn-ros-operation-update-keeps-type
  (implies (and (fn-resource-ledgerp ledger) (unsigned-byte-p 64 v))
           (fn-resource-ledgerp (update-fn-rl-worker-operation v ledger)))
  :hints (("Goal" :in-theory (enable fn-resource-ledgerp unsigned-byte-p)))))
(local
 (defthm fn-ros-physical-update-keeps-wfp
  (equal (fn-rl-wfp (update-fn-rl-worker-physical v ledger)) (fn-rl-wfp ledger))
  :hints (("Goal" :in-theory (enable fn-rl-wfp)))))
(local
 (defthm fn-ros-physical-update-keeps-type
  (implies (and (fn-resource-ledgerp ledger) (unsigned-byte-p 1 v))
           (fn-resource-ledgerp (update-fn-rl-worker-physical v ledger)))
  :hints (("Goal" :in-theory (enable fn-resource-ledgerp unsigned-byte-p)))))
(local
 (defthm fn-ros-outcome-update-keeps-wfp
  (equal (fn-rl-wfp (update-fn-rl-worker-outcome v ledger)) (fn-rl-wfp ledger))
  :hints (("Goal" :in-theory (enable fn-rl-wfp)))))
(local
 (defthm fn-ros-outcome-update-keeps-type
  (implies (and (fn-resource-ledgerp ledger) (unsigned-byte-p 1 v))
           (fn-resource-ledgerp (update-fn-rl-worker-outcome v ledger)))
  :hints (("Goal" :in-theory (enable fn-resource-ledgerp unsigned-byte-p)))))

(defthm fn-ros-issue-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 2 (fn-ros-issue operation-gen ledger)))
       (fn-rl-wfp (mv-nth 2 (fn-ros-issue operation-gen ledger)))))
 :hints (("Goal" :in-theory
   (e/d (fn-ros-issue unsigned-byte-p)
        (fn-rl-draw fn-rl-wfp fn-resource-ledgerp
         update-fn-rl-worker-operation update-fn-rl-worker-physical update-fn-rl-worker-outcome)))))
(defthm fn-ros-settle-ready-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 1 (fn-ros-settle-ready ledger)))
       (fn-rl-wfp (mv-nth 1 (fn-ros-settle-ready ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-ros-settle-ready)
                               (fn-rl-settle fn-rl-wfp fn-resource-ledgerp)))))
(defthm fn-ros-physical-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 1 (fn-ros-physical token receipt ledger)))
       (fn-rl-wfp (mv-nth 1 (fn-ros-physical token receipt ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-ros-physical)
              (fn-ros-settle-ready fn-rl-wfp fn-resource-ledgerp update-fn-rl-worker-physical)))))
(defthm fn-ros-outcome-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (mv-nth 1 (fn-ros-outcome token operation-gen ledger)))
       (fn-rl-wfp (mv-nth 1 (fn-ros-outcome token operation-gen ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-ros-outcome)
              (fn-ros-settle-ready fn-rl-wfp fn-resource-ledgerp update-fn-rl-worker-outcome)))))
)

(defthm fn-ros-timeout-keeps-custody-by-definition
 (implies (not (member-eq receipt '(:terminal :no-actor-created)))
          (equal (mv-nth 1 (fn-ros-physical token receipt ledger)) ledger))
 :hints (("Goal" :in-theory (enable fn-ros-physical))))
(defthm fn-ros-unmatched-outcome-keeps-custody-by-definition
 (implies (not (equal operation-gen (fn-rl-worker-operation ledger)))
          (equal (mv-nth 1 (fn-ros-outcome token operation-gen ledger)) ledger))
 :hints (("Goal" :in-theory (enable fn-ros-outcome))))

(in-theory (disable fn-ros-worker-vector fn-ros-install fn-ros-install-syncer fn-ros-token fn-ros-tokenp
                    fn-ros-livep fn-ros-issue fn-ros-settle-ready
                    fn-ros-physical fn-ros-outcome fn-ros-drainedp))
