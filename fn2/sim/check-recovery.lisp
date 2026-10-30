; RECOVERY (ROUND2 §F.1): the real B5 recovery row, driven through the executor,
; the simulated adapter and the router after death; the harness's own ground
; truth about the durable image; and the check that classification, recovered
; history and witness outcome agree with the fault profile and that evidence
; through fn2-lm-recovery-allowedp. Lists are test evidence only.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "sim")
(include-book "check-death")
(fn2-book-layer :b)

(local (defthm fn2-b-rec-countdown
 (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))) :rule-classes nil))
(local (defthm fn2-b-rec-count-op (o-p (nfix left)) :rule-classes nil))

(defun fn2-b-rec-flight (left fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)))
 (if (zp left) nil
  (if (equal (fn2-sim-active (- left 1) fn2-sim) 1) (- left 1)
   (fn2-b-rec-flight (- left 1) fn2-sim))))
(defun fn2-b-rec-posted (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-post-count fn2-ops) (not (zp n))))

; One adapter or scheduler action per step: harvest, hand over, complete
; (READ-FAULT applies to the first READS completions), or run principal 0.
(defun fn2-b-rec-drive (fuel id read-fault reads fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)
  :hints (("Goal" :use ((:instance fn2-b-rec-countdown (left fuel)) (:instance fn2-b-rec-count-op (left fuel))) :in-theory nil))))
 (cond
  ((zp fuel) (mv :fuel fn2-core fn2-sim fn2-own))
  ((= (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*) (mv :done fn2-core fn2-sim fn2-own))
  ((fn2-b-rec-posted fn2-core)
   (b* (((mv & & & & & fn2-core) (fn2-exec-harvest fn2-core)))
    (fn2-b-rec-drive (- fuel 1) id read-fault reads fn2-core fn2-sim fn2-own)))
  ((consp (fn2-b-outbox fn2-core))
   (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)))
    (fn2-b-rec-drive (- fuel 1) id read-fault reads fn2-core fn2-sim fn2-own)))
  ((fn2-b-rec-flight (fn2-sim-rows fn2-sim) fn2-sim)
   (b* ((slot (fn2-b-rec-flight (fn2-sim-rows fn2-sim) fn2-sim))
        (fault (if (posp reads) read-fault *fn2-fault-none*))
        (fn2-sim (fn2-sim-clock (fn2-sim-due slot fn2-sim) *fn2-fault-none* fn2-sim))
        (fn2-sim (fn2-sim-environment slot fault 1 fn2-sim))
        ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-complete slot fault 1 fn2-core fn2-sim fn2-own)))
    (fn2-b-rec-drive (- fuel 1) id read-fault (if (posp reads) (- reads 1) 0) fn2-core fn2-sim fn2-own)))
  (t (b* ((before (fn2-machine-phase id fn2-core))
          ((mv & & actions & steps fn2-core) (fn2-exec-principal 0 0 4 fn2-core)))
      (if (and (zp actions) (zp steps) (= before (fn2-machine-phase id fn2-core)))
          (mv :stuck fn2-core fn2-sim fn2-own)
       (fn2-b-rec-drive (- fuel 1) id read-fault reads fn2-core fn2-sim fn2-own))))))

(defun fn2-b-rec-extents (c chain fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (+ 1 (nfix chain)) (nfix c)))))
 (if (or (not (posp c)) (> c (nfix chain))) nil
  (cons (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (e) (fn2-commit-root-extent c fn2-commit-root) e)
        (fn2-b-rec-extents (+ 1 c) chain fn2-core))))

; Run recovery on the fresh post-crash core. WITNESS is nil or (commit . words).
(defun fn2-b-rec-run (profile assume witness read-fault reads fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 profile))
      (words (cdr witness))
      ((mv w fn2-core)
       (if witness
           (b* (((mv c0 fn2-core) (fn2-recovery-present-witness-word 0 (nth 0 words) fn2-core))
                ((mv c1 fn2-core) (fn2-recovery-present-witness-word 1 (nth 1 words) fn2-core))
                ((mv c2 fn2-core) (fn2-recovery-present-witness-word 2 (nth 2 words) fn2-core))
                ((mv c3 fn2-core) (fn2-recovery-present-witness-word 3 (nth 3 words) fn2-core))
                ((mv c4 fn2-core) (fn2-recovery-present-witness-word 4 (nth 4 words) fn2-core))
                ((mv c5 fn2-core) (fn2-recovery-present-witness-word 5 (nth 5 words) fn2-core))
                ((mv c6 fn2-core) (fn2-recovery-present-witness-word 6 (nth 6 words) fn2-core))
                ((mv c7 fn2-core) (fn2-recovery-present-witness-word 7 (nth 7 words) fn2-core)))
             (mv (and (eq c0 :ok) (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok) (eq c5 :ok)
                      (eq c6 :ok) (eq c7 :ok)) fn2-core))
         (mv t fn2-core)))
      ((mv code fn2-core) (fn2-recovery-start id assume (if witness (car witness) 0) fn2-core))
      ((unless (and w (eq code :ok))) (mv (list :start code) nil nil nil fn2-core fn2-sim fn2-own))
      ((mv status fn2-core fn2-sim fn2-own) (fn2-b-rec-drive 100000 id read-fault reads fn2-core fn2-sim fn2-own))
      (chain (fn2-machine-rc-chain id fn2-core)))
  (mv status (nth (fn2-machine-rc-class id fn2-core) *fn2-rec-classes*)
      (nth (fn2-machine-rc-witness-outcome id fn2-core) *fn2-rec-witness-outcomes*)
      (fn2-b-rec-extents 1 chain fn2-core) fn2-core fn2-sim fn2-own)))

(defun fn2-b-rec-assume (profile)
 (declare (xargs :verify-guards nil))
 (+ (if (eq (fn2-cm-profile-kind profile) :crash-only) *fn2-rec-assume-crash-only* 0)
    (if (fn2-cm-persistence-fence profile) *fn2-rec-assume-fence* 0)
    (if (fn2-cm-integrity-evidence profile) *fn2-rec-assume-integrity* 0)
    (if (fn2-cm-independent-frontier profile) *fn2-rec-assume-frontier* 0)))

; ---------------------------------------------------------------------------
; Harness ground truth over the durable image, from the manifests captured
; before death. Independent of the recovery row: it knows which extent each
; submitted batch used and the bytes it meant to write.
(defun fn2-b-rec-check-batch (manifest fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (b* ((e (fn2-b-manifest-extent manifest))
      ((mv pc page) (fn2-b-durable-image e 0 fn2-sim))
      ((mv rc records) (fn2-b-durable-image e 1 fn2-sim))
      ((mv sc seal) (fn2-b-durable-image e 2 fn2-sim))
      ((unless (and (eq pc :ok) (eq rc :ok) (eq sc :ok))) (mv :unreadable nil nil)))
  (fn2-b-recover-images manifest (fn2-b-manifest-previous-seal manifest) page records seal)))
(defun fn2-b-rec-landed (manifests fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (if (atom manifests) nil
  (mv-let (code batch final) (fn2-b-rec-check-batch (car manifests) fn2-sim)
   (declare (ignore final))
   (if (eq code :ok)
       (cons (cons (fn2-lm-batch-number (fn2-b-manifest-batch (car manifests))) batch)
             (fn2-b-rec-landed (cdr manifests) fn2-sim))
    (fn2-b-rec-landed (cdr manifests) fn2-sim)))))
(defun fn2-b-rec-nonzero (left address fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-b-rec-countdown fn2-b-rec-count-op) :in-theory nil))))
 (if (zp left) nil
  (or (and (natp address) (< address (fn2-sim-storage-rows fn2-sim-storage))
           (not (equal (fn2-sim-storage-durable address fn2-sim-storage) 0)))
      (fn2-b-rec-nonzero (- left 1) (+ 1 (nfix address)) fn2-sim-storage))))
(defun fn2-b-rec-extent-nonzero (e fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (yes)
  (fn2-b-rec-nonzero *fn2-commit-extent-bytes* (* *fn2-commit-extent-bytes* (nfix e)) fn2-sim-storage) yes))
(defun fn2-b-rec-manifest-extents (manifests)
 (declare (xargs :verify-guards nil))
 (if (atom manifests) nil
  (cons (cons (fn2-lm-batch-number (fn2-b-manifest-batch (car manifests))) (fn2-b-manifest-extent (car manifests)))
        (fn2-b-rec-manifest-extents (cdr manifests)))))
; Positions whose bytes are nonzero and are not a landed, non-excluded batch.
(defun fn2-b-rec-dirty (e arena landed-extents fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix (- (nfix arena) (nfix e)))))
 (if (or (not (natp e)) (>= e (nfix arena))) nil
  (or (and (not (member-equal e landed-extents)) (fn2-b-rec-extent-nonzero e fn2-sim))
      (fn2-b-rec-dirty (+ 1 e) arena landed-extents fn2-sim))))
(defun fn2-b-rec-first-missing (n count landed excluded)
 (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix count)) (nfix n)))))
 (cond ((or (not (posp n)) (> n (nfix count))) nil)
       ((and (not (assoc-equal n landed)) (not (member-equal n excluded))) n)
       (t (fn2-b-rec-first-missing (+ 1 n) count landed excluded))))
(defun fn2-b-rec-landed-extents (landed excluded extents)
 (declare (xargs :verify-guards nil))
 (if (atom landed) nil
  (if (member-equal (caar landed) excluded) (fn2-b-rec-landed-extents (cdr landed) excluded extents)
   (cons (cdr (assoc-equal (caar landed) extents)) (fn2-b-rec-landed-extents (cdr landed) excluded extents)))))
(defun fn2-b-rec-survives (landed excluded)
 (declare (xargs :verify-guards nil))
 (if (atom landed) nil
  (if (member-equal (caar landed) excluded) (fn2-b-rec-survives (cdr landed) excluded)
   (cons (list :evidence (list :survives (caar landed))) (fn2-b-rec-survives (cdr landed) excluded)))))
; Ground-truth observations: every landed batch survives; a dirty arena
; names its first non-landed, non-injected batch as the bad tail.
(defun fn2-b-rec-truth (manifests excluded arena fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (let* ((landed (fn2-b-rec-landed manifests fn2-sim))
        (extents (fn2-b-rec-manifest-extents manifests))
        (dirty (fn2-b-rec-dirty 0 arena (fn2-b-rec-landed-extents landed excluded extents) fn2-sim))
        (first (fn2-b-rec-first-missing 1 (len manifests) landed excluded)))
  (append (fn2-b-rec-survives landed excluded)
          (if (and dirty first) (list (list :evidence (list :bad-tail first))) nil))))

; Recovered history: for each chained extent, the batch the harness knows was
; written there, decoded independently from the durable bytes. A chained
; extent the harness cannot confirm yields a foreign entry, failing HISTORY.
(defun fn2-b-rec-history (c extents manifests fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (if (atom extents) nil
  (let ((m (fn2-b-manifest-for c manifests)))
   (cons (if (and m (equal (fn2-b-manifest-extent m) (car extents)))
             (mv-let (code batch final) (fn2-b-rec-check-batch m fn2-sim)
              (declare (ignore final))
              (if (eq code :ok) batch (list :foreign c (car extents) code)))
           (list :foreign c (car extents)))
         (fn2-b-rec-history (+ 1 c) (cdr extents) manifests fn2-sim)))))

; ---------------------------------------------------------------------------
; Post-death faults (scenarios 15 and 16). Each acts on the durable image and
; reports the log-model observation it constitutes, if any.
;   (:corrupt B UNIT OFFSET)  flip one byte of batch B's unit
;   (:corrupt-last UNIT OFFSET) the same, on the last batch that issued
;   (:misdirect B UNIT TO)    batch B's unit landed at extent TO instead
;   (:rollback K)             the device shows the older image of batches 1..K
;   (:witness F)              an independent receipt for batch F is presented
(defun fn2-b-rec-zero-range (left address fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-b-rec-countdown fn2-b-rec-count-op) :in-theory nil))))
 (if (zp left) fn2-sim-storage
  (let ((fn2-sim-storage (fn2-storage-corrupt-byte address 0 fn2-sim-storage)))
   (fn2-b-rec-zero-range (- left 1) (+ 1 (nfix address)) fn2-sim-storage))))
(defun fn2-b-rec-copy-range (left from to fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-b-rec-countdown fn2-b-rec-count-op) :in-theory nil))))
 (if (zp left) fn2-sim-storage
  (let ((fn2-sim-storage
         (if (and (natp from) (< from (fn2-sim-storage-rows fn2-sim-storage)))
             (fn2-storage-corrupt-byte to (fn2-sim-storage-durable from fn2-sim-storage) fn2-sim-storage)
           fn2-sim-storage)))
   (fn2-b-rec-copy-range (- left 1) (+ 1 (nfix from)) (+ 1 (nfix to)) fn2-sim-storage))))
(defun fn2-b-rec-rollback (manifests k fn2-sim-storage)
 (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
 (if (atom manifests) fn2-sim-storage
  (let ((fn2-sim-storage
         (if (> (fn2-lm-batch-number (fn2-b-manifest-batch (car manifests))) (nfix k))
             (fn2-b-rec-zero-range *fn2-commit-extent-bytes*
              (* *fn2-commit-extent-bytes* (nfix (fn2-b-manifest-extent (car manifests)))) fn2-sim-storage)
           fn2-sim-storage)))
   (fn2-b-rec-rollback (cdr manifests) k fn2-sim-storage))))
(defun fn2-b-rec-unit-address (manifests b unit)
 (declare (xargs :verify-guards nil))
 (let ((m (fn2-b-manifest-for b manifests)))
  (and m (+ (* *fn2-commit-extent-bytes* (nfix (fn2-b-manifest-extent m))) (* *fn2-commit-unit-bytes* (nfix unit))))))
(defun fn2-b-rec-fenced-p (b events)
 (declare (xargs :verify-guards nil))
 (mv-let (code trace) (fn2-history-translate events)
  (and (eq code :ok) (member-equal b (fn2-lm-state-fenced (fn2-lm-trace-state trace))) t)))
; Witness words are the batch's final seal as written, read before any fault.
(defun fn2-b-rec-witness-words (manifests f fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (let ((m (fn2-b-manifest-for f manifests)))
  (if (not m) nil
   (mv-let (code batch final) (fn2-b-rec-check-batch m fn2-sim)
    (declare (ignore batch))
    (and (eq code :ok) (consp final) (fn-b3-words 8 (cdr final)))))))
(defun fn2-b-rec-last (manifests best)
 (declare (xargs :verify-guards nil))
 (if (atom manifests) best
  (fn2-b-rec-last (cdr manifests) (max (nfix best) (fn2-lm-batch-number (fn2-b-manifest-batch (car manifests)))))))
(defun fn2-b-rec-later (manifests k)
 (declare (xargs :verify-guards nil))
 (if (atom manifests) nil
  (let ((n (fn2-lm-batch-number (fn2-b-manifest-batch (car manifests)))))
   (if (> n (nfix k)) (cons n (fn2-b-rec-later (cdr manifests) k)) (fn2-b-rec-later (cdr manifests) k)))))
(defun fn2-b-rec-inject (faults manifests events excluded witness fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil))
 (if (atom faults) (mv :ok (reverse events) excluded witness fn2-sim)
  (b* ((f0 (car faults))
       ; (:corrupt-last UNIT OFFSET) names the last batch that issued.
       (f (if (and (eq (fn2-lm-event-tag f0) :corrupt-last) (consp manifests))
              (list :corrupt (fn2-b-rec-last manifests 0) (nth 1 f0) (nth 2 f0)) f0))
       ((when (eq (fn2-lm-event-tag f) :corrupt-last))
        (fn2-b-rec-inject (cdr faults) manifests events excluded witness fn2-sim))
       (tag (fn2-lm-event-tag f)) (b (fn2-lm-event-argument f)))
   (case tag
    (:corrupt
     (let ((at (fn2-b-rec-unit-address manifests b (nth 2 f))))
      (if (not at) (mv :bad-fault (reverse events) excluded witness fn2-sim)
       (let ((fn2-sim (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (fn2-sim-storage)
                        (fn2-storage-corrupt-byte (+ at (nfix (nth 3 f)))
                         (mod (+ 1 (fn2-sim-storage-durable (+ at (nfix (nth 3 f))) fn2-sim-storage)) 256)
                         fn2-sim-storage) fn2-sim)))
        ; A fenced batch damaged after its fence is required data destroyed; an
        ; unfenced one is only more dirt in the tail.
        (let ((fenced (fn2-b-rec-fenced-p b (reverse events))))
         (fn2-b-rec-inject (cdr faults) manifests
          (if fenced (cons (list :evidence (list :corrupt-required b)) events) events)
          (if fenced (cons b excluded) excluded) witness fn2-sim))))))
    (:misdirect
     (let ((at (fn2-b-rec-unit-address manifests b (nth 2 f)))
           (to (+ (* *fn2-commit-extent-bytes* (nfix (nth 3 f))) (* *fn2-commit-unit-bytes* (nfix (nth 2 f))))))
      (if (not at) (mv :bad-fault (reverse events) excluded witness fn2-sim)
       (let ((fn2-sim (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (fn2-sim-storage)
                        (let ((fn2-sim-storage (fn2-b-rec-copy-range *fn2-commit-unit-bytes* at to fn2-sim-storage)))
                         (fn2-b-rec-zero-range *fn2-commit-unit-bytes* at fn2-sim-storage)) fn2-sim)))
        ; A fenced batch damaged after its fence is required data destroyed; an
        ; unfenced one is only more dirt in the tail.
        (let ((fenced (fn2-b-rec-fenced-p b (reverse events))))
         (fn2-b-rec-inject (cdr faults) manifests
          (if fenced (cons (list :evidence (list :corrupt-required b)) events) events)
          (if fenced (cons b excluded) excluded) witness fn2-sim))))))
    (:rollback
     (let ((fn2-sim (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (fn2-sim-storage)
                      (fn2-b-rec-rollback manifests b fn2-sim-storage) fn2-sim)))
      (fn2-b-rec-inject (cdr faults) manifests (cons (list :evidence (list :rollback b)) events)
       (append (fn2-b-rec-later manifests b) excluded) witness fn2-sim)))
    (:witness
     (let ((words (fn2-b-rec-witness-words manifests b fn2-sim)))
      (if (not words) (mv :bad-witness (reverse events) excluded witness fn2-sim)
       (fn2-b-rec-inject (cdr faults) manifests
        (cons (list :evidence (list :present-frontier :receipt b)) events) excluded (cons b words) fn2-sim))))
    (otherwise (mv :bad-fault (reverse events) excluded witness fn2-sim))))))

; ---------------------------------------------------------------------------
; Death, post-death faults, real recovery, ground truth. EVENTS are the
; projected pre-death events in order; the result's events end with the
; death, the injected observations and the ground truth.
(defun fn2-b-crash-recover (profile model faults manifests events read-fault reads fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
      ; Every scenario first checks that death left a fresh process.
      (stale (fn2-b-death-difference profile fn2-core))
      ((when stale) (mv (list :stale-death stale) :unknown :none nil events fn2-core fn2-sim fn2-own))
      ((mv code events excluded witness fn2-sim)
       (fn2-b-rec-inject faults manifests (reverse (append events (list '(:crash)))) nil nil fn2-sim))
      ((unless (eq code :ok)) (mv (list :inject code) :unknown :none nil events fn2-core fn2-sim fn2-own))
      (truth (fn2-b-rec-truth manifests excluded (fn2-b-capacity :extent-slots 16 profile) fn2-sim))
      ((mv status class outcome extents fn2-core fn2-sim fn2-own)
       (fn2-b-rec-run profile (fn2-b-rec-assume model) witness read-fault reads fn2-core fn2-sim fn2-own))
      (recovered (fn2-b-rec-history 1 extents manifests fn2-sim)))
  (mv status class outcome recovered (append events truth) fn2-core fn2-sim fn2-own)))

; RECOVERY: HISTORY's allowed-recovery relation, plus the witness outcome.
; Detection is reported exactly when a credited presented witness is beyond
; the recovered history; an uncredited witness is never detection.
(defun fn2-check-recovery (events profile classification recovered outcome)
 (declare (xargs :verify-guards nil))
 (mv-let (code trace) (fn2-history-translate events)
  (let* ((s (fn2-lm-trace-state trace))
         (presented (consp (fn2-lm-state-witnesses s)))
         (credited (and (fn2-cm-independent-frontier profile)
                        (fn2-lm-conflicting-witness (fn2-lm-state-witnesses s) recovered))))
   (and (eq code :ok)
        (fn2-lm-recovery-allowedp trace profile classification recovered)
        (iff (eq outcome :rollback-detected) credited)
        (iff (eq outcome :none) (not presented))
        (iff (eq outcome :uncredited) (and presented (not (fn2-cm-independent-frontier profile))))
        (or (not (eq outcome :discontinuity)) (eq classification :damaged))))))

