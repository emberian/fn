; Actual commit continuations, adapter descriptors, and harvested observations.
; Test evidence uses lists; the served machine never calls these functions.
(in-package "ACL2")
(include-book "../sim/commit-history")
(include-book "../sim/sim")
(include-book "../books/executor")
(include-book "../books/commit-proof")
(include-book "std/util/bstar" :dir :system)

; Termination depends only on bounded test counters, not unfolded core state.
(local (defthm fn2-b-scenario-countdown
 (implies (not (zp fuel)) (o< (nfix (- fuel 1)) (nfix fuel))) :rule-classes nil))
(local (defthm fn2-b-scenario-count-op (o-p (nfix fuel)) :rule-classes nil))
(local (defthm fn2-b-scenario-stage-down
 (implies (< (nfix stage) 4)
   (o< (nfix (- 4 (nfix (+ 1 (nfix stage))))) (nfix (- 4 (nfix stage))))) :rule-classes nil))
(local (defthm fn2-b-scenario-stage-op (o-p (nfix (- 4 (nfix stage)))) :rule-classes nil))

(fn2-cm-defreaders fn2-b-result-status fn2-b-result-steps fn2-b-result-deaths
  fn2-b-result-fault fn2-b-result-reorders fn2-b-result-dirty
  fn2-b-result-fence-max fn2-b-result-history fn2-b-result-write-bytes
  fn2-b-result-acks fn2-b-result-phases fn2-b-result-events fn2-b-result-payload-bytes
  fn2-b-result-write-target)

; Count queued, submitted and posted-but-unharvested fences independently.
(defun fn2-b-fence-count-aux (left fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix left)))
  (if (zp left) 0
    (+ (if (and (= (fn2-ops-kind (- left 1) fn2-ops) *fn2-action-fence*)
                 (not (member-equal (fn2-ops-phase (- left 1) fn2-ops)
                         (list *fn2-op-phase-free* *fn2-op-phase-retired*)))) 1 0)
       (fn2-b-fence-count-aux (- left 1) fn2-ops))))
(defun fn2-b-fence-count (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (count) (fn2-b-fence-count-aux (fn2-ops-rows fn2-ops) fn2-ops) count))
(defun fn2-b-fence-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* 0))
           (fn2-core (fn2-core-init profile fn2-core))
           (id (fn2-machine-global-id *fn2-commit-kind* 0 profile))
           (gen (fn2-machine-generation id fn2-core))
           ((mv a & & fn2-core) (fn2-issue-fence *fn2-commit-kind* id gen 0 fn2-core))
           ((mv b & & fn2-core) (fn2-issue-fence *fn2-commit-kind* id gen 0 fn2-core)))
        ; The adapter has not taken either descriptor. The control must catch
        ; the second queued fence, before its single physical slot can hide it.
        (mv (and (eq a :ok) (eq b :ok) (= (fn2-b-fence-count fn2-core) 2)) fn2-core))
      answer)))

(defun fn2-b-flight-list (left fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (if (= (fn2-sim-active (- left 1) fn2-sim) 1)
        (cons (- left 1) (fn2-b-flight-list (- left 1) fn2-sim))
      (fn2-b-flight-list (- left 1) fn2-sim))))
(defun fn2-b-oldest-flight (tokens fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (if (atom tokens) nil
    (if (and (= (fn2-sim-active (caar tokens) fn2-sim) 1)
             (= (fn2-sim-gen (caar tokens) fn2-sim) (cadar tokens)))
        (caar tokens) (fn2-b-oldest-flight (cdr tokens) fn2-sim))))

(defun fn2-b-cache-readable (i left different fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
  (if (zp left) different
    (mv-let (code byte) (fn2-storage-read-byte i i :none fn2-sim-storage)
      (and (eq code :ok)
           (fn2-b-cache-readable (+ 1 (nfix i)) (- left 1)
             (or different (not (= byte (fn2-sim-storage-durable i fn2-sim-storage)))) fn2-sim-storage)))))
(defun fn2-b-cached-not-durable (fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
    (yes) (fn2-b-cache-readable 0 (fn2-sim-storage-rows fn2-sim-storage) nil fn2-sim-storage) yes))

(defun fn2-b-unit-fingerprint (i left pending acc fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
  (if (zp left) acc
    (fn2-b-unit-fingerprint (+ 1 (nfix i)) (- left 1) pending
      (mod (+ (* 257 (nfix acc)) (if pending (fn2-sim-storage-pending i fn2-sim-storage)
                                  (fn2-sim-storage-durable i fn2-sim-storage))) 4294967296)
      fn2-sim-storage)))
(defun fn2-b-unit-snapshots (left fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (let ((unit (- left 1)))
      (if (fn2-storage-unit-pendingp unit fn2-sim-storage)
          (cons (list unit (fn2-b-unit-fingerprint (* 512 unit) 512 nil 0 fn2-sim-storage)
                           (fn2-b-unit-fingerprint (* 512 unit) 512 t 0 fn2-sim-storage))
                (fn2-b-unit-snapshots unit fn2-sim-storage))
        (fn2-b-unit-snapshots unit fn2-sim-storage)))))
(defun fn2-b-tears-after (units fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (if (atom units) 0
    (let ((now (fn2-b-unit-fingerprint (* 512 (caar units)) 512 nil 0 fn2-sim-storage)))
      (+ (if (and (not (= now (cadar units))) (not (= now (caddar units)))) 1 0)
         (fn2-b-tears-after (cdr units) fn2-sim-storage)))))

(defun fn2-b-write-fault-target (seed)
  (declare (xargs :verify-guards nil))
  (if (= (mod (floor (nfix seed) 10) 2) 0) :dependency :log))
(defun fn2-b-fault-choice (scenario hit kind write-ready)
  (declare (xargs :verify-guards nil))
  (if hit 26
    (cond ((and write-ready (eq scenario :partial)) 24)
          ((and write-ready (eq scenario :enospc)) 12)
          ((and (= kind *fn2-action-fence*) (eq scenario :failed-barrier)) 23)
          (t 26))))

(defun fn2-b-finishedp (views members)
  (declare (xargs :verify-guards nil))
  (if (atom views) t
    (and (= (fn2-b-visible-acks (car views)) members)
         (= (fn2-b-visible-stopped (car views)) 1) (fn2-b-finishedp (cdr views) members))))
(defun fn2-b-uncertainp (views)
  (declare (xargs :verify-guards nil))
  (if (atom views) nil
    (or (= (fn2-b-visible-phase (car views)) *fn2-commit-state-uncertain*)
        (fn2-b-uncertainp (cdr views)))))
(defun fn2-b-phases (views)
  (declare (xargs :verify-guards nil))
  (if (atom views) nil
    (cons (fn2-b-visible-phase (car views)) (fn2-b-phases (cdr views)))))
(defun fn2-b-uncertain-stoppedp (views)
  (declare (xargs :verify-guards nil))
  (if (atom views) t
    (and (or (not (= (fn2-b-visible-phase (car views)) *fn2-commit-state-uncertain*))
             (= (fn2-b-visible-stopped (car views)) 1))
         (fn2-b-uncertain-stoppedp (cdr views)))))

(defun fn2-b-clock-pendingp (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (posted) (= (fn2-ops-clock-posted fn2-ops) 1) posted))
(defun fn2-b-expired-batch (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) nil
    (if (and (= (fn2-machine-phase (car ids) fn2-core) *fn2-commit-state-uncertain*)
             (= (fn2-machine-cb-fence-live (car ids) fn2-core) 1))
        (fn2-machine-batch-no (car ids) fn2-core)
      (fn2-b-expired-batch (cdr ids) fn2-core))))

(fn2-cm-defreaders fn2-b-fail-id fn2-b-fail-latched fn2-b-fail-outcome fn2-b-fail-reason)
(defun fn2-b-failures (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) nil
    (cons (list (car ids) (fn2-machine-cb-failed (car ids) fn2-core)
                (fn2-machine-outcome (car ids) fn2-core) (fn2-machine-cb-reason (car ids) fn2-core))
          (fn2-b-failures (cdr ids) fn2-core))))
(defun fn2-b-sticky-failures-p (before fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom before) t
    (let* ((row (car before)) (id (fn2-b-fail-id row)))
      (and (or (= (fn2-b-fail-latched row) 0)
               (and (= (fn2-machine-cb-failed id fn2-core) 1)
                    (= (fn2-machine-outcome id fn2-core) (fn2-b-fail-outcome row))
                    (= (fn2-machine-cb-reason id fn2-core) (fn2-b-fail-reason row))))
           (fn2-b-sticky-failures-p (cdr before) fn2-core)))))

; Each call performs exactly one scheduler visit, descriptor handoff, physical
; completion, or harvest. Death cuts occur between ALL these calls, including
; preparation and each incremental notification. A seed chooses flight order.
(defun fn2-b-rounds (fuel step cut seed scenario hit ids members seen manifests events bytes reorders maximum phases quiet
                         fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)
    :hints (("Goal" :use (fn2-b-scenario-countdown fn2-b-scenario-count-op) :in-theory nil))))
  (b* ((views (fn2-b-visibility ids fn2-core))
       (phases (union-equal (fn2-b-phases views) phases))
       (fences (fn2-b-fence-count fn2-core)) (maximum (max fences (nfix maximum)))
       (flights (fn2-b-flight-list (fn2-sim-rows fn2-sim) fn2-sim))
       (posted (fn2-b-next-result fn2-core))
       (outbox (fn2-b-outbox fn2-core))
       ; Continue eight scheduler opportunities after the last uncertain
       ; completion, exposing an erroneous restart or follower issue.
       (quiet (if (and (fn2-b-uncertainp views) (fn2-b-uncertain-stoppedp views)
                       (not flights) (not posted) (not outbox)) (+ 1 (nfix quiet)) 0))
       ((when (or (< 1 fences) (zp fuel) (= step cut)
                  (fn2-b-finishedp views members)
                  (>= quiet 8)))
        (mv (cond ((< 1 fences) :two-fences) ((zp fuel) :fuel) ((= step cut) :cut)
                  ((fn2-b-finishedp views members) :done) (t :uncertain))
            step hit manifests events bytes reorders maximum phases fn2-core fn2-sim fn2-own))
       (stage (mod step 4))
       (failures (fn2-b-failures ids fn2-core))
       ((mv new-hit extra-events more-reorder fn2-core fn2-sim fn2-own)
        (cond
         ((fn2-b-clock-pendingp fn2-core)
          (b* (((mv & & & & & fn2-core) (fn2-exec-mailbox fn2-core)))
            (mv (if (eq hit :clock-posted) :clock-observed hit) nil 0 fn2-core fn2-sim fn2-own)))
         ((and posted (or (not (eq scenario :none)) (= stage 0) (and (not outbox) (not flights))))
          (b* (((mv & & & & & fn2-core) (fn2-exec-harvest fn2-core)))
            (mv hit (list posted) 0 fn2-core fn2-sim fn2-own)))
         ((and outbox (or (= stage 1) (not flights)))
          (mv-let (taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)
            (declare (ignore taken))
            (mv hit nil 0 fn2-core fn2-sim fn2-own)))
         ((and flights (= stage 3))
          (b* ((slot (nth (mod (fn2-prng-mix32 (fn2-u32 (+ (nfix seed) step))) (len flights)) flights))
               (oldest (fn2-b-oldest-flight (reverse seen) fn2-sim))
               (kind (fn2-sim-kind slot fn2-sim))
               (timeout (and (eq scenario :late-success) (not hit) (= kind *fn2-action-fence*)))
               ((when timeout)
                (b* ((id (fn2-sim-owner-slot slot fn2-sim))
                     (deadline (+ 1 (fn2-machine-deadline id fn2-core)))
                     (fn2-sim (fn2-sim-delay-flight slot 14 1 fn2-sim))
                     (fn2-sim (fn2-sim-clock deadline 26 fn2-sim))
                     (fn2-core (fn2-sim-post-clock deadline deadline fn2-core)))
                  (mv :clock-posted nil 0 fn2-core fn2-sim fn2-own)))
               ((when (and (= kind *fn2-action-fence*)
                           (member-eq hit '(:clock-posted :clock-observed))))
                ; Clock posting, mailbox harvest, scheduled timeout, and the
                ; late fence completion are separate process-death boundaries.
                (mv hit nil 0 fn2-core fn2-sim fn2-own))
               (dependency-target (eq (fn2-b-write-fault-target seed) :dependency))
               (log-write (and (= kind *fn2-action-write*)
                               (not (= (mod (fn2-sim-storage-offset slot fn2-sim) 12288) 0))))
               ((when (and (not hit) (member-eq scenario '(:partial :eio :enospc)) log-write (not dependency-target)
                           (< (fn2-machine-cb-issued (fn2-sim-owner-slot slot fn2-sim) fn2-core) 2)))
                ; Let the runnable issuer submit its sibling before harvesting
                ; either result, making sticky failure accumulation observable.
                (mv hit nil 0 fn2-core fn2-sim fn2-own))
               ; A has no transient write-EIO selector. Drive its real result
               ; adapter with :io and zero physical bytes; this environment
               ; fault neither kills the device nor invents a successful write.
               ; The seed alternates dependency faults and concurrent-log faults.
               ; A log sibling completion must retain the first failure.
               (write-ready (if dependency-target
                                  (and (= kind *fn2-action-write*) (not log-write))
                                (and log-write
                                  (= (fn2-machine-cb-issued (fn2-sim-owner-slot slot fn2-sim) fn2-core) 2)
                                  (= (fn2-machine-cb-done (fn2-sim-owner-slot slot fn2-sim) fn2-core) 0))))
               (write-eio (and (not hit) (eq scenario :eio) write-ready))
               (fault (fn2-b-fault-choice scenario hit kind write-ready))
               (fn2-sim (fn2-sim-clock (fn2-sim-due slot fn2-sim) 26 fn2-sim))
               (fn2-sim (fn2-sim-environment slot fault 1 fn2-sim))
               ((mv & fn2-core fn2-sim fn2-own)
                (if write-eio
                    (fn2-sim-complete-result slot (fn2-sim-gen slot fn2-sim) kind
                      *fn2-event-write-result* (fn2-sim-range-len slot fn2-sim) :io 0 0 26 1
                      (fn2-sim-now fn2-sim) nil fn2-core fn2-sim fn2-own)
                  (fn2-sim-complete slot fault 1 fn2-core fn2-sim fn2-own)))
               (hit (if write-eio :eio (if (= fault 26) hit
                      (if (and (= fault 23) (not (fn2-b-cached-not-durable fn2-sim))) :cache-control-failed scenario)))))
            (mv hit nil (if (and oldest (not (= slot oldest)) (= kind *fn2-action-write*)
                              (= (fn2-sim-kind oldest fn2-sim) *fn2-action-write*)) 1 0)
                fn2-core fn2-sim fn2-own)))
         (t (b* (((mv & & actions bytes steps fn2-core) (fn2-exec-principal 0 0 4 fn2-core)))
              (assert$ (and (<= actions 4) (<= bytes 4096) (<= steps 32))
                (mv hit nil 0 fn2-core fn2-sim fn2-own))))))
       (fn2-core (assert$ (fn2-b-sticky-failures-p failures fn2-core) fn2-core))
       (expired (and (eq new-hit :clock-observed) (fn2-b-expired-batch ids fn2-core)))
       (new-hit (if expired :late-success new-hit))
       (events (append (if expired (list (list :timeout expired)) nil)
                       (reverse extra-events) events))
       (events (fn2-b-project-visible views (fn2-b-visibility ids fn2-core) events))
       ((mv code seen manifests events bytes)
        (fn2-b-project-issues (fn2-b-outbox fn2-core) seen manifests events bytes fn2-core))
       ((unless (eq code :ok))
        (mv code step new-hit manifests events bytes reorders maximum phases fn2-core fn2-sim fn2-own)))
    (fn2-b-rounds (- fuel 1) (+ 1 step) cut seed scenario new-hit ids members seen manifests events bytes
                   (+ reorders more-reorder) maximum phases quiet fn2-core fn2-sim fn2-own)))

(defun fn2-b-ack-total (views)
  (declare (xargs :verify-guards nil))
  (if (atom views) 0 (+ (nfix (fn2-b-visible-acks (car views))) (fn2-b-ack-total (cdr views)))))

(defun fn2-b-payload-total (manifests)
  (declare (xargs :verify-guards nil))
  (if (atom manifests) 0
    (+ (nfix (fn2-b-manifest-record-bytes (car manifests)))
       (fn2-b-payload-total (cdr manifests)))))

(defun fn2-b-case (profile seed cut scenario mode members fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((profile (fn2-b-test-profile (put-assoc-equal :sim-sectors 8 profile) mode))
       (fn2-core (fn2-core-init profile fn2-core))
       ; Recovery fixture: the preceding writer epoch fence has completed.
       ; B3 does not implement or claim this bootstrap protocol.
       ((mv epoch-code fn2-core)
        (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
          (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
       (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
       (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
       ((mv ca ea & fn2-core) (fn2-b-start a members 1 mode b fn2-core))
       ((mv cb eb & fn2-core) (fn2-b-start b members (+ 1 members) mode a fn2-core))
       ; A real busy-row admission refuses a fresh operation. HISTORY must
       ; retain that refusal independently of the two accepted request ranges.
       ((mv cr er & fn2-core) (fn2-b-start a 1 999 mode b fn2-core))
       (fn2-core (fn2-exec-wake a fn2-core))
       (fn2-core (fn2-exec-wake b fn2-core))
       (fn2-sim (fn2-sim-init seed :none "B3b" profile fn2-sim))
       (fn2-own (fn2-own-init profile fn2-own))
       ((unless (and (eq epoch-code :ok) (eq ca :ok) (eq cb :ok) (eq cr :admission)))
        (mv (list :admission epoch-code ca cb cr) fn2-core fn2-sim fn2-own))
       ((mv status steps hit manifests events bytes reorders maximum phases fn2-core fn2-sim fn2-own)
        (fn2-b-rounds 10000 0 cut seed scenario nil (list a b) members nil nil (reverse (append ea eb er)) 0 0 0 nil 0 fn2-core fn2-sim fn2-own))
       (hit (if (member-eq hit '(:clock-posted :clock-observed)) nil hit))
       (acks (fn2-b-ack-total (fn2-b-visibility (list a b) fn2-core)))
       (payload (fn2-b-payload-total manifests))
       (units (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                (units) (fn2-b-unit-snapshots (floor (fn2-sim-storage-rows fn2-sim-storage) 512) fn2-sim-storage) units))
       ((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
       (dirty (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                (count) (fn2-b-tears-after units fn2-sim-storage) count))
       ((mv class recovered evidence fn2-core) (fn2-b-recover manifests fn2-core fn2-sim))
       (events (append (reverse events) (list '(:crash)) evidence))
       ; Only crash-only runs call an incomplete final frame a torn tail.
       ; Broad error runs cannot infer that the invalid tail is merely torn.
       (class (if (and hit (eq class :torn-tail)) :unknown class))
       (history (fn2-check-history events (fn2-cm-profile (if hit :broad :crash-only)
                                                       t t nil 0 0) class recovered))
       (pass (and (member-eq status '(:cut :done :uncertain)) history (<= maximum 1)
                  (not (eq hit :cache-control-failed))
                  (or (eq scenario :none) (eq hit scenario)
                      (and (eq status :cut) (not hit))))))
    (mv (list (if pass :pass (list :fail status class hit)) steps (fn2-sim-deaths fn2-sim)
              hit reorders dirty maximum history bytes acks phases (if pass nil events) payload
              (and (member-eq hit '(:partial :eio :enospc)) (fn2-b-write-fault-target seed)))
        fn2-core fn2-sim fn2-own)))

(defun fn2-b-one (profile seed cut scenario mode members)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (answer fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (answer fn2-core fn2-sim fn2-own)
              (fn2-b-case profile seed cut scenario mode members fn2-core fn2-sim fn2-own)
              (mv answer fn2-core fn2-sim)))
          (mv answer fn2-core)))
      answer)))

(fn2-cm-defreaders fn2-b-control-pass fn2-b-control-detail)

; Reuse control deliberately holds the follower in collect until its parent's
; workspace has been released. The same real stepper serves the owed teeth.
(defun fn2-b-free-workspaces (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (count) (fn2-pool-free-count (fn2-pool-class-for 4096 fn2-pool) fn2-pool) count))
(defun fn2-b-control-steps (fuel slot ids seen manifests events fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)
    :hints (("Goal" :use (fn2-b-scenario-countdown fn2-b-scenario-count-op) :in-theory nil))))
  (if (zp fuel) (mv t seen manifests events fn2-core fn2-sim fn2-own)
    (b* ((before (fn2-b-visibility ids fn2-core))
         ((mv legal extra fn2-core fn2-sim fn2-own)
          (fn2-commit-proof-step (list :auto-slot slot 26) 0 ids
            (fn2-cm-profile :crash-only t t nil 0 0) fn2-core fn2-sim fn2-own))
         (events (fn2-b-project-visible before (fn2-b-visibility ids fn2-core)
                   (append (reverse extra) events)))
         ((mv code seen manifests events &)
          (fn2-b-project-issues (fn2-b-outbox fn2-core) seen manifests events 0 fn2-core))
         ((unless (and legal (eq code :ok) (<= (fn2-b-fence-count fn2-core) 1)))
          (mv nil seen manifests events fn2-core fn2-sim fn2-own)))
      (fn2-b-control-steps (- fuel 1) slot ids seen manifests events fn2-core fn2-sim fn2-own))))
(defun fn2-b-reuse-stages (stage mode ids seen manifests events fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :measure (nfix (- 4 (nfix stage)))
    :hints (("Goal" :use (fn2-b-scenario-stage-down fn2-b-scenario-stage-op) :in-theory nil))))
  (if (>= (nfix stage) 4) (mv t manifests events fn2-core fn2-sim fn2-own)
    (b* ((slot (mod (nfix stage) 2)) (id (nth slot ids)) (partner (nth (- 1 slot) ids))
         ((mv okay seen manifests events fn2-core fn2-sim fn2-own)
          (fn2-b-control-steps 256 slot ids seen manifests events fn2-core fn2-sim fn2-own))
         ((unless (and okay (= (fn2-machine-phase id fn2-core) *fn2-commit-state-free*)
                       (= (fn2-machine-stopped id fn2-core) 1) (= (fn2-machine-cb-acks id fn2-core) 1)
                       (= (fn2-b-free-workspaces fn2-core) (if (< stage 3) 4 8))))
          (mv nil manifests events fn2-core fn2-sim fn2-own))
         (old-gen (fn2-machine-generation id fn2-core))
         ((mv okay admission-events fn2-core)
          (if (< stage 2)
              (b* ((held (= (fn2-machine-phase partner fn2-core) *fn2-commit-state-collect*))
                   ((mv code admission-events & fn2-core) (fn2-b-start id 1 (+ 3 stage) mode partner fn2-core))
                   ; An actual old-generation completion must be refused before
                   ; observation bookkeeping can change this rearmed row.
                   ((mv wake fn2-core) (fn2-machine-observe *fn2-commit-kind* id old-gen
                      *fn2-event-write-result* *fn2-outcome-done* 0 4096 0 0 fn2-core)))
                (mv (and held (eq code :ok) (= wake 4294967295)
                         (= (fn2-machine-generation id fn2-core) (+ 1 old-gen))
                         (= (fn2-machine-phase id fn2-core) *fn2-commit-state-collect*)
                         (= (fn2-machine-cb-done id fn2-core) 0)) admission-events fn2-core))
            (mv t nil fn2-core)))
         (events (append (reverse admission-events) events))
         ((unless okay) (mv nil manifests events fn2-core fn2-sim fn2-own)))
      (fn2-b-reuse-stages (+ 1 (nfix stage)) mode ids seen manifests events fn2-core fn2-sim fn2-own))))
(defun fn2-b-reuse-case (mode fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* mode))
       (fn2-core (fn2-core-init profile fn2-core))
       ((mv ec fn2-core)
        (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
          (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
       (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
       (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
       ((mv ca ea & fn2-core) (fn2-b-start a 1 1 mode b fn2-core))
       ((mv cb eb & fn2-core) (fn2-b-start b 1 2 mode a fn2-core))
       (fn2-sim (fn2-sim-init 20261028 :none "B3-reuse" profile fn2-sim))
       (fn2-own (fn2-own-init profile fn2-own))
       ((mv okay manifests events fn2-core fn2-sim fn2-own)
        (fn2-b-reuse-stages 0 mode (list a b) nil nil (reverse (append ea eb)) fn2-core fn2-sim fn2-own))
       ; Exhaustion is refused before reservation or proposal. The fixture puts
       ; a genuinely drained/reused row at its finite generation limit.
       (fn2-core (fn2-machine-set-generation a (fn2-machine-gen-limit fn2-core) fn2-core))
       ((mv old-next old-key old-capacity old-mode) (fn2-commit-frontier fn2-core))
       ((mv refusal refused & fn2-core) (fn2-b-start a 1 5 mode b fn2-core))
       ((mv next key capacity config) (fn2-commit-frontier fn2-core))
       (okay (and okay (= next old-next) (= key old-key) (= capacity old-capacity) (= config old-mode) (eq refusal :exhausted) (not refused) (= (fn2-b-free-workspaces fn2-core) 8)
                   (not (fn2-b-outbox fn2-core)) (= (fn2-machine-batch-no a fn2-core) 3)))
       ((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
       ((mv class recovered evidence fn2-core) (fn2-b-recover manifests fn2-core fn2-sim))
       (history (fn2-check-history (append (reverse events) (list '(:crash)) evidence)
                  (fn2-cm-profile :crash-only t t nil 0 0) class recovered)))
    (mv (list (and (eq ec :ok) (eq ca :ok) (eq cb :ok) okay history (= (len recovered) 4))
              mode class (len recovered) refusal) fn2-core fn2-sim fn2-own)))
(defun fn2-b-reuse-control (mode)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (answer fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (answer fn2-core fn2-sim fn2-own)
              (fn2-b-reuse-case mode fn2-core fn2-sim fn2-own) (mv answer fn2-core fn2-sim)))
          (mv answer fn2-core))) answer)))

(defun fn2-b-resource-refusal (pool-short)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((profile (fn2-b-test-profile
                     (put-assoc-equal :extent-slots 1
                       (put-assoc-equal :pool-classes
                         (append (fn2-profile-pool-classes *fn2-profile-tiny*)
                           (list (cons (if pool-short 3 8) 4096))) *fn2-profile-tiny*)) 0))
           (fn2-core (fn2-core-init profile fn2-core))
           ((mv ec fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv occupied fn2-core)
            (if pool-short (mv :ok fn2-core)
              (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
                (code fn2-extents)
                (mv-let (code pressure extent epoch counter fn2-extents) (fn2-alloc-reserve fn2-extents)
                  (declare (ignore pressure extent epoch counter)) (mv code fn2-extents))
                (mv code fn2-core))))
           (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
           (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
           ((mv old-next old-key old-capacity old-mode) (fn2-commit-frontier fn2-core))
           ((mv code admission-events & fn2-core) (fn2-b-start a 1 1 0 b fn2-core))
           ((mv next key capacity config) (fn2-commit-frontier fn2-core)))
        (mv (list (and (eq ec :ok) (eq occupied :ok) (not admission-events)
                       (eq code (if pool-short :exhausted :no-space))
                       (= (fn2-b-free-workspaces fn2-core) (if pool-short 3 8))
                       (= next old-next) (= key old-key) (= capacity old-capacity) (= config old-mode)
                       (= next 1) (= key 0) (= (fn2-machine-batch-no a fn2-core) 0)
                       (= (fn2-machine-phase a fn2-core) *fn2-commit-state-free*)
                       (not (fn2-b-outbox fn2-core))) code)
            fn2-core)) answer)))

(defun fn2-b-mode-refusal (mode)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* mode))
           (fn2-core (fn2-core-init profile fn2-core))
           ((mv ec fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
              (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
           (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
           ((mv old-next old-key old-capacity old-mode) (fn2-commit-frontier fn2-core))
           ((mv wrong admission-events & fn2-core) (fn2-b-start a 1 1 (- 1 mode) b fn2-core))
           ((mv next key capacity config) (fn2-commit-frontier fn2-core))
           (unchanged (and (not admission-events) (= next old-next) (= key old-key)
                           (= capacity old-capacity) (= config old-mode) (= next 1) (= key 0) (= (fn2-b-free-workspaces fn2-core) 8)
                           (= (fn2-machine-batch-no a fn2-core) 0)
                           (= (fn2-machine-phase a fn2-core) *fn2-commit-state-free*)
                           (not (fn2-b-outbox fn2-core))))
           ((mv right & & fn2-core) (fn2-b-start a 1 1 mode b fn2-core)))
        (mv (list (and (eq ec :ok) (eq wrong :profile) unchanged (eq right :ok)
                       (= (fn2-machine-cb-mode a fn2-core) mode)) wrong right) fn2-core)) answer)))
