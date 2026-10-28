; Run from repo root: nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 timeout -k 5 3600 tools/acl2 < fn2/tests/sim-layer-a-a4-driver.lsp > build/a4-sim-layer-a.log 2>&1 & echo $! > build/a4-sim-layer-a.pid
; This is an ACL2 ld script, not a certified book. Checkers and workload
; traversals are test-only; the adapter and core runtime books are certified.
(in-package "ACL2")
(include-book "../sim/sim-recovery")
(include-book "../sim/check")
(include-book "std/util/bstar" :dir :system)

; Updated from HEAD and the sorted runtime-book source manifest before acceptance.
(defconst *fn2-scenario-revision* "HEAD=e0cd1f4ddd728c044cdb11d1242d1d854f475e90;fn2-runtime-sha256=3d4fa7b0772ea8e78670222263d747705a45c5e86b56c6b63c68f9b273e1c9b1")

; Termination depends only on the explicit fuel, not the threaded states.
(defthm fn2-test-countdown
  (implies (not (zp x)) (o< (nfix (- x 1)) (nfix x)))
  :rule-classes nil)
(defthm fn2-test-count-op (o-p (nfix x)) :rule-classes nil)


; Workload owner is the constant MRef (1,0,1). It discovers its retained
; workspace through the concrete pool; no list of payload bytes is built.
(defun fn2-scenario-find-slot-aux (left filled fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) (mv nil 0 0 0)
    (let ((slot (- left 1)))
      (if (and (eq (fn2-pool-slot-state slot fn2-pool) :workspace)
               (fn2-pool-ownerp slot 1 0 1 fn2-pool)
               (if filled (< 0 (fn2-pool-slot-fill slot fn2-pool))
                 (equal (fn2-pool-slot-fill slot fn2-pool) 0)))
          (mv t slot (fn2-pool-slot-gen slot fn2-pool)
              (fn2-pool-slot-fill slot fn2-pool))
        (fn2-scenario-find-slot-aux slot filled fn2-pool)))))
(in-theory (disable fn2-scenario-find-slot-aux))
(defun fn2-scenario-find-slot (filled fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (found slot gen filled-bytes)
    (fn2-scenario-find-slot-aux (fn2-pool-nslots fn2-pool) filled fn2-pool)
    (mv found slot gen filled-bytes)))
(in-theory (disable fn2-scenario-find-slot))

(defun fn2-scenario-target-aux (left fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) (mv 0 0)
    (let ((slot (- left 1)))
      (if (or (equal (fn2-op-phase slot fn2-ops) *fn2-op-phase-queued*)
              (equal (fn2-op-phase slot fn2-ops) *fn2-op-phase-submitted*))
          (mv slot (fn2-op-gen slot fn2-ops))
        (fn2-scenario-target-aux slot fn2-ops)))))
(in-theory (disable fn2-scenario-target-aux))
(defun fn2-scenario-target (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (slot gen) (fn2-scenario-target-aux (fn2-ops-rows fn2-ops) fn2-ops)
    (mv slot gen)))
(in-theory (disable fn2-scenario-target))

; A fresh receive/read needs an empty workspace. Reserving and resetting
; are separately checked core steps. Exhaustion is ordinary backpressure.
(defun fn2-scenario-empty-window (fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (b* (((mv found slot gen filled-bytes) (fn2-scenario-find-slot nil fn2-core))
       (- filled-bytes)
       ((when found) (mv :ok slot gen fn2-core fn2-own))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       (status (fn2-check-own fn2-core fn2-own)))
    (mv (if (eq status :pass) code :checker) slot gen fn2-core fn2-own)))
(in-theory (disable fn2-scenario-empty-window))

; Probe every pool slot's first uninitialized byte, including lent input.
; OWN observes both successful reads and refusals. Read the full initialized
; prefix when it belongs to our machine, which binds received bytes to client
; evidence before the echo path leases them out.
(defun fn2-scenario-read-bytes (left slot gen fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil
                  :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) fn2-own
    (b* (((mv code byte) (fn2-core-read slot gen (- left 1) 1 0 1 fn2-core))
         (fn2-own (fn2-own-observe-read slot gen (- left 1) code byte fn2-core fn2-own)))
      (fn2-scenario-read-bytes (- left 1) slot gen fn2-core fn2-own))))
(in-theory (disable fn2-scenario-read-bytes))
(defun fn2-scenario-slot-info (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (gen filled-bytes phase)
    (mv (fn2-pool-slot-gen slot fn2-pool)
        (fn2-pool-slot-fill slot fn2-pool)
        (fn2-pool-slot-state slot fn2-pool))
    (mv gen filled-bytes phase)))
(in-theory (disable fn2-scenario-slot-info))
(defun fn2-scenario-probe-reads (left fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil
                  :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) fn2-own
    (b* ((slot (- left 1))
         ((mv gen filled-bytes phase) (fn2-scenario-slot-info slot fn2-core))
         ((mv code byte) (fn2-core-read slot gen filled-bytes 1 0 1 fn2-core))
         (fn2-own (fn2-own-observe-read slot gen filled-bytes code byte fn2-core fn2-own))
         (fn2-own (if (eq phase :workspace)
                      (fn2-scenario-read-bytes filled-bytes slot gen fn2-core fn2-own)
                    fn2-own)))
      (fn2-scenario-probe-reads slot fn2-core fn2-own))))
(in-theory (disable fn2-scenario-probe-reads))
(defun fn2-scenario-nslots (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (n) (fn2-pool-nslots fn2-pool) n))
(in-theory (disable fn2-scenario-nslots))

(defun fn2-scenario-note-issued (code op kind mask fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (let ((fn2-own (if (eq code :ok)
                    (fn2-own-observe-issue op fn2-core fn2-own) fn2-own)))
    (mv (fn2-check-own fn2-core fn2-own)
        (if (eq code :ok) (logior (nfix mask) (ash 1 (nfix kind))) mask)
        fn2-core fn2-own)))
(in-theory (disable fn2-scenario-note-issued))

(defun fn2-scenario-machine (step nonce mask fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (let ((phase (mod (nfix step) 16)))
    (cond
     ((or (equal phase 0) (equal phase 1) (equal phase 6) (equal phase 9))
      (b* (((mv code slot gen fn2-core fn2-own)
            (fn2-scenario-empty-window fn2-core fn2-own))
           ((unless (eq code :ok))
            (mv (fn2-check-own fn2-core fn2-own) mask fn2-core fn2-own))
           ((mv code op ogen fn2-core)
            (if (equal phase 6)
                (fn2-issue-read (* 32 (mod (floor (nfix step) 16) 8)) slot gen 32 1 0 1 0 fn2-core)
              (fn2-issue-receive 0 nonce slot gen 32 1 0 1 0 fn2-core)))
           (- ogen))
        (fn2-scenario-note-issued code op
          (if (equal phase 6) *fn2-action-read* *fn2-action-receive*)
          mask fn2-core fn2-own)))
     ((or (equal phase 2) (equal phase 3) (equal phase 7) (equal phase 10))
      (b* (((mv found slot gen filled-bytes) (fn2-scenario-find-slot t fn2-core))
           ((unless found) (mv :pass mask fn2-core fn2-own))
           ((mv code op ogen fn2-core)
            (if (equal phase 3)
                (fn2-issue-write (* 32 (mod (floor (nfix step) 16) 8)) slot gen 0 filled-bytes
                                 (mod (floor (nfix step) 16) 2) 1 0 1 0 fn2-core)
              (fn2-issue-send 0 nonce slot gen 0 filled-bytes
                              (if (equal phase 10) 1 0) 1 0 1 0 fn2-core)))
           (- ogen))
        (fn2-scenario-note-issued code op
          (if (equal phase 3) *fn2-action-write* *fn2-action-send*) mask fn2-core fn2-own)))
     ((or (equal phase 4) (equal phase 11))
      (b* (((mv target gen) (fn2-scenario-target fn2-core))
           ((mv code op ogen fn2-core) (fn2-issue-cancel target gen 1 0 1 0 fn2-core))
           (- ogen))
        (fn2-scenario-note-issued code op *fn2-action-cancel* mask fn2-core fn2-own)))
     ((equal phase 5)
      (mv-let (code op ogen fn2-core) (fn2-issue-fence 1 0 1 0 fn2-core)
        (declare (ignore ogen))
        (fn2-scenario-note-issued code op *fn2-action-fence* mask fn2-core fn2-own)))
     ((equal phase 12)
      (mv-let (code op ogen fn2-core) (fn2-issue-close 0 nonce 1 0 1 0 fn2-core)
        (declare (ignore ogen))
        (fn2-scenario-note-issued code op *fn2-action-close* mask fn2-core fn2-own)))
     ((equal phase 13)
      (mv-let (code op ogen fn2-core) (fn2-issue-accept 0 nonce 1 0 1 0 fn2-core)
        (declare (ignore ogen))
        (fn2-scenario-note-issued code op *fn2-action-accept* mask fn2-core fn2-own)))
     (t
      (b* (((mv found slot gen filled-bytes) (fn2-scenario-find-slot t fn2-core))
           (- filled-bytes)
           ((unless found) (mv :pass mask fn2-core fn2-own))
           ((mv code fn2-core)
            (if (equal phase 15) (fn2-core-release slot gen 1 0 1 fn2-core)
              (fn2-core-reset slot gen 1 0 1 fn2-core)))
           (- code))
        (mv (fn2-check-own fn2-core fn2-own) mask fn2-core fn2-own))))))
(in-theory (disable fn2-scenario-machine))

(defun fn2-scenario-harvest (left fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil
                  :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) (mv (fn2-check-own fn2-core fn2-own) fn2-core fn2-own)
    (b* (((mv found op gen cell ev outcome reason count a b fn2-core)
          (fn2-harvest-one fn2-core))
         (- op gen cell ev outcome reason count a b)
         (status (fn2-check-own fn2-core fn2-own))
         ((unless (and found (eq status :pass))) (mv status fn2-core fn2-own)))
      (fn2-scenario-harvest (- left 1) fn2-core fn2-own))))
(in-theory (disable fn2-scenario-harvest))

(defun fn2-scenario-rounds (left step mask fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left)
      (mv (fn2-check-own fn2-core fn2-own) mask fn2-core fn2-sim fn2-own)
    (b* (((mv status mask fn2-core fn2-own)
          (fn2-scenario-machine step (fn2-sim-cap 0 fn2-sim) mask fn2-core fn2-own))
         ((unless (eq status :pass)) (mv status mask fn2-core fn2-sim fn2-own))
         (fn2-own (fn2-scenario-probe-reads (fn2-scenario-nslots fn2-core) fn2-core fn2-own))
         (status (fn2-check-own fn2-core fn2-own))
         ((unless (eq status :pass)) (mv status mask fn2-core fn2-sim fn2-own))
         ; Four issue steps with no take exercise a full tiny outbox. Other
         ; boundaries take a proper prefix, allowing multiple flights.
         ((mv took fn2-core fn2-sim fn2-own)
          (fn2-sim-take (if (< (mod (nfix step) 16) 4) 0 2)
                        fn2-core fn2-sim fn2-own))
         (- took)
         (status (fn2-check-own fn2-core fn2-own))
         ((unless (eq status :pass)) (mv status mask fn2-core fn2-sim fn2-own))
         ((mv found fn2-core fn2-sim fn2-own)
          (fn2-sim-advance fn2-core fn2-sim fn2-own))
         (- found)
         (status (fn2-check-own fn2-core fn2-own))
         ((unless (eq status :pass)) (mv status mask fn2-core fn2-sim fn2-own))
         ((mv status fn2-core fn2-own) (fn2-scenario-harvest 2 fn2-core fn2-own))
         ((unless (eq status :pass)) (mv status mask fn2-core fn2-sim fn2-own)))
      (fn2-scenario-rounds (- left 1) (+ 1 (nfix step)) mask fn2-core fn2-sim fn2-own))))
(in-theory (disable fn2-scenario-rounds))

(defun fn2-scenario-fault-mask (left fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) 0
    (logior (if (< 0 (fn2-sim-hitsi (- left 1) fn2-sim))
                (ash 1 (- left 1)) 0)
            (fn2-scenario-fault-mask (- left 1) fn2-sim))))
(in-theory (disable fn2-scenario-fault-mask))

; Count adapter submission, not merely successful core issue, in the report.
(defun fn2-scenario-action-mask (left fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) 0
    (logior (if (< 0 (fn2-sim-action-countsi (- left 1) fn2-sim))
                (ash 1 (- left 1)) 0)
            (fn2-scenario-action-mask (- left 1) fn2-sim))))
(in-theory (disable fn2-scenario-action-mask))

(defun fn2-scenario-recovery-loop
  (fuel i n bad-tail damaged never profile fn2-core fn2-sim fn2-own fn2-recovery-image)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own fn2-recovery-image)
                  :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x fuel))
                                 (:instance fn2-test-count-op (x fuel)))))))
  (if (or (zp fuel) (>= (nfix i) (nfix n)))
      (mv (fn2-check-own fn2-core fn2-own) fn2-core fn2-sim fn2-own fn2-recovery-image)
    (b* (((mv code next bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)
          (fn2-sim-recovery-step i n 0 bad-tail damaged never profile
                                 fn2-core fn2-sim fn2-own fn2-recovery-image))
         (status (fn2-check-own fn2-core fn2-own))
         ((unless (and (eq status :pass) (not (eq code :bounds))))
          (mv (if (eq status :pass) '(:fail :recovery-loader-bounds) status)
              fn2-core fn2-sim fn2-own fn2-recovery-image))
         ; Sticky device death is the model's named unavailable read, so
         ; recovery stops unknown. OWN still has to pass at this boundary.
         ((unless (member-eq code '(:ok :dead)))
          (mv status fn2-core fn2-sim fn2-own fn2-recovery-image)))
      (fn2-scenario-recovery-loop (- fuel 1) next n bad-tail damaged never profile
                                  fn2-core fn2-sim fn2-own fn2-recovery-image))))
(in-theory (disable fn2-scenario-recovery-loop))

; Scratch is allocated at each run's init, before any adapter action. The
; recovery scan then uses the exact durable bytes after the run's death cuts.
; This pool workload has made no storage acknowledgements (ack frontier zero).
(defun fn2-scenario-one-run (profile fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (with-local-stobj fn2-recovery-image
    (mv-let (status mask fn2-core fn2-sim fn2-own fn2-recovery-image)
      (b* ((fn2-recovery-image (fn2-recovery-init (fn2-sim-sectors profile) fn2-recovery-image))
           ((mv status mask fn2-core fn2-sim fn2-own)
            (fn2-scenario-rounds 96 0 0 fn2-core fn2-sim fn2-own))
           ((unless (eq status :pass))
            (mv status mask fn2-core fn2-sim fn2-own fn2-recovery-image))
           ((mv code n bad-tail damaged) (fn2-recover-start 0 fn2-recovery-image))
           ((unless (eq code :ok))
            (mv '(:fail :recovery-init) mask fn2-core fn2-sim fn2-own fn2-recovery-image))
           ((mv status fn2-core fn2-sim fn2-own fn2-recovery-image)
            (fn2-scenario-recovery-loop 64 0 n bad-tail damaged 0 profile
                                        fn2-core fn2-sim fn2-own fn2-recovery-image)))
        (mv status mask fn2-core fn2-sim fn2-own fn2-recovery-image))
      (mv status mask fn2-core fn2-sim fn2-own))))
(in-theory (disable fn2-scenario-one-run))

; The oldest retained observation prints first; at most the bounded ring
; appears in a failure report. Normal runs do not format these records.
(defun fn2-scenario-print-observations (left fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) nil
    (let ((i (mod (- (fn2-sim-ring-head fn2-sim) left) 64)))
      (progn$ (cw "OBS op=~x0 gen=~x1 cell=~x2 event=~x3 outcome=~x4 reason=~x5 count=~x6 aux0=~x7 aux1=~x8 fault=~x9~%"
                  (fn2-sim-ring-opi i fn2-sim) (fn2-sim-ring-geni i fn2-sim)
                  (fn2-sim-ring-celli i fn2-sim) (fn2-sim-ring-eventi i fn2-sim)
                  (fn2-sim-ring-outcomei i fn2-sim) (fn2-sim-ring-reasoni i fn2-sim)
                  (fn2-sim-ring-counti i fn2-sim) (fn2-sim-ring-aux0i i fn2-sim)
                  (fn2-sim-ring-aux1i i fn2-sim) (fn2-sim-ring-faulti i fn2-sim))
              (fn2-scenario-print-observations (- left 1) fn2-sim)))))
(in-theory (disable fn2-scenario-print-observations))

(defun fn2-scenario-runs (seed left profile passes mask fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil
                  :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left) (mv passes nil mask fn2-core fn2-sim fn2-own)
    (b* ((fn2-core (fn2-core-init profile fn2-core))
         (fn2-own (fn2-own-init profile fn2-own))
         (fn2-sim (fn2-sim-init seed :broad *fn2-scenario-revision* profile fn2-sim))
         ((mv status run-mask fn2-core fn2-sim fn2-own)
          (fn2-scenario-one-run profile fn2-core fn2-sim fn2-own))
         (- run-mask)
         (mask (logior (nfix mask) (fn2-scenario-action-mask 14 fn2-sim)
                       (ash (fn2-scenario-fault-mask 26 fn2-sim) 14))))
      (if (eq status :pass)
          (fn2-scenario-runs (+ 1 (nfix seed)) (- left 1) profile (+ 1 (nfix passes))
                             mask fn2-core fn2-sim fn2-own)
        (progn$ (cw "POOL FAILURE seed=~x0 digest=~x1 status=~x2 action-mask=~x3~%"
                    seed (fn2-sim-digest fn2-sim) status mask)
                (cw "POOL REPLAY fault-profile=~x0 revision=~x1~%"
                    (fn2-sim-profile-name fn2-sim) (fn2-sim-revision fn2-sim))
                (fn2-scenario-print-observations (min 64 (fn2-sim-observations fn2-sim)) fn2-sim)
          (mv passes seed mask fn2-core fn2-sim fn2-own))))))
(in-theory (disable fn2-scenario-runs))

(defun fn2-sim-run-pool-scenarios (first-seed nruns profile)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (passes failure mask fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (passes failure mask fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (passes failure mask fn2-core fn2-sim fn2-own)
              (fn2-scenario-runs first-seed nruns profile 0 0 fn2-core fn2-sim fn2-own)
              (mv passes failure mask fn2-core fn2-sim)))
          (mv passes failure mask fn2-core)))
      (progn$ (cw "POOL REVISION ~x0~%" *fn2-scenario-revision*)
              (cw "POOL SCENARIOS profile=~x0 first-seed=~x1 runs=~x2 passed=~x3 first-failure=~x4 action-mask=~x5 fault-choice-mask=~x6 OWN=~x7~%"
                  (if (equal profile *fn2-profile-tiny-near-limit*) :tiny-near-limit :tiny)
                  first-seed nruns passes failure (logand mask 16383)
                  (ash mask -14) (if failure :fail :pass))
              (mv passes failure)))))
(in-theory (disable fn2-sim-run-pool-scenarios))

; Deterministic controls make the swarm figure nonvacuous: fill the outbox
; while submission is delayed, retire every op and pool slot at its limit,
; and deliver a stale observation after each finished incarnation.
(defun fn2-scenario-ack (n fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code fn2-ops) (fn2-outbox-ack n fn2-ops) (mv code fn2-core)))
(in-theory (disable fn2-scenario-ack))
(defun fn2-scenario-post-fence (slot gen stale fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code fn2-ops fn2-own)
    (fn2-own-post-result 0 slot gen *fn2-event-fence-result*
                         *fn2-outcome-done* *fn2-reason-none* 0 0 0 stale fn2-ops fn2-own)
    (mv code fn2-core fn2-own)))
(in-theory (disable fn2-scenario-post-fence))
(defun fn2-scenario-op-retirement (left fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left)
      (mv-let (code op gen fn2-core) (fn2-issue-fence 1 0 1 0 fn2-core)
        (declare (ignore op gen))
        (mv (and (eq code :exhausted) (eq (fn2-check-own fn2-core fn2-own) :pass))
            fn2-core fn2-own))
    (b* (((mv code op gen fn2-core) (fn2-issue-fence 1 0 1 0 fn2-core))
         ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own))
         ((mv code fn2-core) (fn2-scenario-ack 1 fn2-core))
         ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own))
         ((mv code fn2-core fn2-own) (fn2-scenario-post-fence op gen nil fn2-core fn2-own))
         ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own))
         ((mv status fn2-core fn2-own) (fn2-scenario-harvest 1 fn2-core fn2-own))
         ((unless (eq status :pass)) (mv nil fn2-core fn2-own))
         ((mv code fn2-core fn2-own) (fn2-scenario-post-fence op gen t fn2-core fn2-own))
         ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own)))
      (fn2-scenario-op-retirement (- left 1) fn2-core fn2-own))))
(in-theory (disable fn2-scenario-op-retirement))
(defun fn2-scenario-pool-retirement (left fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (if (zp left)
      (mv-let (code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core)
        (declare (ignore slot gen))
        (mv (and (eq code :exhausted) (eq (fn2-check-own fn2-core fn2-own) :pass))
            fn2-core fn2-own))
    (b* (((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
         ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own))
         ((mv code fn2-core) (fn2-core-release slot gen 1 0 1 fn2-core))
         ((unless (and (member-eq code '(:ok :retired))
                        (eq (fn2-check-own fn2-core fn2-own) :pass)))
          (mv nil fn2-core fn2-own)))
      (fn2-scenario-pool-retirement (- left 1) fn2-core fn2-own))))
(in-theory (disable fn2-scenario-pool-retirement))
(defun fn2-scenario-fill-outbox (left fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-test-countdown (x left))
                                 (:instance fn2-test-count-op (x left)))))))
  (mv-let (code op gen fn2-core) (fn2-issue-fence 1 0 1 0 fn2-core)
    (declare (ignore op gen))
    (if (zp left)
        (mv (and (eq code :exhausted) (eq (fn2-check-own fn2-core fn2-own) :pass))
            fn2-core fn2-own)
      (if (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass))
          (fn2-scenario-fill-outbox (- left 1) fn2-core fn2-own)
        (mv nil fn2-core fn2-own)))))
(in-theory (disable fn2-scenario-fill-outbox))
(defun fn2-scenario-controls-run (fn2-core fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-own) :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (fn2-own (fn2-own-init *fn2-profile-tiny* fn2-own))
       ((mv ok fn2-core fn2-own) (fn2-scenario-fill-outbox 4 fn2-core fn2-own))
       ((unless ok) (mv :outbox fn2-core fn2-own))
       (fn2-core (fn2-core-init *fn2-profile-tiny-near-limit* fn2-core))
       (fn2-own (fn2-own-init *fn2-profile-tiny-near-limit* fn2-own))
       ((mv ok fn2-core fn2-own) (fn2-scenario-op-retirement 32 fn2-core fn2-own))
       ((unless ok) (mv :op-retirement fn2-core fn2-own))
       ((mv ok fn2-core fn2-own) (fn2-scenario-pool-retirement 32 fn2-core fn2-own)))
    (mv (if ok :pass :pool-retirement) fn2-core fn2-own)))
(in-theory (disable fn2-scenario-controls-run))
(defun fn2-scenario-controls ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (status fn2-core)
      (with-local-stobj fn2-own
        (mv-let (status fn2-core fn2-own)
          (fn2-scenario-controls-run fn2-core fn2-own) (mv status fn2-core)))
      (progn$ (cw "POOL CONTROLS: outbox saturation, op/pool retirement, stale results, OWN=~x0~%" status)
              status))))
(in-theory (disable fn2-scenario-controls))

; A4 executes the real scheduler and machines under the same adapter. These
; are test drivers (independent list oracles), not served runtime books.
(ld "../sim/echo-scenario.lisp" :ld-error-action :error)
(ld "scribe-scenario.lisp" :ld-error-action :error)
