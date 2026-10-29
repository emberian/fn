; Seeded device acceptance phase. Each trial starts a fresh device,
; writes real pending bytes, then lets the ordinary adapter select a fault
; for a Read, Write, Fence or Receive flight. Fatal faults cannot starve later classes.
(in-package "ACL2")
(defun fn2-device-broad-one (seed fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (fn2-own (fn2-own-init *fn2-profile-tiny* fn2-own))
       (fn2-sim (fn2-sim-init seed :broad *fn2-scenario-revision* *fn2-profile-tiny* fn2-sim))
       (fn2-sim (update-fn2-sim-fault-budget 0 fn2-sim))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv nil fn2-core fn2-sim fn2-own))
       ((mv status fn2-core fn2-own) (fn2-fault-control-fill 0 32 slot gen fn2-core fn2-own))
       ((unless (eq status :pass)) (mv nil fn2-core fn2-sim fn2-own))
       ; Unit 1 admits garbage tears: selecting unit 0 forces the same PRNG
       ; word even, hence a zero tear that cannot change an initially zero disk.
       ((mv code op & fn2-core) (fn2-issue-write 512 slot gen 0 32 0 1 0 1 0 fn2-core))
       (fn2-own (if (eq code :ok) (fn2-own-observe-issue op fn2-core fn2-own) fn2-own))
       ((unless (and (eq code :ok) (eq (fn2-check-own fn2-core fn2-own) :pass)))
        (mv nil fn2-core fn2-sim fn2-own))
       ((mv taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
       ((unless (= taken 1)) (mv nil fn2-core fn2-sim fn2-own))
       ((mv status fn2-core fn2-sim fn2-own) (fn2-fault-control-step 26 fn2-core fn2-sim fn2-own))
       ((unless (eq status :pass)) (mv nil fn2-core fn2-sim fn2-own))
       ((mv word fn2-sim) (fn2-sim-random fn2-sim))
       (kind (nth (mod word 4) (list *fn2-action-read* *fn2-action-write* *fn2-action-fence* *fn2-action-receive*)))
       ((mv ok & fn2-core fn2-own) (fn2-fault-control-issue kind slot gen fn2-core fn2-own))
       ((unless ok) (mv nil fn2-core fn2-sim fn2-own))
       ((mv taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
       ((unless (= taken 1)) (mv nil fn2-core fn2-sim fn2-own))
       (fn2-sim (update-fn2-sim-fault-budget 128 fn2-sim))
       ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-advance fn2-core fn2-sim fn2-own))
       ((mv status fn2-core fn2-own) (fn2-scenario-harvest 2 fn2-core fn2-own)))
    (mv (eq status :pass) fn2-core fn2-sim fn2-own)))
(in-theory (disable fn2-device-broad-one))

(defun fn2-device-broad-rounds (left seed counts fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil :use ((:instance fn2-test-countdown (x left))
                                                       (:instance fn2-test-count-op (x left)))))))
  (if (zp left) (mv :pass counts fn2-core fn2-sim fn2-own)
    (b* (((mv ok fn2-core fn2-sim fn2-own) (fn2-device-broad-one seed fn2-core fn2-sim fn2-own))
         ((unless ok) (mv (list :fail :device-broad seed) counts fn2-core fn2-sim fn2-own))
         (counts (fn2-echo-merge-stats (fn2-echo-fault-counts *fn2-echo-fault-names* 0 fn2-sim) counts)))
      (fn2-device-broad-rounds (- left 1) (fn2-prng-mix32 (fn2-u32 (+ 1 (nfix seed)))) counts
                               fn2-core fn2-sim fn2-own))))
(in-theory (disable fn2-device-broad-rounds))

(defun fn2-sim-run-device-broad (seed trials)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (answer fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (status counts fn2-core fn2-sim fn2-own)
              (fn2-device-broad-rounds trials seed nil fn2-core fn2-sim fn2-own)
              (progn$ (cw "DEVICE BROAD seed=~x0 trials=~x1 applied=~x2 OWN=~x3 stop=~x4~%"
                          seed trials counts status (fn2-stop-reason-code->keyword (fn2-core-stop-reason fn2-core)))
                      (mv (list status counts) fn2-core fn2-sim))))
          (mv answer fn2-core))) answer)))
(in-theory (disable fn2-sim-run-device-broad))
