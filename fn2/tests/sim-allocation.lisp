; Run from repo root: nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-a3-acl2-slots FN_ACL2_SLOTS=4 timeout -k 5 900 tools/acl2 < fn2/tests/sim-allocation-driver.lsp > build/a3-sim-allocation.log 2>&1 & echo $! > build/a3-sim-allocation.pid
; The live phase includes OWN evidence, physical byte effects, and strict
; successful completion checks. Initialization is allowed to allocate and is
; measured separately. Crash work omits only the explicit fn2-core-init call
; in fn2-sim-crash; full restarts include that initialization.
(in-package "ACL2")
(include-book "../sim/sim")
(include-book "std/util/bstar" :dir :system)

; Termination depends only on the explicit fuel, not the threaded states.
(defthm fn2-test-countdown
  (implies (not (zp x)) (o< (nfix (- x 1)) (nfix x)))
  :rule-classes nil)
(defthm fn2-test-count-op (o-p (nfix x)) :rule-classes nil)

(in-theory (disable fn2-core-wfp fn2-sim-ready fn2-own-wfp))

; These audit compositions call already framed APIs. Preserve the generator's
; exact statements, but keep the parent invariant closed instead of expanding
; every child's representation through five successive calls.

(defun fn2-sim-audit-drain (expected fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* (((mv took fn2-core fn2-sim fn2-own)
        (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
       ((unless (equal took 1)) (mv nil fn2-core fn2-sim fn2-own))
       ((mv completed fn2-core fn2-sim fn2-own)
        (fn2-sim-advance fn2-core fn2-sim fn2-own))
       ((mv found op gen cell ev outcome reason count a b fn2-core)
        (fn2-harvest-one fn2-core))
       (- cell a b)
       ; Harvest recycled this incarnation. Exercise the exact preallocated
       ; rejection snapshot, not only the normal result posting path.
       ((mv stray-code fn2-core fn2-sim fn2-own)
        (fn2-sim-post 0 op gen ev *fn2-outcome-done* *fn2-reason-none*
                      0 0 0 19 t fn2-core fn2-sim fn2-own)))
    (mv (and completed found (equal outcome *fn2-outcome-done*)
             (equal reason *fn2-reason-none*) (equal count expected)
             (eq stray-code :ok) (equal (fn2-own-error fn2-own) 0))
        fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-audit-drain (expected fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

; Close the parent observer boundary without unfolding it at every issue kind.
(defthm fn2-audit-observe-issue-own-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
           (fn2-own-wfp (fn2-own-observe-issue op fn2-core fn2-own)))
  :hints (("Goal" :in-theory (enable fn2-own-observe-issue fn2-core-wfp))))
(defthm fn2-audit-observe-issue-own-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
           (fn2-ownp (fn2-own-observe-issue op fn2-core fn2-own)))
  :hints (("Goal" :in-theory (enable fn2-own-observe-issue fn2-core-wfp))))
(in-theory (disable fn2-own-observe-issue))

(defun fn2-sim-audit-op (kind slot gen fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* ((nonce (fn2-sim-cap 0 fn2-sim))
       ((mv code op ogen fn2-core)
        (case kind
          (0 (fn2-issue-read 0 slot gen 1 1 0 1 0 fn2-core))
          (1 (fn2-issue-write 0 slot gen 0 1 0 1 0 1 0 fn2-core))
          (2 (fn2-issue-fence 1 0 1 0 fn2-core))
          (3 (fn2-issue-send 0 nonce slot gen 0 1 0 1 0 1 0 fn2-core))
          (otherwise (fn2-issue-receive 0 nonce slot gen 1 1 0 1 0 fn2-core))))
       (- ogen)
       ((unless (eq code :ok)) (mv nil fn2-core fn2-sim fn2-own))
       (fn2-own (fn2-own-observe-issue op fn2-core fn2-own)))
    (fn2-sim-audit-drain (if (equal kind 2) 0 1) fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-audit-op (kind slot gen fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

; Reopen and refill the preallocated pipe after each death so the measured
; send/receive paths transfer bytes, rather than only returning Closed.
(defun fn2-sim-audit-connect (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (let ((old-nonce (fn2-sim-cap 0 fn2-sim)))
    (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
      (fn2-sim-network)
      (b* (((mv & fn2-sim-network) (fn2-network-close 0 old-nonce fn2-sim-network))
           ((mv & nonce fn2-sim-network) (fn2-network-accept 0 fn2-sim-network)))
        (fn2-sim-client-feed 0 nonce 1 65 fn2-sim-network))
      fn2-sim)))
(fn2-sim-preserves fn2-sim-audit-connect (fn2-sim) :forward t
  :hyps ((fn2-simp fn2-sim) (fn2-sim-ready fn2-sim))
  :specs (("-TYPE" fn2-simp nil) ("-READY" fn2-sim-ready nil) ("-WFP" fn2-sim-wfp nil)))

(defun fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* ((fn2-sim (fn2-sim-audit-connect fn2-sim))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv nil fn2-core fn2-sim fn2-own))
       ((mv a fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 0 slot gen fn2-core fn2-sim fn2-own))
       ((mv b fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 1 slot gen fn2-core fn2-sim fn2-own))
       ((mv c fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 2 slot gen fn2-core fn2-sim fn2-own))
       ((mv d fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 3 slot gen fn2-core fn2-sim fn2-own))
       ((mv e fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 4 slot gen fn2-core fn2-sim fn2-own))
       ((mv fn2-core fn2-sim fn2-own)
        (fn2-sim-crash *fn2-profile-tiny* fn2-core fn2-sim fn2-own)))
    (mv (and a b c d e) fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 1
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 2
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 3
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 4
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 5
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 6
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-cycle (fn2-core fn2-sim fn2-own) :part 7
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-audit-loop (left fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own) (natp left)) :measure (nfix left)))
  (if (zp left) (mv t fn2-core fn2-sim fn2-own)
    (mv-let (ok fn2-core fn2-sim fn2-own) (fn2-sim-audit-cycle fn2-core fn2-sim fn2-own)
      (if ok (fn2-sim-audit-loop (- left 1) fn2-core fn2-sim fn2-own)
        (mv nil fn2-core fn2-sim fn2-own)))))
(fn2-sim-preserves fn2-sim-audit-loop (left fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defthm fn2-audit-crash-flight-core-car-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                (fn2-ownp fn2-own) (fn2-own-wfp fn2-own))
           (fn2-core-wfp (car (fn2-sim-crash-flight-writes left fn2-core fn2-sim fn2-own))))
  :hints (("Goal" :use fn2-sim-crash-flight-writes-core-wfp
                   :in-theory (disable fn2-sim-crash-flight-writes-core-wfp))))

(defun fn2-sim-audit-crash-work-loop (left fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (natp left) (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (zp left) (mv t fn2-core fn2-sim fn2-own)
    (mv-let (fn2-core fn2-sim fn2-own)
      (b* (((mv fn2-core fn2-sim fn2-own)
             (fn2-sim-crash-flight-writes (fn2-sim-rows fn2-sim) fn2-core fn2-sim fn2-own))
            (fn2-sim (fn2-sim-crash-state fn2-sim))
            (fn2-own (fn2-own-restart fn2-own)))
        (mv fn2-core fn2-sim fn2-own))
      (fn2-sim-audit-crash-work-loop (- left 1) fn2-core fn2-sim fn2-own))))
(fn2-sim-preserves fn2-sim-audit-crash-work-loop (left fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-audit-init-loop (left fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (natp left) (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (zp left) (mv t fn2-core fn2-sim fn2-own)
    (mv-let (fn2-core fn2-sim fn2-own)
      (let ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))) (mv fn2-core fn2-sim fn2-own))
      (fn2-sim-audit-init-loop (- left 1) fn2-core fn2-sim fn2-own))))
(fn2-sim-preserves fn2-sim-audit-init-loop (left fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-audit-death-loop (left fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (natp left) (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (zp left) (mv t fn2-core fn2-sim fn2-own)
    (mv-let (fn2-core fn2-sim fn2-own)
      (fn2-sim-crash *fn2-profile-tiny* fn2-core fn2-sim fn2-own)
      (fn2-sim-audit-death-loop (- left 1) fn2-core fn2-sim fn2-own))))
(fn2-sim-preserves fn2-sim-audit-death-loop (left fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

; Reuse the reserved buffer by resetting its fill before each five-operation
; cycle; read and receive each append one byte. Reopen/refill the pipe too.
(defun fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own)
                  :guard (and (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (b* (((mv reset-code fn2-core) (fn2-core-reset slot gen 1 0 1 fn2-core))
       ((unless (eq reset-code :ok)) (mv nil fn2-core fn2-sim fn2-own))
       (fn2-sim (fn2-sim-audit-connect fn2-sim))
       ((mv a fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 0 slot gen fn2-core fn2-sim fn2-own))
       ((mv b fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 1 slot gen fn2-core fn2-sim fn2-own))
       ((mv c fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 2 slot gen fn2-core fn2-sim fn2-own))
       ((mv d fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 3 slot gen fn2-core fn2-sim fn2-own))
       ((mv e fn2-core fn2-sim fn2-own) (fn2-sim-audit-op 4 slot gen fn2-core fn2-sim fn2-own)))
    (mv (and a b c d e) fn2-core fn2-sim fn2-own)))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 1
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 2
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 3
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 4
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 5
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 6
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))
(fn2-sim-preserves fn2-sim-audit-live-cycle (slot gen fn2-core fn2-sim fn2-own) :part 7
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

(defun fn2-sim-audit-live-loop (left slot gen fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :measure (nfix left)
                  :guard (and (natp left) (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
                              (fn2-own-wfp fn2-own))))
  (if (zp left) (mv t fn2-core fn2-sim fn2-own)
    (mv-let (ok fn2-core fn2-sim fn2-own)
      (fn2-sim-audit-live-cycle slot gen fn2-core fn2-sim fn2-own)
      (if ok (fn2-sim-audit-live-loop (- left 1) slot gen fn2-core fn2-sim fn2-own)
        (mv nil fn2-core fn2-sim fn2-own)))))
(fn2-sim-preserves fn2-sim-audit-live-loop (left slot gen fn2-core fn2-sim fn2-own) :part nil
  :carriers ((fn2-core 1 :prefix "-CORE") (fn2-sim 2 :invariant fn2-sim-ready :prefix "-SIM" :suffix "-READY") (fn2-own 3 :prefix "-OWN")))

; Prove creation once, keeping the large nested constant out of the audit's
; composition guard. The runtime and the 300000-step budget are unchanged.
(defthm fn2-audit-create-core-type
  (fn2-corep (create-fn2-core))
  :hints (("Goal" :in-theory (enable fn2-corep create-fn2-core))))
(in-theory (disable create-fn2-core))

(defun fn2-sim-allocation-audit ()
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn2-simp fn2-ownp)))))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (ok fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (ok fn2-core fn2-sim fn2-own)
              (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
                   (fn2-own (fn2-own-init *fn2-profile-tiny* fn2-own))
                   (fn2-sim (fn2-sim-init 0 :none "A3-allocation" *fn2-profile-tiny* fn2-sim))
                   ((mv ok fn2-core fn2-sim fn2-own) (fn2-sim-audit-loop 2 fn2-core fn2-sim fn2-own))
                   ((unless ok) (mv nil fn2-core fn2-sim fn2-own)))
                (b* (((mv work-ok fn2-core fn2-sim fn2-own)
                       (time$ (fn2-sim-audit-crash-work-loop 100 fn2-core fn2-sim fn2-own)
                              :msg "CRASH WORK: 100 deaths excluding only explicit core-init, ~sa bytes, ~st seconds~%"))
                     ((mv init-ok fn2-core fn2-sim fn2-own)
                       (time$ (fn2-sim-audit-init-loop 100 fn2-core fn2-sim fn2-own)
                              :msg "INITIALIZATION (allocation permitted): 100 core-init calls, ~sa bytes, ~st seconds~%"))
                     ((mv deaths-ok fn2-core fn2-sim fn2-own)
                      (time$ (fn2-sim-audit-death-loop 100 fn2-core fn2-sim fn2-own)
                             :msg "FULL RESTART: 100 deaths including core-init, ~sa bytes, ~st seconds~%"))
                     ((mv code slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
                     ((unless (and work-ok init-ok deaths-ok (eq code :ok))) (mv nil fn2-core fn2-sim fn2-own)))
                  (time$ (fn2-sim-audit-live-loop 10000 slot gen fn2-core fn2-sim fn2-own)
                         :msg "LIVE: 50000 strict successful operations, ~sa bytes, ~st seconds~%")))
              (mv ok fn2-core fn2-sim)))
          (mv ok fn2-core)))
      ok)))

(in-theory (disable fn2-sim-allocation-audit))
(assert-event (fn2-assert-compliant-p
  '(fn2-sim-audit-loop fn2-sim-audit-crash-work-loop fn2-sim-audit-init-loop fn2-sim-audit-death-loop
    fn2-sim-audit-live-loop fn2-sim-allocation-audit) (w state)))
