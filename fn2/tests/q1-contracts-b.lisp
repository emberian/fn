; Q1's honest classification for layer B's kinds (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 3): the independent contract of fn2-recovery-machine. Its oracle is B's RECOVERY checker
; (sim/check-recovery.lisp: HISTORY's allowed-recovery relation over the harness's own ground truth,
; decoded from the durable image independently of the recovery row) and the death control
; (sim/check-death.lisp: death leaves every core child at its init values). Nothing on the checking
; side calls a recovery handler.
;
; Why this book has its own runner: B's scenarios drive recovery by stepping the executor's parts
; (fn2-exec-harvest, fn2-exec-principal; check-recovery's fn2-b-rec-drive), so no fn2-turn runs and
; Q1's TRACE per case never sees a recovery transition. Here the same pre-death workload
; (sim-layer-b's fn2-b-rounds), death, post-death faults and ground truth are B's, and recovery runs
; on an executor-initialized core through fn2-turn, the served loop, with the simulator completing
; I/O between turns as the scribe's contract does.
(in-package "ACL2")
(include-book "sim-layer-b")
(include-book "../sim/check-death")

(defun fn2-q1r-outbox (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-outbox-queued fn2-ops) n))
; Turns until the recovery row is :done, the core stops, or FUEL runs out.
(defun fn2-q1r-drive (fuel id fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) (mv :fuel fn2-core fn2-sim fn2-own))
        ((equal (fn2-machine-phase id fn2-core) *fn2-recovery-machine-state-done*) (mv :done fn2-core fn2-sim fn2-own))
        ((not (equal (fn2-core-stop-reason fn2-core) 0)) (mv :stopped fn2-core fn2-sim fn2-own))
        (t (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix (fn2-q1r-outbox fn2-core) 0 fn2-core fn2-sim fn2-own))
                ((mv & & & & fn2-core) (fn2-turn fn2-core))
                ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix (fn2-q1r-outbox fn2-core) 0 fn2-core fn2-sim fn2-own))
                ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-advance-with-clients nil nil fn2-core fn2-sim fn2-own)))
             (fn2-q1r-drive (- fuel 1) id fn2-core fn2-sim fn2-own)))))
; The witness words presented before start (check-recovery's fn2-b-rec-run does the same).
(defun fn2-q1r-present (words fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv c0 fn2-core) (fn2-recovery-present-witness-word 0 (nth 0 words) fn2-core))
       ((mv c1 fn2-core) (fn2-recovery-present-witness-word 1 (nth 1 words) fn2-core))
       ((mv c2 fn2-core) (fn2-recovery-present-witness-word 2 (nth 2 words) fn2-core))
       ((mv c3 fn2-core) (fn2-recovery-present-witness-word 3 (nth 3 words) fn2-core))
       ((mv c4 fn2-core) (fn2-recovery-present-witness-word 4 (nth 4 words) fn2-core))
       ((mv c5 fn2-core) (fn2-recovery-present-witness-word 5 (nth 5 words) fn2-core))
       ((mv c6 fn2-core) (fn2-recovery-present-witness-word 6 (nth 6 words) fn2-core))
       ((mv c7 fn2-core) (fn2-recovery-present-witness-word 7 (nth 7 words) fn2-core)))
    (mv (and (eq c0 :ok) (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok) (eq c5 :ok) (eq c6 :ok) (eq c7 :ok))
        fn2-core)))
; Scenario 15/16's case (sim-layer-b's fn2-b-case with POST = (MODEL FAULTS SECTORS)) with recovery
; through fn2-turn. Result: (status stale class outcome recovered events).
(defun fn2-q1r-case (profile seed mode members post fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((model (nth 0 post)) (faults (nth 1 post))
       (profile (fn2-b-test-profile (put-assoc-equal :sim-sectors (nth 2 post) profile) mode))
       (fn2-core (fn2-core-init profile fn2-core))
       ((mv epoch-code fn2-core)
        (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
          (code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
       (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
       (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
       ((mv ca ea & fn2-core) (fn2-b-start a members 1 mode b fn2-core))
       ((mv cb eb & fn2-core) (fn2-b-start b members (+ 1 members) mode a fn2-core))
       (fn2-core (fn2-exec-wake a fn2-core))
       (fn2-core (fn2-exec-wake b fn2-core))
       (fn2-sim (fn2-sim-init seed :none "B3b" profile fn2-sim))
       (fn2-own (fn2-own-init profile fn2-own))
       ((unless (and (eq epoch-code :ok) (eq ca :ok) (eq cb :ok)))
        (mv (list (list :admission epoch-code ca cb)) fn2-core fn2-sim fn2-own))
       ((mv & & & manifests events & & & & fn2-core fn2-sim fn2-own)
        (fn2-b-rounds 10000 0 1000000 seed :none nil (list a b) members nil nil (reverse (append ea eb))
                      0 0 0 nil 0 fn2-core fn2-sim fn2-own))
       ; Death, then the death control, then the executor's init on the fresh core (the turn loop's
       ; engine; listeners in :null mode, so no network operation is issued).
       ((mv fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own))
       (stale (fn2-b-death-difference profile fn2-core))
       (fn2-core (fn2-init-executor profile :null nil fn2-core))
       ((mv code events excluded witness fn2-sim)
        (fn2-b-rec-inject faults manifests (reverse (append (reverse events) (list '(:crash)))) nil nil fn2-sim))
       ((unless (eq code :ok)) (mv (list (list :inject code)) fn2-core fn2-sim fn2-own))
       (truth (fn2-b-rec-truth manifests excluded (fn2-b-capacity :extent-slots 16 profile) fn2-sim))
       (id (fn2-machine-global-id *fn2-recovery-machine-kind* 0 profile))
       ((mv w fn2-core) (if witness (fn2-q1r-present (cdr witness) fn2-core) (mv t fn2-core)))
       ((mv scode fn2-core) (fn2-recovery-start id (fn2-b-rec-assume model) (if witness (car witness) 0) fn2-core))
       ((unless (and w (eq scode :ok))) (mv (list (list :start scode)) fn2-core fn2-sim fn2-own))
       ((mv status fn2-core fn2-sim fn2-own) (fn2-q1r-drive 20000 id fn2-core fn2-sim fn2-own))
       (extents (fn2-b-rec-extents 1 (fn2-machine-rc-chain id fn2-core) fn2-core)))
    (mv (list status stale (nth (fn2-machine-rc-class id fn2-core) *fn2-rec-classes*)
              (nth (fn2-machine-rc-witness-outcome id fn2-core) *fn2-rec-witness-outcomes*)
              (fn2-b-rec-history 1 extents manifests fn2-sim) (append events truth))
        fn2-core fn2-sim fn2-own)))
; Scenarios 15 and 16's fault profile: :broad, with FRONTIER credited or not.
(defun fn2-q1r-post (frontier budget faults)
  (declare (xargs :verify-guards nil))
  (list (fn2-cm-profile :broad t t frontier 0 budget) faults 16))
(defun fn2-recovery-served (mode frontier budget faults)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (answer fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (answer fn2-core fn2-sim fn2-own)
              (fn2-q1r-case *fn2-profile-tiny* 20261028 mode 2 (fn2-q1r-post frontier budget faults)
                            fn2-core fn2-sim fn2-own)
              (mv answer fn2-core fn2-sim)))
          (mv answer fn2-core)))
      answer)))
; The oracle over a run: recovery finished, death left nothing behind, and RECOVERY accepts the
; classification, the recovered history (decoded by the harness) and the witness outcome.
(defun fn2-q1r-recovery-ok-p (r frontier budget)
  (declare (xargs :verify-guards nil))
  (and (equal (nth 0 r) :done) (null (nth 1 r))
       (fn2-check-recovery (nth 5 r) (fn2-cm-profile :broad t t frontier 0 budget) (nth 2 r) (nth 4 r) (nth 3 r))))
(defun fn2-q1r-ok (mode frontier budget faults)
  (declare (xargs :verify-guards nil))
  (fn2-q1r-recovery-ok-p (fn2-recovery-served mode frontier budget faults) frontier budget))
; Scenario 15 and 16's post-death fault sets (sim-layer-b.lsp), each (frontier budget faults).
(defconst *fn2-q1r-cases*
  '((nil 1 nil) (nil 1 ((:corrupt 1 0 100))) (nil 1 ((:corrupt 1 2 3000))) (nil 1 ((:corrupt-last 2 100)))
    (nil 1 ((:misdirect 2 2 3))) (nil 1 ((:misdirect 1 1 4))) (nil 1 ((:rollback 1))) (nil 1 ((:rollback 0)))
    (t 0 ((:witness 2) (:rollback 1))) (t 0 ((:rollback 1))) (nil 0 ((:witness 2) (:rollback 1)))
    (t 0 ((:witness 1) (:rollback 1))) (t 0 ((:witness 2))) (t 0 ((:witness 2) (:rollback 0)))))
(defthm-owed fn2-recovery-machine-recovers (mode case)
  (implies (and (member mode '(0 1)) (member-equal case *fn2-q1r-cases*))
           (fn2-q1r-ok mode (nth 0 case) (nth 1 case) (nth 2 case)))
  :schema :invariant :claim :semantic
  :teeth (fn2-recovery-recovers-positive fn2-recovery-recovers-negative)
  :doc "After scenario 15/16's pre-death workload, death and each post-death fault set, in both barrier modes, the recovery row run through fn2-turn reaches :done on a core the death control finds fresh, and RECOVERY (HISTORY's allowed-recovery relation over the harness's own decoding of the durable image, plus the witness outcome) accepts its classification, recovered history and witness outcome.")
(defun fn2-q1r-all (mode cases)
  (declare (xargs :verify-guards nil))
  (or (atom cases)
      (and (or (fn2-q1r-ok mode (nth 0 (car cases)) (nth 1 (car cases)) (nth 2 (car cases)))
               (cw "RECOVERY CONTRACT mode ~x0 case ~x1 FAIL ~x2~%" mode (car cases)
                   (let ((r (fn2-recovery-served mode (nth 0 (car cases)) (nth 1 (car cases)) (nth 2 (car cases)))))
                     (list (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r) (len (nth 4 r))))))
           (fn2-q1r-all mode (cdr cases)))))
; Positive: every case in both modes.
(defun fn2-recovery-recovers-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1r-all 0 *fn2-q1r-cases*) (fn2-q1r-all 1 *fn2-q1r-cases*)))
; Negative: the conclusion refuses a wrong recovery: the intact run's recovered history without its
; last batch, and the rollback-detected run reported :none.
(defun fn2-recovery-recovers-negative ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-recovery-served 0 nil 1 nil)) (w (fn2-recovery-served 0 t 0 '((:witness 2) (:rollback 1)))))
    (and (fn2-q1r-recovery-ok-p r nil 1) (consp (nth 4 r))
         (not (fn2-q1r-recovery-ok-p (update-nth 4 (butlast (nth 4 r) 1) r) nil 1))
         (fn2-q1r-recovery-ok-p w t 0) (eq (nth 3 w) :rollback-detected)
         (not (fn2-q1r-recovery-ok-p (update-nth 3 :none w) t 0)))))

(fn2-assert-owed-teeth fn2-recovery-machine-recovers)
(value-triple (cw "Q1 CONTRACTS B: recovery teeth PASS~%"))
