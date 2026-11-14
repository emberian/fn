; Real issued storage operations through the explicit native cut program.
(in-package "ACL2")
(include-book "../sim/native-cut-program")
(include-book "../sim/check-core")

(defun fn2-native-cut-fixture (takep fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (fn2-own (fn2-own-init *fn2-profile-tiny* fn2-own))
       (fn2-sim (fn2-sim-init 7 :friendly "native-cut-unit" *fn2-profile-tiny* fn2-sim))
       ((mv code range gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
       ((unless (eq code :ok)) (mv nil 0 fn2-core fn2-sim fn2-own))
       ((mv code fn2-core) (fn2-core-write range gen 0 17 1 0 1 fn2-core))
       (fn2-own (fn2-own-observe-core-write range gen 0 code 17 fn2-core fn2-own))
       ((unless (eq code :ok)) (mv nil 0 fn2-core fn2-sim fn2-own))
       ((mv code op & fn2-core) (fn2-issue-write 0 range gen 0 1 0 1 0 1 0 fn2-core))
       (fn2-own (fn2-own-observe-issue op fn2-core fn2-own))
       ((unless (eq code :ok)) (mv nil 0 fn2-core fn2-sim fn2-own))
       ((mv taken fn2-core fn2-sim fn2-own)
        (if takep (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)
          (mv 0 fn2-core fn2-sim fn2-own))))
    (mv (and (= taken (if takep 1 0)) (fn2-corep fn2-core) (fn2-simp fn2-sim) (fn2-ownp fn2-own)
             (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim)
             (fn2-own-wfp fn2-own) (unsigned-byte-p 32 0)
             (or (not takep) (fn2-sim-native-storagep op fn2-sim)) (fn2-sim-native-faultp *fn2-fault-none*))
        op fn2-core fn2-sim fn2-own)))

(defun fn2-native-cut-write-control (cut fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv hyps op fn2-core fn2-sim fn2-own) (fn2-native-cut-fixture t fn2-core fn2-sim fn2-own))
       ((mv found fn2-core fn2-sim fn2-own) (fn2-sim-native-cut cut op *fn2-fault-none* 0 fn2-core fn2-sim fn2-own))
       (posted (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                 (n) (fn2-ops-post-count fn2-ops) n)))
    (mv (and hyps found (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim) (fn2-own-wfp fn2-own)
             (equal (fn2-sim-active op fn2-sim) 0)
             (if (eq cut :finish)
                 (and (= posted 1) (= (fn2-sim-deaths fn2-sim) 0) (= (fn2-sim-stamp fn2-sim) 1))
               (and (= posted 0) (= (fn2-sim-deaths fn2-sim) 1)
                    ; A returned physical write must not be executed again by crash.
                    (or (eq cut :before-physical) (= (fn2-sim-stamp fn2-sim) 1)))))
        fn2-core fn2-sim fn2-own)))

(defun fn2-native-cut-packet-control (fault expected-count expected-outcome expected-reason fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv hyps op fn2-core fn2-sim fn2-own) (fn2-native-cut-fixture t fn2-core fn2-sim fn2-own))
       ((mv status packet fn2-core fn2-sim fn2-own) (fn2-sim-native-stage op fault 0 fn2-core fn2-sim fn2-own))
       ((mv found &) (fn2-sim-find-write (fn2-sim-rows fn2-sim) 0 fn2-sim))
       (returned (and (eq status :returned) (fn2-sim-native-packetp packet fn2-sim)
                      (eq (nth 5 packet) :ok) (= (nth 6 packet) expected-count) (= (nth 7 packet) 0)
                      (= (fn2-sim-active op fn2-sim) *fn2-sim-native-returned*) (not found)))
       (stamp (fn2-sim-stamp fn2-sim))
       ((mv reissued fn2-core fn2-sim fn2-own)
        (fn2-sim-complete op fault 0 fn2-core fn2-sim fn2-own))
       (no-reissue (and (not reissued) (= (fn2-sim-stamp fn2-sim) stamp)
                        (= (fn2-sim-active op fn2-sim) *fn2-sim-native-returned*)))
       ((mv posted fn2-core fn2-sim fn2-own) (fn2-sim-native-post packet fn2-core fn2-sim fn2-own))
       (terminal (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                   (ok) (and (= (fn2-ops-c0-posted op fn2-ops) 1)
                             (= (fn2-ops-c0-outcome op fn2-ops) expected-outcome)
                             (= (fn2-ops-c0-reason op fn2-ops) expected-reason)
                             (= (fn2-ops-c0-count op fn2-ops) expected-count)) ok)))
    (mv (and hyps returned no-reissue posted terminal) fn2-core fn2-sim fn2-own)))

(defun fn2-native-cut-fence-control (fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv ok fn2-core fn2-sim fn2-own) (fn2-native-cut-write-control :finish fn2-core fn2-sim fn2-own))
       ((mv code op & fn2-core) (fn2-issue-fence 1 0 1 0 fn2-core))
       (fn2-own (fn2-own-observe-issue op fn2-core fn2-own))
       ((mv taken fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own))
       ((mv found fn2-core fn2-sim fn2-own) (fn2-sim-native-cut :after-physical op *fn2-fault-none* 0 fn2-core fn2-sim fn2-own))
       (byte (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
               (b) (fn2-sim-storage-durable 0 fn2-sim-storage) b)))
    (mv (and ok (eq code :ok) (= taken 1) found (= byte 17)
             (= (fn2-sim-deaths fn2-sim) 1) (= (fn2-sim-stamp fn2-sim) 2))
        fn2-core fn2-sim fn2-own)))

(defun fn2-native-cut-take-control (cut fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv hyps op fn2-core fn2-sim fn2-own) (fn2-native-cut-fixture nil fn2-core fn2-sim fn2-own))
       ((mv found fn2-core fn2-sim fn2-own) (fn2-sim-native-take-cut cut fn2-core fn2-sim fn2-own)))
    (mv (and hyps found (= (fn2-sim-deaths fn2-sim) 1)
             (= (fn2-sim-active op fn2-sim) 0)
             (or (eq cut :after-take) (= (fn2-sim-stamp fn2-sim) 0)))
        fn2-core fn2-sim fn2-own)))

(defun fn2-native-cut-controls ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (ok fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (ok fn2-core fn2-sim fn2-own)
              (b* (((mv a fn2-core fn2-sim fn2-own) (fn2-native-cut-write-control :before-physical fn2-core fn2-sim fn2-own))
                   ((mv b fn2-core fn2-sim fn2-own) (fn2-native-cut-write-control :after-physical fn2-core fn2-sim fn2-own))
                   ((mv c fn2-core fn2-sim fn2-own) (fn2-native-cut-write-control :after-post fn2-core fn2-sim fn2-own))
                   ((mv d fn2-core fn2-sim fn2-own) (fn2-native-cut-write-control :finish fn2-core fn2-sim fn2-own))
                   ((mv e fn2-core fn2-sim fn2-own) (fn2-native-cut-packet-control *fn2-fault-none* 1 *fn2-outcome-done* *fn2-reason-none* fn2-core fn2-sim fn2-own))
                   ((mv f fn2-core fn2-sim fn2-own) (fn2-native-cut-fence-control fn2-core fn2-sim fn2-own))
                   ((mv g fn2-core fn2-sim fn2-own) (fn2-native-cut-packet-control *fn2-fault-short-write* 0 *fn2-outcome-failed* *fn2-reason-uncertain* fn2-core fn2-sim fn2-own))
                   ((mv h fn2-core fn2-sim fn2-own) (fn2-native-cut-take-control :before-take fn2-core fn2-sim fn2-own))
                   ((mv i fn2-core fn2-sim fn2-own) (fn2-native-cut-take-control :after-take fn2-core fn2-sim fn2-own)))
                (mv (list a b c d e f g h i) fn2-core fn2-sim fn2-own))
              (mv ok fn2-core fn2-sim)))
          (mv ok fn2-core)))
      ok)))

(assert-event (equal (fn2-native-cut-controls) '(t t t t t t t t t)))

; Whole-formula witnesses use logical stobjs so both executions start from
; the identical immutable state.  The live controls above separately exercise
; actual mutable stobjs and the physical-return crash path.
(defun-nx fn2-native-cut-atomic-witness (remove-pending)
  (mv-let (ready op c s o)
    (fn2-native-cut-fixture t (create-fn2-core) (create-fn2-sim) (create-fn2-own))
    (let ((s (if remove-pending (fn2-sim-set-active op 0 s) s)))
      (and ready (fn2-corep c) (fn2-simp s) (fn2-ownp o)
           (fn2-core-wfp c) (fn2-sim-ready s) (fn2-own-wfp o)
           (unsigned-byte-p 32 0) (fn2-sim-native-faultp *fn2-fault-none*)
           (if remove-pending (not (fn2-sim-native-storagep op s))
             (fn2-sim-native-storagep op s))
           (equal (not remove-pending)
             (equal (fn2-sim-native-cut :finish op *fn2-fault-none* 0 c s o)
                    (fn2-sim-complete op *fn2-fault-none* 0 c s o)))))))

(defthm fn2-native-cut-atomic-positive-witness
  (fn2-native-cut-atomic-witness nil)
  :rule-classes nil
  :hints (("Goal"
    ; Evaluate the declared concrete fixture while the admitted storage
    ; equality rewrites its two executions. Keep implementation bodies opaque.
    :in-theory
    (e/d (fn2-native-cut-atomic-witness
          (:executable-counterpart fn2-native-cut-fixture)
          (:executable-counterpart create-fn2-core)
          (:executable-counterpart create-fn2-sim)
          (:executable-counterpart create-fn2-own))
         ((:definition fn2-native-cut-fixture)
          fn2-sim-native-cut fn2-sim-native-stage fn2-sim-native-post
          fn2-sim-physical fn2-sim-complete fn2-sim-complete-result)))))
(defthm fn2-native-cut-atomic-pending-hypothesis-removal
  (fn2-native-cut-atomic-witness t)
  :rule-classes nil
  :hints (("Goal"
    ; The deliberate active=0 mutation is a hypothesis control, not evidence
    ; of reachability in composition. Evaluate its concrete two executions;
    ; the storage equality is unavailable once its pending premise is removed.
    :in-theory
    (e/d (fn2-native-cut-atomic-witness
          (:executable-counterpart fn2-native-cut-fixture)
          (:executable-counterpart create-fn2-core)
          (:executable-counterpart create-fn2-sim)
          (:executable-counterpart create-fn2-own)
          (:executable-counterpart fn2-sim-native-cut)
          (:executable-counterpart fn2-sim-complete))
         ((:definition fn2-native-cut-fixture)
          (:definition fn2-sim-native-cut) (:definition fn2-sim-native-stage)
          (:definition fn2-sim-native-post) (:definition fn2-sim-physical)
          (:definition fn2-sim-complete) (:definition fn2-sim-complete-result))))))
