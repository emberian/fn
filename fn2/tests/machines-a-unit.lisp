(in-package "ACL2")
(include-book "../books/assembly")

; Focused lifetime fixtures, independent of the random simulator world.
(defun fn2-machine-test-post (ack cell op opgen event count aux fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (b* (((mv & fn2-ops) (fn2-outbox-ack ack fn2-ops)))
      (fn2-post-result cell op opgen event *fn2-outcome-done* 0 count aux 0 fn2-ops))
    fn2-core))
(defun fn2-machine-test-harvest (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv & & & & event outcome reason count aux0 aux1 fn2-core)
        (fn2-harvest-one fn2-core))
       ((mv wake fn2-core)
        (fn2-machine-observe (fn2-machine-kind id fn2-core) id 1
          event outcome reason count aux0 aux1 fn2-core)))
    (mv wake fn2-core)))
(defun fn2-machine-test-input (slot gen opgen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (fn2-pool)
    (b* (((mv & fn2-pool) (fn2-pool-adapter-write slot gen 0 opgen 0 7 fn2-pool))
         ((mv & fn2-pool) (fn2-pool-adapter-write slot gen 0 opgen 1 8 fn2-pool)))
      fn2-pool)
    fn2-core))
(defun fn2-machine-test-range (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (s g off len) (fn2-op-range slot fn2-ops) (mv s g off len)))

; The listener's state after a successful Accept issue: :admitting, one row
; credit reserved. Fixtures inject the completion directly.
(defun fn2-machine-test-admitting (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((fn2-core (fn2-listener-take-credit *fn2-echo-admission-ordinal* fn2-core)))
    (fn2-listener-put-core 0 (phase *fn2-listener-state-admitting*))))

(defun fn2-machine-test-short-send (release-already-posted-p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (fn2-core (fn2-listener-set-mode-all 1 fn2-core))
       (fn2-core (fn2-machine-test-admitting fn2-core))
       ((mv & fn2-core) (fn2-machine-observe 0 0 1 *fn2-event-accept-result*
                         *fn2-outcome-done* 0 0 4 9 fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run 0 4 fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core))
       ((unless (and (equal actions 0) (equal id 2))) (mv :admission fn2-core))
       (slot (fn2-machine-pool-slot id fn2-core))
       (gen (fn2-machine-pool-gen id fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       ((unless (equal actions 1)) (mv :receive fn2-core))
       (fn2-core (fn2-machine-test-input slot gen 1 fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 1 *fn2-event-receive-result* 2 0 fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       ((mv send-slot send-gen off len) (fn2-machine-test-range 0 fn2-core))
       ((unless (and (equal actions 1) (equal slot send-slot)
                     (equal gen send-gen) (equal off 0) (equal len 2)))
        (mv :zero-copy fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 2 *fn2-event-send-result* 1
                   (if release-already-posted-p 0 1) fn2-core))
       ; The ABI accepts a release posted after the terminal but before its
       ; harvest, even when the terminal says no future release is pending.
       ; The posted cell, not that payload bit, then retains the loan.
       (fn2-core (if release-already-posted-p
                     (fn2-machine-test-post 0 1 0 2 *fn2-event-borrow-released* 0 0 fn2-core)
                   fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions runnable fn2-core) (fn2-machine-run id 4 fn2-core))
       ((unless (and (equal actions 0) (not runnable)
                     (equal (fn2-machine-off id fn2-core) 1)
                     (equal (fn2-machine-borrows id fn2-core) 1)))
        (mv :borrow-lifetime fn2-core))
       (fn2-core (if release-already-posted-p fn2-core
                   (fn2-machine-test-post 0 1 0 2 *fn2-event-borrow-released* 0 0 fn2-core)))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       ((mv send-slot send-gen off len) (fn2-machine-test-range 0 fn2-core)))
    (mv (if (and (equal actions 1) (equal slot send-slot) (equal gen send-gen)
                 (equal off 1) (equal len 1)) :ok :short-remainder)
        fn2-core)))

(defun fn2-machine-test-resource-and-retirement (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (put-assoc-equal :generation-limit 1 *fn2-profile-tiny*))
       (fn2-core (fn2-core-init profile fn2-core))
       (fn2-core (fn2-machine-test-admitting fn2-core))
       ((mv & fn2-core) (fn2-machine-observe 0 0 1 *fn2-event-accept-result*
                         *fn2-outcome-done* 0 0 4 9 fn2-core))
       ((mv & & & & fn2-core) (fn2-machine-run 0 4 fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-machine-park id fn2-core))
       (fn2-core (fn2-machine-park id fn2-core))
       ((mv wake fn2-core) (fn2-machine-observe 1 id 1 *fn2-event-borrow-released*
                           *fn2-outcome-done* 0 0 0 0 fn2-core))
       ((unless (and (equal wake *fn2-none*)
                     (equal (fn2-machine-wait-head fn2-core) id)
                     (equal (fn2-machine-wait-tail fn2-core) id)
                     (equal (fn2-machine-ready-next id fn2-core) *fn2-none*)))
        (mv :parked-wake fn2-core))
       ((mv wake fn2-core) (fn2-machine-grant-one fn2-core))
       ((unless (and (equal wake id) (not (fn2-machine-waiting-p fn2-core))))
        (mv :grant fn2-core))
       (fn2-core (fn2-echo-put-core id (phase *fn2-echo-state-draining*)))
       ((mv & & & & fn2-core) (fn2-machine-run id 4 fn2-core)))
    (mv (if (and (equal (fn2-machine-phase id fn2-core) *fn2-echo-state-retired*)
                 (equal (fn2-machine-pool-slot id fn2-core) *fn2-none*))
            :ok :retirement)
        fn2-core)))

; Null mode issues a real Accept and two real Receive operations. The first
; completion contains bytes; the second is EOF. There is no Send, and the
; retained RX slot is not released until the real CloseResult is harvested.
(defun fn2-machine-test-null (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (fn2-core (fn2-listener-set-mode-all 0 fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run 0 4 fn2-core))
       ((unless (equal actions 1)) (mv :null-accept fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 1 *fn2-event-accept-result* 0 4 fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest 0 fn2-core))
       ((mv & & & & fn2-core) (fn2-machine-run 0 4 fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core))
       ((unless (and (equal id (fn2-machine-global-id *fn2-echo-kind* 0 *fn2-profile-tiny*)) (equal (fn2-machine-mode id fn2-core) 0)))
        (mv :null-admission fn2-core))
       (slot (fn2-machine-pool-slot id fn2-core))
       (gen (fn2-machine-pool-gen id fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       ((unless (equal actions 1)) (mv :null-receive fn2-core))
       (fn2-core (fn2-machine-test-input slot gen 2 fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 2 *fn2-event-receive-result* 2 0 fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions runnable fn2-core) (fn2-machine-run id 4 fn2-core))
       (discarded (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
                             (fn2-ops (fn2-core-ops fn2-core)))
                    (yes)
                    (and (equal (fn2-pool-fill slot fn2-pool) 0)
                         (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)
                         (equal (fn2-outbox-queued fn2-ops) 0)) yes))
       ((unless (and discarded (equal actions 0) runnable
                     (equal (fn2-machine-phase id fn2-core) *fn2-echo-state-command*)))
        (mv :null-discard fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       ((unless (equal actions 1)) (mv :null-next-receive fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 3 *fn2-event-receive-result* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions & fn2-core) (fn2-machine-run id 4 fn2-core))
       (close-kind (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                     (kind) (fn2-ops-kind 0 fn2-ops) kind))
       ((unless (and (equal actions 1) (equal close-kind *fn2-action-close*)
                     (equal (fn2-machine-pool-slot id fn2-core) slot)
                     (equal (fn2-machine-pending id fn2-core) 1)))
        (mv :null-close-retention fn2-core))
       (fn2-core (fn2-machine-test-post 1 0 0 4 *fn2-event-close-result* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-machine-test-harvest id fn2-core))
       ((mv & & actions runnable fn2-core) (fn2-machine-run id 4 fn2-core))
       (released (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
                            (fn2-ops (fn2-core-ops fn2-core)))
                   (yes)
                   (and (equal (fn2-pool-state slot fn2-pool) *fn2-pool-state-free*)
                        (equal (fn2-pool-gen slot fn2-pool) 2)
                        (equal (fn2-ops-free-count fn2-ops) 8)
                        (equal (fn2-outbox-queued fn2-ops) 0)) yes)))
    (mv (if (and released (equal actions 0) (not runnable)
                 (equal (fn2-machine-phase id fn2-core) *fn2-echo-state-free*)
                 (equal (fn2-machine-generation id fn2-core) 2)
                 (equal (fn2-machine-pool-slot id fn2-core) *fn2-none*)
                 (equal (fn2-machine-free-head *fn2-echo-admission-ordinal* fn2-core) id))
            :ok :null-release)
        fn2-core)))

(defun fn2-machines-a-unit ()
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* (((mv answer fn2-core) (fn2-machine-test-short-send nil fn2-core))
           ((unless (eq answer :ok)) (mv answer fn2-core))
           ((mv answer fn2-core) (fn2-machine-test-short-send t fn2-core))
           ((unless (eq answer :ok)) (mv answer fn2-core))
           ((mv answer fn2-core) (fn2-machine-test-null fn2-core)))
        (if (eq answer :ok) (fn2-machine-test-resource-and-retirement fn2-core)
          (mv answer fn2-core)))
      answer)))
(assert-event (equal (fn2-machines-a-unit) :ok))

; Directory identity comes from declarations. Test both directions at every
; tiny-profile slot and at the sentinel.
(defun fn2-machine-index-control (left profile)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (mv-let (kind slot) (fn2-machine-local-id (- left 1) profile)
      (and (= (fn2-machine-global-id kind slot profile) (- left 1))
           (fn2-machine-index-control (- left 1) profile)))))
(assert-event (fn2-machine-index-control (fn2-machine-index-count *fn2-profile-tiny*) *fn2-profile-tiny*))
(assert-event (mv-let (kind slot)
                (fn2-machine-local-id (fn2-machine-index-count *fn2-profile-tiny*) *fn2-profile-tiny*)
                (and (= kind 255) (= slot 0))))
(assert-event
 (let* ((world (w state))
        (listener (fn2-machine-property 'fn2-listener :columns world))
        (scribe (fn2-machine-property 'fn2-scribe :columns world)))
   (and ; A's kinds come first, in A's order; other layers may register more after them.
        (equal (take 3 (fn2-machine-names world)) '(fn2-listener fn2-echo fn2-scribe))
        (not (assoc-eq 'checksum listener)) (assoc-eq 'checksum scribe)
        (equal (fn2-machine-property 'fn2-scribe :layout world) scribe)
        (equal (car (fn2-machine-property 'fn2-scribe :packed world))
               '(phase :bit-offset 0 :bit-width 8 :tags
                 ((0 :free) (1 :reserve) (2 :fill) (3 :patch) (4 :write)
                  (5 :write-result) (6 :fence) (7 :fence-result) (8 :reset)
                  (9 :read) (10 :read-result) (11 :verify) (12 :next) (13 :stopped)))))))

(defun fn2-machine-refusal-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
           ; Corrupt the storage encoding directly: the semantic setter rejects unnamed enum tags.
           (fn2-core
            (stobj-let ((fn2-listener (fn2-listener-table fn2-core)))
              (fn2-listener) (update-fn2-listener-phase$ai 0 255 fn2-listener) fn2-core))
           ((mv bytes steps actions runnable fn2-core) (fn2-machine-run 0 4 fn2-core)))
        (mv (and (= (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-phase*)
                 (= (fn2-machine-phase 0 fn2-core) 255)
                 (= bytes 0) (= steps 1) (= actions 0) (not runnable)) fn2-core)) answer)))
(assert-event (fn2-machine-refusal-control))
(value-triple (cw "MACHINE UNIT: lifetimes/null/retirement, declaration layout, ID roundtrip, :machine-phase STOP PASS~%"))

; An over-width directory value stops the core with :machine-write and leaves
; the field as it was (a scalar and a per-partition field); a fitting one is written.
(defun fn2-machine-width-control (which value)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
           (before (if (eq which :scalar) (fn2-machine-accept-count fn2-core) (fn2-machine-free-head 0 fn2-core)))
           (fn2-core (if (eq which :scalar) (fn2-machine-set-accept-count value fn2-core)
                       (fn2-machine-set-free-head 0 value fn2-core)))
           (after (if (eq which :scalar) (fn2-machine-accept-count fn2-core) (fn2-machine-free-head 0 fn2-core))))
        (mv (if (unsigned-byte-p 32 value)
                (and (= (fn2-core-stop-reason fn2-core) 0) (= after value))
              (and (= (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-write*) (= after before)))
            fn2-core)) answer)))
(assert-event (and (fn2-machine-width-control :scalar 4294967296) (fn2-machine-width-control :scalar 3)
                   (fn2-machine-width-control :partition 4294967296) (fn2-machine-width-control :partition 1)))
(value-triple (cw "MACHINE UNIT: over-width scalar and partition writes STOP :machine-write PASS~%"))

; A reclaim with no active row stops the core with :machine-write and leaves the
; partition as it was; with one active row it returns the row and its credit.
(defun fn2-machine-reclaim-control (active)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
           (o *fn2-echo-admission-ordinal*)
           (fn2-core (fn2-machine-set-active-count o active fn2-core))
           (credits (fn2-machine-admission-credits o fn2-core))
           (head (fn2-machine-free-head o fn2-core))
           (id (fn2-machine-global-id *fn2-echo-kind* 0 *fn2-profile-tiny*))
           (fn2-core (fn2-machine-reclaim-fn2-echo id nil fn2-core)))
        (mv (if (zp active)
                (and (= (fn2-core-stop-reason fn2-core) *fn2-stop-reason-machine-write*)
                     (= (fn2-machine-active-count o fn2-core) 0)
                     (= (fn2-machine-admission-credits o fn2-core) credits)
                     (= (fn2-machine-free-head o fn2-core) head))
              (and (= (fn2-core-stop-reason fn2-core) 0)
                   (= (fn2-machine-active-count o fn2-core) (- active 1))
                   (= (fn2-machine-admission-credits o fn2-core) (+ 1 credits))
                   (= (fn2-machine-free-head o fn2-core) id)))
            fn2-core)) answer)))
(assert-event (and (fn2-machine-reclaim-control 0) (fn2-machine-reclaim-control 1)))
(value-triple (cw "MACHINE UNIT: reclaim with no active row STOPS :machine-write PASS~%"))

(include-book "std/testing/must-fail" :dir :system)
; These are rejected programs, not failed theorem searches. Echo COMMAND
; and listener ADMITTING both encode 1: the first control checks provenance.
(assert-event (= *fn2-echo-state-command* *fn2-listener-state-admitting*))
(must-fail
 (defun fn2-control-cross-kind (fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (fn2-listener-put-core 0 (phase *fn2-echo-state-command*)))
 :with-output-off nil :check-expansion t)
(must-fail
 (defun fn2-control-duplicate-phase (fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (fn2-listener-put-core 0 (phase *fn2-listener-state-closing*)
                            (phase *fn2-echo-state-command*)))
 :with-output-off nil :check-expansion t)
(must-fail
 (defun fn2-control-wide-set (fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (fn2-machine-set-generation 0 1152921504606846976 fn2-core))
 :with-output-off nil :check-expansion t)
(must-fail
 (defun fn2-control-missing-set (id fn2-core)
   (declare (xargs :stobjs fn2-core
                   :guard (and (fn2-core-wfp fn2-core)
                               (equal (fn2-machine-kind id fn2-core) *fn2-listener-kind*))))
   (fn2-machine-set-checksum id 0 fn2-core))
 :with-output-off nil :check-expansion t)
(must-fail
 (defun fn2-control-unknown-charge ()
   (declare (xargs :guard t))
   (fn2-machine-charge 255 999999999 999999999 999999999))
 :with-output-off nil :check-expansion t)
(must-fail
 (defun fn2-control-unrouted-event (fn2-core)
   (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
   (fn2-machine-observe-fn2-listener 0 *fn2-event-send-result* 0 0 0 0 0 fn2-core))
 :with-output-off nil :check-expansion t)

(must-fail
 (defmachine fn2-control-empty-observer
   :states (:ready) :budget (:bytes 1 :steps 1 :descriptors 1)
   :continuations ((:ready fn2-machine-idle))
   :observes ((:accept-result nil)))
 :expected :hard :with-output-off nil :check-expansion t)

(defun fn2-machine-checked-write-control (control)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
           (before (fn2-machine-phase 0 fn2-core))
           (free (fn2-machine-global-id *fn2-echo-kind* 0 *fn2-profile-tiny*))
           (fn2-core (fn2-echo-put-core free (pending 2)))
           (fn2-core (if (eq control :retired)
                         (fn2-echo-put-core free (phase *fn2-echo-state-retired*)) fn2-core))
           ((mv wake fn2-core)
            (case control
              (:kind (let ((fn2-core (fn2-echo-put-core 0 (phase *fn2-echo-state-closing*))))
                       (mv *fn2-none* fn2-core)))
              (:width (let ((fn2-core (fn2-machine-write-generation 0 1152921504606846976 fn2-core)))
                        (mv *fn2-none* fn2-core)))
              (:field (let ((fn2-core (fn2-machine-write-checksum 0 0 fn2-core)))
                        (mv *fn2-none* fn2-core)))
              (:event (fn2-machine-observe *fn2-listener-kind* 0 1 *fn2-event-send-result* 0 0 0 0 0 fn2-core))
              (:generation (fn2-machine-observe *fn2-listener-kind* 0 2 *fn2-event-accept-result* 0 0 0 0 0 fn2-core))
              (:wrong-kind (fn2-machine-observe *fn2-echo-kind* 0 1 *fn2-event-receive-result* 0 0 1 0 0 fn2-core))
              (otherwise (fn2-machine-observe *fn2-echo-kind* free 1 *fn2-event-receive-result* 0 0 1 0 0 fn2-core)))))
        (mv (and (= before (fn2-machine-phase 0 fn2-core))
                 (= (fn2-machine-generation 0 fn2-core) 1)
                 (= (fn2-core-stop-reason fn2-core)
                    (if (member-eq control '(:kind :width :field))
                        *fn2-stop-reason-machine-write* *fn2-stop-reason-machine-observation*))
                 (= (fn2-machine-pending free fn2-core) 2) (= wake *fn2-none*)) fn2-core)) answer)))
(assert-event (and (fn2-machine-checked-write-control :kind) (fn2-machine-checked-write-control :width)
                   (fn2-machine-checked-write-control :field) (fn2-machine-checked-write-control :event)
                   (fn2-machine-checked-write-control :free) (fn2-machine-checked-write-control :generation)
                   (fn2-machine-checked-write-control :wrong-kind) (fn2-machine-checked-write-control :retired)))
(value-triple (cw "R5d MACHINE CONTROLS: :machine-write and :machine-observation STOP; all eight controls PASS~%"))

; Two issued writes complete before any machine run. The test declaration
; chooses accumulation instead of scribe's one-cell policy; routing is the
; same generator, and completions pass through the real FIFO and harvest.
; The saturation is one opaque function with its range proved once, so the
; callback's preservation proofs do not split on four MINs.
(defun fn2-machine-test-saturate (x)
  (declare (xargs :guard (natp x)))
  (min *fn2-none* x))
(defthm fn2-machine-test-saturate-range
  (<= (fn2-machine-test-saturate x) *fn2-none*)
  :hints (("Goal" :in-theory (enable fn2-machine-test-saturate)))
  :rule-classes :linear)
(defthm fn2-machine-test-saturate-natp
  (implies (natp x) (natp (fn2-machine-test-saturate x)))
  :hints (("Goal" :in-theory (enable fn2-machine-test-saturate)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-machine-test-saturate))
(defmachine-callback fn2-machine-test-accumulate fn2-scribe (id event outcome reason count aux0 aux1) 1
  ; A test-only handler calling a test helper: the declared escape.
  :contract (:cost (:steps 1) :writes (completed verified checksum cursor) :next () :uses ()
             :language :unchecked)
  (let ((fn2-core (fn2-scribe-put-core id
          (completed (fn2-machine-test-saturate (+ 1 row-completed)))
          (verified (fn2-machine-test-saturate (+ (nfix count) row-verified)))
          (checksum (fn2-machine-test-saturate (+ (nfix reason) (* 16 row-checksum))))
          (cursor (fn2-machine-test-saturate (+ row-pending
                                    (* 10 row-cursor)))))))
    (mv id fn2-core)))

(encapsulate ()
 (local (table fn2-machine-kinds 'fn2-scribe
          (list* :observes
                 (cons '(:write-result fn2-machine-test-accumulate)
                       (cdr (fn2-machine-property 'fn2-scribe :observes world)))
                 (fn2-decl-row (list :machine 'fn2-scribe) world))))
 (make-event
  (value (cons 'progn (fn2-machine-observe-events 'fn2-machine-test-observe
                       (fn2-machine-names (w state)) (w state))))))

(defun fn2-machine-test-harvest-accumulate (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv found kind id gen &) (fn2-core-next-owner fn2-core))
       ((unless found) (mv nil fn2-core))
       ((mv harvested & & & event outcome reason count aux0 aux1 fn2-core)
        (fn2-harvest-one fn2-core))
       ((mv wake fn2-core) (fn2-machine-test-observe kind id gen
                            event outcome reason count aux0 aux1 fn2-core)))
    (mv (and harvested (equal wake id)) fn2-core)))

(defun fn2-machine-test-two-completions (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (id (fn2-machine-scribe-id fn2-core))
       (fn2-core (fn2-scribe-put-core id (phase *fn2-scribe-state-write*) (pending 2)))
       ((mv code slot gen fn2-core) (fn2-core-reserve 0 *fn2-scribe-kind* id 1 fn2-core))
       ((unless (eq code :ok)) (mv :reserve fn2-core))
       ((mv & fn2-core) (fn2-core-write slot gen 0 7 *fn2-scribe-kind* id 1 fn2-core))
       ((mv & fn2-core) (fn2-core-write slot gen 1 8 *fn2-scribe-kind* id 1 fn2-core))
       ((mv & fn2-core) (fn2-core-write slot gen 2 9 *fn2-scribe-kind* id 1 fn2-core))
       ((mv code op0 og0 fn2-core) (fn2-issue-write 0 slot gen 0 3 0 *fn2-scribe-kind* id 1 0 fn2-core))
       ((unless (eq code :ok)) (mv :write-first fn2-core))
       ((mv code op1 og1 fn2-core) (fn2-issue-write 3 slot gen 0 3 0 *fn2-scribe-kind* id 1 0 fn2-core))
       ((unless (eq code :ok)) (mv :write-second fn2-core))
       (fn2-core
        (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
          (b* (((mv & fn2-ops) (fn2-outbox-ack 2 fn2-ops))
               (fn2-ops (fn2-post-result 0 op0 og0 *fn2-event-write-result*
                         *fn2-outcome-failed* *fn2-reason-io* 3 0 0 fn2-ops)))
            (fn2-post-result 0 op1 og1 *fn2-event-write-result*
              *fn2-outcome-failed* *fn2-reason-uncertain* 2 0 0 fn2-ops)) fn2-core))
       ((mv first fn2-core) (fn2-machine-test-harvest-accumulate fn2-core))
       ((mv second fn2-core) (fn2-machine-test-harvest-accumulate fn2-core)))
    (mv (if (and first second (= (fn2-machine-completed id fn2-core) 2)
                 (= (fn2-machine-verified id fn2-core) 5)
                 (= (fn2-machine-checksum id fn2-core)
                    (+ (* 16 *fn2-reason-io*) *fn2-reason-uncertain*))
                 (= (fn2-machine-cursor id fn2-core) 21)
                 (= (fn2-machine-pending id fn2-core) 0)
                 (= (fn2-machine-event-ready id fn2-core) 0)
                 (= (fn2-machine-refusals fn2-core) 0)) :ok :lost-completion) fn2-core)))
(defun fn2-machine-two-completions-control ()
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core) (fn2-machine-test-two-completions fn2-core) answer)))
(assert-event (equal (fn2-machine-two-completions-control) :ok))
(value-triple (cw "R5a OBSERVE: two harvested writes counted before run; reason order, pre-decrement pending 2/1, no cell overwrite PASS~%"))

(must-fail
 (defmachine fn2-control-code-continuation :states (:ready)
   :budget (:bytes 1 :steps 1 :descriptors 1)
   :continuations ((:ready (fn2-machine-idle id fn2-core))))
 :expected :hard :with-output-off nil :check-expansion t)
(must-fail
 (defmachine fn2-control-code-initial :states (:ready)
   :budget (:bytes 1 :steps 1 :descriptors 1) :continuations ((:ready fn2-machine-idle))
   :initial ((generation (+ slot base))))
 :expected :hard :with-output-off nil :check-expansion t)
; The seven-name obligation list is gone: a machine contributes its case
; catalogue and states nothing; an :obligations key is refused.
(must-fail
 (defmachine fn2-control-obligations-key :states (:ready)
   :budget (:bytes 1 :steps 1 :descriptors 1) :continuations ((:ready fn2-machine-idle))
   :obligations ((initialization :owed)))
 :expected :any :with-output-off nil :check-expansion t)
(assert-event
 (and (equal (fn2-machine-property 'fn2-listener :cases (w state))
             '((:run fn2-listener :accepting) (:run fn2-listener :admitting) (:run fn2-listener :closing)
               (:observe fn2-listener :accept-result) (:observe fn2-listener :close-result)))
      (equal (getpropc 'fn2-listener-run 'formals nil (w state)) '(id budget fn2-core))
      (equal (strip-cadrs (fn2-machine-property 'fn2-listener :continuations (w state)))
             '(fn2-listener-accept fn2-listener-admitting fn2-listener-close))))
(value-triple (cw "R5a DECLARATION: named callbacks and initializers; case catalogue; code and :obligations refusals PASS~%"))

(must-fail
 (defun fn2-control-wrong-kind-run (id fn2-core)
   (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core)
                     (fn2-machine-idp id fn2-core)
                     (equal (fn2-machine-kind id fn2-core) *fn2-listener-kind*))))
   (fn2-echo-run id 4 fn2-core))
 :with-output-off nil :check-expansion t)
(defun fn2-machine-call-count (fn term)
  (declare (xargs :verify-guards nil))
  (if (atom term) 0
    (+ (if (eq (car term) fn) 1 0)
       (fn2-machine-call-count fn (car term)) (fn2-machine-call-count fn (cdr term)))))
; The run entry reads the phase once through the kind's own row reader, and
; each arm reads only its fields (no whole-row snapshot).
(assert-event
 (let ((run (getpropc 'fn2-echo-run 'unnormalized-body nil (w state)))
       (length (getpropc 'fn2-echo-row-length 'unnormalized-body nil (w state))))
   (and (= (fn2-machine-call-count 'fn2-echo-row-phase run) 1)
        (= (fn2-machine-call-count 'fn2-echo-length length) 1)
        (not (getpropc 'fn2-echo-snapshot 'formals nil (w state)))
        (= (fn2-machine-call-count 'fn2-machine-length run) 0))))
(value-triple (cw "R5a OWN-TABLE: one phase read at run entry, per-field own readers, wrong-kind guard refusal PASS~%"))

; A new kind may own ID or SLOT columns: values must not shadow the
; batch writer's directory ID/SLOT temporaries.
(assert-event
 (equal (fn2-machine-write-values '((id caller-id) (slot caller-slot)))
        '((fn2-write-value-id caller-id) (fn2-write-value-slot caller-slot))))

(assert-event
 (let ((columns (fn2-decl-get :generated (fn2-decl-row '(:columns fn2-echo) (w state))))
       (machine (fn2-decl-get :generated (fn2-decl-row '(:machine fn2-echo) (w state)))))
   (and (fn2-decl-find-artifact 'fn2-echo-put columns)
        (not (fn2-decl-find-artifact 'fn2-echo-put machine)))))

(defun fn2-machine-read-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
  (mv-let (ok fn2-core)
    (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
         ((mv valid zero) (fn2-machine-kind-read 0 fn2-core))
         ((mv invalid absent) (fn2-machine-kind-read *fn2-none* fn2-core))
         ((mv wrong-kind missing) (fn2-machine-cap-index-read (fn2-machine-scribe-id fn2-core) fn2-core)))
      (mv (and (eq valid :ok) (= zero 0) (eq invalid :bounds) (null absent)
               (eq wrong-kind :kind) (null missing)) fn2-core)) ok)))
(assert-event (fn2-machine-read-control))

(defun fn2-machine-invalid-read-control ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
   (mv-let (answer fn2-core)
     (let ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core)))
       (mv (fn2-machine-kind *fn2-none* fn2-core) fn2-core)) answer)))
(must-fail (assert-event (fn2-machine-invalid-read-control)) :with-output-off nil)
