; Concrete dispatcher over the intrusive scheduler. No fusion.
(in-package "ACL2")
(include-book "executor-wake")
(include-book "assembly")

(defconst *fn2-turn-transition-max*
  (+ *fn2-work-empty*
     (max (+ *fn2-listener-run-bytes* *fn2-listener-run-steps*)
          (max (+ *fn2-echo-run-bytes* *fn2-echo-run-steps*)
               (+ *fn2-scribe-run-bytes* *fn2-scribe-run-steps*)))))

(defun fn2-exec-eligible-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (or (fn2-exec-runnable-p fn2-core) (fn2-exec-wake-p fn2-core)))

(defun fn2-turn-status (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((= 1 (fn2-exec-stop fn2-core)) :stop)
        ((or (fn2-exec-observation-p fn2-core) (fn2-exec-eligible-p fn2-core)) :more)
        (t :idle)))

(defun fn2-exec-harvest (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv ownerp kind id gen principal) (fn2-core-next-owner fn2-core))
       (start (fn2-exec-queued fn2-core))
       (bytes (if (and ownerp (fn2-machine-charge-kindp kind))
                  (fn2-machine-next-input-bytes fn2-core) 0))
       ; Leave an over-budget observation posted, without exposing its range.
       ((unless (or (not ownerp) (not (fn2-machine-charge-kindp kind))
                    (fn2-machine-work-fits-p kind bytes *fn2-work-transition* 0)))
        (mv 0 0 0 0 0 fn2-core))
       ((mv delivered & & & event outcome reason count aux0 aux1 fn2-core)
        (fn2-harvest-one fn2-core))
       ((unless delivered) (mv 1 0 0 0 *fn2-work-transition* fn2-core))
       ((mv wake fn2-core)
        (fn2-machine-observe kind id gen event outcome reason count aux0 aux1 fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-record *fn2-trace-kind-mailbox* wake principal 0 bytes *fn2-work-transition* 0 nil *fn2-none* start fn2-core)))
    (mv 1 0 0 bytes *fn2-work-transition* fn2-core)))
(fn2-core-preserves fn2-exec-harvest (fn2-core) :position 5 :rows nil)

(defun fn2-exec-mailbox (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (b* ((clockp (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                (yes) (= 1 (fn2-ops-clock-posted fn2-ops)) yes))
       (start (fn2-exec-queued fn2-core))
       (fn2-core
        (if clockp
            (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
              (posted mono real flags fn2-ops) (fn2-take-clock fn2-ops)
              (let ((unused-posted posted) (unused-real real) (unused-flags flags))
                (declare (ignore unused-posted unused-real unused-flags))
                (fn2-exec-clock mono fn2-core)))
          (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
            (bits fn2-ops) (fn2-take-signal fn2-ops)
            (if (< 0 (nfix bits)) (fn2-core-stop *fn2-stop-reason-signal* fn2-core) fn2-core))))
       (fn2-core (fn2-exec-record (if clockp *fn2-trace-kind-clock* *fn2-trace-kind-signal*) *fn2-none* 0 0 0 *fn2-work-mailbox* 0
                                 nil *fn2-none* start fn2-core)))
    (mv 1 0 0 0 *fn2-work-mailbox* fn2-core)))
(fn2-core-preserves fn2-exec-mailbox (fn2-core) :position 5 :rows nil :prefix "" :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-exec-principal (principal position budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((start (fn2-exec-queued fn2-core))
       ((mv code id fn2-core) (fn2-exec-pop principal fn2-core))
       ((unless (eq code :ok))
        (let ((fn2-core (fn2-exec-record *fn2-trace-kind-machine* *fn2-none* principal position
                          0 *fn2-work-empty* 0 nil *fn2-none* start fn2-core)))
          (mv 0 1 0 0 *fn2-work-empty* fn2-core)))
       ((mv bytes steps actions runnable fn2-core) (fn2-machine-run id budget fn2-core))
       (fn2-core (fn2-exec-charge-run principal bytes steps fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       ; New work enters before the running machine's tail requeue. The
       ; trace checker reconstructs this order without consulting links.
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (if runnable (fn2-exec-wake id fn2-core) fn2-core))
       (fn2-core (fn2-exec-record *fn2-trace-kind-machine* id principal position bytes steps actions
                                 runnable wake start fn2-core)))
    (mv 0 1 actions bytes steps fn2-core)))
(fn2-core-preserves fn2-exec-principal (principal position budget fn2-core) :position 5 :rows nil)

(defun fn2-exec-service (service position budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((start (fn2-exec-queued fn2-core))
       (fn2-core (fn2-exec-clear-service service fn2-core))
       ((mv wake fn2-core)
        (if (and (equal service 1) (fn2-exec-grant-p fn2-core))
            (fn2-machine-grant-one fn2-core) (mv *fn2-none* fn2-core)))
       ((mv actions fn2-core)
        (if (and (equal service 1) (natp budget) (< 0 budget))
            (fn2-exec-arm fn2-core) (mv 0 fn2-core)))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-charge-run (fn2-exec-system-row fn2-core) 0
                   (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*)
                   fn2-core))
       (fn2-core (fn2-exec-record *fn2-trace-kind-service* *fn2-none* service position 0
                    (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*) actions nil wake start fn2-core)))
    (mv 0 1 actions 0 (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*) fn2-core)))
(fn2-core-preserves fn2-exec-service (service position budget fn2-core) :position 5 :rows nil)

; Observation order is the posted FIFO, then the coalesced clock mailbox,
; then sticky signals. Each turn stops at the first exhausted budget.
; Every empty calendar entry still consumes one visit.
(defun fn2-transition (allow-observation action-budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond
   ((and allow-observation (fn2-exec-observation-p fn2-core))
    (if (fn2-core-posted-p fn2-core)
        (fn2-exec-harvest fn2-core) (fn2-exec-mailbox fn2-core)))
   ((fn2-exec-eligible-p fn2-core)
    (mv-let (kind principal position fn2-core) (fn2-exec-visit fn2-core)
      (if (equal kind *fn2-visit-principal*)
          (fn2-exec-principal principal position action-budget fn2-core)
        (fn2-exec-service (nfix (- (nfix kind) *fn2-visit-commit*)) position action-budget fn2-core))))
   (t (mv 0 0 0 0 0 fn2-core))))
(fn2-core-preserves fn2-transition (allow-observation action-budget fn2-core) :position 5 :rows nil)

(defun fn2-exec-account-work (bytes steps fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((b (+ (nfix bytes) (fn2-exec-turn-bytes fn2-core)))
        (s (+ (nfix steps) (fn2-exec-turn-steps fn2-core))))
    (if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 s))
        (let* ((fn2-core (fn2-exec-set-turn-bytes b fn2-core))
               (fn2-core (fn2-exec-set-turn-steps s fn2-core))) fn2-core)
      (fn2-core-stop *fn2-stop-reason-work-overflow* fn2-core))))
(fn2-core-preserves fn2-exec-account-work (bytes steps fn2-core) :rows nil :prefix "")

(in-theory (disable fn2-turn-status fn2-exec-eligible-p
                    fn2-exec-observation-p fn2-exec-runnable-p))

; Preserve the existing refinement cost bound when harvest exposes payload.
; Reserve one maximum transition (4096 bytes + 32 steps + one visit) before
; executing it. Insufficient room yields with all pending work retained.
(defun fn2-turn-work-room-p (h k visits bytes steps)
  (declare (xargs :guard t))
  (<= (+ (nfix visits) (nfix bytes) (nfix steps) *fn2-turn-transition-max*)
      (+ (* (nfix h) *fn2-work-transition*) (* (nfix k) *fn2-turn-transition-max*))))
(in-theory (disable fn2-turn-work-room-p))

; The loop's stop condition, named so that a checker stepping the loop one
; transition at a time (TRACE's per-case mode, sim/check-trace.lisp) asks the
; loop itself whether it continues. Left enabled: the loop's proofs see it inline.
(defun fn2-concrete-loop-stop-p (h k a nobs nvisits nactions fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (natp h) (natp k) (natp a)
                              (natp nobs) (natp nvisits) (natp nactions))))
  (or (>= nobs h) (>= nvisits k) (>= nactions a)
      (= 1 (fn2-exec-stop fn2-core))
      (not (fn2-turn-work-room-p h k nvisits
             (fn2-exec-turn-bytes fn2-core) (fn2-exec-turn-steps fn2-core)))
      (and (or (>= nobs h) (not (fn2-exec-observation-p fn2-core)))
           (not (fn2-exec-eligible-p fn2-core)))))

(defun fn2-concrete-loop (fuel h k a nobs nvisits nactions fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel)
                  :guard (and (fn2-core-wfp fn2-core) (natp fuel)
                              (natp h) (natp k) (natp a) (natp nobs)
                              (natp nvisits) (natp nactions))))
  (cond
   ((or (zp fuel) (fn2-concrete-loop-stop-p h k a nobs nvisits nactions fn2-core))
    (mv (fn2-turn-status fn2-core) nobs nvisits nactions fn2-core))
   (t
    (b* (((mv obs visits actions bytes steps fn2-core)
          (fn2-transition (< nobs h) (- a nactions) fn2-core))
         (fn2-core (fn2-exec-account-work bytes steps fn2-core)))
      (fn2-concrete-loop (- fuel 1) h k a (+ nobs (nfix obs))
                           (+ nvisits (nfix visits)) (+ nactions (nfix actions)) fn2-core)))))
(fn2-core-preserves fn2-concrete-loop (fuel h k a nobs nvisits nactions fn2-core) :position 4 :rows nil)

(defun fn2-concrete-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core))
         (a (fn2-exec-aturn fn2-core))
         (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
         (fn2-core (fn2-exec-set-turn-steps 0 fn2-core)))
    (fn2-concrete-loop (+ h k) h k a 0 0 0 fn2-core)))
(fn2-core-preserves fn2-concrete-turn (fn2-core) :position 4 :rows nil)

(defun fn2-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-concrete-turn fn2-core))
(fn2-core-preserves fn2-turn (fn2-core) :position 4 :rows nil)

(defun fn2-exec-start-listeners (left id fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp id))))
  (if (zp left) fn2-core
    (let ((fn2-core (fn2-exec-wake id fn2-core)))
      (fn2-exec-start-listeners (- left 1) (+ id 1) fn2-core))))
(fn2-core-preserves fn2-exec-start-listeners (left id fn2-core) :rows nil :prefix "")

; Bookings the listeners hold (D7's S1): a listener with an Accept outstanding
; holds one :connection-row booking on its principal for the connection it is
; waiting for, so at quiescence a principal's hold is its live connections plus
; these (D 13.5). Read by D's checkers; the executor never calls it.
(defun fn2-listener-bookings-from (left id p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) 0
    (+ (if (and (eq (fn2-machine-account-ref-read-code id fn2-core) :ok)
                (equal (fn2-machine-account-ref id fn2-core) p)) 1 0)
       (fn2-listener-bookings-from (- left 1) (+ 1 (nfix id)) p fn2-core))))
(defun fn2-listener-bookings (p fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-listener-bookings-from (fn2-machine-accept-count fn2-core)
                              (fn2-machine-kind-base *fn2-listener-kind* fn2-core) p fn2-core))

;; Layer C's genesis (the profile's group directory, S-GROUP) right after the
;; core init; a refusal stops the core before anything runs.
(defun fn2-init-engine (profile fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (genesis fn2-core) (fn2-groups-genesis profile fn2-core)
    (if (eq genesis :ok) fn2-core (fn2-core-stop *fn2-stop-reason-engine-genesis* fn2-core))))
(defthm fn2-init-engine-type
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-corep (fn2-init-engine profile fn2-core))))
(defthm fn2-init-engine-wfp
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) (fn2-core-wfp (fn2-init-engine profile fn2-core))))
(in-theory (disable fn2-init-engine))

(defun fn2-init-executor (profile mode scribe-p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)
    :guard-hints (("Goal" :use
      (:instance fn2-machine-kind-base-natp (kind *fn2-listener-kind*)
        (fn2-core (fn2-listener-set-mode-all (if (eq mode :null) 0 1)
                    (fn2-init-engine profile (fn2-core-init profile fn2-core)))))))))
  (b* ((fn2-core (fn2-core-init profile fn2-core))
       (fn2-core (fn2-init-engine profile fn2-core))
       (fn2-core (fn2-listener-set-mode-all (if (eq mode :null) 0 1) fn2-core))
       (fn2-core (fn2-listener-set-target-all
                  (fn2-machine-admission-ordinal-of (fn2-profile-get :listener-targets profile)) fn2-core))
       (fn2-core (fn2-listener-set-principals (fn2-profile-get :listener-principals profile) fn2-core))
       (fn2-core (fn2-exec-start-listeners (fn2-machine-accept-count fn2-core)
                   (fn2-machine-kind-base *fn2-listener-kind* fn2-core) fn2-core))
       (fn2-core (if scribe-p (fn2-scribe-start fn2-core) fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core)))
    (fn2-exec-wake wake fn2-core)))

(defthm-owed fn2-turn-bounds (core)
  (implies (and (fn2-corep core) (fn2-core-wfp core))
    (mv-let (status nobs nvisits nactions after) (fn2-turn core)
      (declare (ignore status after))
      (and (<= nobs (fn2-exec-h core)) (<= nvisits (fn2-exec-k core))
           (<= nactions (fn2-exec-aturn core)))))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-executor-bounds-teeth fn2-executor-bounds-negative)
  :doc "Owed simultaneous observation, calendar-visit and descriptor bounds over fn2-turn.")

; The turn bound as composition (HIGHER-STRUCTURES entry 9): a word of
; machine runs, each charged within its arm's certificate, costs at most the
; sum of the arms' declared bounds; T3's bound is this lemma's instance with
; at most K runs. Its partner is the residual budget: a run handed the turn's
; remaining descriptor budget never spends more than it (Lawvere's
; spent + c <= A iff c <= A - spent, with truncated subtraction covering
; exhaustion: an exhausted budget admits only zero-descriptor runs).
; A word element is (kind phase bytes steps descriptors).
(defun fn2-arm-word-certified-p (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) t
    (and (true-listp (car word)) (equal (len (car word)) 5)
         (fn2-machine-arm-charge-ok-p (nth 0 (car word)) (nth 1 (car word))
                                      (nth 2 (car word)) (nth 3 (car word)) (nth 4 (car word)))
         (fn2-arm-word-certified-p (cdr word)))))
(defun fn2-arm-word-charge (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) 0
    (+ (nfix (and (consp (car word)) (nth 2 (car word))))
       (nfix (and (consp (car word)) (nth 3 (car word))))
       (fn2-arm-word-charge (cdr word)))))
(defun fn2-arm-word-bound (word)
  (declare (xargs :verify-guards nil))
  (if (atom word) 0
    (+ (nfix (and (consp (car word)) (fn2-machine-arm-bound (nth 0 (car word)) (nth 1 (car word)))))
       (fn2-arm-word-bound (cdr word)))))
(defthm-owed fn2-arm-cost-composition (word)
  (implies (fn2-arm-word-certified-p word)
           (<= (fn2-arm-word-charge word) (fn2-arm-word-bound word)))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-arm-composition-positive fn2-arm-composition-negative)
  :doc "Runs charged within their arm certificates compose: the word's bytes and steps are at most the sum of its arms' declared bounds.")
(defthm-owed fn2-arm-residual-budget (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core) (natp budget))
           (<= (mv-nth 2 (fn2-machine-run id budget core)) budget))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-arm-residual-positive fn2-arm-residual-negative)
  :doc "A machine run handed the turn's residual descriptor budget spends at most that budget; an exhausted budget admits no descriptor.")

(assert-event
 (fn2-assert-compliant-p
  '(fn2-transition fn2-concrete-loop fn2-concrete-turn fn2-turn fn2-init-executor
    fn2-core-idle-deadline fn2-exec-harvest fn2-exec-mailbox fn2-exec-principal
    fn2-exec-service fn2-exec-account-work) (w state)))

; The executor's case source (DSL-METATHEORY 3.2): the executor is not a
; machine; it contributes seven labels with named selectors over the core in
; which fn2-transition runs with observations allowed. Selectors are
; proof-facing (non-executable); that they partition the non-machine
; transitions under the loop invariant is owed by the correspondence.
(defun-nx fn2-exec-select-clock (fn2-core)
  (and (fn2-exec-observation-p fn2-core) (not (fn2-core-posted-p fn2-core))
       (equal (fn2-ops-clock-posted (fn2-core-ops fn2-core)) 1)))
(defun-nx fn2-exec-select-signal (fn2-core)
  (and (fn2-exec-observation-p fn2-core) (not (fn2-core-posted-p fn2-core))
       (not (equal (fn2-ops-clock-posted (fn2-core-ops fn2-core)) 1))))
(defun-nx fn2-exec-select-visit (kind fn2-core)
  (and (not (fn2-exec-observation-p fn2-core)) (fn2-exec-eligible-p fn2-core)
       (mv-let (visit principal position core) (fn2-exec-visit fn2-core)
         (declare (ignore position))
         (and (equal visit kind)
              (or (not (equal kind *fn2-visit-principal*))
                  (mv-let (code id core) (fn2-exec-pop principal core)
                    (declare (ignore id core)) (not (eq code :ok))))))))
(defun-nx fn2-exec-select-service-0 (fn2-core) (fn2-exec-select-visit *fn2-visit-commit* fn2-core))
(defun-nx fn2-exec-select-service-1 (fn2-core) (fn2-exec-select-visit *fn2-visit-timer* fn2-core))
(defun-nx fn2-exec-select-service-2 (fn2-core) (fn2-exec-select-visit *fn2-visit-notification* fn2-core))
(defun-nx fn2-exec-select-service-3 (fn2-core) (fn2-exec-select-visit *fn2-visit-maintenance* fn2-core))
(defun-nx fn2-exec-select-empty-principal (fn2-core)
  (fn2-exec-select-visit *fn2-visit-principal* fn2-core))
(make-event
 (value (fn2-declare '(:operation-set fn2-executor-cases)
          '(:cases ((:executor :clock) (:executor :signal)
                    (:executor :service 0) (:executor :service 1)
                    (:executor :service 2) (:executor :service 3)
                    (:executor :empty-principal))
            :selectors (((:executor :clock) fn2-exec-select-clock)
                        ((:executor :signal) fn2-exec-select-signal)
                        ((:executor :service 0) fn2-exec-select-service-0)
                        ((:executor :service 1) fn2-exec-select-service-1)
                        ((:executor :service 2) fn2-exec-select-service-2)
                        ((:executor :service 3) fn2-exec-select-service-3)
                        ((:executor :empty-principal) fn2-exec-select-empty-principal))
            :doc "Clock, signal, four service visits and the empty principal visit.")
          nil nil)))
