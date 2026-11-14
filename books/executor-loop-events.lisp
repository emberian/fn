; Shared executor loop events for concrete core compositions.
(in-package "ACL2")

(defmacro fn2-executor-loop-events ()
 '(progn

; One transition's largest declared work: a visit and the largest per-run
; budget (bytes and steps) over every registered machine kind, read from the
; registry, so a kind's budget joins the turn's bound when it is declared.
(defun fn2-exec-kinds-work-max (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) 0
    (let ((budget (fn2-machine-property (car names) :budget world)))
      (max (+ (nfix (fn2-arm-get :bytes budget)) (nfix (fn2-arm-get :steps budget)))
           (fn2-exec-kinds-work-max (cdr names) world)))))
(make-event
 `(defconst *fn2-turn-transition-max*
    ,(max (+ *fn2-work-empty* (fn2-exec-kinds-work-max (fn2-machine-names (w state)) (w state)))
           (+ *fn2-work-empty* *fn2-services-work-max* *fn2-work-transition*))))
(assert-event (<= (+ *fn2-work-empty* *fn2-listener-run-bytes* *fn2-listener-run-steps*) *fn2-turn-transition-max*))

(defun fn2-exec-eligible-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (or (fn2-exec-runnable-p fn2-core) (fn2-exec-wake-p fn2-core)
      (fn2-exec-services-ready-p fn2-core)))

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
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :use fn2-exec-run-services-work-natp
                                 :in-theory (disable fn2-exec-grant-p fn2-exec-system-row fn2-exec-queued)))))
  (b* ((start (fn2-exec-queued fn2-core))
       ((mv service-steps fn2-core) (fn2-exec-run-services service fn2-core))
       ((mv wake fn2-core)
        (if (and (equal service 1) (fn2-exec-grant-p fn2-core))
            (fn2-machine-grant-one fn2-core) (mv *fn2-none* fn2-core)))
       ((mv actions fn2-core)
        (if (and (equal service 1) (natp budget) (< 0 budget))
            (fn2-exec-arm fn2-core) (mv 0 fn2-core)))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-charge-run (fn2-exec-system-row fn2-core) 0
                   (+ service-steps (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*))
                   fn2-core))
       (fn2-core (fn2-exec-record *fn2-trace-kind-service* *fn2-none* service position 0
                    (+ service-steps (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*)) actions nil wake start fn2-core)))
    (mv 0 1 actions 0 (+ service-steps (if (and (equal wake *fn2-none*) (equal actions 0)) *fn2-work-empty* *fn2-work-transition*)) fn2-core)))
; the predicates its tests read stay closed: opened, their cases multiplied
; the walk to 9,000 subgoals (D26: 44 s, 0.1 s closed)
(fn2-core-preserves fn2-exec-service (service position budget fn2-core) :position 5 :rows nil
  :hints (("Goal" :in-theory (disable fn2-exec-grant-p fn2-exec-system-row fn2-exec-queued))))

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
(fn2-core-preserves fn2-transition (allow-observation action-budget fn2-core) :position 5 :rows nil
  :hints (("Goal" :in-theory (disable fn2-exec-observation-p fn2-core-posted-p fn2-exec-eligible-p))))

; The residual contract follows actual callback reports through each selector
; branch. It is unconditional on stop/success and accepts every input budget.
(defun fn2-exec-descriptor-result-events (entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((fn (caar entries)) (args (cadar entries)) (budget (caddar entries))
         (call (cons fn args)) (count `(mv-nth 2 ,call))
         (hyps '(and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)))
         (opaque (remove1-eq fn
          '(fn2-machine-run fn2-exec-arm fn2-exec-harvest fn2-exec-mailbox
            fn2-exec-principal fn2-exec-service fn2-transition fn2-exec-visit fn2-exec-pop
            fn2-exec-record fn2-exec-charge-run fn2-exec-wake fn2-machine-take-wake
            fn2-corep fn2-core-wfp fn2-exec-observation-p fn2-core-posted-p
            fn2-exec-eligible-p fn2-exec-grant-p fn2-exec-run-services))))
   (cons `(defthm ,(fn2-columns-sym fn "-DESCRIPTORS-WITHIN-RESIDUAL")
     (implies ,hyps (and (natp ,count) (<= ,count (nfix ,budget))))
     :rule-classes (:rewrite
       (:type-prescription :corollary (implies ,hyps (natp ,count)))
       (:linear :corollary (implies ,hyps (<= ,count (nfix ,budget)))))
     :hints (("Goal" :in-theory (e/d (,fn) ,opaque))))
    (fn2-exec-descriptor-result-events (cdr entries))))))
(make-event (value (cons 'progn (fn2-exec-descriptor-result-events
 '((fn2-exec-harvest (fn2-core) 0)
   (fn2-exec-mailbox (fn2-core) 0)
   (fn2-exec-principal (principal position budget fn2-core) budget)
   (fn2-exec-service (service position budget fn2-core) budget)
   (fn2-transition (allow-observation action-budget fn2-core) action-budget))))))

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
      (not (fn2-turn-descriptor-room-p nactions a))
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

(defthm fn2-concrete-loop-actions-within-limit
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
               (natp a) (natp nactions) (<= nactions a))
  (and (natp (mv-nth 3 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)))
       (<= (mv-nth 3 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)) a)))
 :hints (("Goal" :induct (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)
   :in-theory (e/d (fn2-concrete-loop fn2-concrete-loop-stop-p)
     (fn2-transition fn2-exec-account-work fn2-corep fn2-core-wfp fn2-turn-work-room-p
      fn2-turn-descriptor-room-p fn2-turn-status fn2-exec-eligible-p fn2-exec-observation-p)))))

; Stopping before selection retains the calendar cursor, every queued row,
; and every continuation. A later turn starts with a fresh descriptor quantum.
(defthm fn2-concrete-loop-short-residual-preserves-core
  (implies (not (fn2-turn-descriptor-room-p nactions a))
           (equal (mv-nth 4 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core))
                  fn2-core))
  :hints (("Goal" :in-theory (enable fn2-concrete-loop fn2-concrete-loop-stop-p))))

(defun fn2-concrete-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core))
         (a (fn2-exec-aturn fn2-core))
         (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
         (fn2-core (fn2-exec-set-turn-steps 0 fn2-core)))
    (fn2-concrete-loop (+ h k) h k a 0 0 0 fn2-core)))
(fn2-core-preserves fn2-concrete-turn (fn2-core) :position 4 :rows nil)
(defthm fn2-concrete-turn-actions-within-limit
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (and (natp (mv-nth 3 (fn2-concrete-turn fn2-core)))
       (<= (mv-nth 3 (fn2-concrete-turn fn2-core)) (fn2-exec-aturn fn2-core))))
 :hints (("Goal" :in-theory (e/d (fn2-concrete-turn)
   (fn2-concrete-loop fn2-corep fn2-core-wfp fn2-exec-aturn)))))


(defun fn2-turn (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-concrete-turn fn2-core))
(fn2-core-preserves fn2-turn (fn2-core) :position 4 :rows nil)
(defthm fn2-turn-actions-within-limit
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (and (natp (mv-nth 3 (fn2-turn fn2-core)))
       (<= (mv-nth 3 (fn2-turn fn2-core)) (fn2-exec-aturn fn2-core))))
 :hints (("Goal" :in-theory (e/d (fn2-turn) (fn2-concrete-turn fn2-exec-aturn)))))



(defthm-owed fn2-arm-residual-budget (id budget core)
  (implies (and (fn2-corep core) (fn2-core-wfp core) (natp budget))
           (<= (mv-nth 2 (fn2-machine-run id budget core)) budget))
  :schema :bound :from (:operation fn2-turn)
  :teeth (fn2-arm-residual-positive fn2-arm-residual-negative)
  :doc "A machine run handed the turn's residual descriptor budget spends at most that budget; an exhausted budget admits no descriptor.")
(defthm fn2-arm-residual-budget-statement
 (fn2-arm-residual-budget$owed id budget core)
 :hints (("Goal" :in-theory (e/d (fn2-arm-residual-budget$owed)
   (fn2-machine-run fn2-corep fn2-core-wfp)))))
(fn2-owed-discharge fn2-arm-residual-budget fn2-arm-residual-budget-statement)

))
