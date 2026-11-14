; Full-turn issuance history: effects of actual callees, not queue deltas.
(in-package "ACL2")
(include-book "core-issued-events")
(include-book "machines")

; The frame layer establishes exact OPS equality for these control-only
; functions. Derive it from their inferred child footprints, rejecting any
; future service/selector which starts writing the operation table.
(defun fn2-executor-issued-frame-events (fns world)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil
  (let* ((fn (car fns))
         (d (fn2-dc-entry fn nil world))
         (k (fn2-arm-frame-child-index 'fn2-core-ops world)))
   (cons
    (if (or (not d) (member-equal k (car d)))
        `(make-event (er soft 'fn2-executor-issued-frame
                     "~x0 has no operation-table frame; prove its actual issue effect." ',fn))
      (fn2-machine-ops-frame-event fn nil world))
    (fn2-executor-issued-frame-events (cdr fns) world)))))

; Count position and core position are explicit interfaces of the actual
; transition functions. Each leaf theorem includes fixed row count, enabling
; composition across recycling and completion consumption.
(defun fn2-executor-issued-step-event (fn count-pos core-pos enabled world)
 (declare (xargs :verify-guards nil))
 (let ((call (cons fn (formals fn world))))
  `(defthm ,(fn2-columns-sym fn "-ISSUED-TOTAL")
    (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
     ,(fn2-run-issued-claim (if count-pos `(mv-nth ,count-pos ,call) 0)
        '(fn2-core-ops fn2-core) `(fn2-core-ops (mv-nth ,core-pos ,call))))
    :hints (("Goal" :in-theory (e/d (,fn ,@enabled)
      (fn2-core-ops fn2-corep fn2-core-wfp fn2-ops-issued-count
       fn2-op-issued-weight fn2-ops-rows fn2-opsp fn2-ops-wfp)))))))

(defun fn2-executor-concrete-observers (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (append
   (and (function-symbolp (fn2-columns-sym (car names) "-RUN") world)
        (list (fn2-columns-col-name 'fn2-machine-observe (car names))))
   (fn2-executor-concrete-observers (cdr names) world))))

(defun fn2-executor-observe-ops-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((name (car names))
         (runp (function-symbolp (fn2-columns-sym name "-RUN") world))
         (handler (fn2-columns-col-name 'fn2-machine-observe
                    (if runp name (fn2-columns-sym name "-STUB"))))
         (route (fn2-columns-col-name 'fn2-machine-observe-route name))
         (call (cons handler (formals handler world)))
         (route-call (cons route (formals route world))))
   (append
    (list
     (if runp
         (fn2-machine-ops-frame-event handler nil world)
       `(defthm ,(fn2-columns-sym handler "-OPS-CHILD-FRAME")
         (equal (fn2-core-ops (mv-nth 1 ,call)) (fn2-core-ops fn2-core))
         :hints (("Goal" :use ,(fn2-columns-sym handler "-OPS-POOL")
                  :in-theory '(fn2-dispatch-ops-pool fn2-core-ops)))))
     `(defthm ,(fn2-columns-sym route "-OPS-CHILD-FRAME")
       (equal (fn2-core-ops (mv-nth 1 ,route-call)) (fn2-core-ops fn2-core))
       :hints (("Goal" :in-theory (e/d (,route)
         (,handler fn2-machine-observe-terminal fn2-machine-refuse-observation
          fn2-core-ops))))))
    (fn2-executor-observe-ops-events (cdr names) world)))))

(defmacro fn2-executor-issued-loop-events ()
 '(progn
; TRANSITION-ISSUED-TOTAL must already have been proved from the real
; mailbox/harvest/principal/service branches. No abstract substitute is used.
(make-event
 (value `(defthm fn2-concrete-loop-issued-total
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp nactions))
   ,(fn2-run-issued-claim
      '(- (mv-nth 3 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)) nactions)
      '(fn2-core-ops fn2-core)
      '(fn2-core-ops (mv-nth 4 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)))))
  :hints (("Goal" :induct (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)
    :in-theory (e/d (fn2-concrete-loop)
     (fn2-transition fn2-concrete-loop-stop-p fn2-exec-account-work
      fn2-turn-status fn2-corep fn2-core-wfp fn2-core-ops
      fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows)))))))
(make-event
 (value `(defthm fn2-concrete-turn-issued-total
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
   ,(fn2-run-issued-claim '(mv-nth 3 (fn2-concrete-turn fn2-core))
     '(fn2-core-ops fn2-core)
     '(fn2-core-ops (mv-nth 4 (fn2-concrete-turn fn2-core)))))
  :hints (("Goal" :in-theory (e/d (fn2-concrete-turn)
   (fn2-concrete-loop fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
    fn2-corep fn2-core-wfp fn2-core-ops fn2-ops-issued-count fn2-ops-rows)))))))
(make-event
 (value `(defthm fn2-turn-issued-total
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
   ,(fn2-run-issued-claim '(mv-nth 3 (fn2-turn fn2-core))
     '(fn2-core-ops fn2-core) '(fn2-core-ops (mv-nth 4 (fn2-turn fn2-core)))))
  :hints (("Goal" :in-theory (e/d (fn2-turn)
    (fn2-concrete-turn fn2-corep fn2-core-wfp fn2-core-ops
     fn2-ops-issued-count fn2-ops-rows)))))))
(defthm fn2-turn-issued-history-within-limit
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (<= (- (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core))
                              (fn2-core-ops (mv-nth 4 (fn2-turn fn2-core))))
         (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core))
                              (fn2-core-ops fn2-core)))
      (fn2-exec-aturn fn2-core)))
 :hints (("Goal" :use (fn2-turn-issued-total fn2-turn-actions-within-limit)
   :in-theory (disable fn2-turn fn2-corep fn2-core-wfp fn2-core-ops
                      fn2-ops-issued-count fn2-ops-rows))))
))

(defmacro fn2-executor-issued-events ()
 '(progn
(fn2-core-issued-events)
(make-event
 (value (cons 'progn
  (fn2-dc-forms
   (fn2-dc-todo
    '(fn2-exec-pop fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake
      fn2-exec-record fn2-exec-visit fn2-exec-run-services fn2-machine-grant-one
      fn2-exec-account-work fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
      fn2-exec-set-armed-deadline fn2-machine-observe-terminal
      fn2-machine-refuse-observation)
    nil (w state) nil 64) nil))))
(make-event
 (value (cons 'progn
  (fn2-executor-issued-frame-events
    '(fn2-exec-pop fn2-exec-charge-run fn2-machine-take-wake fn2-exec-wake
      fn2-exec-record fn2-exec-visit fn2-exec-run-services fn2-machine-grant-one
      fn2-exec-account-work fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
      fn2-exec-set-armed-deadline fn2-machine-observe-terminal
      fn2-machine-refuse-observation) (w state)))))
(make-event
 (value (cons 'progn
  (fn2-dc-forms
   (fn2-dc-todo (fn2-executor-concrete-observers (fn2-machine-names (w state)) (w state))
               nil (w state) nil 64) nil))))
(make-event
 (value (cons 'progn (fn2-executor-observe-ops-events (fn2-machine-names (w state)) (w state)))))
(make-event
 (value `(defthm fn2-machine-observe-ops-child-frame
  (equal (fn2-core-ops (mv-nth 1 (fn2-machine-observe okind id gen event outcome reason count aux0 aux1 fn2-core)))
         (fn2-core-ops fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-machine-observe)
   (fn2-core-ops fn2-machine-refuse-observation
    ,@(all-fnnames (getpropc 'fn2-machine-observe 'unnormalized-body nil (w state))))))))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-exec-mailbox nil 5 '(fn2-core-stop) (w state))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-exec-arm 0 1 nil (w state))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-exec-harvest nil 5 nil (w state))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-exec-principal 2 5 nil (w state))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-exec-service 2 5 nil (w state))))
(make-event
 (value (fn2-executor-issued-step-event 'fn2-transition 2 5 nil (w state))))
(fn2-executor-issued-loop-events)
))
