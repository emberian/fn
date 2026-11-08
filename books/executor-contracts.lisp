; One induction for invariants of the actual executor.  G is ghost context
; (history, device evidence, identifiers, etc.), never a served allocation.
; REL is a declared relation at each named cut point, not a frame inferred
; to imply semantics.  Functional instantiation must prove both the callee's
; relation and that the relation preserves INV.
(in-package "ACL2")
(include-book "executor")

(defun fn2-executor-contract-name (fn suffix)
  (declare (xargs :verify-guards nil))
  (fn2-columns-sym fn suffix))

; Read the functions the LOGICAL dispatcher actually calls.  A kind whose
; implementation is attached still dispatches through its constrained stub.
; Recomputing RUN-ARMS after attachment would silently select a different fn.
; A kind's observe route is not a cut: only fn2-exec-harvest reaches it, on
; the completion that step harvested, and the harvest is one cut.
(defun fn2-executor-kind-cuts (names run-callees)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names)) (run (fn2-columns-sym name "-RUN"))
           (stub (fn2-columns-sym name "-RUN-STUB")))
      (cons (if (member-eq run run-callees) run stub)
            (fn2-executor-kind-cuts (cdr names) run-callees)))))

(defun fn2-executor-boundary-cuts (fns world)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (union-eq (fn2-arm-frame-body-callees (car fns) world)
              (fn2-executor-boundary-cuts (cdr fns) world))))

(make-event
 (let* ((world (w state))
        (run-callees (all-fnnames (getpropc 'fn2-machine-run 'unnormalized-body nil world)))
        (kind-cuts (fn2-executor-kind-cuts (fn2-machine-names world) run-callees))
        (boundaries (fn2-executor-boundary-cuts
                     '(fn2-machine-admit fn2-machine-grant-one fn2-exec-genesis-row) world)))
   (value
    `(defconst *fn2-executor-contract-cuts*
       ',(remove-duplicates-eq (append kind-cuts boundaries
          ; fn2-exec-harvest is one cut: delivering a harvested completion
          ; to its owner's handler is one executor step, and no invariant is
          ; owed between the harvest and the delivery
          '(fn2-machine-refuse-phase fn2-machine-idle
            fn2-exec-harvest fn2-exec-mailbox fn2-exec-pop fn2-exec-charge-run
            fn2-machine-take-wake fn2-exec-wake fn2-exec-record fn2-exec-visit
            fn2-exec-clear-service fn2-exec-arm
            fn2-exec-account-work fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
            fn2-machine-reclaim)))))))

(defun fn2-executor-contract-args (fn world)
  (declare (xargs :verify-guards nil))
  (let ((args (formals fn world)))
    (if (member-eq fn '(fn2-exec-set-turn-bytes fn2-exec-set-turn-steps))
        (subst 0 'value args) args)))

(defun fn2-executor-contract-domain (fn)
  (declare (xargs :verify-guards nil))
  ; CORE-STOP writes a typed reason directly.  Its actual callers supply
  ; a declared reason; preservation outside that domain would be false.
  (if (eq fn 'fn2-core-stop) '(unsigned-byte-p 8 reason) t))

(defun fn2-executor-contract-events (fns world relationsp)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (let* ((fn (car fns)) (args (fn2-executor-contract-args fn world))
           (domain (fn2-executor-contract-domain fn))
           (out (fn2-arm-frame-out-term fn (cons fn args) world))
           (rel `(fn2-executor-rel ',fn (list ,@(remove-eq 'fn2-core args)) g fn2-core ,out)))
      (cons
       (if relationsp
           `(defthm ,(fn2-executor-contract-name fn "-EXECUTOR-REL")
              (implies (and ,domain (fn2-corep fn2-core) (fn2-core-wfp fn2-core)) ,rel))
         `(defthm ,(fn2-executor-contract-name fn "-EXECUTOR-INV")
            (implies (and ,domain (fn2-executor-inv g fn2-core)
                          (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                     (fn2-executor-inv g ,out))
            :hints (("Goal" :use ((:instance fn2-executor-rel-preserves
                                  (tag ',fn) (args (list ,@(remove-eq 'fn2-core args)))
                                  (before fn2-core) (after ,out)))))))
       (fn2-executor-contract-events (cdr fns) world relationsp)))))

(make-event
 (value
  `(encapsulate
    (((fn2-executor-inv * *) => *)
     ((fn2-executor-rel * * * * *) => *))
    (local (defun fn2-executor-inv (g c) (declare (ignore g c)) t))
    (local (defun fn2-executor-rel (tag args g before after)
             (declare (ignore tag args g before after)) t))
    (defthm fn2-executor-rel-preserves
      (implies (and (fn2-executor-inv g before)
                    (fn2-corep before) (fn2-core-wfp before)
                    (fn2-executor-rel tag args g before after))
               (fn2-executor-inv g after))
      :rule-classes nil)
    ,@(fn2-executor-contract-events *fn2-executor-contract-cuts* (w state) t))))

(defun fn2-executor-reader-cuts (fns world)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (let ((fn (car fns)))
      (if (and (member-eq 'fn2-core (formals fn world))
               (not (fn2-arm-frame-corep-fn fn world))
               (getpropc fn 'unnormalized-body nil world))
          (cons fn (fn2-executor-reader-cuts (cdr fns) world))
        (fn2-executor-reader-cuts (cdr fns) world)))))

(defun fn2-executor-compose-events (fns)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (cons
     `(make-event
       (let* ((fn ',(car fns)) (world (w state)) (args (formals fn world))
              (out (fn2-arm-frame-out-term fn (cons fn args) world)))
         (value
          `(defthm ,(fn2-executor-contract-name fn "-EXECUTOR-INV")
             (implies (and (fn2-executor-inv g fn2-core)
                           (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                      (fn2-executor-inv g ,out))
             :hints (("Goal" :in-theory
                       (e/d (,fn)
                            ,(fn2-executor-reader-cuts
                              (all-fnnames (getpropc fn 'unnormalized-body nil world)) world))
                      :do-not-induct t))))))
     (fn2-executor-compose-events (cdr fns)))))

; These two proofs are the finite dispatch coverage, generated from the
; same registry as the dispatcher, including refusal/default branches.
; A newly registered kind produces a new cut contract, never a new loop proof.
(make-event
 (value (cons 'progn (fn2-executor-contract-events *fn2-executor-contract-cuts* (w state) nil))))
(make-event
 (value (cons 'progn
   (fn2-executor-compose-events
    '(fn2-machine-run fn2-machine-admit
      fn2-machine-grant-one fn2-exec-genesis-row
      fn2-exec-principal fn2-exec-service fn2-transition)))))

(defthm fn2-executor-inv-concrete-loop
  (implies (and (fn2-executor-inv g fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-executor-inv g
             (mv-nth 4 (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core))))
  :hints (("Goal" :induct (fn2-concrete-loop fuel h k a nobs nvisits nactions fn2-core)
           :in-theory (e/d (fn2-concrete-loop)
                          (fn2-concrete-loop-stop-p fn2-transition fn2-exec-account-work)))))
(defthm fn2-executor-inv-turn
  (implies (and (fn2-executor-inv g fn2-core)
                (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (fn2-executor-inv g (mv-nth 4 (fn2-turn fn2-core))))
  :hints (("Goal" :in-theory (e/d (fn2-turn fn2-concrete-turn)
                        (fn2-concrete-loop fn2-exec-set-turn-bytes fn2-exec-set-turn-steps)))))

; Non-commit instance: the complete assembled concrete representation
; invariant, including every child's types and well-formedness.  Its
; certificates are the actual callees' CORE-PRESERVES facts, not executions
; of a replacement scheduler.
(defun-nx fn2-executor-representation-inv (g c)
  (declare (xargs :verify-guards nil) (ignorable g))
  (and (fn2-corep c) (fn2-core-wfp c)))
(defun-nx fn2-executor-representation-rel (tag args g before after)
  (declare (xargs :verify-guards nil) (ignorable tag args g before))
  (and (fn2-corep after) (fn2-core-wfp after)))
(defmacro fn2-executor-instantiate (name predicate relation &key disable)
  `(defthm ,name
     (implies (and (,predicate g fn2-core)
                   (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
              (,predicate g (mv-nth 4 (fn2-turn fn2-core))))
     :hints (("Goal"
              :use ((:functional-instance fn2-executor-inv-turn
                      (fn2-executor-inv ,predicate)
                      (fn2-executor-rel ,relation)))
              :in-theory (disable fn2-corep fn2-core-wfp fn2-turn ,@disable)
              :do-not-induct t))))
(fn2-executor-instantiate fn2-executor-representation-turn
                         fn2-executor-representation-inv
                         fn2-executor-representation-rel)
