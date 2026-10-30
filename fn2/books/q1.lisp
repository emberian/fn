; Q1, the loop-iteration correspondence between fn2-transition (with its work
; accounting) and the independent reference transition, bound through
; defsquare to every label of the assembled case catalogue (DSL-METATHEORY
; 3.3; adopted from the squares experiment E2, fn2/experiments/squares/e2/
; q1-contract.lisp and q1-bindings.lisp, renamed sq-q1-* -> fn2-q1-*). The
; contract functions are proof-only; no implementation is added on either side.
; The composition row is the existing fn2-turn-refinement, referenced unchanged.
(in-package "ACL2")
(include-book "reference")
(include-book "squares")

; ctx = (fuel h k a observations visits actions reference-bytes reference-steps).
(defun fn2-q1-fuel (ctx) (nfix (nth 0 ctx)))
(defun fn2-q1-h (ctx) (nfix (nth 1 ctx)))
(defun fn2-q1-k (ctx) (nfix (nth 2 ctx)))
(defun fn2-q1-a (ctx) (nfix (nth 3 ctx)))
(defun fn2-q1-obs (ctx) (nfix (nth 4 ctx)))
(defun fn2-q1-visits (ctx) (nfix (nth 5 ctx)))
(defun fn2-q1-actions (ctx) (nfix (nth 6 ctx)))
(defun fn2-q1-ref-bytes (ctx) (nfix (nth 7 ctx)))
(defun fn2-q1-ref-steps (ctx) (nfix (nth 8 ctx)))
(defun fn2-q1-budget (ctx) (- (fn2-q1-a ctx) (fn2-q1-actions ctx)))
(defun fn2-q1-advance (ctx o v d rb rs)
  (list (nfix (- (fn2-q1-fuel ctx) 1)) (fn2-q1-h ctx) (fn2-q1-k ctx)
        (fn2-q1-a ctx) (+ (fn2-q1-obs ctx) (nfix o))
        (+ (fn2-q1-visits ctx) (nfix v)) (+ (fn2-q1-actions ctx) (nfix d))
        (+ (fn2-q1-ref-bytes ctx) (nfix rb))
        (+ (fn2-q1-ref-steps ctx) (nfix rs))))

; Only these two fields differ in their time of accounting: a logical
; normalisation, not a mutation of the reference implementation.
(defun-nx fn2-q1-normalize-reference-work (reference bytes steps)
  (fn2-exec-set-turn-steps steps (fn2-exec-set-turn-bytes bytes reference)))
(defun-nx fn2-q1-loop-relatedp (ctx concrete reference lists)
  (fn2-representation-relation
   concrete (fn2-q1-normalize-reference-work
             reference (fn2-q1-ref-bytes ctx) (fn2-q1-ref-steps ctx)) lists))

(defun fn2-q1-nat-listp (xs)
  (if (atom xs) (null xs)
    (and (natp (car xs)) (fn2-q1-nat-listp (cdr xs)))))

; The bounded arithmetic domain excludes the concrete u60 overflow stop,
; absent in the unbounded reference accumulator; it does NOT enter the
; existing turn-refinement statement. The reference lists have five elements
; since R5e2 (calendar, cursor, principal FIFOs, service flags, selection
; history); E2's contract said four.
(defun-nx fn2-q1-loop-invp (ctx concrete reference lists)
  (and (true-listp ctx) (equal (len ctx) 9) (fn2-q1-nat-listp ctx)
       (true-listp lists) (equal (len lists) 5)
       (fn2-corep concrete) (fn2-core-wfp concrete)
       (fn2-ref-corep reference) (fn2-core-wfp reference)
       (equal (fn2-q1-h ctx) (fn2-exec-h concrete))
       (equal (fn2-q1-k ctx) (fn2-exec-k concrete))
       (equal (fn2-q1-a ctx) (fn2-exec-aturn concrete))
       (<= (fn2-q1-obs ctx) (fn2-q1-h ctx))
       (<= (fn2-q1-visits ctx) (fn2-q1-k ctx))
       (<= (fn2-q1-actions ctx) (fn2-q1-a ctx))
       (equal (+ (fn2-q1-fuel ctx) (fn2-q1-obs ctx) (fn2-q1-visits ctx))
              (+ (fn2-q1-h ctx) (fn2-q1-k ctx)))
       (<= (+ (* *fn2-work-transition* (fn2-q1-h ctx)) (* *fn2-turn-transition-max* (fn2-q1-k ctx)))
           *fn2-u60-max*)
       (<= (+ (fn2-q1-ref-bytes ctx) (fn2-q1-ref-steps ctx))
           (+ (* *fn2-work-transition* (fn2-q1-obs ctx)) (* *fn2-turn-transition-max* (fn2-q1-visits ctx))))
       (fn2-q1-loop-relatedp ctx concrete reference lists)))
(defun-nx fn2-q1-continuep (ctx concrete reference lists)
  (and (< 0 (fn2-q1-fuel ctx))
       (< (fn2-q1-obs ctx) (fn2-q1-h ctx))
       (< (fn2-q1-visits ctx) (fn2-q1-k ctx))
       (< (fn2-q1-actions ctx) (fn2-q1-a ctx))
       (equal (fn2-exec-stop concrete) 0)
       (or (fn2-exec-observation-p concrete) (fn2-exec-eligible-p concrete))
       (eq (fn2-ref-status lists reference) :more)))

; The label of the transition fn2-transition takes from CONCRETE, read from
; the assembled catalogue (E1's labeller, fn2-e1-label, over the registry).
(defun fn2-q1-phase-map (names world)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (cons (car names) (fn2-machine-property (car names) :states world))
          (fn2-q1-phase-map (cdr names) world))))
(make-event (value `(defconst *fn2-q1-phases*
                      ',(fn2-q1-phase-map (fn2-machine-names (w state)) (w state)))))
(make-event (value `(defconst *fn2-q1-catalogue* ',(fn2-case-catalogue (w state)))))
(defun fn2-q1-next-event (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (event)
    (let* ((index (fn2-ops-posted-fifoi (fn2-ops-post-head fn2-ops) fn2-ops))
           (slot (floor index 2)) (cell (mod index 2)))
      (mv-let (p h event o r c a b) (fn2-op-cell cell slot fn2-ops)
        (declare (ignore p h o r c a b)) event)) event))
(defun fn2-q1-label (lists fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond
   ((fn2-core-posted-p fn2-core)
    (mv-let (found kind id gen principal) (fn2-core-next-owner fn2-core)
      (declare (ignore principal))
      (let* ((event (fn2-q1-next-event fn2-core))
             (name (car (nth kind *fn2-q1-phases*)))
             (label (list :observe name (fn2-event-code->keyword event))))
        (if (and found (fn2-machine-idp id fn2-core)
                 (equal gen (fn2-machine-generation id fn2-core))
                 (equal kind (fn2-machine-kind id fn2-core))
                 (fn2-machine-observe-accepts-p kind (fn2-machine-phase id fn2-core) event)
                 (member-equal label *fn2-q1-catalogue*)) label '(:router :fallback)))))
   ((fn2-exec-observation-p fn2-core)
    (if (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
          (= (fn2-ops-clock-posted fn2-ops) 1) yes)
        '(:executor :clock) '(:executor :signal)))
   ((fn2-exec-eligible-p fn2-core)
    (let* ((entry (nth (nth 1 lists) (nth 0 lists)))
           (queue (fn2-ref-queue (cadr entry) (nth 2 lists))) (id (car queue)))
      (cond ((eq (car entry) :service) (list :executor :service (cadr entry)))
            ((atom queue) '(:executor :empty-principal))
            ((or (not (fn2-machine-idp id fn2-core)) (= (fn2-machine-stopped id fn2-core) 1))
             '(:outside-catalogue :stopped-or-invalid))
            (t (let* ((entry (nth (fn2-machine-kind id fn2-core) *fn2-q1-phases*))
                      (phase (nth (fn2-machine-phase id fn2-core) (cdr entry))))
                 (if phase (list :run (car entry) phase) '(:outside-catalogue :invalid-phase)))))))
   (t '(:outside-catalogue :no-transition))))
(defun-nx fn2-q1-casep (case ctx concrete lists)
  (declare (ignorable ctx))
  (equal case (fn2-q1-label lists concrete)))

; The reference comparison includes ordered outbox descriptors, ownership,
; pool fills and live bytes; it omits the diagnostic trace and the reference's
; unused intrusive scheduler. Work is checked by loop-relatedp, independently.
(defun-nx fn2-q1-effects-agreep (concrete reference concrete1 reference1)
  (and
   (not (fn2-ref-core-difference
         concrete (fn2-q1-normalize-reference-work
                   reference (fn2-exec-turn-bytes concrete) (fn2-exec-turn-steps concrete))))
   (not (fn2-ref-core-difference
         concrete1 (fn2-q1-normalize-reference-work
                    reference1 (fn2-exec-turn-bytes concrete1) (fn2-exec-turn-steps concrete1))))))

; Direct roles describe the formula: the successor relation is the full
; invariant (admissibility included), not its nested pure relation helper.
(defconst *fn2-q1-contract*
  '(:pre fn2-q1-loop-invp :enabled fn2-q1-continuep :casep fn2-q1-casep
    :relation fn2-q1-loop-invp :observation fn2-q1-effects-agreep
    :budget fn2-q1-budget :advance fn2-q1-advance))
(defconst *fn2-q1-sides*
  '(:concrete (fn2-transition fn2-exec-account-work)
    :reference (fn2-ref-transition)))

; One semantic template; every named contract/side call comes from the roles.
(defun fn2-q1-case-formula (case contract sides)
  (declare (xargs :verify-guards nil))
  `(implies
    (and (,(fn2-decl-get :pre contract) ctx concrete reference lists)
         (,(fn2-decl-get :enabled contract) ctx concrete reference lists)
         (,(fn2-decl-get :casep contract) ',case ctx concrete lists))
    (mv-let (o v d b s concrete1)
      (,(car (fn2-decl-get :concrete sides)) t (,(fn2-decl-get :budget contract) ctx) concrete)
      (mv-let (ro rv rd rb rs lists1 reference1)
        (,(car (fn2-decl-get :reference sides)) (,(fn2-decl-get :budget contract) ctx) lists reference)
        (let ((concrete2 (,(cadr (fn2-decl-get :concrete sides)) b s concrete1))
              (ctx1 (,(fn2-decl-get :advance contract) ctx o v d rb rs)))
          (and (equal (list o v d b s) (list ro rv rd rb rs))
               (,(fn2-decl-get :observation contract) concrete reference concrete2 reference1)
               (,(fn2-decl-get :relation contract) ctx1 concrete2 reference1 lists1)))))))

(defun fn2-q1-id (index)
  (declare (xargs :verify-guards nil))
  (packn-pos (list 'fn2-q1-case- (nfix index)) 'fn2-q1))
(defconst *fn2-q1-requirements*
  '((fn2-q1-entry :schema :g1 :doc "Turn entry establishes fn2-q1-loop-invp from fn2-turn-refinement's antecedent.")
    (fn2-q1-exit :schema :g1 :doc "Loop exit: status and the reference's counter finalisation agree with fn2-turn.")
    (fn2-q1-termination :schema :bound :doc "Both loops stop within fuel h+k under the shared budgets.")
    (fn2-q1-partition :schema :invariant :doc "The catalogue's selectors partition the loop's transitions under the invariant; stopped, invalid and no-transition dispatch excluded.")
    (fn2-q1-accounting :schema :bound :doc "Per-arm cost certificates compose to the turn work bound of fn2-turn-refinement.")))
(defun fn2-q1-bind-cases (cases index contract sides world)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let* ((case (car cases)) (id (fn2-q1-id index)))
      (cons
       (cons case
             (list :id id :schema :g1 :source (fn2-case-source case world)
                   :origin (fn2-case-source case world)
                   :boundary :loop-iteration :vars '(ctx concrete reference lists)
                   :formula (fn2-q1-case-formula case contract sides) :proof '(:owed)
                   :depends '(fn2-q1-entry fn2-q1-exit fn2-q1-partition)
                   :checker (list :function 'fn2-q1-check-case :case case)
                   :teeth (list :positive (fn2-columns-sym id "-POSITIVE")
                                :negative (fn2-columns-sym id "-NEGATIVE"))
                   :doc "One loop-iteration case of Q1."))
       (fn2-q1-bind-cases (cdr cases) (+ 1 (nfix index)) contract sides world)))))

(make-event
 (value `(defsquare fn2-q1
           :template :q1-loop-iteration
           :cases-from (fn2-case-catalogue (w state))
           :bindings (fn2-q1-bind-cases (fn2-case-catalogue (w state)) 0
                                        *fn2-q1-contract* *fn2-q1-sides* (w state))
           :requirements ,*fn2-q1-requirements*
           :contract ,*fn2-q1-contract* :sides ,*fn2-q1-sides*)))
