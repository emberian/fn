; E2 Q1 proof-only loop contract; no new reference/concrete implementation.
(in-package "ACL2")
(include-book "../checks")
(include-book "defsquare")

; ctx = (fuel h k a observations visits actions reference-bytes reference-steps).
(defun sq-q1-fuel (ctx) (nfix (nth 0 ctx)))
(defun sq-q1-h (ctx) (nfix (nth 1 ctx)))
(defun sq-q1-k (ctx) (nfix (nth 2 ctx)))
(defun sq-q1-a (ctx) (nfix (nth 3 ctx)))
(defun sq-q1-obs (ctx) (nfix (nth 4 ctx)))
(defun sq-q1-visits (ctx) (nfix (nth 5 ctx)))
(defun sq-q1-actions (ctx) (nfix (nth 6 ctx)))
(defun sq-q1-ref-bytes (ctx) (nfix (nth 7 ctx)))
(defun sq-q1-ref-steps (ctx) (nfix (nth 8 ctx)))
(defun sq-q1-budget (ctx) (- (sq-q1-a ctx) (sq-q1-actions ctx)))
(defun sq-q1-advance (ctx o v d rb rs)
  (list (nfix (- (sq-q1-fuel ctx) 1)) (sq-q1-h ctx) (sq-q1-k ctx)
        (sq-q1-a ctx) (+ (sq-q1-obs ctx) (nfix o))
        (+ (sq-q1-visits ctx) (nfix v)) (+ (sq-q1-actions ctx) (nfix d))
        (+ (sq-q1-ref-bytes ctx) (nfix rb))
        (+ (sq-q1-ref-steps ctx) (nfix rs))))

; Only these two fields differ in their time of accounting. This is logical
; normalization, not a mutation of the reference implementation.
(defun-nx sq-q1-normalize-reference-work (reference bytes steps)
  (fn2-exec-set-turn-steps steps (fn2-exec-set-turn-bytes bytes reference)))
(defun-nx sq-q1-loop-relatedp (ctx concrete reference lists)
  (fn2-representation-relation
   concrete (sq-q1-normalize-reference-work
             reference (sq-q1-ref-bytes ctx) (sq-q1-ref-steps ctx)) lists))

(defun sq-q1-nat-listp (xs)
  (if (atom xs) (null xs)
    (and (natp (car xs)) (sq-q1-nat-listp (cdr xs)))))

; The bounded arithmetic domain explicitly excludes the concrete u60 overflow
; stop, absent in the unbounded reference accumulator. This extra loop domain
; does NOT enter the existing turn-refinement composition statement.
(defun-nx sq-q1-loop-invp (ctx concrete reference lists)
  (and (true-listp ctx) (equal (len ctx) 9) (sq-q1-nat-listp ctx)
       (true-listp lists) (equal (len lists) 4)
       (fn2-corep concrete) (fn2-core-wfp concrete)
       (fn2-ref-corep reference) (fn2-core-wfp reference)
       (equal (sq-q1-h ctx) (fn2-exec-h concrete))
       (equal (sq-q1-k ctx) (fn2-exec-k concrete))
       (equal (sq-q1-a ctx) (fn2-exec-aturn concrete))
       (<= (sq-q1-obs ctx) (sq-q1-h ctx))
       (<= (sq-q1-visits ctx) (sq-q1-k ctx))
       (<= (sq-q1-actions ctx) (sq-q1-a ctx))
       (equal (+ (sq-q1-fuel ctx) (sq-q1-obs ctx) (sq-q1-visits ctx))
              (+ (sq-q1-h ctx) (sq-q1-k ctx)))
       (<= (+ (* 24 (sq-q1-h ctx)) (* 4129 (sq-q1-k ctx)))
           1152921504606846975)
       (<= (+ (sq-q1-ref-bytes ctx) (sq-q1-ref-steps ctx))
           (+ (* 24 (sq-q1-obs ctx)) (* 4129 (sq-q1-visits ctx))))
       (sq-q1-loop-relatedp ctx concrete reference lists)))
(defun-nx sq-q1-continuep (ctx concrete reference lists)
  (and (< 0 (sq-q1-fuel ctx))
       (< (sq-q1-obs ctx) (sq-q1-h ctx))
       (< (sq-q1-visits ctx) (sq-q1-k ctx))
       (< (sq-q1-actions ctx) (sq-q1-a ctx))
       (equal (fn2-exec-stop concrete) 0)
       (or (fn2-exec-observation-p concrete) (fn2-exec-eligible-p concrete))
       (eq (fn2-ref-status lists reference) :more)))
(defun-nx sq-q1-casep (case ctx concrete lists)
  (declare (ignorable ctx))
  (equal case (fn2-e1-label lists concrete)))

; The reference comparison includes ordered outbox descriptors, ownership,
; pool fills and live bytes; it omits the diagnostic trace and unused reference
; intrusive scheduler. Work is checked by loop-relatedp, independently of this
; observation. Before-and-after comparisons retain the observable prefix too.
(defun-nx sq-q1-effects-agreep (concrete reference concrete1 reference1)
  (and
   (not (fn2-ref-core-difference
         concrete (sq-q1-normalize-reference-work
                   reference (fn2-exec-turn-bytes concrete)
                   (fn2-exec-turn-steps concrete))))
   (not (fn2-ref-core-difference
         concrete1 (sq-q1-normalize-reference-work
                    reference1 (fn2-exec-turn-bytes concrete1)
                    (fn2-exec-turn-steps concrete1))))))

; Direct roles describe the unchanged formula: the successor relation is the
; full invariant (including admissibility), not its nested pure relation helper.
(defconst *sq-q1-contract*
  '(:pre sq-q1-loop-invp :enabled sq-q1-continuep :casep sq-q1-casep
    :relation sq-q1-loop-invp :observation sq-q1-effects-agreep
    :budget sq-q1-budget :advance sq-q1-advance))
(defconst *sq-q1-sides*
  '(:concrete (fn2-transition fn2-exec-account-work)
    :reference (fn2-ref-transition)))

; One semantic template; all named contract/side calls come from these roles.
(defun sq-q1-case-formula (case contract sides)
  (declare (xargs :verify-guards nil))
  `(implies
    (and (,(sq-get :pre contract) ctx concrete reference lists)
         (,(sq-get :enabled contract) ctx concrete reference lists)
         (,(sq-get :casep contract) ',case ctx concrete lists))
    (mv-let (o v d b s concrete1)
      (,(car (sq-get :concrete sides)) t (,(sq-get :budget contract) ctx) concrete)
      (mv-let (ro rv rd rb rs lists1 reference1)
        (,(car (sq-get :reference sides)) (,(sq-get :budget contract) ctx) lists reference)
        (let ((concrete2 (,(cadr (sq-get :concrete sides)) b s concrete1))
              (ctx1 (,(sq-get :advance contract) ctx o v d rb rs)))
          (and (equal (list o v d b s) (list ro rv rd rb rs))
               (,(sq-get :observation contract) concrete reference concrete2 reference1)
               (,(sq-get :relation contract) ctx1 concrete2 reference1 lists1)))))))
