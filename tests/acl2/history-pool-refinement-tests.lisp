(in-package "ACL2")
(include-book "../../books/history-pool-refinement")

(defun hpert-row (row fuel)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (ok fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin 'epoch 'lease fn-hpb))
          (c (fn-hpe-begin (list :resident row) 'epoch 'lease))
          (antecedent (and (fn-hrcur-tree-domainp row)
                           (< (len (fn-scc-encode row)) 18446744073709551616)
                           (fn-hpbp fn-hpb) (equal (fn-hpb-prefix fn-hpb) nil)
                           (fn-hper-invariantp c nil)
                           (equal (fn-hper-pending c nil)
                                  (fn-hper-pack (fn-scc-encode row))))))
    (mv-let (next partial completed fn-hpb) (fn-hper-run fuel c nil nil fn-hpb)
     (mv (and antecedent (equal (fn-hrcur-field 0 next) :prepared)
              (fn-hper-invariantp next partial) (fn-hpbp fn-hpb)
              (equal (fn-hper-pending next partial) nil)
              (equal (append completed (fn-hpb-prefix fn-hpb))
                     (fn-hper-pack (fn-scc-encode row)))
              (equal (fn-hrcur-field 4 next) (len (fn-scc-encode row)))) fn-hpb)))
   ok)))
(assert-event (hpert-row '("hello" . 256) 200))
(assert-event (hpert-row '(1 2 3) 200))
; An actual page reset occurs in this nonempty current-codec trace.
(assert-event (hpert-row (make-list 16400 :initial-element 42) 50000))

(defun hpert-step (fuel)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (ok fn-hpb)
   (let ((fn-hpb (fn-hpb-begin 'epoch 'lease fn-hpb)))
    (mv-let (c partial completed fn-hpb)
      (fn-hper-run fuel (fn-hpe-begin '(:resident "hello") 'epoch 'lease) nil nil fn-hpb)
     (declare (ignore completed))
     (let* ((antecedent (and (fn-hper-invariantp c partial) (fn-hpbp fn-hpb)))
            (old (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial)))
            (next-partial (fn-hper-partial-next c partial fn-hpb)))
      (mv-let (v summary next fn-hpb) (fn-hpe-tick c fn-hpb)
       (declare (ignore v summary))
       (mv (and antecedent (fn-hper-invariantp next next-partial)
                (equal old (append (fn-hpb-prefix fn-hpb) (fn-hper-pending next next-partial))))
           fn-hpb)))))
   ok)))
(assert-event (and (hpert-step 0) (hpert-step 3) (hpert-step 10)
                   (hpert-step 15) (hpert-step 20) (hpert-step 30)))

; Corrupted-state removal of residual attribution: all retained hypotheses
; (the concrete scratch invariant) hold; omitted ghost invariant and exact
; semantic conclusion fail. The actual emitter remains valid here.
(defun hpert-wrong-partial ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (ok fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin 'epoch 'lease fn-hpb))
          (codec '(:done (nil epoch lease) nil epoch lease nil))
          (c (list :finish codec 1 42 1 'epoch 'lease))
          (partial '(43))
          (retained (and (fn-hpbp fn-hpb) (fn-hpe-invariantp c)
                         (not (fn-hper-invariantp c partial))))
          (old (append (fn-hpb-prefix fn-hpb) (fn-hper-pending c partial)))
          (next-partial (fn-hper-partial-next c partial fn-hpb)))
    (mv-let (v summary next fn-hpb) (fn-hpe-tick c fn-hpb)
     (declare (ignore v summary))
     (mv (and retained
              (not (equal old (append (fn-hpb-prefix fn-hpb) (fn-hper-pending next next-partial)))))
         fn-hpb)))
   ok)))
(assert-event (hpert-wrong-partial))

; Logical corrupted scratch: raw bounded used cannot hold -1. Every retained
; residual premise holds; concrete invariant and the conclusion fail.
(defthm hpert-negative-used-residual-removal
 (let* ((codec '(:done (nil epoch lease) nil epoch lease nil))
        (c (list :finish codec 1 42 1 'epoch 'lease))
        (partial '(42)) (s '((0) -1 epoch lease)))
  (and (fn-hper-invariantp c partial) (not (fn-hpbp s))
       (not (equal (append (fn-hpb-prefix s) (fn-hper-pending c partial))
                   (append (fn-hpb-prefix (mv-nth 3 (fn-hpe-tick c s)))
                           (fn-hper-pending (mv-nth 2 (fn-hpe-tick c s))
                                            (fn-hper-partial-next c partial s)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpe-tick fn-hpb-put fn-hpb-prefix)
                 :expand ((:free (x) (hide x))))))

; Sole carry hypothesis removal, explicitly corrupted terminal state.
(defthm hpert-terminal-carry-removal
 (let* ((codec '(:done (nil epoch lease) nil epoch lease nil))
        (c (list :prepared codec 1 42 1 'epoch 'lease))
        (partial '(42)) (s (create-fn-hpb)))
  (and (not (fn-hper-invariantp c partial))
       (not (fn-hper-invariantp (mv-nth 2 (fn-hpe-tick c s))
                                (fn-hper-partial-next c partial s)))))
 :rule-classes nil)

; Each prepared-empty hypothesis has a literal corrupted-state counterexample.
(defthm hpert-prepared-invariant-removal
 (let* ((codec '(:done (nil epoch lease) nil epoch lease nil))
        (c (list :prepared codec 1 42 1 'epoch 'lease)))
  (and (equal (fn-hrcur-field 0 c) :prepared)
       (not (fn-hper-invariantp c '(42)))
       (not (equal (fn-hper-pending c '(42)) nil))))
 :rule-classes nil)
(defthm hpert-prepared-phase-removal
 (let* ((codec '(:done (nil epoch lease) nil epoch lease nil))
        (c (list :finish codec 1 42 1 'epoch 'lease)))
  (and (fn-hper-invariantp c '(42))
       (not (equal (fn-hrcur-field 0 c) :prepared))
       (not (equal (fn-hper-pending c '(42)) nil))))
 :rule-classes nil)
