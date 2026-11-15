; Exact named contracts for the only opaque shape/diagnostic leaves admitted
; by selected-body effect lowering. These are proof events, not a whitelist.
(in-package "ACL2")
(include-book "reference-effect-semantics")
(include-book "reference-effect-lowering")
(include-book "enqueue-trace")

; A single writer needs only O(number of children) read-over-write laws.
; No scheduler queue accessor is authorized by these trace frame facts.
(defun fn2-ref-effect-trace-lens-events (children trace)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (let ((field (caar children)))
      (append
       (and (not (eq field 'fn2-core-trace))
            (append (fn2-core-lens-read-events field (list trace))
                    (fn2-core-lens-read-events (fn2-columns-sym field "-REF") (list trace))))
       (fn2-ref-effect-trace-lens-events (cdr children) trace)))))
(make-event
 (let ((trace (assoc-eq 'fn2-core-trace *fn2-core-children*)))
   (if (not trace)
       (er soft 'fn2-ref-effect-trace-lens-events "Actual trace child is missing.")
     (let* ((events (fn2-ref-effect-trace-lens-events *fn2-core-children* trace))
            (missing (fn2-core-lens-missing-events events (w state))))
       (value `(progn ,@missing
                 (deftheory fn2-ref-effect-trace-lenses ',(strip-cadrs events))))))))

(defthm fn2-ref-effect-trace-update-concrete-frame
  (equal (fn2-representation-relation (update-fn2-core-trace trace fn2-core)
                                     fn2-ref-core lists)
         (fn2-representation-relation fn2-core fn2-ref-core lists))
  :hints (("Goal" :in-theory
           (union-theories (theory 'fn2-ref-effect-trace-lenses)
            (union-theories
             '(fn2-representation-relation fn2-ref-difference fn2-ref-scheduler-difference
               fn2-ref-timer-state-difference fn2-ref-core-difference)
             (theory 'minimal-theory))))))
(defthm fn2-ref-effect-trace-update-reference-frame
  (equal (fn2-representation-relation fn2-core
                                     (update-fn2-core-trace trace fn2-ref-core) lists)
         (fn2-representation-relation fn2-core fn2-ref-core lists))
  :hints (("Goal" :in-theory
           (union-theories (theory 'fn2-ref-effect-trace-lenses)
            (union-theories
             '(fn2-representation-relation fn2-ref-difference fn2-ref-scheduler-difference
               fn2-ref-timer-state-difference fn2-ref-core-difference)
             (theory 'minimal-theory))))))

; The reference core is declared congruent to the original core; their
; recognizers inspect the same child types at the same logical positions.
(defthm fn2-ref-effect-core-recognizer-by-definition
  (equal (fn2-corep fn2-ref-core) (fn2-ref-corep fn2-ref-core))
  :hints (("Goal" :in-theory
           (union-theories '(fn2-corep fn2-ref-corep) (theory 'minimal-theory)))))

(make-event
 (value `(defthm fn2-ref-effect-corep-shape
           ,(fn2-reference-effect-leaf-formula 'fn2-corep :shape
              'fn2-representation-relation (w state))
           :rule-classes nil
           :hints (("Goal" :use fn2-ref-effect-core-recognizer-by-definition
                    :in-theory (theory 'minimal-theory))))))
(make-event
 (value `(defthm fn2-ref-effect-core-wfp-shape
           ,(fn2-reference-effect-leaf-formula 'fn2-core-wfp :shape
              'fn2-representation-relation (w state))
           :rule-classes nil
           :hints (("Goal" :in-theory (theory 'minimal-theory))))))
(make-event
 (value `(defthm fn2-ref-effect-record-enqueue-frame
           ,(fn2-reference-effect-leaf-formula 'fn2-core-record-enqueue :frame
              'fn2-representation-relation (w state))
           :rule-classes nil
           :hints (("Goal" :in-theory
                    (union-theories
                     '(fn2-ref-effect-whole-resultp fn2-core-record-enqueue
                       fn2-ref-effect-trace-update-concrete-frame
                       fn2-ref-effect-trace-update-reference-frame)
                     (theory 'minimal-theory)))))))
