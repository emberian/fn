; Actual pool/child/core release outputs and complete frames. This book
; requires the core prefix, not canonical CNS callback materialization.
(in-package "ACL2")
(include-book "cns-pool-refinement")
(include-book "cns-core-projections")

(defthm fn2-cns-owned-release-admission-by-definition
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
           (fn2-pool-release-countp slot pool))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'fn2-cns-pool-readers)
            (e/d (fn2-pool-release-countp fn2-pool-rows fn2-pool-nclasses
                  fn2-pool-retired-count fn2-pool-class-countsi
                  fn2-cns-drain-releasablep fn2-cns-drain-cell
                  fn2-cns-drain-get fn2-cns-drain-index)
                 (fn2-poolp fn2-pool-wfp))))))

(defun fn2-cns-release-children-expected (slot gen kind id ogen pool control)
  (let ((out (fn2-cns-owned-pool-release-expected slot gen kind id ogen pool)))
    (list (car out) (cadr out)
      (if (member-eq (car out) '(:ok :retired :held)) control
        (fn2-cns-drain-stopped-control *fn2-stop-reason-pool-release* control)))))

(defthm fn2-cns-core-release-children-independent
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (equal
     (fn2-core-release-children slot gen *fn2-cns-kind* id ogen pool control)
     (fn2-cns-release-children-expected slot gen *fn2-cns-kind* id ogen pool control)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-release-admission-by-definition
                 fn2-cns-owned-pool-release-independent)
           :in-theory
           (e/d (fn2-core-release-children fn2-cns-release-children-expected
                 fn2-cns-owned-pool-release-expected fn2-cns-drain-stopped-control
                 fn2-control-record-stop fn2-control-stop
                 update-fn2-control-stop update-fn2-control-stop-reason)
                (fn2-pool-release fn2-pool-release-countp fn2-poolp fn2-pool-wfp
                 fn2-cns-drain-releasablep fn2-cns-drain-released-pool
                 fn2-cns-drain-cell fn2-cns-drain-get)))))

(defun fn2-cns-core-release-output-expected (out before)
  (let ((after (fn2-cns-drain-put-child 'fn2-pool (cadr out) before)))
    (list (car out)
      (if (member-eq (car out) '(:ok :retired :held)) after
        (fn2-cns-drain-put-child 'fn2-control
          (fn2-cns-drain-stopped-control *fn2-stop-reason-pool-release*
            (fn2-cns-drain-child 'fn2-control before)) after)))))
(defun fn2-cns-core-release-expected (slot gen kind id ogen before)
  (fn2-cns-core-release-output-expected
    (fn2-cns-owned-pool-release-expected slot gen kind id ogen
      (fn2-cns-drain-child 'fn2-pool before)) before))
(defun fn2-cns-core-release-zero-query-expected (slot gen kind id ogen before)
  (fn2-cns-core-release-output-expected
    (fn2-cns-owned-zero-query-pool-release-expected slot gen kind id ogen
      (fn2-cns-drain-child 'fn2-pool before)) before))
; The previous oracle is a control, not the current permission contract.
(defun fn2-cns-core-release-pre-credit-expected (slot gen kind id ogen before)
  (let* ((pool (fn2-cns-drain-child 'fn2-pool before))
         (out (if (< 0 (fn2-cns-drain-cell 'fn2-pool-query-ref-count slot pool))
                  (list :held pool)
                (fn2-cns-owned-uncredited-zero-query-pool-release-expected slot gen kind id ogen pool))))
    (list (car out) (fn2-cns-drain-put-child 'fn2-pool (cadr out) before))))
(defthm fn2-cns-core-release-uncredited-equivalence-by-definition
  (implies (not (fn2-cns-drain-credit-boundp slot (fn2-cns-drain-child 'fn2-pool before)))
           (equal (fn2-cns-core-release-expected slot gen kind id ogen before)
                  (fn2-cns-core-release-pre-credit-expected slot gen kind id ogen before)))
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-core-release-expected fn2-cns-core-release-pre-credit-expected
                 fn2-cns-core-release-output-expected fn2-cns-owned-pool-release-expected
                 fn2-cns-owned-uncredited-zero-query-pool-release-expected)
                (fn2-cns-drain-released-pool fn2-cns-drain-credit-boundp)))))
(defthm fn2-cns-core-release-zero-query-equivalence-by-definition
  (implies (equal (fn2-cns-drain-cell 'fn2-pool-query-ref-count slot
                    (fn2-cns-drain-child 'fn2-pool before)) 0)
           (equal (fn2-cns-core-release-expected slot gen kind id ogen before)
                  (fn2-cns-core-release-zero-query-expected slot gen kind id ogen before)))
  :hints (("Goal" :in-theory
           (enable fn2-cns-core-release-expected fn2-cns-core-release-zero-query-expected
                   fn2-cns-owned-zero-query-release-equivalence-by-definition))))

; Keep this consequential component visible in the actual obligation store.
; Admission of the universal theorem and formula-bound teeth are separate.
(defthm-owed fn2-cns-core-release-independent (slot gen id ogen core)
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal (fn2-core-release slot gen *fn2-cns-kind* id ogen core)
           (fn2-cns-core-release-expected slot gen *fn2-cns-kind* id ogen core)))
  :schema :invariant :claim :semantic :boundary :ownership-reclamation
  :sides (:concrete fn2-core-release :reference fn2-cns-core-release-expected)
  :teeth (fn2-cns-core-release-positive fn2-cns-core-release-without-generation
          fn2-cns-core-release-sibling-mutation fn2-cns-core-release-query-held-positive
          fn2-cns-core-release-credit-positive)
  :doc "The actual core release returns the independent complete scalar/core result and frames every other child and protected sibling. A credit-bound input returns :credit with the complete pool retained and only the sticky stop effect. An ordinary positive query count retains the complete core with :held; noncredited semantics are preserved. A stale handle removes releasability without changing the typed/WFP input; actual sibling corruption falsifies the complete result. Component ownership is not a claim of reachable CNS admission.")

(defthm fn2-cns-core-release-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal (fn2-core-release slot gen *fn2-cns-kind* id ogen core)
           (fn2-cns-core-release-expected slot gen *fn2-cns-kind* id ogen core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-core-release-children-independent
                            (pool (fn2-core-pool core))
                            (control (fn2-core-control core)))
                 (:instance fn2-product-core-shape (fn2-core core)))
           :in-theory
           (e/d (fn2-core-release fn2-cns-core-release-expected
                 fn2-cns-release-children-expected fn2-cns-core-release-output-expected)
                (fn2-core-release-children fn2-core-pool fn2-core-control
                 update-fn2-core-pool update-fn2-core-control
                 fn2-cns-drain-releasablep fn2-cns-owned-pool-release-expected
                 fn2-corep fn2-core-wfp)))))

(defthm fn2-cns-core-release-protected-children
  (let ((after (mv-nth 1 (fn2-core-release slot gen kind id ogen core))))
    (and (equal (fn2-core-machines after) (fn2-core-machines core))
         (equal (fn2-cns-table after) (fn2-cns-table core))
         (equal (fn2-core-sched after) (fn2-core-sched core))))
  :hints (("Goal" :in-theory
           (e/d (fn2-core-release)
                (fn2-core-release-children fn2-core-machines fn2-cns-table fn2-core-sched
                 fn2-core-pool fn2-core-control update-fn2-core-pool update-fn2-core-control)))))
