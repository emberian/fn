; Child output/effect refinement used by the independent CNS contract.
; This is not the full composed CNS-body or caller-domain theorem.
(in-package "ACL2")
(include-book "cns-draining-contract")
(include-book "pool-release-admission")

(make-event
 (value `(deftheory fn2-cns-pool-readers
           ',(fn2-cns-drain-column-names 'fn2-pool
               (fn2-decl-get :columns
                 (cdr (assoc-eq 'fn2-pool (fn2-decl-rows :columns (w state)))))))))

(defun fn2-cns-owned-pool-release-expected (slot gen okind id ogen pool)
  (declare (ignore gen okind id ogen) (xargs :verify-guards nil))
  (list (if (>= (fn2-cns-drain-cell 'fn2-pool-gen slot pool)
                 (fn2-cns-drain-get 'fn2-pool-gen-limit pool)) :retired :ok)
        (fn2-cns-drain-released-pool slot pool)))

(defthm fn2-cns-owned-pool-release-independent
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (equal
     (fn2-pool-release slot gen *fn2-cns-kind* id ogen pool)
     (fn2-cns-owned-pool-release-expected slot gen *fn2-cns-kind* id ogen pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'fn2-cns-pool-readers)
            (e/d (fn2-pool-release fn2-pool-release-countp fn2-pool-rows
                 fn2-pool-nclasses fn2-pool-gen-limit fn2-pool-retired-count
                 fn2-pool-class-headsi fn2-pool-class-countsi
                 fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp
                 fn2-pool-set-gen fn2-pool-set-state fn2-pool-set-fill fn2-pool-set-next-free
                 update-fn2-pool-gen$ai update-fn2-pool-state$ai
                 update-fn2-pool-fill$ai update-fn2-pool-next-free$ai
                 update-fn2-pool-class-headsi update-fn2-pool-class-countsi
                 update-fn2-pool-retired-count
                 fn2-cns-owned-pool-release-expected
                 fn2-cns-drain-releasablep fn2-cns-drain-released-pool
                 fn2-cns-drain-put-cells fn2-cns-drain-put-cell
                 fn2-cns-drain-put fn2-cns-drain-cell fn2-cns-drain-get
                 fn2-cns-drain-index)
                 (fn2-poolp fn2-pool-wfp))))))
