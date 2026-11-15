; Actual core read/write laws shared by the release and whole-arm proofs.
(in-package "ACL2")
(include-book "cns-draining-model")
(include-book "core-product-lowering")

(make-event
 (let* ((world (w state))
        (selected (fn2-product-entries (fn2-core-child-registry world)
                                      '(fn2-core-pool fn2-core-control fn2-core-machines
                                        fn2-core-sched fn2-cns-table) world)))
   (value (cons 'progn
     (append (fn2-product-core-shape-events world)
             (fn2-product-writeback-facts selected selected world)
             (fn2-product-spine-facts selected world))))))

(defun fn2-cns-core-model-projection-events (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((field (caar entries))
           (child (fn2-core-child-property (car entries) :stobj))
           (writer (fn2-product-writer field)))
      (append
       `((defthm ,(fn2-columns-sym field "-CNS-MODEL-BY-DEFINITION")
           (equal (fn2-cns-drain-child ',child core) (,field core))
           :hints (("Goal" :in-theory
                    (enable fn2-cns-drain-child fn2-cns-drain-child-index ,field))))
         (defthm ,(fn2-columns-sym writer "-CNS-MODEL-BY-DEFINITION")
           (equal (fn2-cns-drain-put-child ',child value core) (,writer value core))
           :hints (("Goal" :in-theory
                    (enable fn2-cns-drain-put-child fn2-cns-drain-child-index ,writer)))))
       (fn2-cns-core-model-projection-events (cdr entries))))))

(make-event
 (value (cons 'progn
   (fn2-cns-core-model-projection-events
     (fn2-product-entries (fn2-core-child-registry (w state))
       '(fn2-core-pool fn2-core-control fn2-core-machines fn2-core-sched fn2-cns-table) (w state))))))
