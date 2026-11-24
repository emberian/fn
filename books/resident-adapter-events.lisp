; Lift operation-table shape preservation to the assembled registry's measure.
(in-package "ACL2")
(include-book "resident")
(include-book "ops-resident-proof")

(defun fn2-resident-column-length-claims (lengths)
  (declare (xargs :verify-guards nil))
  (if (endp lengths) nil
    (cons `(equal (,(car lengths) ops) (fn2-ops-rows ops))
          (fn2-resident-column-length-claims (cdr lengths)))))

(defmacro fn2-resident-adapter-events ()
  '(make-event
    (let* ((entries (fn2-core-child-registry (w state)))
           (measures (strip-cars (fn2-resident-sum entries)))
           (columns (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-ops) (w state)))))
      (value
       `(progn
          (local
           (defthm fn2-resident-op-column-lengths
             (implies (fn2-ops-wfp ops)
                      (and ,@(fn2-resident-column-length-claims
                              (fn2-columns-length-names 'fn2-ops columns))))
             :hints (("Goal" :in-theory (enable fn2-ops-wfp)))))
          (defthm fn2-core-resident-replace-ops
            (implies (and (fn2-ops-wfp ops) (fn2-ops-wfp (fn2-core-ops core))
                          (equal (fn2-ops-resident-shape ops)
                                 (fn2-ops-resident-shape (fn2-core-ops core))))
                     (equal (fn2-core-resident-measure (update-fn2-core-ops ops core))
                            (fn2-core-resident-measure core)))
            :hints (("Goal" :in-theory
                     (e/d (fn2-core-resident-measure ,@measures fn2-ops-resident-shape)
                          (fn2-ops-wfp fn2-ops-rows
                           ,@(fn2-columns-length-names 'fn2-ops columns))))))
          (defthm fn2-core-resident-after-adapter-entries
            (implies (and (fn2-corep core) (fn2-core-wfp core))
                     (and
                      (equal (fn2-core-resident-measure
                              (update-fn2-core-ops (mv-nth 1 (fn2-outbox-ack n (fn2-core-ops core))) core))
                             (fn2-core-resident-measure core))
                      (equal (fn2-core-resident-measure
                              (update-fn2-core-ops (fn2-post-result cell slot gen evkind outcome reason
                                                   count aux0 aux1 (fn2-core-ops core)) core))
                             (fn2-core-resident-measure core))
                      (equal (fn2-core-resident-measure
                              (update-fn2-core-ops (fn2-post-clock mono real flags (fn2-core-ops core)) core))
                             (fn2-core-resident-measure core))))
            :hints (("Goal" :in-theory
                     (disable fn2-core-resident-measure fn2-corep fn2-core-wfp fn2-ops-wfp
                              fn2-opsp fn2-ops-resident-shape update-fn2-core-ops)))))))))
