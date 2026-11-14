; Exact history frame through actual completion consumption.
(in-package "ACL2")
(include-book "ops-issued-observation")
(include-book "ops-harvest-phase")

(make-event
 (let* ((schema (cdr (assoc-eq 'fn2-ops (fn2-decl-rows :columns (w state)))))
        (writers (append (fn2-issued-payload-column-writers (fn2-decl-get :columns schema))
                         (fn2-issued-extra-writers (fn2-decl-get :extra-fields schema)))))
  (value `(defthm fn2-harvest-next-issued-count
 (equal (fn2-ops-issued-count n (mv-nth 4 (fn2-harvest-next fn2-ops)))
        (fn2-ops-issued-count n fn2-ops))
 :hints (("Goal" :in-theory (e/d
  (,@writers fn2-harvest-next fn2-ops-peek-posted fn2-op-slotp fn2-completion-phasep
   fn2-op-harvest-phase fn2-ops-latch-peer fn2-ops-phase)
  (fn2-ops-issued-count fn2-op-issued-weight fn2-ops-set-phase
   fn2-opsp fn2-ops-wfp fn2-ops-rows
   fn2-ops-post-head fn2-ops-post-count fn2-ops-posted-fifo-length fn2-ops-posted-fifoi
   fn2-ops-c0-posted fn2-ops-c0-harvested fn2-ops-c1-posted fn2-ops-c1-harvested
   fn2-ops-kind fn2-ops-c0-aux0 update-nth update-nth-array))))))))

(make-event
 (value `(defthm fn2-harvest-next-issued-total
  ,(fn2-run-issued-claim 0 'fn2-ops '(mv-nth 4 (fn2-harvest-next fn2-ops)))
  :hints (("Goal" :in-theory (disable fn2-harvest-next fn2-ops-issued-count fn2-ops-rows))))))
