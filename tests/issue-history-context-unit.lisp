; An operation-table frame may simplify the history index before a nested
; issue call. Keep the actual input correlation as an equality hypothesis.
(in-package "ACL2")
(include-book "machine-budget-core-fixture")
(include-book "std/testing/must-fail" :dir :system)

(defthm fn2-context-account-book-ops-frame
 (equal (fn2-core-ops (mv-nth 1 (fn2-account-book p fn2-core)))
        (fn2-core-ops fn2-core))
 :hints (("Goal" :in-theory (enable fn2-account-book fn2-core-stop))))

(local (in-theory (disable fn2-issue-accept-issued-count-at-rows)))
; Strategy-removal control, not a counterexample to the unchanged effect law.
(must-fail
(defthm fn2-context-booked-issue-old
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (equal
   (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core))
    (fn2-core-ops (mv-nth 3 (fn2-issue-accept 0 0 0 id gen 0
                            (mv-nth 1 (fn2-account-book p fn2-core))))))
   (+ (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core)) (fn2-core-ops fn2-core))
      (if (eq (car (fn2-issue-accept 0 0 0 id gen 0
                    (mv-nth 1 (fn2-account-book p fn2-core)))) :ok) 1 0))))
 :hints (("Goal" :in-theory
  (disable fn2-issue-accept fn2-account-book fn2-core-ops fn2-corep fn2-core-wfp
           fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows nfix nth)))))
(defthm fn2-context-booked-issue-fixed
 (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
  (equal
   (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core))
    (fn2-core-ops (mv-nth 3 (fn2-issue-accept 0 0 0 id gen 0
                            (mv-nth 1 (fn2-account-book p fn2-core))))))
   (+ (fn2-ops-issued-count (fn2-ops-rows (fn2-core-ops fn2-core)) (fn2-core-ops fn2-core))
      (if (eq (car (fn2-issue-accept 0 0 0 id gen 0
                    (mv-nth 1 (fn2-account-book p fn2-core)))) :ok) 1 0))))
 :hints (("Goal" :in-theory
  (e/d (fn2-issue-accept-issued-count-at-rows)
       (fn2-issue-accept fn2-account-book fn2-core-ops fn2-corep fn2-core-wfp
           fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows nfix nth)))))
