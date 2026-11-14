; Issuance accounting for the actual common action pipeline.
(in-package "ACL2")
(include-book "ops-issued-count")

(defthm fn2-issue-children-issued-total
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
  (equal
   (fn2-ops-issued-count
    (fn2-ops-rows (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
    (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
   (+ (fn2-ops-issued-count (fn2-ops-rows fn2-ops) fn2-ops)
      (if (eq (car (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)) :ok) 1 0))))
 :hints (("Goal" :use (:instance fn2-env-op-reserve-ok-facts (o fn2-ops))
 :in-theory (e/d (fn2-issue-children)
  (fn2-ops-issued-count fn2-op-issued-weight fn2-op-enqueue fn2-opsp fn2-ops-wfp fn2-ops-rows)))))
