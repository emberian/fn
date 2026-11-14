; Whole reachable-invariant witnesses, connected to the actual initializer.
(in-package "ACL2")
(include-book "../books/commit-reachable")

(defun fn2-reach-test-profile ()
  (declare (xargs :guard t))
  (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (8 . 4096)) *fn2-profile-tiny*))
(defun fn2-reach-initial-witness ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (let ((fn2-core (fn2-init-executor (fn2-reach-test-profile) :echo nil fn2-core)))
        (mv (fn2-env-reach-initial-data-p (fn2-reach-test-profile) fn2-core) fn2-core))
      ok)))
(assert-event (and (fn2-core-profilep (fn2-reach-test-profile)) (fn2-reach-initial-witness)))
(defthm fn2-reach-initial-witness-unfolds
  (equal (fn2-reach-initial-witness)
         (fn2-env-reach-initial-data-p (fn2-reach-test-profile)
           (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core))))
  :hints (("Goal" :in-theory '(fn2-reach-initial-witness))))
(defthm fn2-reach-initial-witness-whole
  (and (fn2-env-reach-active-inv (fn2-reach-test-profile) nil nil
         (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core)))
       (not (fn2-core-stopped-p
         (fn2-init-executor (fn2-reach-test-profile) :echo nil (create-fn2-core)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-corep-of-fresh-core
                               (:e fn2-reach-initial-witness) (:e fn2-reach-test-profile)
                               (:e fn2-core-profilep))
           :use ((:instance fn2-env-reach-initial-data-covers-whole
                            (profile (fn2-reach-test-profile)) (c (create-fn2-core)))
                 fn2-reach-initial-witness-unfolds))))
