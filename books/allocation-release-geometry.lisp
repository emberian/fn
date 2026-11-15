; One authoritative outgoing RELEASE workspace capacity and credit identity.
; The singleton release control owns at most one such workspace at a time.
(in-package "ACL2")
(include-book "commit-format")
(include-book "pool-credit-contracts")
(fn2-book-layer :b)
(defun fn2-allocation-release-member-capacity ()
 (declare (xargs :guard t))
 (+ 32 *fn2-format-txn-record-max-size* *fn2-format-release-allocation-max-size*))
(defun fn2-allocation-release-credit-group (commitrows)
 (declare (xargs :guard t))
 (+ 1 (nfix commitrows)))
(defun fn2-allocation-release-credit-vector (class fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (and (natp class) (fn2-pool-wfp fn2-pool))
                 :measure (nfix (- (nfix (fn2-pool-nclasses fn2-pool)) (nfix class)))))
 (if (not (and (natp class) (< class (nfix (fn2-pool-nclasses fn2-pool))))) nil
  (cons (if (equal class (fn2-pool-class-for (fn2-allocation-release-member-capacity) fn2-pool)) 1 0)
        (fn2-allocation-release-credit-vector (+ 1 class) fn2-pool))))
