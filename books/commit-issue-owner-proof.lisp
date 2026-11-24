; Issuing a commit write or fence preserves ownership of every live descriptor,
; including the descriptor restored to the free list after a lease refusal.
(in-package "ACL2")
(include-book "arm-children")
(include-book "commit-replay-operation-owner-proof")
(fn2-book-layer :b)

(local (defthm fn2-issue-owner-mv-choice
  (equal (mv-nth n (if c x y)) (if c (mv-nth n x) (mv-nth n y)))))
(local (defthm fn2-issue-owner-mv-cons
  (equal (mv-nth n (cons x y)) (if (zp n) x (mv-nth (- n 1) y)))))
(defthm fn2-issue-children-keeps-active-owner-at
 (implies (fn2-op-owner-active-p i okind fn2-ops)
          (fn2-op-owner-active-p i okind
             (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len
                                may-release target-slot target-gen okind oslot ogen principal
                                fn2-pool fn2-ops fn2-control))))
 :hints (("Goal" :do-not-induct t
          :in-theory (union-theories
           '(fn2-issue-children (:t fn2-op-reserve) (:t fn2-op-unreserve) (:t fn2-core-lease)
             (:t fn2-op-set-range) (:t fn2-op-set-capability) (:t fn2-op-set-storage)
             (:t fn2-op-set-cancel-target) (:t fn2-op-enqueue)
             fn2-issue-owner-mv-choice fn2-issue-owner-mv-cons (:e mv-nth)
             (:e zp) (:e equal) (:e binary-+) (:e unary--) car-cons cdr-cons
             fn2-op-reserve-keeps-active-owner-at fn2-op-unreserve-keeps-active-owner-at
             fn2-op-set-range-keeps-active-owner-at fn2-op-set-capability-keeps-active-owner-at
             fn2-op-set-storage-keeps-active-owner-at fn2-op-set-cancel-target-keeps-active-owner-at
             fn2-op-enqueue-keeps-active-owner-at) (theory 'minimal-theory)))))

(defthm fn2-issue-children-keeps-active-owners
 (let ((after (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len
                          may-release target-slot target-gen okind oslot ogen principal
                          fn2-pool fn2-ops fn2-control))))
  (implies (fn2-op-active-owners-p okind fn2-ops) (fn2-op-active-owners-p okind after)))
 :hints (("Goal" :expand ((:free (x) (fn2-op-active-owners-p okind x)))
          :use ((:instance fn2-op-active-owners-p-necc (ops fn2-ops) (kind okind)
                 (slot (fn2-op-active-owners-p-witness okind
                        (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len
                                   may-release target-slot target-gen okind oslot ogen principal
                                   fn2-pool fn2-ops fn2-control))))))
          :in-theory '(fn2-issue-children-keeps-active-owner-at))))

(defthm fn2-issue-write-children-keeps-active-owners
 (implies (fn2-op-active-owners-p okind fn2-ops)
          (fn2-op-active-owners-p okind
           (mv-nth 4 (fn2-issue-write-children offset slot gen off len fua okind oslot ogen principal
                                              fn2-pool fn2-ops fn2-control))))
 :hints (("Goal" :in-theory '(fn2-issue-write-children fn2-issue-children-keeps-active-owners))))

(defthm fn2-issue-fence-children-keeps-active-owners
 (implies (fn2-op-active-owners-p okind fn2-ops)
          (fn2-op-active-owners-p okind
           (mv-nth 4 (fn2-issue-fence-children okind oslot ogen principal fn2-pool fn2-ops fn2-control))))
 :hints (("Goal" :in-theory '(fn2-issue-fence-children fn2-issue-children-keeps-active-owners))))
