; What a successful traversal guarantees about a nonempty FIFO's head.
(in-package "ACL2")
(include-book "account-fifo")

(defthm fn2-account-visit-never-ends-at-seen-tail
  (implies (and (member-equal tail seen) (not (equal prev tail)))
           (equal (fn2-account-fifo-visit fuel id prev tail seen machines) :invalid))
  :hints (("Goal" :induct (fn2-account-fifo-visit fuel id prev tail seen machines)
           :in-theory (e/d (fn2-account-fifo-visit) (fn2-machines-rows fn2-machines-wait-reason
                          fn2-machines-ready-next fn2-machines-ready-prev)))))

(defthm fn2-account-valid-fifo-head
  (implies (and (not (equal id *fn2-none*))
                (not (equal (fn2-account-fifo-visit fuel id prev tail seen machines) :invalid)))
           (let ((next (fn2-machines-ready-next id machines)))
             (and (natp id) (< id (fn2-machines-rows machines))
                  (equal (fn2-machines-wait-reason id machines) *fn2-wait-principal-reservation*)
                  (equal (fn2-machines-ready-prev id machines) prev)
                  (not (equal next id))
                  (iff (equal next *fn2-none*) (equal id tail))
                  (or (equal next *fn2-none*)
                      (and (natp next) (< next (fn2-machines-rows machines))
                           (equal (fn2-machines-ready-prev next machines) id)
                           (equal (fn2-machines-wait-reason next machines) *fn2-wait-principal-reservation*))))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-account-fifo-visit fuel id prev tail seen machines)
                            (fn2-account-fifo-visit (+ -1 fuel) (fn2-machines-ready-next id machines)
                                                    id tail (cons id seen) machines))
           :in-theory (disable fn2-account-fifo-visit fn2-machines-rows fn2-machines-ready-next
                               fn2-machines-ready-prev fn2-machines-wait-reason))))

(defthm fn2-account-visit-tail-in-range
  (implies (and (not (equal id *fn2-none*))
                (not (equal (fn2-account-fifo-visit fuel id prev tail seen machines) :invalid)))
           (and (natp tail) (< tail (fn2-machines-rows machines)) (not (equal tail *fn2-none*))))
  :hints (("Goal" :induct (fn2-account-fifo-visit fuel id prev tail seen machines)
           :in-theory (e/d (fn2-account-fifo-visit) (fn2-machines-rows fn2-machines-wait-reason
                                      fn2-machines-ready-next fn2-machines-ready-prev)))))
(defun-nx fn2-account-fifo-head-linksp (id tail machines)
  (let ((next (fn2-machines-ready-next id machines)))
    (or (equal id *fn2-none*)
        (and (natp id) (< id (fn2-machines-rows machines))
             (natp tail) (< tail (fn2-machines-rows machines)) (not (equal tail *fn2-none*))
             (equal (fn2-machines-ready-prev id machines) *fn2-none*)
             (equal (fn2-machines-wait-reason id machines) *fn2-wait-principal-reservation*)
             (not (equal next id)) (iff (equal next *fn2-none*) (equal id tail))
             (or (equal next *fn2-none*)
                 (and (natp next) (< next (fn2-machines-rows machines))
                      (equal (fn2-machines-ready-prev next machines) id)
                      (equal (fn2-machines-wait-reason next machines) *fn2-wait-principal-reservation*)))))))
(defthm fn2-account-visit-head-links
  (implies (not (equal (fn2-account-fifo-visit fuel id *fn2-none* tail seen machines) :invalid))
           (fn2-account-fifo-head-linksp id tail machines))
  :hints (("Goal" :use ((:instance fn2-account-valid-fifo-head (prev *fn2-none*))
                        (:instance fn2-account-visit-tail-in-range (prev *fn2-none*)))
           :in-theory '(fn2-account-fifo-head-linksp))))
(defthm fn2-account-all-fifos-head-links
  (implies (and (natp p) (< p (nfix rows))
                (not (equal (fn2-account-fifos-visit rows seen acts machines) :invalid)))
           (fn2-account-fifo-head-linksp (fn2-accounts-wait-head p acts) (fn2-accounts-wait-tail p acts) machines))
  :hints (("Goal" :induct (fn2-account-fifos-visit rows seen acts machines)
           :in-theory (e/d (fn2-account-fifos-visit) (fn2-account-fifo-head-linksp
                            fn2-accounts-wait-head fn2-accounts-wait-tail fn2-machines-rows
                            fn2-account-fifo-visit)))))
