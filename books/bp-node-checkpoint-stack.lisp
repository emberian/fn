; Logical shape/cost boundary of the actual encoder task queue. These walkers
; are proof-only; a served tick carries the invariant instead of scanning it.
(in-package "ACL2")
(include-book "bp-node-checkpoint-job")
(set-verify-guards-eagerness 0)
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-bpcks-rank (task)
  (declare (xargs :guard t))
  (if (member-equal (fn-bpn-nth 0 task) '(:value :scan))
      (nfix (fn-bpn-nth 2 task)) 0))

; Nondecreasing ranks, at most two tasks at each rank. A pair expansion
; replaces rank D by two rank D-1 tasks before the remaining >=D tasks.
(defun fn-bpcks-orderedp (tasks low high already)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom tasks) (null tasks)
    (let ((rank (fn-bpcks-rank (car tasks))))
      (and (integerp low) (<= -1 low) (natp high) (<= low rank) (<= rank high)
           (not (and already (equal low rank)))
           (fn-bpcks-orderedp (cdr tasks) rank high (equal low rank))))))

(defun fn-bpcks-stackp (tasks depth)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp depth) (fn-bpcks-orderedp tasks -1 depth nil)))

(defthm fn-bpcks-begin-is-depth-bounded
  (implies (natp depth) (fn-bpcks-stackp (fn-bpnrc-begin x depth) depth))
  :hints (("Goal" :in-theory (enable fn-bpcks-stackp fn-bpcks-orderedp
                                     fn-bpcks-rank fn-bpnrc-begin fn-bpn-nth))))

; The selected concrete cons/cell envelope is a separate primitive assumption;
; this source theorem supplies the actual maximum queue length to that roster.
(defthm fn-bpcks-ordered-task-count
  (implies (and (integerp low) (<= -1 low) (natp high) (<= low high)
                (fn-bpcks-orderedp tasks low high already))
           (<= (len tasks)
               (+ (* 2 (+ 1 (- (nfix high) (ifix low))))
                  (if already -1 0))))
  :hints (("Goal" :induct (fn-bpcks-orderedp tasks low high already)
           :in-theory (e/d (fn-bpcks-orderedp) (fn-bpcks-rank)))))

(defthm fn-bpcks-stack-task-count
  (implies (fn-bpcks-stackp tasks depth)
           (<= (len tasks) (* 2 (+ 2 depth))))
  :hints (("Goal" :use ((:instance fn-bpcks-ordered-task-count
                                   (low -1) (high depth) (already nil)))
           :in-theory (enable fn-bpcks-stackp))))

(defthm fn-bpcks-ordered-lower-start
  (implies (and (fn-bpcks-orderedp tasks low high already)
                (integerp lesser) (<= -1 lesser) (integerp low) (<= lesser low))
           (fn-bpcks-orderedp tasks lesser high nil))
  :hints (("Goal" :induct (fn-bpcks-orderedp tasks low high already)
           :in-theory (e/d (fn-bpcks-orderedp) (fn-bpcks-rank))))
  :rule-classes nil)

(defthm fn-bpcks-ordered-lower-start-with-flag
  (implies (and (fn-bpcks-orderedp tasks low high already)
                (integerp lesser) (<= -1 lesser) (integerp low) (<= lesser low)
                (or (< lesser low) (not next-already) already))
           (fn-bpcks-orderedp tasks lesser high next-already))
  :hints (("Goal" :induct (fn-bpcks-orderedp tasks low high already)
           :in-theory (e/d (fn-bpcks-orderedp) (fn-bpcks-rank))))
  :rule-classes nil)

(defthm fn-bpcks-step-preserves-task-depth-envelope
  (implies (fn-bpcks-stackp tasks depth)
           (fn-bpcks-stackp (fn-bpn-nth 2 (fn-bpnrc-step tasks)) depth))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpcks-ordered-lower-start
                            (tasks (cdr tasks))
                            (low (fn-bpcks-rank (car tasks)))
                            (high depth) (already nil)
                            (lesser -1))
                 (:instance fn-bpcks-ordered-lower-start
                            (tasks (cdr tasks))
                            (low (fn-bpcks-rank (car tasks)))
                            (high depth) (already nil) (lesser 0))
                 (:instance fn-bpcks-ordered-lower-start-with-flag
                            (tasks (cdr tasks))
                            (low (fn-bpcks-rank (car tasks))) (high depth)
                            (already nil)
                            (lesser 0) (next-already t))
                 (:instance fn-bpcks-ordered-lower-start-with-flag
                            (tasks (cdr tasks))
                            (low (fn-bpcks-rank (car tasks))) (high depth)
                            (already nil)
                            (lesser (nfix (1- (fn-bpcks-rank (car tasks)))))
                            (next-already t)))
           :in-theory (enable fn-bpcks-stackp fn-bpcks-orderedp fn-bpcks-rank
                              fn-bpnrc-step fn-bpnrc-answer fn-bpnrc-counted-start
                              fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr)))
  :rule-classes nil)

(defthm fn-bpcks-next-task-count-is-depth-bounded
  (implies (fn-bpcks-stackp tasks depth)
           (<= (len (fn-bpn-nth 2 (fn-bpnrc-step tasks)))
               (* 2 (+ 2 depth))))
  :hints (("Goal" :use (fn-bpcks-step-preserves-task-depth-envelope
                        (:instance fn-bpcks-stack-task-count
                                   (tasks (fn-bpn-nth 2 (fn-bpnrc-step tasks)))))
           :in-theory (disable fn-bpcks-stackp)))
  :rule-classes nil)

; Subject of the private native writer's source turn, not a sibling encoder.
(defthm fn-bpck-emit-preserves-depth-bounded-stack
  (implies (fn-bpcks-stackp (fn-bpn-nth 7 job) (fn-bpn-nth 4 job))
           (fn-bpcks-stackp
            (fn-bpn-nth 7 (fn-bpn-nth 0 (fn-bpck-emit-step job)))
            (fn-bpn-nth 4 (fn-bpn-nth 0 (fn-bpck-emit-step job)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpcks-step-preserves-task-depth-envelope
                            (tasks (fn-bpn-nth 7 job)) (depth (fn-bpn-nth 4 job))))
           :in-theory (e/d (fn-bpck-emit-step fn-bpck-make fn-bpn-nth
                                           fn-cbor-ag-car fn-cbor-ag-cdr)
                           (fn-bpcks-stackp fn-bpnrc-step))))
  :rule-classes nil)

(defun fn-bpcks-small-tasks-p (tasks)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom tasks) (null tasks)
    (and (true-listp (car tasks)) (<= (len (car tasks)) 5)
         (fn-bpcks-small-tasks-p (cdr tasks)))))

(defthm fn-bpcks-begin-has-fixed-small-tasks
  (fn-bpcks-small-tasks-p (fn-bpnrc-begin x depth))
  :hints (("Goal" :in-theory (enable fn-bpcks-small-tasks-p fn-bpnrc-begin))))

(defthm fn-bpcks-step-preserves-fixed-small-tasks
  (implies (fn-bpcks-small-tasks-p tasks)
           (fn-bpcks-small-tasks-p (fn-bpn-nth 2 (fn-bpnrc-step tasks))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpcks-small-tasks-p fn-bpnrc-step
                              fn-bpnrc-answer fn-bpnrc-counted-start
                              fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr)))
  :rule-classes nil)

(in-theory (disable fn-bpcks-rank fn-bpcks-orderedp fn-bpcks-stackp))
