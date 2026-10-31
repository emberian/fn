; B5-4a controls (b-durability.md §11 B5-4 M2, M3, M6): admission through the
; member table, the suffix abort of a refused leader and its follower, and
; settled outcomes taken by their owner.
(in-package "ACL2")
(include-book "../sim/commit-history")
(local (defthm fn2-cmu-countdown
 (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))) :rule-classes nil))
(local (defthm fn2-cmu-count-op (o-p (nfix left)) :rule-classes nil))
; Run both rows' arms, alternating, until neither is runnable work left.
(defun fn2-cmu-loop (left turn a b fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-cmu-countdown fn2-cmu-count-op) :in-theory nil))))
 (if (zp left) fn2-core
  (b* ((id (if (equal (mod (nfix turn) 2) 0) a b))
       ((mv & & & & fn2-core) (fn2-commit-run id 4 fn2-core)))
   (fn2-cmu-loop (- left 1) (+ 1 (nfix turn)) a b fn2-core))))
(defconst *fn2-cmu-owner* (list 7 3 5)) ; an owner triple no row has: no wake
(defun fn2-cmu-take (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (fn2-commit-take (nth 0 *fn2-cmu-owner*) (nth 1 *fn2-cmu-owner*) (nth 2 *fn2-cmu-owner*) fn2-core))
(defun fn2-cmu-root (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (p k a)
  (mv (fn2-commit-root-proposed 0 fn2-commit-root) (fn2-commit-root-first-key 0 fn2-commit-root)
      (fn2-commit-root-aborting 0 fn2-commit-root)) (list p k a)))
; FOLLOWER: also open the second batch before the leader seals. BREAK: the
; leader's first event is pushed past the record encoding's width, so its
; :records stage refuses before any journal write.
(defun fn2-cmu-abort-execute (follower breakp fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* 0))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv & fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      ((mv ca ia ba ea fn2-core) (fn2-commit-admit-keyed 2 0 7 3 5 fn2-core))
      ((mv pending & & & fn2-core) (fn2-cmu-take fn2-core))
      ((mv cb ib bb eb fn2-core) (if follower (fn2-commit-admit-keyed 1 0 7 3 5 fn2-core) (mv :none 0 0 0 fn2-core)))
      ((mv cx & & & fn2-core) (fn2-commit-admit-keyed 1 0 0 0 0 fn2-core))
      (fn2-core (if breakp (fn2-commit-put-core a (first-key (- (expt 2 60) 1))) fn2-core))
      (fn2-core (fn2-cmu-loop 400 0 a b fn2-core))
      ((mv t1 bt1 et1 o1 fn2-core) (fn2-cmu-take fn2-core))
      ((mv t2 bt2 et2 o2 fn2-core) (fn2-cmu-take fn2-core))
      ((mv t3 bt3 et3 o3 fn2-core) (fn2-cmu-take fn2-core))
      ((mv t4 & & & fn2-core) (fn2-cmu-take fn2-core))
      ((mv other & & & fn2-core) (fn2-commit-take 7 3 6 fn2-core))
      (root (fn2-cmu-root fn2-core)))
  (mv (list :admit ca ia ba ea cb ib bb eb cx :pending pending
            :takes (list t1 bt1 et1 o1) (list t2 bt2 et2 o2) (list t3 bt3 et3 o3) t4 other
            :phases (fn2-machine-phase a fn2-core) (fn2-machine-phase b fn2-core)
            :root root :stop (fn2-core-stop-reason fn2-core) :ids a b)
      fn2-core)))
(defun fn2-cmu-abort (follower breakp)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core) (fn2-cmu-abort-execute follower breakp fn2-core) result)))
; Attachments run in make-event, never in defconst's evaluation.
(make-event `(defconst *fn2-cmu-leader-refused* ',(fn2-cmu-abort nil t)))
(make-event `(defconst *fn2-cmu-pair-refused* ',(fn2-cmu-abort t t)))
; A refused leader drops with its follower; its owned members settle
; :refused (outcome code 3) in event order; nothing else is owed to the
; owner (another incarnation of it is owed nothing); both rows are free; the
; frontier is restored (proposed 0, next event 1, no abort); the core runs.
(assert-event (equal *fn2-cmu-leader-refused*
 '(:admit :ok 7 1 1 :none 0 0 0 :ok :pending :pending
   :takes (:ok 1 1 3) (:ok 1 2 3) (:none 0 0 0) :none :none
   :phases 0 0 :root (0 1 0) :stop 0 :ids 7 8)))
(assert-event (equal *fn2-cmu-pair-refused*
 '(:admit :ok 7 1 1 :ok 8 2 3 :exhausted :pending :pending
   :takes (:ok 1 1 3) (:ok 1 2 3) (:ok 2 3 3) :none :none
   :phases 0 0 :root (0 1 0) :stop 0 :ids 7 8)))
; Teeth: without the injected failure the same admissions are not refused.
(make-event `(defconst *fn2-cmu-unbroken* ',(fn2-cmu-abort t nil)))
(assert-event (not (equal (nth 13 *fn2-cmu-unbroken*) '(:ok 1 1 3))))
(value-triple (cw "B5-4a MEMBERS: refused leader and pair abort in order, outcomes taken, frontier restored PASS~%"))
