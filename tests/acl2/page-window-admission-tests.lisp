(in-package "ACL2")
(include-book "../../host/page-window-executor-host")

; Reachable startup/registration; the staged source demand is NOT runtime
; allocator adequacy. No externally supplied demand or ticket is accepted.
(defun pwat-example (descriptor)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-page-read-pool
    (mv-let (answer fn-page-read-pool)
      (mv-let (installed fn-page-read-pool)
        (fn-owner-page-read-install-baseline '(10000000 0 2 1 20)
          '(1000 0 0 0 0) 0 64 2 fn-page-read-pool)
        (declare (ignore installed))
        (mv-let (registered fn-page-read-pool)
          (fn-owner-page-read-register 11 fn-page-read-pool)
          (declare (ignore registered))
          (mv-let (word row token fn-page-read-pool)
            (fn-owner-page-window-executor-acquire-funded (fn-pxe-new 0) descriptor fn-page-read-pool)
            (mv (list word row token (fn-owner-page-read-ledger fn-page-read-pool))
                fn-page-read-pool))))
      answer)))

(assert-event
 (let ((r (pwat-example '(11 100 3 100 3 0 77))))
   (and (equal (nth 0 r) :assigned)
        (equal (nth 1 (nth 2 r)) 0)
        (equal (nth 2 r) '(:window 0 11 100 3 100 3 0 77))
        (fn-pwx-boundp (nth 3 r) (nth 1 r) (nth 2 r) :running)
        (equal (fn-prl-nth 2 (nth 3 r)) 1))))

; Selected signed native end is representational, not a stored-data ceiling.
; Refusal neither advances the core ticket nor assigns the idle worker.
(assert-event
 (let ((r (pwat-example (list 11 0 (expt 2 63) 0 3 0 77))))
   (and (not (equal (nth 0 r) :assigned)) (null (nth 2 r))
        (equal (nth 1 r) (fn-pxe-new 0))
        (equal (fn-prl-nth 2 (nth 3 r)) 0))))
