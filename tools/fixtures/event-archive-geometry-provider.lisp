(defun fn2-b-run-cursor-rows-from-counts (transactions reads)
 (declare (xargs :guard t))
 (+ (nfix transactions) (* (+ 1 *fn2-b-range-source-cursors*) (nfix reads))
    *fn2-b-seal-source-cursors* 2))
(defun fn2-b-checkpoint-source-cursor (profile)
 (declare (xargs :guard t))
 (+ (nfix (fn2-profile-t profile)) (* (+ 1 *fn2-b-range-source-cursors*) (fn2-b-read-rows profile))
    *fn2-b-seal-source-cursors*))
(defun fn2-b-event-archive-cursor (profile)
 (declare (xargs :guard t)) (+ 1 (fn2-b-checkpoint-source-cursor profile)))
(defun fn2-b-run-cursor-rows (profile)
 (declare (xargs :guard t)) (+ 1 (fn2-b-event-archive-cursor profile)))
(defun fn2-b-checkpoint-source-cursor-from-rows (rows)
 (declare (xargs :guard t)) (nfix (- (nfix rows) 2)))
(defun fn2-b-event-archive-cursor-from-rows (rows)
 (declare (xargs :guard t)) (nfix (- (nfix rows) 1)))
(defthm fn2-b-checkpoint-source-cursor-from-profile-rows
 (equal (fn2-b-checkpoint-source-cursor-from-rows (fn2-b-run-cursor-rows profile))
        (fn2-b-checkpoint-source-cursor profile))
 :hints (("Goal" :in-theory (enable fn2-b-checkpoint-source-cursor-from-rows fn2-b-run-cursor-rows
                                  fn2-b-event-archive-cursor fn2-b-checkpoint-source-cursor))))
(defthm fn2-b-event-archive-cursor-from-profile-rows
 (equal (fn2-b-event-archive-cursor-from-rows (fn2-b-run-cursor-rows profile))
        (fn2-b-event-archive-cursor profile))
 :hints (("Goal" :in-theory (enable fn2-b-event-archive-cursor-from-rows fn2-b-run-cursor-rows
                                  fn2-b-event-archive-cursor fn2-b-checkpoint-source-cursor))))
(defthm fn2-b-run-cursor-rows-counts-from-profile
 (equal (fn2-b-run-cursor-rows-from-counts (fn2-profile-t profile) (fn2-b-read-rows profile))
        (fn2-b-run-cursor-rows profile))
 :hints (("Goal" :in-theory (enable fn2-b-run-cursor-rows-from-counts fn2-b-run-cursor-rows
                                  fn2-b-event-archive-cursor fn2-b-checkpoint-source-cursor))))
