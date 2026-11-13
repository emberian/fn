; Machine wait durations use the monotonic clock mailbox's microsecond unit.
(in-package "ACL2")
(include-book "sched")

(defun fn2-sched-arm-delay-ms (machine milliseconds fn2-sched fn2-control)
  (declare (xargs :stobjs (fn2-sched fn2-control)
                  :guard (and (fn2-sched-wfp fn2-sched) (fn2-control-wfp fn2-control))))
  (let ((deadline (+ (fn2-control-now fn2-control) (* 1000 (nfix milliseconds)))))
    (if (not (and (unsigned-byte-p 32 milliseconds) (< 0 milliseconds)
                  (unsigned-byte-p 60 deadline) (< deadline *fn2-no-deadline*)))
        (mv :bounds 0 fn2-sched fn2-control)
      (mv-let (code fn2-sched fn2-control)
        (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)
        (mv code deadline fn2-sched fn2-control)))))
(defthm fn2-sched-arm-delay-ms-deadline-width
  (implies (fn2-controlp fn2-control)
           (unsigned-byte-p 60 (mv-nth 1 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))))
(defthm fn2-sched-arm-delay-ms-sched-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 2 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))))
(defthm fn2-sched-arm-delay-ms-sched-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 2 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))))
(defthm fn2-sched-arm-delay-ms-sched-rows
  (equal (fn2-sched-rows (mv-nth 2 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-arm-delay-ms-control-wfp
  (implies (fn2-control-wfp fn2-control)
           (fn2-control-wfp (mv-nth 3 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))))
(defthm fn2-sched-arm-delay-ms-control-type
  (implies (fn2-controlp fn2-control)
           (fn2-controlp (mv-nth 3 (fn2-sched-arm-delay-ms machine milliseconds fn2-sched fn2-control)))))
(in-theory (disable fn2-sched-arm-delay-ms))

(defun fn2-sched-timer-expired-p (machine fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
       (= 1 (fn2-sched-expired machine fn2-sched))))
(in-theory (disable fn2-sched-timer-expired-p))
