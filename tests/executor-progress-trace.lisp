; H=1 with both clock and sticky signal pending: after consuming the clock,
; the calendar must run while the signal remains queued for another turn.
(in-package "ACL2")
(include-book "executor-progress-unit")
(include-book "../sim/check-trace")

(defun fn2-progress-trace-witness (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* ((profile (put-assoc-equal :h 1
                  (put-assoc-equal :trace t
                    (put-assoc-equal :pool-classes '((8 . 4096) (4 . 65536))
                                     *fn2-profile-tiny*))))
       (fn2-core (fn2-init-executor profile :echo nil fn2-core))
       (fn2-core (fn2-host-post-clock 1 1 1 fn2-core))
       (fn2-core (fn2-host-post-signal 1 fn2-core))
       (fn2-ref-core (fn2-ref-reset profile fn2-core fn2-ref-core))
       (fn2-ref-core (fn2-ref-import-boundary fn2-core fn2-ref-core))
       (lists (fn2-ref-lists-of-core (fn2-profile-weights profile) fn2-core))
       (before (fn2-ref-difference fn2-core fn2-ref-core lists))
       (h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core))
       (a (fn2-exec-aturn fn2-core))
       ((mv failure cases & obs visits & robs rvisits & lists fn2-core fn2-ref-core)
        (fn2-trace-lockstep (+ h k) h k a 0 0 0 h k a 0 0 0
                            lists nil nil fn2-core fn2-ref-core)))
    (mv (list (fn2-core-profilep profile) before failure
              (fn2-ref-difference fn2-core fn2-ref-core lists)
              obs visits robs rvisits (fn2-core-stopped-p fn2-core)
              (fn2-exec-observation-p fn2-core) cases)
        fn2-core fn2-ref-core)))
(defun fn2-progress-trace-test ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-ref-core
        (mv-let (result fn2-core fn2-ref-core)
          (fn2-progress-trace-witness fn2-core fn2-ref-core)
          (mv result fn2-core)))
      result)))
(assert-event
 (let ((result (fn2-progress-trace-test)))
   (and (equal (take 10 result) '(t nil nil nil 1 8 1 8 nil t))
        (equal (cdr (assoc-equal '(:executor :clock) (nth 10 result))) 1)
        (not (assoc-equal '(:executor :signal) (nth 10 result))))))
