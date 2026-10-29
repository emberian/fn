; M5: coherent FIFO head insertion instead of tail insertion.
; Original: fn2/books/sched.lisp:127-153 at 137695dfc.
; One algorithm change: dualize head/tail and prev/next in enqueue only.
; Links/counts remain coherent; reference FN2-REF-ENQUEUE remains FIFO.
(in-package "ACL2")
; Test-only redefinition in a fresh process. Never include/certify this file.
; REDEF! updates both ACL2 executable counterpart and raw function.
(redef!)
(defun fn2-sched-make-runnable (machine principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :guard (fn2-sched-wfp fn2-sched)))
  (cond
   ((not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
              (fn2-sched-principalp principal fn2-sched))) (mv :bounds fn2-sched))
   ((= (fn2-sched-in-queue machine fn2-sched) 1) (mv :already fn2-sched))
   (t
    (let ((head (fn2-sched-headsi principal fn2-sched))
          (count (fn2-sched-countsi principal fn2-sched)))
      (if (or (>= count *fn2-sched-none*)
              (>= (fn2-sched-queued fn2-sched) *fn2-sched-none*)
              (and (< 0 count) (>= head (fn2-sched-rows fn2-sched))))
          (mv :state fn2-sched)
        (let* ((fn2-sched (fn2-sched-set-principal machine principal fn2-sched))
               (fn2-sched (fn2-sched-set-in-queue machine 1 fn2-sched))
               (fn2-sched (fn2-sched-set-next machine
                           (if (= count 0) *fn2-sched-none* head) fn2-sched))
               (fn2-sched (fn2-sched-set-prev machine *fn2-sched-none* fn2-sched))
               (fn2-sched (if (= count 0)
                              (update-fn2-sched-tailsi principal machine fn2-sched)
                            (fn2-sched-set-prev head machine fn2-sched)))
               (fn2-sched (update-fn2-sched-headsi principal machine fn2-sched))
               (fn2-sched (update-fn2-sched-countsi principal (+ count 1) fn2-sched))
               (fn2-sched (update-fn2-sched-queued
                           (+ 1 (fn2-sched-queued fn2-sched)) fn2-sched)))
          (mv :ok fn2-sched)))))))
