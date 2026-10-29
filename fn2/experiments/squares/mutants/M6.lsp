; M6: delay/fail-slow class latencies exchanged (R5d regression).
; Original: fn2/sim/sim.lisp:386 at 137695dfc.
; Sole semantic edit: latency selector (equal fault 14) -> (equal fault 2).
(in-package "ACL2")
; Test-only redefinition in a fresh process. Never include/certify this file.
; REDEF! updates both ACL2 executable counterpart and raw function.
(redef!)
(defun fn2-sim-delay-flight (slot fault word fn2-sim)
 (declare (xargs :stobjs fn2-sim :verify-guards nil :guard (fn2-sim-ready fn2-sim)))
 (if (not (and (natp slot) (< slot (fn2-sim-rows fn2-sim))
                (unsigned-byte-p 32 word)))
     fn2-sim
   (let ((latency (if (equal fault 2)
                   (case (mod word 3) (0 1000) (1 10000) (otherwise 100000)) 100)))
    (let* ((due (min #xfffffffffffffff (+ latency (fn2-sim-now fn2-sim))))
           (fn2-sim (if (and (member-equal fault '(2 14)) (< (fn2-sim-due slot fn2-sim) due))
                        (fn2-sim-land fault fn2-sim) fn2-sim)))
      (fn2-sim-set-due slot due fn2-sim)))))
