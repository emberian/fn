(in-package "CL-USER")
(let ((gate *fnn-runtime-participants*))
  (fnn-with-runtime-participants-parked
      (gate (fnn-runtime-participants-pool gate))
    (assert (fnn-runtime-participants-parked gate))
    (assert (zerop *participant-image-hook-runs*))
    ;; Collection while holding the same participant barrier must not deadlock.
    (sb-ext:gc :full t)
    (assert (zerop *participant-image-hook-runs*)))
  (fnn-runtime-participants-stop-and-join gate)
  (assert (null sb-impl::*finalizer-thread*))
  (format t "RESTORED-BORN-PARKED-HOOK-GC-JOIN-PASS~%"))
