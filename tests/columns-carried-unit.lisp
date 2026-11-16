; Real production predicates over their actual generated tables. This fixture
; requires the coherent provider closure; isolated old-world guard/equality
; pilots do not qualify this whole current book.
(in-package "ACL2")
(include-book "../books/runs")
(include-book "../books/checkpoint")
(defun fn2-columns-carried-run-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-run-builds
  (mv-let (yes fn2-run-builds)
   (with-local-stobj fn2-run-writers
   (mv-let (yes fn2-run-builds fn2-run-writers)
    (let* ((fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
           (fn2-run-writers (fn2-run-writers-init *fn2-run-max-levels* fn2-run-writers)))
     (mv (and (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-run-buildp 0 fn2-run-builds fn2-run-writers)
              (fn2-run-buildp-carried 0 fn2-run-builds fn2-run-writers)
              (not (fn2-run-buildp 1 fn2-run-builds fn2-run-writers))
              (not (fn2-run-buildp-carried 1 fn2-run-builds fn2-run-writers)))
         fn2-run-builds fn2-run-writers)) (mv yes fn2-run-builds))) yes)))
(defun fn2-columns-carried-checkpoint-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoints
  (mv-let (yes fn2-checkpoints)
   (with-local-stobj fn2-checkpoint-refs
    (mv-let (yes fn2-checkpoints fn2-checkpoint-refs)
     (with-local-stobj fn2-checkpoint-bytes
    (mv-let (yes fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
     (let* ((fn2-checkpoints (fn2-checkpoints-init 1 fn2-checkpoints))
            (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 fn2-checkpoint-refs))
            (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 fn2-checkpoint-bytes)))
      (mv (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
               (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes)
               (fn2-checkpoint-slotp 0 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
               (fn2-checkpoint-slotp-carried 0 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
               (not (fn2-checkpoint-slotp 1 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes))
               (not (fn2-checkpoint-slotp-carried 1 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)))
          fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes))
      (mv yes fn2-checkpoints fn2-checkpoint-refs)))
     (mv yes fn2-checkpoints))) yes)))
(assert-event (fn2-columns-carried-run-control))
(assert-event (fn2-columns-carried-checkpoint-control))
