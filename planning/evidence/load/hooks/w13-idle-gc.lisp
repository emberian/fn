;;; Measurement hook for tools/load: no image change.  Loaded with --eval before
;;; acl2::sbcl-restart (images), or through XL_HOOK=FILE (fn-core, developer core).
;;; Environment, all optional:
;;;   FN_LOAD_GC_LOG=<path>     one line per GC: GC <epoch-us> <gc-run-time-us> <dynamic-usage>
;;;                             (the MEM-007 mem7hook pattern: *after-gc-hooks*)
;;;   FN_LOAD_IDLE_GC=off       the A arm of W13: no collection beyond SBCL's own triggers
;;;                             (the MEM-003 armA pattern): fnn-owner-maybe-collect-idle
;;;                             does nothing, and the collector policy (memory landing
;;;                             3+4a, host/native/heap.lisp fnn-heap-collector-policy-start)
;;;                             never starts (host/native/owner.lisp
;;;                             fnn-owner-release-recovery-garbage starts it whatever the
;;;                             idle encapsulation says), so its thread runs no full
;;;                             collection.  Measured (planning/evidence/load/
;;;                             2026-10-11-m18-w13, -w13b, -w13c): this moves the arm's anon by a few
;;;                             MB at most.  Arm A's HWM rise at 3119f7d32 (182,076 KiB
;;;                             against 138,796) was file-backed core pages, which vary
;;;                             from 65 to 108 MB between runs of one image (the drain's
;;;                             own two arms: 65,500 and 106,352 KiB file)
(in-package "ACL2")
(let ((path (sb-ext:posix-getenv "FN_LOAD_GC_LOG")))
  (when (and path (plusp (length path)))
    (let ((log (open path :direction :output :if-exists :supersede))
          (lock (sb-thread:make-mutex :name "fn-load-gc")))
      (push (lambda ()
              (sb-thread:with-mutex (lock)
                (multiple-value-bind (s us) (sb-ext:get-time-of-day)
                  (format log "GC ~d ~d ~d~%" (+ (* s 1000000) us)
                          (round (* 1000000 sb-ext:*gc-run-time*) internal-time-units-per-second)
                          (sb-kernel:dynamic-usage)))
                (finish-output log)))
            sb-ext:*after-gc-hooks*))))
(when (equal (sb-ext:posix-getenv "FN_LOAD_IDLE_GC") "off")
  (sb-int:encapsulate 'fnn-owner-maybe-collect-idle 'fn-load-idle-gc-off
                      (lambda (f service) (declare (ignore f service)) nil))
  (when (fboundp 'fnn-heap-collector-policy-start)
    (sb-int:encapsulate 'fnn-heap-collector-policy-start 'fn-load-idle-gc-off
                        (lambda (f) (declare (ignore f)) nil))))
