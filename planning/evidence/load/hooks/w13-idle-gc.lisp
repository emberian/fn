;;; Measurement hook for tools/load: no image change.  Loaded with --eval before
;;; acl2::sbcl-restart (images), or through XL_HOOK=FILE (fn-core, developer core).
;;; Environment, all optional:
;;;   FN_LOAD_GC_LOG=<path>     one line per GC: GC <epoch-us> <gc-run-time-us> <dynamic-usage>
;;;                             (the MEM-007 mem7hook pattern: *after-gc-hooks*)
;;;   FN_LOAD_IDLE_GC=off       the A arm of W13: fnn-owner-maybe-collect-idle does nothing
;;;                             (the MEM-003 armA pattern)
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
                      (lambda (f service) (declare (ignore f service)) nil)))
