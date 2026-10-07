;;; MEM-007 measurement hook: no image change.  Loaded with --eval before acl2::sbcl-restart.
;;; MEM7_PUBNURSERY=<octets> pins fnn-gc-nursery-octets (the publication trigger, owner.lisp:7218) to that value;
;;; unset leaves the image's own 64 MiB.  MEM7_LOG=<path> receives one line per event:
;;;   PUB-START/PUB-END <epoch-us>   (fnn-owner-publish-captured)   GC <epoch-us> <gc-run-time-us> <dynamic-usage>
(in-package "ACL2")
(defvar *m7-log* nil)
(defvar *m7-lock* (sb-thread:make-mutex :name "m7"))
(defun m7-now () (multiple-value-bind (s us) (sb-ext:get-time-of-day) (+ (* s 1000000) us)))
(defun m7-emit (&rest parts)
  (when *m7-log*
    (sb-thread:with-mutex (*m7-lock*)
      (format *m7-log* "~{~a~^ ~}~%" parts) (finish-output *m7-log*))))
(let ((path (sb-ext:posix-getenv "MEM7_LOG")))
  (when path
    (setq *m7-log* (open path :direction :output :if-exists :supersede))
    (push (lambda () (m7-emit "GC" (m7-now) (round (* 1000000 sb-ext:*gc-run-time*) internal-time-units-per-second)
                              (sb-kernel:dynamic-usage)))
          sb-ext:*after-gc-hooks*)
    (sb-int:encapsulate 'fnn-owner-publish-captured 'm7-pub
      (lambda (f &rest a)
        (m7-emit "PUB-START" (m7-now))
        (unwind-protect (apply f a) (m7-emit "PUB-END" (m7-now)))))))
(let ((v (sb-ext:posix-getenv "MEM7_PUBNURSERY")))
  (when (and v (plusp (length v)))
    (let ((n (parse-integer v)))
      (sb-int:encapsulate 'fnn-gc-nursery-octets 'm7-nursery (lambda (f &rest a) (declare (ignore f a)) n)))))
