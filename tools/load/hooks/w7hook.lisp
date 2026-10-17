;;; W7 measurement hook (extent-cache contention): no image change.  Loaded with --eval before acl2::sbcl-restart.
;;; W7_LOG=<path> receives a line every 100 ms (columns below).
;;;   hits/misses/refusals are *fnn-extent-stats* (hits count per byte served; misses are physical preads).
;;; W7_MODE=stats  (default) only that dump thread; nothing in the lock path changes.
;;; W7_MODE=full   also measures *fnn-extent-lock*.  with-mutex is inlined into the host, so a grab cannot be
;;;   wrapped at entry; an uncontended grab is a CAS that waits for nothing, and a contended grab calls
;;;   sb-thread::mutex-wait, which is encapsulated: its duration on the extent lock is the WAIT (and the call
;;;   count is the contended grabs).  Hold = :release reservation time - :acquire time: *fnn-native-observer* is set
;;;   non-nil and fnn-native-observe / -observation-reserve / -observation-complete are replaced by counters
;;;   (the observer's row log is bypassed; it is never read).  Cost: two clock reads and two atomic adds per
;;;   extent-lock section, plus the observer-gated host paths now run with a non-nil observer.
;;; Log columns: epoch-us hits misses refusals acquires wait-us hold-us contended-waits mutex-wait-calls-all observer-set
(in-package "ACL2")
(defvar *w7-log* nil)
(declaim (type (simple-array sb-ext:word (6)) *w7-counts*))
(sb-ext:defglobal *w7-counts* (make-array 6 :element-type (quote sb-ext:word) :initial-element 0))   ; acquires, wait-us, hold-us
(defvar *w7-entry* nil)
(defvar *w7-acq* nil)
(defun w7-now () (multiple-value-bind (s us) (sb-ext:get-time-of-day) (+ (* s 1000000) us)))
(let ((path (sb-ext:posix-getenv "W7_LOG"))
      (mode (or (sb-ext:posix-getenv "W7_MODE") "stats")))
  (when path
    (setq *w7-log* (open path :direction :output :if-exists :supersede))
    (when (string= mode "full")
      ;; with-mutex is inlined into the host (call-with-mutex is never reached), so the grab cannot be
      ;; wrapped at its entry.  An uncontended grab is a CAS and waits for nothing; a contended grab calls
      ;; sb-thread::mutex-wait, a real function: its duration on the extent lock IS the lock wait.
      (sb-int:encapsulate 'sb-thread::mutex-wait 'w7-wait
        (lambda (f &rest a)
          (sb-ext:atomic-incf (aref *w7-counts* 5) 1)
          (if (member *fnn-extent-lock* a :test #'eq)
              (let ((t0 (w7-now)))
                (sb-ext:atomic-incf (aref *w7-counts* 3) 1)
                (unwind-protect (apply f a)
                  (sb-ext:atomic-incf (aref *w7-counts* 1) (max 0 (- (w7-now) t0)))))
              (apply f a))))
      (sb-int:encapsulate 'fnn-native-observe 'w7-acquire
        (lambda (f event)
          (declare (ignore f))
          (sb-ext:atomic-incf (aref *w7-counts* 4) 1)
          (when (and (consp event) (eq (first event) :acquire) (eq (third event) :extent)
                     (not *w7-acq*))
            (let ((now (w7-now)))
              (setq *w7-acq* now)
              (sb-ext:atomic-incf (aref *w7-counts* 0) 1)))
          nil))
      (sb-int:encapsulate 'fnn-native-observation-reserve 'w7-release
        (lambda (f event complete)
          (declare (ignore f complete))
          (when (and (consp event) (eq (first event) :release) (eq (third event) :extent) *w7-acq*)
            (sb-ext:atomic-incf (aref *w7-counts* 2) (max 0 (- (w7-now) *w7-acq*)))
            (setq *w7-acq* nil))
          nil))
      (sb-int:encapsulate 'fnn-native-observation-complete 'w7-complete
        (lambda (f row) (declare (ignore f row)) nil))
      (setq *fnn-native-observer* t))
    (sb-thread:make-thread
     (lambda ()
       (loop
         (let ((s *fnn-extent-stats*))
           (format *w7-log* "~d ~d ~d ~d ~d ~d ~d ~d ~d ~d~%" (w7-now) (first s) (second s) (third s)
                   (aref *w7-counts* 0) (aref *w7-counts* 1) (aref *w7-counts* 2)
                   (aref *w7-counts* 3) (aref *w7-counts* 5) (if *fnn-native-observer* 1 0))
           (finish-output *w7-log*))
         (sleep 0.1)))
     :name "w7-dump")))
