;;; W7 measurement hook (extent-cache contention): no image change.  Loaded with --eval before acl2::sbcl-restart.
;;; W7_LOG=<path> receives a line every 100 ms:  <epoch-us> hits misses refusals acquires wait-us hold-us
;;;   hits/misses/refusals are *fnn-extent-stats* (hits count per byte served; misses are physical preads).
;;; W7_MODE=stats  (default) only that dump thread; nothing in the lock path changes.
;;; W7_MODE=full   also measures *fnn-extent-lock*: sb-thread::call-with-mutex is encapsulated to timestamp entry
;;;   when the mutex is the extent lock, and *fnn-native-observer* is set non-nil with fnn-native-observe /
;;;   -observation-reserve / -observation-complete replaced by counters.  Wait = :acquire event time - entry time
;;;   of the enclosing call-with-mutex (the physical grab); hold = release reservation time - acquire time.
;;;   The observer's own row log is bypassed (it is never read), so this adds two clock reads and three atomic
;;;   adds per extent-lock section, and sends every other observer-gated host path through its (now empty) events.
(in-package "ACL2")
(defvar *w7-log* nil)
(declaim (type (simple-array sb-ext:word (3)) *w7-counts*))
(sb-ext:defglobal *w7-counts* (make-array 3 :element-type (quote sb-ext:word) :initial-element 0))   ; acquires, wait-us, hold-us
(defvar *w7-entry* nil)
(defvar *w7-acq* nil)
(defun w7-now () (multiple-value-bind (s us) (sb-ext:get-time-of-day) (+ (* s 1000000) us)))
(let ((path (sb-ext:posix-getenv "W7_LOG"))
      (mode (or (sb-ext:posix-getenv "W7_MODE") "stats")))
  (when path
    (setq *w7-log* (open path :direction :output :if-exists :supersede))
    (when (string= mode "full")
      (sb-int:encapsulate 'sb-thread::call-with-mutex 'w7-entry
        (lambda (f thunk mutex &rest a)
          (if (eq mutex *fnn-extent-lock*)
              (let ((*w7-entry* (w7-now)) (*w7-acq* nil)) (apply f thunk mutex a))
              (apply f thunk mutex a))))
      (sb-int:encapsulate 'fnn-native-observe 'w7-acquire
        (lambda (f event)
          (declare (ignore f))
          (when (and (consp event) (eq (first event) :acquire) (eq (third event) :extent)
                     *w7-entry* (not *w7-acq*))
            (let ((now (w7-now)))
              (setq *w7-acq* now)
              (sb-ext:atomic-incf (aref *w7-counts* 0) 1)
              (sb-ext:atomic-incf (aref *w7-counts* 1) (max 0 (- now *w7-entry*)))))
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
           (format *w7-log* "~d ~d ~d ~d ~d ~d ~d~%" (w7-now) (first s) (second s) (third s)
                   (aref *w7-counts* 0) (aref *w7-counts* 1) (aref *w7-counts* 2))
           (finish-output *w7-log*))
         (sleep 0.1)))
     :name "w7-dump")))
