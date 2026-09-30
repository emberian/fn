(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defstruct fnn-owner-service retire stopping (roster (sb-thread:make-mutex)))
(defvar *fnn-sigterm-requested* nil)
(defvar *semantic-lock* (sb-thread:make-mutex))
(defvar *clock* 0)
(defvar *hold-clock* nil)
(defvar *clock-observed* (sb-thread:make-semaphore))
(defvar *release-clock* (sb-thread:make-semaphore))
(defvar *semantic-calls* 0)
(defun snapshot (n) (list nil nil (list n)))
(defun fnn-owner-sched-snapshot (service)
 (declare (ignore service))
 (let ((s (snapshot *clock*)))
  (when *hold-clock*
   (sb-thread:signal-semaphore *clock-observed*)
   (assert (sb-thread:wait-on-semaphore *release-clock* :timeout 3)))
  s))
(defun fnn-owner-serialized (&rest args)
 (declare (ignore args)) (incf *semantic-calls*)
 (sb-thread:with-mutex (*semantic-lock*) (error "Unexpected semantic call")))
(defun fnn-fault (&rest args) (error "unexpected fault ~s" args))


(defun fn-otm-clock (s)
  
  (if (and (consp s) (consp (cdr s)) (consp (cddr s))) (caddr s) nil))

(defun fn-otm-c-now (c)
  
  (if (consp c) (nfix (car c)) 0))

(defun fn-otm-now (s)
  
  (fn-otm-c-now (fn-otm-clock s)))

(defun fn-osd-elapsed (s0 s)
  
  (nfix (- (fn-otm-now s) (fn-otm-now s0))))

(defun fn-ort-window-step (s0 s seconds)
  
  (if (<= (* 1000 (nfix seconds)) (fn-osd-elapsed s0 s)) :deadline :wait))

(defun fn-ort-retire-observer-action (record)
  
  (cond ((not (and (consp record) (consp (cdr record)))) :absent)
        ((and (consp (cddr record)) (caddr record)) :done)
        (t :observe)))

(defun fn-ort-retire-publish (record step)
  
  (case (fn-ort-retire-observer-action record)
    (:done (list record t))
    (:observe
     (if (or (equal step :drained) (equal step :deadline))
         (list (list (car record) (cadr record) step) t)
       (list record nil)))
    (otherwise (list record nil))))

(defun fnn-core (name &rest args)
 (assert (member name '(fn-ort-window-step fn-ort-retire-observer-action fn-ort-retire-publish)))
 (apply (symbol-function name) args))

(defmacro fnn-with-roster ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ,@body))

(defun fnn-owner-maybe-retire (service)
  "One drain decision of a retiring owner (row S9), at an accept-loop tick."
  (let ((retire (fnn-with-roster (service)
                  (fnn-owner-service-retire service))))
    (when (and (eq (fnn-core 'fn-ort-retire-observer-action retire) :observe)
               (not *fnn-sigterm-requested*)
               (not (fnn-owner-service-stopping service)))
      (let ((s0 (first retire)) (seconds (second retire)))
        ;; The drain-window observation needs only recorded time. Do not put
        ;; a filesystem free-space I/O observation ahead of that deadline.
        (let* ((s (fnn-owner-sched-snapshot service))
               ;; Producers-settled is not established yet. The named
               ;; equivalence makes this the exact unsettled counted step,
               ;; without waiting for a semantic mutex held across a barrier.
               ;; Early drained success awaits the complete producer fence.
               (step (fnn-core 'fn-ort-window-step s0 s seconds)))
          (unless (member step '(:wait :drained :deadline))
            (fnn-fault "owner returned a malformed retire step ~a" step))
          ;; Serialize only fixed lifecycle metadata, never the semantic
          ;; owner mutex. A concurrent stale wait preserves completed state.
          (fnn-with-roster (service)
            (let ((publication
                    (fnn-core 'fn-ort-retire-publish
                              (fnn-owner-service-retire service) step)))
              (setf (fnn-owner-service-retire service) (first publication))
              (when (second publication)
                (setf *fnn-sigterm-requested* t)))))))))


(defun join-checked (worker)
 (multiple-value-bind (value status) (sb-thread:join-thread worker :timeout 2 :default :timeout)
  (declare (ignore value)) (assert (null status))))
(defun fresh-service () (make-fnn-owner-service :retire (list (snapshot 0) 1)))
;; A semantic mutex held across both observations must not block the observer.
(let ((service (fresh-service)))
 (setq *fnn-sigterm-requested* nil)
 (sb-thread:with-mutex (*semantic-lock*)
  (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 0)) (fnn-owner-maybe-retire service)))))
  (assert (null *fnn-sigterm-requested*))
  (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 2000)) (fnn-owner-maybe-retire service)))))
  (assert (eq (third (fnn-owner-service-retire service)) :deadline))
  (assert *fnn-sigterm-requested*)
  (assert (zerop *semantic-calls*)))
 (format t "PASS held-semantic-mutex before-and-after-deadline~%"))
;; Force an old clock observation to resume only after deadline publication.
(dotimes (i 25)
 (let ((service (fresh-service)) (stale nil))
  (setq *fnn-sigterm-requested* nil)
  (sb-thread:with-mutex (*semantic-lock*)
   (setq stale (sb-thread:make-thread
    (lambda () (let ((*clock* 0) (*hold-clock* t)) (fnn-owner-maybe-retire service)))))
   (assert (sb-thread:wait-on-semaphore *clock-observed* :timeout 2))
   (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 2000)) (fnn-owner-maybe-retire service)))))
   (let ((completed (fnn-owner-service-retire service)))
    (assert (eq (third completed) :deadline))
    (assert *fnn-sigterm-requested*)
    (sb-thread:signal-semaphore *release-clock*)
    (join-checked stale)
    (assert (eq completed (fnn-owner-service-retire service)))
    (assert *fnn-sigterm-requested*)
    ;; Complete observations skip clock I/O altogether.
    (let ((*clock* 0) (*hold-clock* t)) (fnn-owner-maybe-retire service))
    (assert (eq completed (fnn-owner-service-retire service)))))))
(format t "PASS forced-stale-wait-after-deadline 25 iterations~%")
;; Both observers have captured pending metadata before either can publish.
(dotimes (i 25)
 (let ((service (fresh-service)) (workers nil))
  (setq *fnn-sigterm-requested* nil)
  (dotimes (j 2)
   (push (sb-thread:make-thread
    (lambda () (let ((*clock* 2000) (*hold-clock* t)) (fnn-owner-maybe-retire service)))) workers))
  (dotimes (j 2) (assert (sb-thread:wait-on-semaphore *clock-observed* :timeout 2)))
  (sb-thread:signal-semaphore *release-clock* 2)
  (mapc #'join-checked workers)
  (assert (equal (fnn-owner-service-retire service) (list (snapshot 0) 1 :deadline)))
  (assert *fnn-sigterm-requested*)))
(assert (zerop *semantic-calls*))
(format t "PASS two-concurrent-deadline-observers 25 iterations~%")

