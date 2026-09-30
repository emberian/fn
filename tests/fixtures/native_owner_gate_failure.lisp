;; The source loaded by the shared prelude includes actual gate functions.
;; These functions record the ACL2 interface, not its scheduling semantics.
(defvar *scheduler-calls* 0)
(defvar *calls-after-abort* 0)
(defvar *next-count* 0)
(defvar *fail-next-number* nil)
(defvar *fail-observe* nil)
(defvar *observed-owner-held* nil)
(defvar *failed-condition* nil)
(defparameter *classes* '(:reader :poster :transit :control :commit :sync))
(defun scheduler-observation ()
  (incf *scheduler-calls*)
  (when (fnn-owner-gate-aborted (fnn-owner-service-gate *service*))
    (incf *calls-after-abort*)))
(defun scheduler-failure (name)
  (setf *failed-condition*
        (make-condition 'fnn-fixed-callback-fault :message "core-callback-fault"
                        :subject name :tag :raw-callback-failed :cause *cause*))
  (error *failed-condition*))
(defun fnn-core (name &rest args)
  (scheduler-observation)
  (case name
    (fn-ocs-classp (member (first args) *classes*))
    (fn-ocs-class-index (position (first args) *classes*))
    (fn-otm-observe
     (push (sb-thread:holding-mutex-p (fnn-owner-service-lock *service*))
           *observed-owner-held*)
     (when *fail-observe* (scheduler-failure name))
     (first args))
    (otherwise (error "unexpected core subject"))))
(defun fnn-call (name &rest args)
  (scheduler-observation)
  (assert (eq name 'fn-otm-next))
  (incf *next-count*)
  (when (eql *next-count* *fail-next-number*) (scheduler-failure name))
  (let ((index (position-if #'plusp (second args))))
    (list (and index (nth index *classes*)) (first args))))
(defun gate-fresh ()
  (fresh)
  (setf (fnn-owner-service-gate *service*) (%make-fnn-owner-gate :sched :fixture)
        *scheduler-calls* 0 *calls-after-abort* 0 *next-count* 0
        *fail-next-number* nil *fail-observe* nil
        *observed-owner-held* nil *failed-condition* nil))
(defun gate-stopped (exit)
  (assert (fnn-owner-service-stopping *service*))
  (assert (= (fnn-owner-service-exit-code *service*) exit))
  (assert (eq (fnn-owner-gate-aborted (fnn-owner-service-gate *service*))
              *failed-condition*))
  (assert (every #'identity *observed-owner-held*))
  (let ((before *scheduler-calls*))
    (dolist (class '(:reader :poster :transit :control))
      (let ((ran nil))
        (assert (typep (caught (lambda ()
                               (fnn-owner-serialized *service* nil
                                 (lambda () (setf ran t)) class)))
                       'serious-condition))
        (assert (not ran))))
    (assert (= before *scheduler-calls*))
    ;; The actual run cleanup invokes this wrapper before joining workers.
    ;; It must complete even when scheduler admission can no longer run.
    (fnn-owner-stop-service *service* +fnn-exit-ok+)
    (assert (= (fnn-owner-service-exit-code *service*) exit))
    (assert (= before *scheduler-calls*)))
  (assert (zerop *calls-after-abort*))
  (assert (zerop *reports*)))

;; Entry pick, cleanup observation, and cleanup pick are each fallible core
;; calls. All must fence, wake the gate, and preserve the original condition.
(dolist (phase '(:entry :observe :leave-pick))
  (gate-fresh)
  (case phase
    (:entry (setf *fail-next-number* 1))
    (:observe (setf *fail-observe* t))
    (:leave-pick (setf *fail-next-number* 2)))
  (let ((ran nil))
    (assert (eq (caught (lambda ()
                         (fnn-owner-serialized *service* nil
                           (lambda () (setf ran t)) :reader))) *failed-condition*))
    (assert (eq (not (null ran)) (not (eq phase :entry)))))
  (gate-stopped +fnn-exit-fault+)
  (assert (eq (fnn-fixed-fault-cause *failed-condition*) *cause*))
  (incf *cases*))

;; Healthy scheduling preserves all return values and does not introduce a
;; stop for an explicit semantic refusal.
(gate-fresh)
(let ((identity (vector :identity)))
  (multiple-value-bind (word number object)
      (fnn-owner-serialized *service* nil (lambda () (values :ok 17 identity)) :reader)
    (assert (and (eq word :ok) (= number 17) (eq object identity)))))
(assert (not (fnn-owner-service-stopping *service*)))
(assert (every #'identity *observed-owner-held*))
(assert (typep (caught (lambda ()
                         (fnn-owner-serialized *service* nil
                           (lambda () (fnn-refuse "known refusal")) :reader)))
               'fnn-store-error))
(assert (not (fnn-owner-service-stopping *service*)))
(incf *cases*)

;; A later scheduler failure does not overwrite an already-fenced uncertain
;; observation. The same applies if the lifecycle drain itself then fails.
(dolist (drain-fails '(nil t))
  (gate-fresh)
  (setf *fail-observe* t
        *drain-cause* (and drain-fails (make-condition 'print-trap)))
  (caught (lambda ()
            (fnn-owner-serialized *service* nil
              (lambda () (error 'fnn-store-indeterminate :message "uncertain")) :reader)))
  (gate-stopped +fnn-exit-uncertain+)
  (assert (> *stop-hooks* 0))
  (incf *cases*))

;; This is an actual queued gate waiter, not merely a call after the fault.
;; The first thread holds the owner while waiting for the second's ticket.
;; Failure must broadcast and let that waiter exit without a scheduler retry.
(dolist (failure '(:observe :leave-pick))
  (gate-fresh)
  (if (eq failure :observe) (setf *fail-observe* t) (setf *fail-next-number* 2))
  (let ((thread nil) (later-ran nil) (later-fault nil))
    (caught (lambda ()
              (fnn-owner-serialized *service* nil
                (lambda ()
                  (setf thread
                        (sb-thread:make-thread
                         (lambda ()
                           (setf later-fault
                                 (caught (lambda ()
                                           (fnn-owner-serialized *service* nil
                                             (lambda () (setf later-ran t)) :poster)))))))
                  (assert
                   (loop repeat 1000
                         when (let ((gate (fnn-owner-service-gate *service*)))
                                (sb-thread:with-mutex ((fnn-owner-gate-mutex gate))
                                  (plusp (svref (fnn-owner-gate-waiting gate) 1))))
                           return t
                         do (sleep 0.001)))) :reader)))
    (sb-thread:join-thread thread :timeout 5 :default :still-running)
    (assert (not (sb-thread:thread-alive-p thread)))
    (assert (not later-ran))
    (assert (eq later-fault *failed-condition*))
    (gate-stopped +fnn-exit-fault+)
    (incf *cases*)))
(format t "PASS owner gate failure boundary: ~d cases; actual queued waiters wake; no scheduler retry after abort~%"
        *cases*)
