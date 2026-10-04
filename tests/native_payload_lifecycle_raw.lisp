;;; Actual native lifecycle wrappers, deterministic two-thread barriers.
;;; The tiny STATE adapter records effects; ACL2 tests exercise the actual
;;; guarded arena reset. The lifecycle decision below is read from its source
;;; definition unchanged except for the ACL2 declaration (not a host policy).
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-arena-return-observation (log)
  (declare (ignorable log))
  (harness-stub-reached 'fnn-arena-return-observation "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(defun member-equal (x xs) (member x xs :test #'equal))
(defun fixture-load-definitions (file names &optional core)
  (with-open-file (stream file)
    (loop for form = (read stream nil :eof) until (eq form :eof) do
      (when (and (consp form) (member (first form) '(defun defvar defstruct defmacro))
                 (member (if (consp (second form)) (car (second form)) (second form)) names))
        (when core
          (setq form (append (subseq form 0 3)
                             (remove-if (lambda (x) (and (consp x) (eq (car x) 'declare)))
                                        (nthcdr 3 form)))))
        (eval form)))))
(fixture-load-definitions "books/payload-view-lease.lisp"
                          '(fn-pvl-runtime-step fn-pvl-runtime-return-step) t)
;; The arena's return observation (host/native/io.lisp): no release callback
;; is in custody here, so the arena reads :closed.
(fixture-load-definitions "host/native/io.lisp"
                          '(*fnn-arena-release-custody* fnn-arena-return-observation))
(defvar *the-live-state* :fixture-state)
(defvar *fixture-arena* (vector :sealed))
(defvar *fixture-owned* nil)
(defvar *fixture-state-calls* 0)
(defvar *fixture-generation* 0)
(defvar *fixture-reset-entered* nil)
(defvar *fixture-reset-proceed* nil)
(defun fnn-fault (control &rest args) (error (apply #'format nil control args)))
(defun fnn-live-arena () *fixture-arena*)
(defun fnn-core (name &rest args)
  ;; The lifecycle's decision is ACL2's: the step, and since the arena's
  ;; return observation the step over that observation.
  (assert (member name '(fn-pvl-runtime-step fn-pvl-runtime-return-step)))
  (apply name args))
(defun fnn-core-state (name &rest args)
  (incf *fixture-state-calls*)
  (case name
    (fn-owner-payload-view-owned-p *fixture-owned*)
    (fn-owner-payload-view-live-p (equal (first args) *fixture-owned*))
    (fn-owner-payload-view-release
     (cond ((not (equal (first args) *fixture-owned*)) '(:refused :stale))
           ((not (eq (second args) :joined)) '(:retained :cleanup-pending))
           (t (setq *fixture-owned* nil) '(:released))))
    (t (error "unexpected STATE adapter ~s" name))))
(defun fnn-call (name &rest args)
  (incf *fixture-state-calls*)
  (case name
    (fn-owner-payload-view-reset
     (assert (eq (first args) *fixture-arena*))
     (when *fixture-reset-entered*
       (sb-thread:signal-semaphore *fixture-reset-entered*)
       (sb-thread:wait-on-semaphore *fixture-reset-proceed*))
     (if *fixture-owned* (list nil '(:refused :payload-view-live))
       (progn (incf *fixture-generation*)
              (list nil '(:reset)))))
    (fn-owner-payload-view-acquire
     (assert (eq (second args) *fixture-arena*))
     (setq *fixture-owned* (list :payload-view *fixture-generation* 1 9))
     (list nil (list :acquired *fixture-owned*)))
    (t (error "unexpected direct adapter ~s" name))))
(fixture-load-definitions "host/native/io.lisp"
 '( *fnn-payload-lifecycle-lock* *fnn-payload-lifecycle-phase*
    *fnn-payload-lifecycle-arena* *fnn-payload-lifecycle-owner*
    fnn-payload-lifecycle-answer fnn-payload-startup-reset))
(fixture-load-definitions "host/native/owner.lisp"
 '(fnn-snapshot-payload-view fnn-payload-lifecycle-start fnn-payload-lifecycle-drain
   fnn-payload-lifecycle-joined fnn-snapshot-payload-view-acquire
   fnn-snapshot-payload-view-live-p fnn-snapshot-payload-view-release))
(defvar *fixture-owner-lock* (sb-thread:make-mutex :name "fixture owner"))
(defun fixture-clean ()
  (setq *fixture-owned* nil *fixture-state-calls* 0 *fixture-generation* 0
        *fixture-reset-entered* nil *fixture-reset-proceed* nil
        *fnn-payload-lifecycle-phase* :quiescent
        *fnn-payload-lifecycle-arena* nil *fnn-payload-lifecycle-owner* nil))

;; Reset first: startup/capture waits until reset has cleared and changed epoch.
(fixture-clean)
(let* ((service (list :owner)) (holder nil) (reset-answer nil)
       (attempt (sb-thread:make-semaphore))
       (reset (progn
                (setq *fixture-reset-entered* (sb-thread:make-semaphore)
                      *fixture-reset-proceed* (sb-thread:make-semaphore))
                (sb-thread:make-thread
                 (lambda () (setq reset-answer (fnn-payload-startup-reset)))))))
  (sb-thread:wait-on-semaphore *fixture-reset-entered*)
  (let ((start (sb-thread:make-thread
                (lambda ()
                  (sb-thread:signal-semaphore attempt)
                  (sb-thread:with-mutex (*fixture-owner-lock*)
                    (fnn-payload-lifecycle-start service)
                    (multiple-value-bind (word view)
                        (fnn-snapshot-payload-view-acquire service :funded)
                      (assert (eq word :acquired)) (setq holder view)))))))
    (sb-thread:wait-on-semaphore attempt)
    (sb-thread:signal-semaphore *fixture-reset-proceed*)
    (sb-thread:join-thread reset) (sb-thread:join-thread start))
  (assert (eq (first reset-answer) :reset))
  (assert (= (second (fnn-snapshot-payload-view-token holder)) 1))
  (assert (eq (fnn-snapshot-payload-view-arena holder) *fixture-arena*)))

;; Start/acquire first: reset cannot invoke any STATE function or clear arena.
(fixture-clean)
(let ((service (list :owner)) (holder nil))
  (sb-thread:with-mutex (*fixture-owner-lock*)
    (fnn-payload-lifecycle-start service)
    (setq holder (nth-value 1 (fnn-snapshot-payload-view-acquire service :funded))))
  (let ((calls *fixture-state-calls*) (old *fixture-owned*) (answer nil))
    (sb-thread:join-thread (sb-thread:make-thread
                           (lambda () (setq answer (fnn-payload-startup-reset)))))
    (assert (equal answer '(:refused :arena-not-quiescent)))
    (assert (= calls *fixture-state-calls*))
    (assert (equal old *fixture-owned*))
    (assert (= *fixture-generation* 0)))
  ;; Stop is only draining. Cancellation and joined-with-live-holder retain it.
  (sb-thread:with-mutex (*fixture-owner-lock*)
    (fnn-payload-lifecycle-drain service)
    (assert (fnn-snapshot-payload-view-live-p holder))
    (assert (eq (first (fnn-snapshot-payload-view-release holder :cancelled)) :retained))
    (fnn-payload-lifecycle-joined service)
    (assert (eq *fnn-payload-lifecycle-phase* :draining)))
  (let ((calls *fixture-state-calls*))
    (assert (equal (fnn-payload-startup-reset) '(:refused :arena-not-quiescent)))
    (assert (= calls *fixture-state-calls*)))
  (sb-thread:with-mutex (*fixture-owner-lock*)
    (assert (eq (first (fnn-snapshot-payload-view-release holder :joined)) :released))
    (fnn-payload-lifecycle-joined service))
  (assert (eq *fnn-payload-lifecycle-phase* :quiescent))
  (assert (eq (first (fnn-payload-startup-reset)) :reset)))
; An abandoned committer still leaves its actual syncer in the join roster.
; Reuse the current typed-adapter/actor fixture rather than a stale partial
; service structure or a fake syncer issuer. Its funding responses remain
; explicitly recording boundaries; real typed methods have their own suite.
(load "tests/native_syncer_custody_raw.lisp")
(in-package "ACL2")
(load-deployed-forms "host/native/owner.lisp" '((defun fnn-owner-wait-workers)))
(defvar *fixture-sync-entered* nil)
(defvar *fixture-sync-proceed* nil)
(defun fnn-owner-batch-job (service job)
  (declare (ignore service job))
  (sb-thread:signal-semaphore *fixture-sync-entered*)
  (sb-thread:wait-on-semaphore *fixture-sync-proceed*)
  (values :done nil))
(setq *fixture-sync-entered* (sb-thread:make-semaphore)
      *fixture-sync-proceed* (sb-thread:make-semaphore))
(let ((service (funded-service)))
  (multiple-value-bind (worker result actor grant) (fnn-owner-start-syncer service 7 nil)
    (wait-label *fixture-sync-entered*)
    (assert (member worker (fnn-with-roster (service)
                             (copy-list (fnn-owner-service-workers service)))))
    (assert (registered service actor))
    (sb-thread:signal-semaphore *fixture-sync-proceed*)
    (fnn-owner-wait-workers service)
    (assert (not (sb-thread:thread-alive-p worker)))
    (assert (null (fnn-with-roster (service) (fnn-owner-service-workers service))))
    (assert (null (fnn-owner-service-actors service)))
    (assert (equal (car result) '(7 :done)))
    ;; Join ended this physical actor, not its separately consumed operation.
    (assert (member grant (fnn-owner-service-syncer-grants service)))
    (assert (eq (test-ledger-physical (fnn-owner-service-syncer-ledger service)) :terminal))
    (assert (null (test-ledger-outcome (fnn-owner-service-syncer-ledger service))))
    (fnn-owner-syncer-outcome service grant 7)
    (assert (null (fnn-owner-service-syncer-grants service)))))
(format t "PAYLOAD-LIFECYCLE: reset-first, start-first, draining, joined cleanup, current syncer roster/dual receipt passed~%")
