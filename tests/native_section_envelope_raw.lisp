;;; Lane WRAPPER (rebuild step 0): the ONE generated owner-section envelope.
;;; Drives the deployed def-section generator and envelope
;;; (host/native/owner.lisp def-section, fnn-section-declare, fnn-section-run,
;;; fnn-section-run-cleanup, fnn-section-envelope, the fence boundary
;;; fnn-owner-shared-action-locked / fnn-owner-classify-escape-locked) over the
;;; deployed decisions (books/failure-scope.lisp: fn-fs-section-declp,
;;; fn-fs-section-admit, fn-fs-section-class-ok, fn-fs-unwind, fn-fs-classify
;;; and the closed tables, read from the book), against recording stubs of the
;;; gate and the service.  Each case asserts what the caller observes AND
;;; whether the fence was installed while the owner mutex was still held.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(declaim (declaration xargs))
(defun member-equal (x l) (member x l :test #'equal))
(defun true-listp (x) (and (listp x) (null (cdr (last x)))))

(defun load-deployed-forms (path wanted)
  "Evaluate PATH's top-level forms named by WANTED, (KIND NAME) each; a book's
defconst becomes a defparameter and its defun loses its xargs declaration."
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval (case (car form)
                         (defconst (cons 'defparameter (cdr form)))
                         (defun (destructuring-bind (name formals &rest body) (cdr form)
                                  `(defun ,name ,formals
                                     ,@(remove-if (lambda (f) (and (consp f) (eq (car f) 'declare)
                                                                   (consp (cadr f))
                                                                   (eq (car (cadr f)) 'xargs)))
                                                  body))))
                         (t form)))
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(load-deployed-forms "host/native/io.lisp"
                     '((define-condition fnn-store-error)
                       (define-condition fnn-store-fault)
                       (define-condition fnn-store-indeterminate)
                       (define-condition fnn-usage-error)
                       (define-condition fnn-os-error)
                       (defvar *fnn-section-step*)
                       (defun fnn-condition-class)
                       (defun fnn-refuse)
                       (defun fnn-fault)
                       (defun fnn-indeterminate)
                       (defun fnn-os-fail)))

(load-deployed-forms "books/failure-scope.lisp"
                     '((defconst *fn-fs-indeterminate-classes*)
                       (defconst *fn-fs-fault-classes*)
                       (defconst *fn-fs-usage-classes*)
                       (defconst *fn-fs-refusal-classes*)
                       (defconst *fn-fs-os-classes*)
                       (defun fn-fs-classify)
                       (defconst *fn-fs-actors*)
                       (defconst *fn-fs-gate-classes*)
                       (defconst *fn-fs-cleanup-purposes*)
                       (defun fn-fs-keyword-subsetp)
                       (defun fn-fs-admissionp)
                       (defun fn-fs-section-declp)
                       (defun fn-fs-section-admit)
                       (defun fn-fs-section-class-ok)
                       (defun fn-fs-unwind)))

;; The exit codes are ACL2's; only which one the owner stops with matters.
(defparameter +fnn-exit-uncertain+ :exit-uncertain)
(defparameter +fnn-exit-fault+ :exit-fault)

;; The service and its gate, recorded.
(defstruct svc (lock (sb-thread:make-mutex :name "owner")) (stopping nil)
  (stops nil) (log nil))
(defun fnn-owner-service-gate (s) s)
(defun fnn-owner-service-lock (s) (svc-lock s))
(defun fnn-owner-service-stopping (s) (svc-stopping s))
(defun note (s x) (push x (svc-log s)))
(defun fnn-owner-gate-check (g) (note g :check))
(defun fnn-owner-space-preobserve (s) (declare (ignore s)) nil)
(defun fnn-owner-gate-enter (g c) (note g (list :enter c)) 0)
(defun fnn-owner-gate-leave (g c held waited)
  (declare (ignore held waited)) (note g (list :leave c)))
(defun fnn-owner-gate-abort (g c) (note g (list :abort (fnn-condition-class c))))
(defun fnn-owner-stop-service-locked (s exit &optional answering)
  (declare (ignore answering))
  ;; The fence is installed while the owner mutex is held, or the case fails.
  (push (list exit (sb-thread:holding-mutex-p (svc-lock s))) (svc-stops s))
  (setf (svc-stopping s) t))
(defun fnn-owner-gate-fail-locked (s g condition)
  (declare (ignore g))
  (fnn-owner-stop-service-locked s +fnn-exit-fault+)
  (error condition))
(defun fnn-ms-since (start) (declare (ignore start)) 0)
(defun fnn-err (control &rest args) (declare (ignore control args)) nil)
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-owner-connection-selected-p (service) (declare (ignore service)) nil)
(defun fnn-owner-action (name &rest args) (declare (ignore name args)) nil)

(load-deployed-forms "host/native/owner.lisp"
                     '((defstruct (fnn-native-observation-row (:constructor %make-fnn-native-observation-row)))
                       (defstruct (fnn-native-observation (:constructor %make-fnn-native-observation)))
                       (defvar *fnn-native-observer*) (defvar *fnn-native-actor-identity*)
                       (defun fnn-native-observation-create) (defun fnn-native-reserve-thread-identity)
                       (defun fnn-native-observed-thread-thunk) (defun fnn-native-observation-reserve)
                       (defun fnn-native-observe) (defun fnn-native-observation-complete)
                       (defun fnn-native-observation-events) (defun fnn-native-observation-start)
                       (defun fnn-native-observation-current-identity)
                       (defun fnn-native-observation-report) (defmacro fnn-native-with-observation)
                       (defmacro fnn-with-observed-owner)
                       (defvar *fnn-owner-measure*)
                       (defvar *fnn-owner-measure-label*)
                       (defmacro fnn-owner-measured)
                       (defvar *fnn-boundary-outcome*)
                       (defmacro fnn-section-envelope)
                       (defun fnn-section-run)
                       (defun fnn-section-run-cleanup)
                       (defvar *fnn-sections*)
                       (defun fnn-section-declare)
                       (defmacro def-section)
                       (def-section fnn-quantum-control)
                       (defun fnn-owner-classify-escape-locked)
                       (defun fnn-owner-shared-action-locked)))

(defvar *seen* nil)
(defun check (test what)
  (unless test (format t "FAIL: ~a (last outcome ~a)~%" what (substitute #\space #\newline (princ-to-string *seen*))) (sb-ext:exit :code 1)))

(defun outcome (thunk)
  "What leaves the call: (:values ...) or (:condition CLASS)."
  (handler-case (setq *seen* (list* :values (multiple-value-list (funcall thunk))))
    (serious-condition (c)
      (setq *seen* (list :condition (fnn-condition-class c) (princ-to-string c)))
      (list :condition (fnn-condition-class c)))))

;; A cleanup section declared for one of ACL2's post-fence purposes.
(def-section test-quantum-fault-cleanup
  :actors (:maintenance) :classes (:control) :admits (:cleanup :fault))

;; 1. A :live section runs its body as the declared class and hands back
;; every value; the gate is entered and left; no stop.
(let ((s (make-svc)))
  (check (equal (outcome (lambda () (fnn-quantum-control s nil (lambda () (values 1 2)))))
                '(:values 1 2))
         "a live section returns the body's values")
  (check (null (svc-stops s)) "no stop for a completed body")
  (check (member '(:enter :control) (svc-log s) :test #'equal) "the gate is entered as :control")
  (check (member '(:leave :control) (svc-log s) :test #'equal) "the gate is left"))

;; 2. Once stopping, a :live section is refused: the known refusal, the body
;; never runs, no further stop (fn-fs-section-admit).
(let ((s (make-svc :stopping t)) (ran nil))
  (check (equal (outcome (lambda () (fnn-quantum-control s nil (lambda () (setq ran t)))))
                '(:condition "fnn-store-error"))
         "a live section is refused once stopping")
  (check (not ran) "the refused body did not run")
  (check (null (svc-stops s)) "the refusal installs no stop"))

;; 3. A (:cleanup PURPOSE) section runs after the fence.
(let ((s (make-svc :stopping t)) (ran nil))
  (check (equal (outcome (lambda () (test-quantum-fault-cleanup s nil (lambda () (setq ran t) :done))))
                '(:values :done))
         "a cleanup section runs once stopping")
  (check ran "the cleanup body ran"))

;; 4. An entry as a class its section did not declare is a fault of the host,
;; fenced before the owner mutex is taken.
(let ((s (make-svc)) (ran nil))
  (check (equal (outcome (lambda () (fnn-quantum-control s nil (lambda () (setq ran t)) :reader)))
                '(:condition "fnn-store-fault"))
         "an undeclared class faults")
  (check (not ran) "the body of an undeclared class did not run")
  (check (equal (mapcar #'first (svc-stops s)) (list +fnn-exit-fault+))
         "the undeclared class stops the service as a fault"))

;; 5. An uncertain outcome inside the body fences (exit 3) BEFORE the owner
;; mutex is released, and the caller sees the fence's class.
(let ((s (make-svc)))
  (check (equal (outcome (lambda () (fnn-quantum-control s nil (lambda () (fnn-indeterminate "x")))))
                '(:condition "fnn-store-indeterminate"))
         "an uncertain body is re-signalled as uncertain")
  (check (equal (svc-stops s) (list (list +fnn-exit-uncertain+ t)))
         "the fence is installed once, under the owner mutex"))

;; 6. An OS error after a durable step is the fence; before one, a fault.
(let ((s (make-svc)))
  (outcome (lambda () (fnn-quantum-control s nil (lambda () (setq *fnn-section-step* :replaced)
                                                     (fnn-os-fail 5)))))
  (check (equal (svc-stops s) (list (list +fnn-exit-uncertain+ t)))
         "an OS error after a durable step fences under the mutex"))
(let ((s (make-svc)))
  (outcome (lambda () (fnn-quantum-control s nil (lambda () (fnn-os-fail 5)))))
  (check (equal (svc-stops s) (list (list +fnn-exit-fault+ t)))
         "an OS error before any durable step faults under the mutex"))

;; 7. A non-local exit that is no condition (a throw) leaves the body
;; unclassified: a fault, installed while the mutex is still held (review M3).
(let ((s (make-svc)))
  (check (eq (catch 'away (fnn-quantum-control s nil (lambda () (throw 'away :thrown))))
             :thrown)
         "the throw still leaves")
  (check (equal (svc-stops s) (list (list +fnn-exit-fault+ t)))
         "an unclassified exit faults under the mutex"))

;; 8. A known refusal passes, unfenced, to its caller.
(let ((s (make-svc)))
  (check (equal (outcome (lambda () (fnn-quantum-control s nil (lambda () (fnn-refuse "no")))))
                '(:condition "fnn-store-error"))
         "a refusal passes")
  (check (null (svc-stops s)) "a refusal installs no stop"))

;; 9. A store-error subclass no table names is a fault, not the refusal its
;; parent is (review M1, through the envelope).
(define-condition fnn-store-future-refusal (fnn-store-error) ())
(let ((s (make-svc)))
  (check (equal (outcome (lambda () (fnn-quantum-control
                                     s nil (lambda () (error 'fnn-store-future-refusal :message "x")))))
                '(:condition "fnn-store-fault"))
         "an unlisted refusal subclass is re-signalled as a fault")
  (check (equal (svc-stops s) (list (list +fnn-exit-fault+ t)))
         "an unlisted refusal subclass faults under the mutex"))

;; 10. ACL2 refuses a declaration whose cleanup purpose is not in the closed
;; post-fence set (review M4: pending-extent release): the load stops.
(check (equal (outcome (lambda ()
                         (eval '(def-section test-quantum-bad
                                 :actors (:maintenance) :classes (:control)
                                 :admits (:cleanup :release-pending-extents)))))
              '(:condition "simple-error"))
       "an unlisted cleanup purpose refuses the declaration")
(check (not (fboundp 'test-quantum-bad)) "a refused declaration defines no entry")
(check (equal (mapcar #'first *fnn-sections*) '(fnn-quantum-control test-quantum-fault-cleanup))
       "the declared table holds the accepted sections only")

(format t "native_section_envelope_raw: PASS~%")
