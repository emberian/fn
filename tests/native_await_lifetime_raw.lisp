;;; Actual logical wait and completion mailbox lifetime. Physical operation
;;; custody is separate and is never settled by cancelling reply publication.
(load "tests/native_actor_envelope_raw.lisp")
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
(defun fnn-mux-handshake-release (loop conn)
  (declare (ignorable loop conn))
  (harness-stub-reached 'fnn-mux-handshake-release "host/native/mux.lisp"))
(defun fnn-owner-cold-abandon (read)
  (declare (ignorable read))
  (harness-stub-reached 'fnn-owner-cold-abandon "host/native/owner.lisp"))
(defun fnn-owner-core (name &rest args)
  (declare (ignorable name args))
  (harness-stub-reached 'fnn-owner-core "host/native/owner.lisp"))
(defun fnn-owner-syncer-physical (service grant receipt)
  (declare (ignorable service grant receipt))
  (harness-stub-reached 'fnn-owner-syncer-physical "host/native/owner.lisp"))
(defun fnn-tls-close-channel (channel)
  (declare (ignorable channel))
  (harness-stub-reached 'fnn-tls-close-channel "host/native/tls.lisp"))
(defun fnn-zout-free (zout)
  (declare (ignorable zout))
  (harness-stub-reached 'fnn-zout-free "host/native/deflate.lisp"))
;;; ---- derived stubs: END ----
(load-deployed-forms "host/native/io.lisp" '((defvar *fnn-monotonic-ticks*) (defun fnn-now)))
(load-deployed-forms "host/native/owner.lisp"
 '((defun fnn-owner-deliver) (defun fnn-owner-await-register)
   (defun fnn-owner-awaiting-sockets) (defun fnn-owner-past-p)
   (defun fnn-owner-await-logical)))
;; Let the unchanged harness execute its behavioral assertions on the baseline.
(when (with-open-file (stream "host/native/owner.lisp")
        (loop for form = (read stream nil :eof) until (eq form :eof)
              thereis (and (consp form) (eq (car form) 'defun)
                           (eq (cadr form) 'fnn-owner-await-abandon))))
  (load-deployed-forms "host/native/owner.lisp" '((defun fnn-owner-await-abandon))))
(let ((which (sb-ext:posix-getenv "FN_AWAIT_TEST_CASE")))
  ;; Real SBCL wait times out once before producer delivery. A timeout returns
  ;; without the mutex: the next observation must acquire it anew.
  (when (or (null which) (string= which "wait"))
    (let* ((s (%make-fnn-owner-service)) (condition nil) (answer nil)
           (completion #(50 52 48))
           (producer (sb-thread:make-thread
                      (lambda () (sleep 1.1) (fnn-owner-deliver s 41 completion)))))
      (unwind-protect
           (handler-case
               (setq answer (fnn-owner-await-logical s 41
                             (+ (fnn-now) (* 3 internal-time-units-per-second))))
             (error (e) (setq condition e)))
        (sb-thread:join-thread producer))
      (check (and (null condition) (eq answer completion))
             (format nil "logical wait survives timed wake and receives completion; condition=~a" condition))
      (check (and (zerop (hash-table-count (fnn-owner-service-awaiting s)))
                  (zerop (hash-table-count (fnn-owner-service-done s))))
             "completed logical wait leaves no mailbox entry")))
  (when (or (null which) (string= which "cancel"))
    (let ((s (%make-fnn-owner-service)))
      (setf (fnn-owner-service-syncer-grants s) '(:physical-operation-still-owed))
      (check (eq (fnn-owner-await-logical s 52 (1- (fnn-now))) :uncertain)
             "expired logical caller receives uncertainty")
      (check (null (fnn-owner-awaiting-sockets s 52)) "abandoned wait names no socket")
      (fnn-owner-deliver s 52 #(50 52 48))
      (check (and (zerop (hash-table-count (fnn-owner-service-awaiting s)))
                  (zerop (hash-table-count (fnn-owner-service-done s))))
             "late completion of abandoned logical caller is not retained forever in DONE")
      (check (equal (fnn-owner-service-syncer-grants s) '(:physical-operation-still-owed))
             "reply abandonment never settles physical operation custody"))))
(format t "native_await_lifetime_raw: PASS actual timed wait and late completion lifetime~%")

;; Cancellation racing a callback already selected by DELIVER creates no
;; replacement mailbox entry. The detached callback retains only its own cell.
(let* ((s (%make-fnn-owner-service)) (entered (sb-thread:make-semaphore :count 0))
       (release (sb-thread:make-semaphore :count 0)) (received nil))
  (fnn-owner-await-register s 63
   (lambda (value) (sb-thread:signal-semaphore entered) (wait-label release)
     (setq received value)) :socket)
  (let ((producer (sb-thread:make-thread (lambda () (fnn-owner-deliver s 63 :completed)))))
    (wait-label entered)
    (fnn-owner-await-abandon s 63)
    (sb-thread:signal-semaphore release)
    (sb-thread:join-thread producer)
    (check (and (eq received :completed)
                (zerop (hash-table-count (fnn-owner-service-awaiting s)))
                (zerop (hash-table-count (fnn-owner-service-done s))))
           "in-flight callback cancellation creates no orphan marker or done entry")))

;; Nonlocal escape from an actual wait also closes the reply route, while
;; retaining the pending-delivery marker until the real result arrives.
(let ((s (%make-fnn-owner-service))
      (*fnn-monotonic-ticks* (lambda () (throw 'await-clock-escape :clock-escaped))))
  (check (eq (catch 'await-clock-escape (fnn-owner-await-logical s 74 1)) :clock-escaped)
         "logical wait preserves original nonlocal escape")
  (fnn-owner-deliver s 74 :completed)
  (check (and (zerop (hash-table-count (fnn-owner-service-awaiting s)))
              (zerop (hash-table-count (fnn-owner-service-done s))))
         "nonlocal wait exit cannot leak late completion"))

;; The actual mux terminal consumer closes its pending reply route too.
(load-deployed-forms "host/native/mux.lisp"
 '((defun fnn-mux-service) (defun fnn-mux-finish)))
(defun fnn-owner-response-unpin (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-serialized (&rest args) (declare (ignore args)) nil)
(defun fnn-mux-start-waiting-handshake (&rest args) (declare (ignore args)) nil)
(let* ((s (%make-fnn-owner-service :clients '(:closing-socket)))
       (loop (%make-fnn-mux-loop :service s))
       (conn (%make-fnn-mux-conn :cid 85 :opened-cid 85 :phase :await
                                :await '(step redeem nil) :socket :closing-socket))
       (published nil))
  (fnn-owner-await-register s 85 (lambda (value) (setq published value)) :closing-socket)
  (fnn-mux-finish loop conn)
  (fnn-owner-deliver s 85 :completed)
  (check (and (eq (fnn-mux-conn-phase conn) :done) (null (fnn-mux-conn-await conn))
              (not published) (null (fnn-owner-service-clients s))
              (zerop (hash-table-count (fnn-owner-service-awaiting s)))
              (zerop (hash-table-count (fnn-owner-service-done s))))
         "finished mux connection drops eventual completion without retained callback"))
(format t "native_await_lifetime_raw: PASS cancellation/callback/nonlocal/mux schedules~%")
