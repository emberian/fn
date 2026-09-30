(load "/Users/ember/dev/fn/build/lanes/operability-3/tests/recording/retirement/store-authority/actual-store-authority.lisp")

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *fnn-log-queue-mutex* (sb-thread:make-mutex))
(defvar *block-writer* t)
(defun fn-ort-log-caller-action (writer-presentp)
  
  (if (equal writer-presentp nil) :write-close :held))
(defparameter +fnn-exit-ok+ 0)
(defvar *fnn-owner-last-fault* nil)
(defvar *fnn-health-min-percent* nil)
(defvar *fnn-owner-log-fd* nil)
(defvar *fnn-owner-log-path* nil)
(defvar *fnn-owner-startup-hooks* nil)
(defvar *fnn-owner-start-hooks* nil)
(defvar *fnn-owner-stop-hooks* nil)
(defvar *fnn-owner-close-hooks* nil)
(defvar *fnn-log-writer* nil)
(defvar *fnn-owner-log-mutex* (sb-thread:make-mutex))
(defvar *release* (sb-thread:make-semaphore))
(defvar *recorded* nil)
(defun fnn-core (name &rest args) (case name (fn-ort-log-caller-action (apply #'fn-ort-log-caller-action args)) ((fn-native-health-host-run-started-line fn-native-health-host-run-stopped-line) '(65)) (otherwise nil)))
(defun fnn-octets (x) x)
(defun fnn-octets-string (x) (declare (ignore x)) "")
(defun fnn-string-octets (x) (declare (ignore x)) nil)
(defun fnn-octet-list (x) x)
(defun fnn-octet-list-p (x) (every #'integerp x))
(defun fnn-operator-optional-path (result projection) (declare (ignore result)) (when (eq projection 'fn-native-operator-host-result-run-log-path-octets) "/recording-log"))
(defun fnn-owner-open-log (path) (declare (ignore path)) 123)
(defun fnn-write-all (fd octets) (declare (ignore octets)) (push (list :write fd (and *fnn-log-writer* (sb-thread:thread-alive-p *fnn-log-writer*))) *recorded*))
(defun fnn-close (fd) (push (list :close fd (and *fnn-log-writer* (sb-thread:thread-alive-p *fnn-log-writer*))) *recorded*))
(defun fnn-web-run-hooks (&rest args) (declare (ignore args)) nil)
(defun fnn-native-auth-startup-hook (&rest args) (declare (ignore args)) nil)
(defun fnn-operator-status-of-exit-code (x) x)
(defun fnn-operator-emit-status (&rest args) (declare (ignore args)) nil)
(defun fnn-exit-code-for (condition) (format t "RECORDING condition ~a~%" condition) 99)
(dolist (name '(fnn-feed-service-start fnn-pull-service-start fnn-feed-service-wake fnn-pull-service-wake fnn-feed-service-close fnn-pull-service-close fnn-web-close-face fnn-web-start fnn-tls-start-context fnn-tls-close-context))
 (setf (symbol-function name) (lambda (&rest args) (declare (ignore args)) nil)))


(defparameter +fnn-exit-uncertain+ 3)
(defvar *caller-mode* :held)
(defvar *caller-service* nil)
(defun fnn-core (name &rest args)
 (case name
  ((fn-native-health-host-run-started-line fn-native-health-host-run-stopped-line) '(65))
  (otherwise (if (fboundp name) (apply (symbol-function name) args) nil))))
(defun fnn-control-owner-run-normalized (&rest args)
 (declare (ignore args))
 (fnn-owner-claim-run-authority *fnn-owner-caller-reservation*)
 (setq *caller-service* (make-fnn-owner-service
         :store (make-fnn-store :log (make-fnn-log :fd 601) :lock-fd 602)))
 (fnn-owner-retain-run-authority *caller-service*)
 (if (eq *caller-mode* :held)
  (progn
   (fnn-log-writer-start)
   (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (let ((answer (fn-log-sink-offer *fnn-log-sink* 3 1048576)))
     (fnn-log-sink-accept (second answer) :caller)
     (fnn-log-queue-push (cons :journal '(65 66 10)))))
   (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
   (assert (eq (fnn-log-writer-stop) :timeout))
   (assert (eq (fnn-owner-store-settlement *caller-service* :held) :held))
   3)
  (progn
   (assert (eq (fnn-owner-store-settlement *caller-service* :joined) :joined)) 0)))


(defun fnn-operator-log-run-line (octets)
  "Append ACL2's run line and one LF only with released writer authority.
A timed-out writer retains its descriptor; no direct write then. A failed write stops
nothing: the log is an operator's record."
  (when (and (eq (fnn-core 'fn-ort-log-caller-action
                          (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                            (and *fnn-log-writer* t)))
                 :write-close)
             *fnn-owner-log-fd* (fnn-octet-list-p octets))
    (ignore-errors
     (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
       (fnn-write-all *fnn-owner-log-fd* (fnn-octets (append octets (list 10))))))))

(defun fnn-operator-execute-run (result)
  "Invoke the one owner entry only with ACL2-normalized plan projections."
  (handler-case
      (progn
        ;; Atomically reserve before any auth/TLS/log I/O or start line.
        ;; Only this caller's dynamic token lets the owner consume that
        ;; reservation; another caller cannot replace retained descriptors.
        (fnn-owner-claim-run-authority nil)
        (setq *fnn-owner-last-fault* nil)
        (let* ((*fnn-owner-caller-reservation* t)
               (auth-path
               (fnn-octets-string
                (fnn-octets
                 (fnn-core
                  'fn-native-operator-host-result-run-auth-path-octets result))))
             (auth-required
               (fnn-core
                'fn-native-operator-host-result-run-auth-requiredp result))
             (auth-protected
               (fnn-core
                'fn-native-operator-host-result-run-auth-protected-onlyp result))
             (certificate
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-tls-cert-octets))
             (private-key
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-tls-key-octets))
             ;; `[log] path', absolute by fn-native-config-log-pathp; NIL
             ;; means the owner writes its service log to stderr.
             (log-path
               (fnn-operator-optional-path
                result 'fn-native-operator-host-result-run-log-path-octets))
             (tls-context nil)
             (run-code nil)
             (run-failure nil))
        (setq *fnn-health-min-percent*
              (fnn-core 'fn-native-operator-host-result-health-min-percent result))
        (unwind-protect
            (handler-case
            (progn
              ;; Append-only, created 0640 if absent, never through a
              ;; symlink, never truncated or rotated here.  Opened before
              ;; the store so a wrong path is refused before recovery runs.
              (when log-path
                (setq *fnn-owner-log-fd* (fnn-owner-open-log log-path)
                      *fnn-owner-log-path* log-path)
                (fnn-operator-log-run-line
                 (fnn-core 'fn-native-health-host-run-started-line)))
              ;; ACL2 already enforced paired presence.  Only a pair ACL2
              ;; accepted (fn-tlsr-start-decide, the decision `tls reload'
              ;; applies; PRF-387) is passed to auth/owner.
              (when certificate
                (setq tls-context
                      (fnn-tls-start-context certificate private-key)))
              (let* ((web-plan
                       ;; The node's own web face (PRF-340): ACL2's plan of
                       ;; the profile's [web] table, or NIL for none.
                       (fnn-web-run-hooks
                        (fnn-core 'fn-native-operator-host-result-run-listener-port result)
                        (and tls-context
                             (fnn-core 'fn-native-operator-host-result-run-implicit-tls-port
                                       result))
                        (and tls-context t)))
                     (*fnn-owner-startup-hooks*
                       (list (fnn-native-auth-startup-hook
                              auth-path auth-required auth-protected)))
                     ;; The NEWNEWS pull feed (PRF-100) is a sibling lifecycle
                     ;; extension: host/native/pull-service.lisp.
                     (*fnn-owner-start-hooks*
                       (append (list* #'fnn-feed-service-start #'fnn-pull-service-start
                                      *fnn-owner-start-hooks*)
                               (and web-plan
                                    (list (lambda (service)
                                            (fnn-web-start service web-plan tls-context))))))
                     (*fnn-owner-stop-hooks*
                       (list* #'fnn-feed-service-wake #'fnn-pull-service-wake
                              *fnn-owner-stop-hooks*))
                     (*fnn-owner-close-hooks*
                       (list* #'fnn-feed-service-close #'fnn-pull-service-close
                              #'fnn-web-close-face
                              *fnn-owner-close-hooks*))
                     (code
                       (fnn-control-owner-run-normalized
                        (fnn-octets
                         (fnn-core
                          'fn-native-operator-host-result-run-store-octets result))
                        (fnn-octets
                         (fnn-core
                          'fn-native-operator-host-result-run-listener-host-octets result))
                        (fnn-core
                         'fn-native-operator-host-result-run-listener-port result)
                        (fnn-core 'fn-native-operator-host-result-run-oncep result)
                        (fnn-core
                         'fn-native-operator-host-result-run-max-connections result)
                        (fnn-octets (fnn-core
                                     'fn-native-operator-host-result-run-control-path-octets result))
                        (fnn-core 'fn-native-operator-host-result-run-posting-enabledp result)
                        tls-context
                        ;; PRF-162: ACL2's implicit-TLS port, offered only
                        ;; beside the certificate and key loaded above.
                        (and tls-context
                             (fnn-core
                              'fn-native-operator-host-result-run-implicit-tls-port
                              result)))))
                (setq run-code code)
                ;; The owner's fault, when it stopped on one, is the
                ;; result line's reason: the last line the service
                ;; manager's journal shows for this run says why.
                (fnn-operator-emit-status
                 (fnn-operator-status-of-exit-code code) "run"
                 (and (/= code +fnn-exit-ok+) *fnn-owner-last-fault*))
                code))
              (error (condition)
                ;; Recorded for the stop line below, then handled as before
                ;; by the outer handler.
                (setq run-failure condition)
                (error condition)))
          (when (eq (fnn-core 'fn-ort-log-caller-action
                             (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                               (and *fnn-log-writer* t)))
                    :write-close)
            (let ((code (or run-code (and run-failure (fnn-exit-code-for run-failure)))))
              (when (integerp code)
                (fnn-operator-log-run-line
                 (fnn-core 'fn-native-health-host-run-stopped-line code
                           (let ((reason (cond (run-failure
                                                (ignore-errors (format nil "~a" run-failure)))
                                               ((/= code +fnn-exit-ok+) *fnn-owner-last-fault*))))
                             (and (stringp reason) (fnn-octet-list (fnn-string-octets reason)))))))))
          (when tls-context (fnn-tls-close-context tls-context))
          (when (eq (fnn-core 'fn-ort-log-caller-action
                             (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                               (and *fnn-log-writer* t)))
                    :write-close)
            (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
              (when *fnn-owner-log-fd*
                ;; An uncertain descriptor close retains its actual handle.
                (handler-case
                    (progn (fnn-close *fnn-owner-log-fd*)
                           (setq *fnn-owner-log-fd* nil
                                 *fnn-owner-log-path* nil))
                  (error ()
                    (setq *fnn-owner-retained-settlement*
                          (fnn-core 'fn-ort-service-settlement-action
                                    *fnn-owner-retained-settlement* :uncertain)))))))
          ;; The actual caller relinquished its log descriptor only above.
          ;; A held writer/close retains the complete service and Store lock.
          (when *fnn-owner-retained-service*
            (let ((holder *fnn-owner-retained-service*))
              (unless (eq (fnn-owner-store-settlement
                           (if (eq holder t) nil holder)
                           *fnn-owner-retained-settlement*) :joined)
                (return-from fnn-operator-execute-run
                  (fnn-core 'fn-ort-log-close-exit
                            (or run-code +fnn-exit-uncertain+)
                            +fnn-exit-uncertain+ :held))))))))
    (error (condition)
      (let ((code (fnn-exit-code-for condition)))
        (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "run" condition)
        code))))

(setq *recorded* nil *caller-mode* :held)
(assert (= (fnn-operator-execute-run nil) 3))
(assert (alive))
(assert (= *fnn-owner-log-fd* 123))
(assert (eq *fnn-owner-retained-service* *caller-service*))
(assert (= (fnn-store-lock-fd (fnn-owner-service-store *caller-service*)) 602))
(assert (equal (reverse *recorded*) '((:write 123 nil))))
(let ((before *recorded*))
 (assert (= (fnn-operator-execute-run nil) 99))
 (assert (eq before *recorded*)))
(sb-thread:signal-semaphore *release*)
(assert (eq (fnn-log-writer-stop) :joined))
;; Recording recovery continuation supplies a fresh definite journal-settled
;; observation after actual writer join, then relinquishes caller descriptor.
(setq *fnn-owner-retained-settlement* :joined)
(fnn-close *fnn-owner-log-fd*)
(setq *fnn-owner-log-fd* nil *fnn-owner-log-path* nil)
(assert (eq (fnn-owner-store-settlement *caller-service* :joined) :joined))
(setq *recorded* nil *caller-mode* :joined)
(assert (= (fnn-operator-execute-run nil) 0))
(assert (null *fnn-owner-log-fd*))
(assert (null *fnn-owner-retained-service*))
(assert (equal (reverse *recorded*)
 '((:write 123 nil) (:write 123 nil) (:close 123 nil)
   (:close 601 nil) (:flock 602 8 nil) (:close 602 nil))))
(format t "PASS actual outer caller: held writer bypasses stop write/FD/Store close; reentry fenced; joined exact teardown~%")
(format t "STORE-CALLER-PASS ~s~%" (reverse *recorded*))

