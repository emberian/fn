;;; Actual actor/section primitive observations; no timestamp reconstruction.
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
(defun fnn-owner-syncer-physical (service grant receipt)
  (declare (ignorable service grant receipt))
  (harness-stub-reached 'fnn-owner-syncer-physical "host/native/owner.lisp"))
;;; ---- derived stubs: END ----
(defvar *observed-hm-packets* nil)
(defun observation-service ()
  (%make-fnn-owner-service :lock (sb-thread:make-mutex :name "observed O") :gate (make-svc)))
(defun record-complete-packet (observer expected)
  (multiple-value-bind (status events reason) (fnn-native-observation-events observer)
    (check (and (eq status :complete) (null reason) (equal events expected))
           "literal actor identity and completed producer order")
    (push events *observed-hm-packets*)))

;; Generated actor reserves identity before creation; the actual shared section
;; reports its physical acquire/release while preserving all body values.
(let* ((s (observation-service)) (*fnn-native-observer* (fnn-native-observation-create 8))
       (result nil))
  (multiple-value-bind (worker actor)
      (fnn-owner-spawn-syncer s nil
       (lambda () (setq result (multiple-value-list
          (fnn-quantum-control s nil (lambda () (values :first :second)))))))
    (check (fnn-owner-actor-join s worker) "observed actual actor physically joined")
    (check (equal result '(:first :second)) "observation preserves multiple values")
    (let ((id (symbol-name (fnn-owner-actor-id actor))))
      (record-complete-packet *fnn-native-observer*
                             (list (list :acquire id :owner) (list :release id :owner))))))

;; Force preemption AFTER physical unlock and BEFORE publishing completion.
;; The second actor can finish its section while the first release is pending.
;; A reader must stop at that reservation, never replay an inverted lock order.
(let* ((s (observation-service)) (*fnn-native-observer* (fnn-native-observation-create 8))
       (unlocked (sb-thread:make-semaphore :count 0))
       (resume (sb-thread:make-semaphore :count 0))
       (second-done (sb-thread:make-semaphore :count 0))
       (original (symbol-function 'fnn-native-observation-complete))
       (first-id nil) (first-worker nil) (second-worker nil) (second-id nil))
  (unwind-protect
      (progn
        (setf (symbol-function 'fnn-native-observation-complete)
          (lambda (row)
            (when (and row (equal *fnn-native-actor-identity* first-id))
              (check (not (sb-thread:holding-mutex-p (fnn-owner-service-lock s)))
                     "release completion occurs after physical unlock")
              (sb-thread:signal-semaphore unlocked)
              (wait-label resume))
            (funcall original row)))
        ;; Hold the child inside its body until parent's exact ID is captured.
        (let ((begin (sb-thread:make-semaphore :count 0)))
          (multiple-value-bind (worker actor)
              (fnn-owner-spawn-syncer s nil
                (lambda () (wait-label begin) (fnn-quantum-control s nil (lambda () :one))))
            (setq first-worker worker first-id (symbol-name (fnn-owner-actor-id actor)))
            (sb-thread:signal-semaphore begin)))
        (wait-label unlocked)
        (multiple-value-bind (worker actor)
            (fnn-owner-spawn-syncer s nil
              (lambda () (fnn-quantum-control s nil (lambda () :two))
                         (sb-thread:signal-semaphore second-done)))
          (setq second-worker worker second-id (symbol-name (fnn-owner-actor-id actor))))
        (wait-label second-done)
        (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
          (check (and (eq status :pending) (null reason)
                      (equal events (list (list :acquire first-id :owner))))
                 "reader exposes only completed prefix across unlock preemption"))
        (sb-thread:signal-semaphore resume)
        (check (and (fnn-owner-actor-join s first-worker)
                    (fnn-owner-actor-join s second-worker)) "both observed actors joined")
        (record-complete-packet *fnn-native-observer*
          (list (list :acquire first-id :owner) (list :release first-id :owner)
                (list :acquire second-id :owner) (list :release second-id :owner))))
    (setf (symbol-function 'fnn-native-observation-complete) original)))

;; Comparison invalidation does not fault/refuse the real section or lose values.
(dolist (case '(:overflow :identity-unavailable :observer-fault))
  (let* ((s (observation-service))
         (*fnn-native-observer* (fnn-native-observation-create (if (eq case :overflow) 1 2)))
         (*fnn-native-actor-identity* (unless (eq case :identity-unavailable) "observed-parent")))
    (when (eq case :observer-fault)
      (setf (aref (fnn-native-observation-rows *fnn-native-observer*) 0) nil))
    (check (equal (multiple-value-list (fnn-quantum-control s nil (lambda () (values 3 4)))) '(3 4))
           "invalid observer cannot change section result")
    (multiple-value-bind (status events reason) (fnn-native-observation-events *fnn-native-observer*)
      (format t "invalid-case ~s ~s ~s ~s~%" case status events reason)
      (check (and (eq status :unavailable) (null events) (eq reason case)
                  (null (fnn-owner-service-stopping s)))
             "overflow, missing identity, and observer fault invalidate comparison only"))))

;; Observation-only executor seam reserves before its maker, binds that literal
;; in its child, and emits nothing if the maker fails before a child exists.
(let* ((s (observation-service)) (*fnn-native-observer* (fnn-native-observation-create 2)) (identity nil)
       (thunk (fnn-native-observed-thread-thunk
               (lambda () (setq identity *fnn-native-actor-identity*)
                          (fnn-quantum-control s nil (lambda () :executor-body))))))
  (let ((worker (sb-thread:make-thread thunk :name "observation-only executor")))
    (sb-thread:join-thread worker))
  (check (and (stringp identity) (> (length identity) 0)) "executor binds native reserved literal")
  (record-complete-packet *fnn-native-observer*
                         (list (list :acquire identity :owner) (list :release identity :owner))))
(let* ((*fnn-native-observer* (fnn-native-observation-create 2))
       (thunk (fnn-native-observed-thread-thunk (lambda () (error "must not run")))))
  (check (handler-case
             (funcall (lambda (child) (declare (ignore child)) (error "maker failed")) thunk)
           (error () t)) "failed maker discriminated")
  (record-complete-packet *fnn-native-observer* nil))

;; Export actual literal producer packets with answers/invariant at every step.
;; Groundwork consumes this in its already loaded ACL2 HM session.
(ensure-directories-exist "build/runtime-tests/native-observation-hm.lsp")
(with-open-file (out "build/runtime-tests/native-observation-hm.lsp" :direction :output :if-exists :supersede)
  (dolist (events (nreverse *observed-hm-packets*))
    (let ((bindings (list (list 'st0 '(fn-hmc-init)))) (checks (list '(fn-hmc-invp st0))) (prev 'st0) (index 0))
      (dolist (event events)
        (let ((next (intern (format nil "ST~D" (incf index)) "ACL2")))
          (setq bindings (append bindings (list (list next (list 'fn-hmc-next-state prev (list 'quote event))))))
          (push (list 'equal (list 'fn-hmc-answer prev (list 'quote event))
                      (if (eq (car event) :acquire) :held :released)) checks)
          (push (list 'fn-hmc-invp next) checks)
          (setq prev next)))
      (write (list 'assert-event (list 'let* bindings (cons 'and (nreverse checks)))) :stream out :pretty t)
      (terpri out))))
(format t "native_observation_raw: PASS; actual HM packet build/runtime-tests/native-observation-hm.lsp~%")
