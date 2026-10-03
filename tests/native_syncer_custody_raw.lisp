;;; Actual native grant/actor callback wiring. The dispatch responses below
;;; are recording stubs, not a typed ledger proof. Typed methods and both
;;; settlement orderings run in tests/acl2/resource-syncer-tests.lisp.
(load "tests/native_actor_envelope_raw.lisp")
(in-package "ACL2")

(load-deployed-forms "host/native/owner.lisp"
 '((defstruct (fnn-syncer-grant (:constructor %make-fnn-syncer-grant)))
   (defun fnn-owner-syncer-install) (defun fnn-owner-syncer-issue)
   (defun fnn-owner-syncer-receipt) (defun fnn-owner-syncer-abort) (defun fnn-owner-syncer-physical)
   (defun fnn-owner-syncer-outcome)))
(defvar *calls* nil)
(defstruct test-ledger token generation (serial 0) physical outcome)
(defun fnn-core (subject &rest args)
  (check (and (eq subject 'create-fn-resource-ledger) (null args)) "creator uses normal dispatcher")
  (push (list subject) *calls*) (make-test-ledger))
(defun fnn-call (subject &rest args)
  (push (cons subject args) *calls*)
  (case subject
    (fn-ros-install-syncer
     (check (equal (subseq args 0 2) '(12 1048576)) "actual qualified producer inputs forwarded")
     (list :installed (third args)))
    (fn-ros-issue
     (destructuring-bind (gen ledger) args
       (if (test-ledger-token ledger) (list :slot-busy nil ledger)
         (let ((token (list :resource :owner 2 (incf (test-ledger-serial ledger)))))
           (setf (test-ledger-token ledger) token (test-ledger-generation ledger) gen
                 (test-ledger-physical ledger) nil (test-ledger-outcome ledger) nil)
           (list :drawn token ledger)))))
    ((fn-ros-physical fn-ros-outcome)
     (destructuring-bind (token receipt ledger) args
       (cond ((not (equal token (test-ledger-token ledger))) (list :stale ledger))
             ((eq subject 'fn-ros-physical)
              (check (member receipt '(:terminal :no-actor-created)) "only affirmative physical observation")
              (setf (test-ledger-physical ledger) receipt)
              (if (test-ledger-outcome ledger)
                  (progn (setf (test-ledger-token ledger) nil) (list :settled ledger))
                (list :pending ledger)))
             ((not (eql receipt (test-ledger-generation ledger))) (list :stale ledger))
             (t (setf (test-ledger-outcome ledger) receipt)
                (if (test-ledger-physical ledger)
                    (progn (setf (test-ledger-token ledger) nil) (list :settled ledger))
                  (list :pending ledger))))))
    (otherwise (error "unexpected mock dispatch ~s" subject))))

(defun funded-service ()
  (let ((service (%make-fnn-owner-service)))
    (fnn-owner-syncer-install service 12 1048576) service))

;; Result is ready while the physical join primitive refuses a still-live
;; cleanup. Only physical join later invokes the affirmative callback.
(let* ((s (funded-service)) (cleanup (sb-thread:make-semaphore :count 0))
       (release (sb-thread:make-semaphore :count 0))
       (grant (fnn-owner-syncer-issue s 7 :captured-job)) (*calls* nil))
  (multiple-value-bind (worker actor)
      (fnn-owner-spawn-syncer s (list :captured-job grant)
       (lambda () (unwind-protect nil
                    (sb-thread:signal-semaphore cleanup) (wait-label release)))
       nil (lambda (physical) (fnn-owner-syncer-physical s grant physical)))
    (wait-label cleanup)
    (fnn-owner-syncer-outcome s grant 7)
    (check (and (member grant (fnn-owner-service-syncer-grants s))
                (not (test-ledger-physical (fnn-owner-service-syncer-ledger s))))
           "operation result alone retains native grant/job")
    (check (not (fnn-owner-actor-join s worker :timeout 0)) "timeout while cleanup held")
    (check (and (registered s actor) (member grant (fnn-owner-service-syncer-grants s)))
           "timeout cannot settle grant or actor")
    (sb-thread:signal-semaphore release)
    (check (fnn-owner-actor-join s worker) "physical return settles after outcome")
    (check (null (fnn-owner-service-syncer-grants s)) "both receipts release native grant")
    (let ((before (length *calls*)))
      (check (fnn-owner-actor-join s worker) "duplicate physical readout")
      (check (= before (length *calls*)) "duplicate physical join never calls ledger twice"))))

;; No child creation emits :no-actor-created, but outcome is still required.
(let* ((s (funded-service)) (grant (fnn-owner-syncer-issue s 8 :job))
       (*fnn-actor-thread-maker* (lambda (&rest args) (declare (ignore args)) (error "maker failed"))))
  (check (handler-case (progn (fnn-owner-spawn-syncer s (list grant) (lambda () nil) nil
                               (lambda (physical) (fnn-owner-syncer-physical s grant physical))) nil)
           (error () t)) "maker failure returns")
  (check (and (null (fnn-owner-service-actors s))
              (eq (test-ledger-physical (fnn-owner-service-syncer-ledger s)) :no-actor-created)
              (member grant (fnn-owner-service-syncer-grants s)))
         "no-child physical receipt retains grant until operation consumed")
  (fnn-owner-syncer-outcome s grant 8)
  (check (null (fnn-owner-service-syncer-grants s)) "failed spawn settles both receipts"))

;; Post-create failure cannot synthesize no-child. A no-op terminator leaves
;; a real parked worker; operation completion still leaves its draw held.
(let* ((s (funded-service)) (grant (fnn-owner-syncer-issue s 9 :job))
       (*fnn-actor-start-signal* (lambda (&rest args) (declare (ignore args)) (error "signal failed")))
       (*fnn-actor-thread-terminator* (lambda (&rest args) (declare (ignore args)) nil)))
  (check (handler-case (progn (fnn-owner-spawn-syncer s (list grant) (lambda () nil) nil
                               (lambda (physical) (fnn-owner-syncer-physical s grant physical))) nil)
           (error () t)) "postcreate failure returns without fake physical receipt")
  (fnn-owner-syncer-outcome s grant 9)
  (check (and (not (test-ledger-physical (fnn-owner-service-syncer-ledger s)))
              (member grant (fnn-owner-service-syncer-grants s)))
         "postcreate failure retains typed/native custody until termination")
  (let ((worker (fnn-owner-actor-thread (first (fnn-owner-service-actors s)))))
    (sb-thread:terminate-thread worker)
    (check (fnn-owner-actor-join s worker) "postcreate eventual join emits terminal")
    (check (null (fnn-owner-service-syncer-grants s)) "eventual both receipts settle once")))
(format t "native_syncer_custody_raw: PASS recording dispatch over actual grant/lifecycle consumers~%")
