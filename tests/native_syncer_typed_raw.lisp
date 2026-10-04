;;; Run inside scoped ACL2 with resource-syncer included. This fixture uses
;;; actual normal fnn-call/entry-guard/counterpart dispatch and private concrete
;;; ledger instances; no mock accounting method or raw entry escape.
(load "tests/native_actor_envelope_raw.lisp")
(in-package "ACL2")

(load-deployed-forms "host/native/io.lisp"
 '((defun fnn-counterpart)
   (defun fnn-guard-conjuncts) (defun fnn-entry-guard-spec)
   (defun fnn-entry-guard-describe) (defun fnn-entry-guard)
   (defun fnn-call) (defun fnn-core)))
;; The dispatcher, its table and traps (D40): host/native/raw-trap.lisp.
(load "host/native/raw-trap.lisp")
(defvar *fnn-entry-guard-specs* (make-hash-table))
;; The six producer guards are T. No non-stobj kind recognizer is consulted.
(defvar *fn-entry-guard-kinds* nil)
(check (handler-case (progn (fnn-core 'create-fn-resource-ledger) nil)
         (fnn-store-fault () t))
       "unregistered creator counterpart refuses private allocation")
(format t "native_syncer_creator_counterpart_refutation: PASS expected ACL2 refusal~%")
;; The declaration is validated against actual loaded world by both definterface
;; and the same native installation function that creates image dispatch.
(check (= (fnn-install-raw-dispatch :report nil) 1) "validated exact creator ABI installed")
(setf *fnn-dispatch-counterpart* t)
(check (and (fnn-raw-dispatch-creator-p 'create-fn-resource-ledger)
            (not (fnn-raw-dispatch-creator-p 'fn-ros-issue)))
       "only actual registered creator allocation survives counterpart selection")
(load-deployed-forms "host/native/owner.lisp"
 '((defstruct (fnn-syncer-grant (:constructor %make-fnn-syncer-grant)))
   (defun fnn-owner-custody-trace)
   (defun fnn-owner-syncer-install) (defun fnn-owner-syncer-issue)
   (defun fnn-owner-syncer-receipt) (defun fnn-owner-syncer-abort)
   (defun fnn-owner-syncer-abandon) (defun fnn-owner-syncer-physical)
   (defun fnn-owner-syncer-outcome) (defun fnn-owner-members-named)
   (defun fnn-owner-complete-generation) (defun fnn-owner-syncer-drained-p)))

;; Shutdown needs both typed idleness and discarded native custody. A ledger
;; with no active draw alone cannot discharge a retained captured object.
(let ((s (%make-fnn-owner-service)))
  (check (fnn-owner-syncer-drained-p s) "startup with no issued grant has no syncer debt")
  (fnn-owner-syncer-install s 12 1048576)
  (check (fnn-owner-syncer-drained-p s) "installed idle projection can drain")
  (setf (fnn-owner-service-syncer-grants s) (list (%make-fnn-syncer-grant :job :retained)))
  (check (not (fnn-owner-syncer-drained-p s)) "idle typed ledger cannot discard native custody")
  (setf (fnn-owner-service-syncer-grants s) nil)
  (check (fnn-owner-syncer-drained-p s) "actual native discard permits idle observation"))

;; Actual typed producer issue is held through consumed outcome + failed live
;; join. Terminal physical join settles and removes native grant only once.
(let* ((s (%make-fnn-owner-service)) (cleanup (sb-thread:make-semaphore :count 0))
       (release (sb-thread:make-semaphore :count 0)))
  (fnn-owner-syncer-install s 12 1048576)
  (let ((grant (fnn-owner-syncer-issue s 7 :captured-job)))
    (check (equal (fnn-syncer-grant-token grant) '(:resource :owner 2 1))
           "actual counterpart produces typed resource token before spawn")
    (multiple-value-bind (worker actor)
        (fnn-owner-spawn-syncer s (list :captured-job grant)
         (lambda () (unwind-protect nil
                      (sb-thread:signal-semaphore cleanup) (wait-label release)))
         nil (lambda (physical) (fnn-owner-syncer-physical s grant physical)))
      (wait-label cleanup)
      (check (eq (fnn-owner-syncer-outcome s grant 7) :pending)
             "actual outcome without physical receipt retains draw")
      (check (not (fnn-owner-syncer-drained-p s))
             "actual typed draw still held")
      (check (not (fnn-owner-actor-join s worker :timeout 0)) "actual live timed-out join")
      (check (and (registered s actor) (member grant (fnn-owner-service-syncer-grants s))
                  (not (fnn-owner-syncer-drained-p s)))
             "actual live join cannot settle typed or native custody")
      (sb-thread:signal-semaphore release)
      (check (fnn-owner-actor-join s worker) "actual terminal physical join")
      (check (and (null (fnn-owner-service-syncer-grants s))
                  (fnn-owner-syncer-drained-p s))
             "actual typed ledger settles both receipts")
      (check (fnn-owner-actor-join s worker) "duplicate actual join")
      (check (fnn-owner-syncer-drained-p s)
             "duplicate observation leaves drained ledger"))))

;; Actual no-child maker failure records only physical receipt, then the
;; consumed fault outcome settles once. Slot generation changes on next issue.
(let ((s (%make-fnn-owner-service)))
  (fnn-owner-syncer-install s 12 1048576)
  (let* ((grant (fnn-owner-syncer-issue s 8 :captured-job))
         (*fnn-actor-thread-maker* (lambda (&rest args) (declare (ignore args)) (error "no child"))))
    (check (handler-case (progn (fnn-owner-spawn-syncer s (list grant) (lambda () nil) nil
                                 (lambda (physical) (fnn-owner-syncer-physical s grant physical))) nil)
             (error () t)) "actual maker failure")
    (check (and (null (fnn-owner-service-actors s))
                (not (fnn-owner-syncer-drained-p s)))
           "actual no-child receipt retains consumed-outcome debt")
    (check (eq (fnn-owner-syncer-outcome s grant 8) :settled) "actual no-child plus outcome settles"))
  (let ((next (fnn-owner-syncer-issue s 9 :next-job)))
    (check (equal (fnn-syncer-grant-token next) '(:resource :owner 2 2))
           "actual slot generation is distinct from operation generation")
    (check (eq (fnn-owner-syncer-physical s next :no-actor-created) :pending) "physical first retains")
    (check (eq (fnn-owner-syncer-outcome s next 9) :settled) "reverse actual order settles")))
(format t "native_syncer_typed_raw: PASS actual validated creator allocation, semantic counterparts and typed custody~%")


;; The actual producer helper issues under the actual private fn-otb ledger;
;; parent consumes the actual fn-oqw receipt before resource outcome settlement.
(let ((s (%make-fnn-owner-service)))
  (fnn-owner-syncer-install s 12 1048576)
  (destructuring-bind (issued gen ledger)
      (fnn-core 'fn-otb-issue (fnn-core 'fn-otb-ledger-init))
    (check (eq issued :issued) "actual operation identity issued")
    (let ((*fnn-actor-thread-maker*
            (lambda (thunk &rest args)
              (check (not (fnn-owner-syncer-drained-p s))
                     "actual start-syncer funded before primitive spawn")
              (apply #'sb-thread:make-thread thunk args))))
      (multiple-value-bind (worker result actor grant) (fnn-owner-start-syncer s gen :actual-job)
        (check (fnn-owner-actor-join s worker) "actual start-syncer terminal physical join")
        (check (and actor grant (equal (car result) (list gen :done))
                    (member grant (fnn-owner-service-syncer-grants s)))
               "actual producer keeps outcome debt after physical join")
        (multiple-value-bind (outcome answer returned)
            (fnn-owner-complete-generation ledger (first (car result)) (second (car result)) nil)
          (declare (ignore returned))
          (check (and (eq outcome :fenced) (null answer)) "actual fn-oqw receipt consumed")
          (check (eq (fnn-owner-syncer-outcome s grant (first (car result))) :settled)
                 "actual producer grant settles actual consumed operation"))))))

;; Release THEN fail: child reports :done before maker's caller sees
;; startup failure. Its real retained result must stay :done/:fenced, not be
;; replaced with blanket :fault. Parent arms one shot, then physical join
;; consumes that actual receipt in the same fn-oqw helper used by the driver.
(let ((s (%make-fnn-owner-service)) (seen nil))
  (fnn-owner-syncer-install s 12 1048576)
  (destructuring-bind (issued gen ledger)
      (fnn-core 'fn-otb-issue (fnn-core 'fn-otb-ledger-init))
    (declare (ignore issued))
    (let* ((grant (fnn-owner-syncer-issue s gen :completed-job))
           (*fnn-actor-start-signal*
             (lambda (latch)
               (sb-thread:signal-semaphore latch)
               (sb-thread:with-mutex ((fnn-owner-service-commit-lock s))
                 (loop until (fnn-owner-service-synced s)
                       do (sb-thread:condition-wait (fnn-owner-service-commit-ready s)
                                                    (fnn-owner-service-commit-lock s))))
               (error "signal released child then failed")))
           (*fnn-actor-thread-terminator* (lambda (&rest args) (declare (ignore args)) nil)))
      (check (handler-case (progn (fnn-owner-start-syncer s gen :completed-job grant) nil)
               (error () t)) "after-release startup failure observed")
      (check (equal (car (fnn-syncer-grant-result grant)) (list gen :done))
             "retained actual result survived starter unwind")
      (fnn-owner-syncer-abort s grant
       (lambda ()
         (let ((r (car (fnn-syncer-grant-result grant))))
           (multiple-value-bind (outcome answer returned)
               (fnn-owner-complete-generation ledger (first r) (second r) nil)
             (declare (ignore answer returned))
             (push outcome seen)
             (fnn-owner-syncer-outcome s grant (first r))))))
      (let ((actor (first (fnn-owner-service-actors s))))
        (when actor (fnn-owner-actor-join s (fnn-owner-actor-thread actor))))
      (check (and (equal seen '(:fenced)) (null (fnn-owner-service-syncer-grants s))
                  (fnn-owner-syncer-drained-p s))
             "reported completed operation preserved through failed starter physical return"))))
(format t "native_syncer_typed_producer_raw: PASS actual start-syncer/fn-oqw/after-release consumer~%")


;; The new abandoned-parent consumer uses the actual private operation ledger,
;; actual typed resource methods, selected dispatch and physical actor callback.
;; I/O result/fence are recording boundaries, as in the schedules above.
(defvar *abandon-fences* 0)
(defun fnn-owner-fence-service (service)
  (declare (ignore service)) (incf *abandon-fences*))
(let ((original (symbol-function 'fnn-owner-batch-job)))
  (unwind-protect
       (dolist (final '(:done :uncertain :fault))
         (dolist (physical-first '(nil t))
           (let ((s (%make-fnn-owner-service)) (*abandon-fences* 0))
             (setf (symbol-function 'fnn-owner-batch-job)
                   (let ((final final))
                     (lambda (service job) (declare (ignore service job))
                       (values final nil))))
             (fnn-owner-syncer-install s 12 1048576)
             (destructuring-bind (issued gen ledger)
                 (fnn-core 'fn-otb-issue (fnn-core 'fn-otb-ledger-init))
               (check (eq issued :issued) "actual abandoned operation is issued")
               (multiple-value-bind (worker result actor grant)
                   (fnn-owner-start-syncer s gen :abandoned-job)
                 (declare (ignore result actor))
                 (when physical-first (fnn-owner-actor-join s worker))
                 (fnn-owner-syncer-abandon s grant ledger nil)
                 (unless physical-first
                   (check (not (fnn-owner-syncer-drained-p s))
                          "actual abandonment alone retains physical custody")
                   (fnn-owner-actor-join s worker))
                 (check (fnn-owner-syncer-drained-p s)
                        "actual typed grant drains after both abandonment receipts")
                 (check (= *abandon-fences* (if (eq final :uncertain) 1 0))
                        "actual fn-oqw outcome preserves uncertainty across abandonment"))))))
    (setf (symbol-function 'fnn-owner-batch-job) original)))
(format t "native_syncer_typed_abandon_raw: PASS six actual typed abandonment schedules~%")

;; Enabled diagnostic failure cannot orphan a successfully issued draw or
;; prevent the actual independent receipts from settling its private ledger.
(let ((old-selector (symbol-function 'fnn-developer-selector))
      (old-err (symbol-function 'fnn-err)))
  (unwind-protect
      (progn
        (setf (symbol-function 'fnn-developer-selector)
              (lambda (name) (and (string= name "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE") "1"))
              (symbol-function 'fnn-err)
              (lambda (&rest args) (declare (ignore args)) (error "diagnostic unavailable")))
        (let ((s (%make-fnn-owner-service)))
          (fnn-owner-syncer-install s 12 1048576)
          (let ((grant (fnn-owner-syncer-issue s 20 :no-child-created)))
            (check (eq (fnn-owner-syncer-physical s grant :no-actor-created) :pending)
                   "failed trace cannot turn one receipt into settlement")
            (check (and (eq (fnn-owner-syncer-outcome s grant 20) :settled)
                        (fnn-owner-syncer-drained-p s) (null (fnn-owner-service-stopping s)))
                   "enabled trace failure cannot change custody settlement or stop the service"))))
    (setf (symbol-function 'fnn-developer-selector) old-selector
          (symbol-function 'fnn-err) old-err)))
(format t "native_syncer_diagnostic_failure_raw: PASS actual ledger unchanged~%")
