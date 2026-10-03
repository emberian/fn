;;; Run inside scoped ACL2 with resource-syncer included. This fixture uses
;;; actual normal fnn-call/entry-guard/counterpart dispatch and private concrete
;;; ledger instances; no mock accounting method or raw entry escape.
(load "tests/native_actor_envelope_raw.lisp")
(in-package "ACL2")

(load-deployed-forms "host/native/io.lisp"
 '((defun fnn-counterpart) (defun fnn-dispatch-function) (defun fnn-install-raw-dispatch)
   (defun fnn-guard-conjuncts) (defun fnn-entry-guard-spec)
   (defun fnn-entry-guard-describe) (defun fnn-entry-guard)
   (defun fnn-call) (defun fnn-core)))
(defvar *fnn-dispatch-counterpart* nil)
(defvar *fnn-raw-dispatch* (make-hash-table))
(defvar *fnn-startup-creators* (make-hash-table))
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
(check (and (gethash 'create-fn-resource-ledger *fnn-startup-creators*)
            (not (gethash 'fn-ros-issue *fnn-startup-creators*)))
       "only actual registered creator allocation survives counterpart selection")
(load-deployed-forms "host/native/owner.lisp"
 '((defstruct (fnn-syncer-grant (:constructor %make-fnn-syncer-grant)))

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
