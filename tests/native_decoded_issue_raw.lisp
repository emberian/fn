;;; Actual native reservation/enqueue function; typed admission is a recording
;;; boundary. Actual same-pool projection/overcommit lives in source probe.
(load "tests/native_decoded_worker_raw.lisp")
(in-package "ACL2")
(load-deployed-forms "host/native/extent.lisp"
 '((defvar *fnn-cold-free*) (defvar *fnn-cold-stopping*)
   (defun fnn-extent-executor-enqueue) (defun fnn-extent-issue-window)))
(defvar *issue-mode* nil)
(defun fnn-core (subject &rest args)
  (assert (eq subject 'fn-owner-page-decoded-window-price-status))
  (assert (equal args '(:descriptor))) :unpriced-decoded-window)
(defun fnn-call (subject &rest args)
  (assert (eq subject 'fn-owner-page-decoded-window-acquire-projected))
  (assert (equal args '(:row :descriptor :same-pool)))
  (assert (null *fnn-cold-free*))
  (case *issue-mode*
    (:refuse (list :unpriced-decoded-window :row nil :unpriced :same-pool))
    (:assigned (list :assigned :bound :token :partial-fixed-storage :same-pool))
    (:binding-fail (list :stale-job :row :token :partial-fixed-storage :same-pool))
    (:torn (error "injected issuer escape"))))
(dolist (mode '(:refuse :assigned :binding-fail :torn))
  (let* ((worker (%make-fnn-cold-worker :row :row :phase :idle))
         (*fnn-cold-free* worker) (*fnn-cold-stopping* nil) (*issue-mode* mode))
    (case mode
      (:refuse
       (multiple-value-bind (token word result) (fnn-extent-issue-window :descriptor)
         (assert (and (null token) (null result) (eq word :unpriced-decoded-window)
                      (eq *fnn-cold-free* worker) (eq (fnn-cold-worker-phase worker) :idle)))))
      (:assigned
       (multiple-value-bind (token word result) (fnn-extent-issue-window :descriptor)
         (assert (and (eq token :token) (eq word :admitted) (eq worker result)
                      (null *fnn-cold-free*) (eq (fnn-cold-worker-phase worker) :queued)
                      (eq (fnn-cold-worker-scope worker) :partial-fixed-storage)))))
      (otherwise
       (assert (handler-case (progn (fnn-extent-issue-window :descriptor) nil) (serious-condition () t)))
       (assert (and (null *fnn-cold-free*) (eq (fnn-cold-worker-scope worker) :partial-fixed-storage)
                    (eq (fnn-cold-worker-phase worker) (if (eq mode :torn) :issuing :binding-fault))))
       (when (eq mode :binding-fail) (assert (eq (fnn-cold-worker-token worker) :token)))))))
(format t "native_decoded_issue_raw: PASS reserve-before-issuer/partial scope/full refusal/failed binding/torn draw~%")
