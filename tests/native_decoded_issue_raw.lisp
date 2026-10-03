;;; Actual native reservation/enqueue function; typed admission is a recording
;;; boundary. Actual same-pool projection/overcommit lives in source probe.
(load "tests/native_decoded_worker_raw.lisp")
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
(defun fnn-extent-pool-funded-p ()
  (harness-stub-reached 'fnn-extent-pool-funded-p "host/native/extent.lisp"))
(defun fnn-extent-window-cancel (worker token)
  (declare (ignorable worker token))
  (harness-stub-reached 'fnn-extent-window-cancel "host/native/extent.lisp"))
(defun fnn-owner-cold-window-result-locked (service read)
  (declare (ignorable service read))
  (harness-stub-reached 'fnn-owner-cold-window-result-locked "host/native/owner.lisp"))
;;; ---- derived stubs: END ----
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

;;; Actual owner registration precedes a notification that wakes a real child
;;; and then signals. No dependency or token may disappear on that escape.
(defvar *fnn-response-capture* nil)
(defvar *fnn-output-grant* nil)
(load-deployed-forms "host/native/owner.lisp"
 '((defstruct (fnn-owner-service (:constructor %make-fnn-owner-service)))
   (defstruct (fnn-response-capture (:constructor %make-fnn-response-capture)))
   (defstruct (fnn-owner-cold-read (:constructor %make-fnn-owner-cold-read)))
   (defstruct (fnn-output-dependency (:constructor %make-fnn-output-dependency)))
   (defstruct (fnn-output-grant (:constructor %make-fnn-output-grant)))
   (defun fnn-owner-cold-enqueue-locked) (defun fnn-owner-cold-remove-locked)
   (defun fnn-owner-output-dependency) (defun fnn-owner-cold-issue-locked)))
(defvar *fnn-response-capture* nil)
(defvar *fnn-output-grant* nil)
(defun fnn-core (subject &rest args)
  (assert (equal args '(:descriptor)))
  (case subject
    (fn-owner-page-window-discovery-kind :decoded-window)
    (fn-owner-page-decoded-window-price-status :unpriced-decoded-window)
    (otherwise (error "unexpected issue subject ~s" subject))))
(dolist (mode '(:refuse :torn :binding-fail :wake-fault))
  (let* ((worker (%make-fnn-cold-worker :row :row :phase :idle))
         (*fnn-cold-free* worker) (*fnn-cold-stopping* nil)
         (*issue-mode* (if (eq mode :wake-fault) :assigned mode))
         (service (%make-fnn-owner-service :exit-code 0 :output-ledger-lock (sb-thread:make-mutex)))
         (grant (%make-fnn-output-grant :stage :active))
         (*fnn-response-capture* (%make-fnn-response-capture :grant grant))
         (*fnn-output-grant* grant)
         (capture *fnn-response-capture*)
         (broadcast (symbol-function 'sb-thread:condition-broadcast))
         (observed nil) (thread nil))
    (unwind-protect
        (progn
          (when (eq mode :wake-fault)
            (setq thread
              (sb-thread:make-thread
               (lambda ()
                 (sb-thread:with-mutex (*fnn-extent-lock*)
                   (loop until (eq (fnn-cold-worker-phase worker) :queued) do
                     (sb-thread:condition-wait (fnn-cold-worker-ready worker) *fnn-extent-lock*))
                   (let ((read (fnn-response-capture-window-read capture)))
                     (assert (and read (eq read (fnn-owner-service-cold-head service))
                                  (eq (fnn-owner-cold-read-worker read) worker)
                                  (eq (fnn-owner-cold-read-token read) :token)
                                  (= 1 (length (fnn-output-grant-dependencies grant)))))
                     (setq observed t))))))
            (sb-ext:without-package-locks
              (setf (symbol-function 'sb-thread:condition-broadcast)
                    (lambda (queue) (funcall broadcast queue) (error "after real wake")))))
          (case mode
            (:refuse
             (assert (eq :unpriced-decoded-window
                         (fnn-owner-cold-issue-locked service 7 :descriptor)))
             (assert (and (null (fnn-response-capture-window-read *fnn-response-capture*))
                          (null (fnn-owner-service-cold-head service))
                          (null (fnn-output-grant-dependencies grant)))))
            (otherwise
             (assert (handler-case
                         (progn (fnn-owner-cold-issue-locked service 7 :descriptor) nil)
                       (serious-condition () t)))
             (let ((read (fnn-response-capture-window-read *fnn-response-capture*)))
               (assert (and read (eq read (fnn-owner-service-cold-head service))
                            (eq (fnn-owner-cold-read-worker read) worker)))
               (when (eq mode :binding-fail)
                 (assert (and (eq (fnn-owner-cold-read-token read) :token)
                              (eq (fnn-cold-worker-phase worker) :binding-fault)
                              (= 1 (length (fnn-output-grant-dependencies grant)))))))
             (when thread (sb-thread:join-thread thread) (assert observed)))))
      (sb-ext:without-package-locks
        (setf (symbol-function 'sb-thread:condition-broadcast) broadcast)))))
(format t "native_decoded_issue_raw: PASS actual owner capture-before-wake/refusal/torn issuer~%")
