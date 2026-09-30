(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defconstant +fnn-lock-un+ 8)
(defstruct fnn-log fd spare)
(defstruct fnn-store log lock-fd completion-pending recovery-identity recovery-source)
(defvar *calls* nil)
(defvar *failure* nil)
(defun fnn-close (fd)
 (push (list :close fd) *calls*)
 (when (eql fd *failure*) (error "recorded close uncertainty")))
(defun fnn-flock (fd mode)
 (push (list :flock fd mode) *calls*)
 (when (eq *failure* :unlock) (error "recorded unlock uncertainty")))
(defun fnn-lstat (path) (declare (ignore path)) t)
(defun fnn-unlink (path) (push (list :unlink path) *calls*))
(defun fnn-log-discard-spare (log)
  "Close and unlink a spare that will not be renamed (another index, or the
store closing).  Removing a staged name is never uncertain for the history:
the open ignores and sweeps it."
  (let ((spare (fnn-log-spare log)))
    (when spare
      (destructuring-bind (index path fd) spare
        (declare (ignore index))
        ;; Keep this identity/debt if the physical close is uncertain.
        (fnn-close fd)
        (setf (fnn-log-spare log) nil)
        (ignore-errors (when (fnn-lstat path) (fnn-unlink path)))))))
(defun fnn-store-close (store)
  (setf (fnn-store-completion-pending store) nil)
  (let ((log (fnn-store-log store)))
    (when log
      ;; Physical close failure retains the Store and its recovery aliases.
      (fnn-log-discard-spare log)
      (fnn-close (fnn-log-fd log))
      (setf (fnn-store-log store) nil)))
  (let ((fd (fnn-store-lock-fd store)))
    (when fd
      ;; Retention after uncertainty is not evidence the lock remains held.
      (unwind-protect (fnn-flock fd +fnn-lock-un+)
        (fnn-close fd))
      (setf (fnn-store-lock-fd store) nil)))
  (setf (fnn-store-recovery-identity store) nil
        (fnn-store-recovery-source store) nil))
;; Each attempted close/unlock failure retains recovery aliases. The remaining
;; descriptor fields describe what is known; they do not prove an unlocked
;; lock remains held or authorize automatic reuse/retry after uncertainty.
(dolist (failure '(503 501 502 :unlock))
 (let* ((identity (list :original-context))
        (source (list :issued-recovery-token))
        (spare (list 1 "/recording-stage" 503))
        (log (make-fnn-log :fd 501 :spare spare))
        (store (make-fnn-store :log log :lock-fd 502
                  :completion-pending :owed :recovery-identity identity
                  :recovery-source source))
        (*failure* failure) (*calls* nil))
  (assert (handler-case (progn (fnn-store-close store) nil) (error () t)))
  (assert (eq (fnn-store-recovery-identity store) identity))
  (assert (eq (fnn-store-recovery-source store) source))
  (assert (= (fnn-store-lock-fd store) 502))
  (if (member failure '(503 501))
      (assert (eq (fnn-store-log store) log))
    (assert (null (fnn-store-log store))))
  (if (eql failure 503)
      (progn (assert (eq (fnn-log-spare log) spare))
             (assert (equal *calls* '((:close 503)))))
    (progn (assert (null (fnn-log-spare log)))
           (assert (= (count '(:close 503) *calls* :test #'equal) 1))
           (assert (= (count '(:close 501) *calls* :test #'equal) 1))))
  (when (member failure '(502 :unlock))
   (assert (= (count '(:close 502) *calls* :test #'equal) 1))
   (assert (= (count '(:flock 502 8) *calls* :test #'equal) 1)))
  (format t "PASS close failure ~s retains recovery authority~%" failure)))
(let* ((log (make-fnn-log :fd 501 :spare (list 1 "/recording-stage" 503)))
       (store (make-fnn-store :log log :lock-fd 502
                 :recovery-identity :identity :recovery-source :source))
       (*failure* nil) (*calls* nil))
 (fnn-store-close store)
 (assert (null (fnn-store-log store)))
 (assert (null (fnn-store-lock-fd store)))
 (assert (null (fnn-store-recovery-identity store)))
 (assert (null (fnn-store-recovery-source store)))
 (assert (equal (reverse *calls*) '((:close 503) (:unlink "/recording-stage")
                                   (:close 501) (:flock 502 8) (:close 502))))
 (format t "PASS definite closes clear aliases after observed return~%"))
