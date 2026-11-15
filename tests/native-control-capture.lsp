;;; Test-only evidence channel. It never syncs/closes the storage descriptor.
;;; Loaded into the selected image immediately before its unchanged main call.
(in-package "ACL2")
(defvar *fn2-control-capture*
  (open (or (sb-ext:posix-getenv "FN2_TEST_CAPTURE") (error "capture path missing"))
        :direction :output :if-exists :error :if-does-not-exist :create))
(defvar *fn2-control-target*
  (let ((text (or (sb-ext:posix-getenv "FN2_TEST_CAPTURE_TARGET") (error "target missing"))))
    (assert (evenp (length text)))
    (loop for i below (length text) by 2
          collect (+ (* 16 (or (digit-char-p (char text i) 16) (error "invalid target")))
                     (or (digit-char-p (char text (1+ i)) 16) (error "invalid target"))))))
(defvar *fn2-control-sent* nil)
(defun fn2-control-capture-write (entry)
  (let ((*print-readably* t) (*print-pretty* nil) (*print-length* nil) (*print-level* nil))
    (write entry :stream *fn2-control-capture*)
    (terpri *fn2-control-capture*)
    (finish-output *fn2-control-capture*)))
(let ((original (symbol-function 'fn2-n-make-host)))
  (setf (symbol-function 'fn2-n-make-host)
    (lambda (profile &rest options)
      (assert (getf options :device-path))
      (fn2-control-capture-write (list :profile (fn2-image-profile profile)))
      (apply original profile options))))
(let ((original (symbol-function 'fn2-boot-start)))
  (setf (symbol-function 'fn2-boot-start)
    (lambda (create size core)
      (multiple-value-bind (code core) (funcall original create size core)
        (fn2-control-capture-write (list :boot-start create size code))
        (values code core)))))
(let ((original (symbol-function 'fn2-n-record)))
  (setf (symbol-function 'fn2-n-record)
    (lambda (host entry)
      ;; The ordinary bounded trace still refuses overflow before recording.
      (funcall original host entry)
      (fn2-control-capture-write entry)
      (when (and (eq (car entry) :post) (= (nth 4 entry) *fn2-event-send-result*))
        ;; This pilot intentionally pauses only on exact successful segments.
        ;; Failed/cancelled consumption cannot be used as a delivery marker.
        (assert (member (nth 5 entry) (list *fn2-outcome-done* *fn2-outcome-short*)))
        (setf *fn2-control-sent* (append *fn2-control-sent* (nth 12 entry)))
        (format t "~%CAPTURE-SEND ~d " (fn2-nhost-trace-count host))
        (dolist (byte (nth 12 entry)) (format t "~2,'0X" byte))
        (terpri) (finish-output)
        (when (equal *fn2-control-sent* *fn2-control-target*)
          (format t "CAPTURE-CUT ~d post-recorded-before-post-boundary~%" (fn2-nhost-trace-count host))
          (finish-output)
          ;; Test-only pause fixes the cut, preventing a truncated final form.
          ;; Parent SIGKILLs this recorded PID; no unwind/storage cleanup runs.
          (sb-thread:wait-on-semaphore (sb-thread:make-semaphore :count 0)))))))
