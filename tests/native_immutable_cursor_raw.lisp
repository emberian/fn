;;; Incremental actual initialized-cache NEWNEWS consumer. This fixture uses
;;; its admitted preconfigured metadata stream, not the newer WMC selector.
;;; Run in the private developer owner; counters are PROCESS inclusive because
;;; idle owner threads remain present. No retained-heap or GC pricing claim.
(in-package "ACL2")

(defun fnic-function (name &optional observer)
  (let ((counterpart (find-symbol (symbol-name name) "ACL2_*1*_ACL2")))
    (unless (and (member (getpropc name 'symbol-class nil (w *the-live-state*))
                        (if observer '(:common-lisp-compliant :ideal)
                          '(:common-lisp-compliant)))
                 counterpart (fboundp counterpart)
                 (compiled-function-p (symbol-function counterpart)))
      (error "actual compiled counterpart unavailable: ~s" name))
    (symbol-function counterpart)))

(defmacro fnic-with-route ((sharedp) &body body)
  (let ((old (gensym "ORIGINAL")))
    `(let ((,old (symbol-function 'fn-cur-make)))
       (unwind-protect
            (progn
              (when ,sharedp
                (setf (symbol-function 'fn-cur-make)
                      (symbol-function 'fn-cur-shared-make)))
              ,@body)
         (setf (symbol-function 'fn-cur-make) ,old)))))

(defun fnic-drain (cur live step)
  (let ((transitions 0))
    (loop while (funcall live cur) do
      ;; Diagnostic runaway guard only, not a production input ceiling.
      (assert (< transitions 16384))
      (incf transitions)
      (multiple-value-bind (octets next visits phase)
          (funcall step cur 1 1 nil nil)
        (declare (ignore octets visits phase))
        (setf cur next)))))

(defun fnic-run ()
  (let* ((step (fnic-function 'fn-nnw-stream-step))
         (live (fnic-function 'fn-nnw-meta-livep))
         (remaining (fnic-function 'fn-nnw-stream-remaining t))
         (metadata (fnic-function 'fn-nnw-cursor))
         (article (fnic-function 'fn-make-article))
         (cur (fnic-function 'fn-cur-make))
         (original (symbol-function 'fn-cur-make))
         (articles (loop for i below 8 collect
                     (funcall article
                       (format nil "<~d-~a@x>" i (make-string 120 :initial-element #\a))
                       '(13 10 13 10 65) '("fn.test") '(("fn.test" . 1)) 1 5)))
         (progress (funcall metadata '("fn.test") 0 articles nil 7))
         (initial (funcall cur '(:snapshot :probe-root) progress nil nil))
         (old initial) (new initial) (got nil) (transitions 0)
         (expected (funcall remaining initial nil nil))
         (*fnn-trace-state* nil) (*fnn-trace-parent* nil)
         (*fnn-trace-operation* nil) (*fnn-trace-connection-generation* nil))
    (fnic-function 'fn-cur-shared-make)
    (loop while (funcall live old) do
      (assert (< transitions 16384))
      (assert (equal old new))
      (let ((a (multiple-value-list (funcall step old 1 1 nil nil)))
            (b (fnic-with-route (t)
                 (multiple-value-list (funcall step new 1 1 nil nil)))))
        (assert (equal a b))
        (assert (<= (third a) 1))
        (dolist (byte (first a)) (push byte got))
        (setf old (second a) new (second b))
        (incf transitions)))
    (assert (not (funcall live new)))
    (assert (equal old new))
    (assert (equal (nreverse got) expected))
    (format t "~%FN_CURSOR_CONSUMER {\"scope\":\"initialized-cache-preconfigured-newnews\",\"steps\":~d,\"output_octets\":~d,\"equal_every_step_and_reply\":true,\"replays\":32}~%"
            transitions (length expected))
    (fnn-trace-start :capacity 4 :allocation :process)
    (unwind-protect
         (dolist (sharedp '(nil t))
           (fnic-with-route (sharedp)
             (dotimes (i 4) (fnic-drain initial live step))
             (sb-ext:gc :full t)
             (fnn-trace-span ((if sharedp :shared-cursor :legacy-cursor) :operation 1)
               (dotimes (i 32) (fnic-drain initial live step)))))
      (assert (eq (symbol-function 'fn-cur-make) original)))
    (fnn-trace-report *standard-output*)
    (format t "NATIVE_IMMUTABLE_CURSOR_PASS~%")
    :passed))
