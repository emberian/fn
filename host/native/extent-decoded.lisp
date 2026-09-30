;;; Actual stored-DEFLATE window dispatcher. Loaded after extent.lisp by
;;; the physical integration, which admits and owns every supplied buffer.
;;; This driver does not admit jobs or allocate a whole compressed payload.
(in-package "ACL2")

(defun fnn-extent-decoded-window-drive
    (fd token incarnation input hash zin win tab out window work-permitted-p)
  "Drive the actual combined core; only :READY can return a decoded result.
The physical owner supplies the complete captured token, funded fixed
buffers and a predicate checking its exact running lease. The core derives
all coordinates and the shipped dictionary from that token."
  (unless (funcall work-permitted-p) (return-from fnn-extent-decoded-window-drive nil))
  (let ((z nil))
    (destructuring-bind (next hash1 zin1 win1 tab1 out1)
        (fnn-core-cold-values 'fn-pwz-begin token incarnation hash zin win tab out)
      (setq z next hash hash1 zin zin1 win win1 tab tab1 out out1))
    (loop
      ;; Cancellation revokes future bounded steps. The surrounding worker
      ;; retains its buffers/charges until actual return and final borrowing.
      (unless (funcall work-permitted-p) (return nil))
      (let ((action (fnn-core-cold-single 'fn-ewz-next-action z hash)))
        (case (first action)
          (:codec
           (destructuring-bind (decision next zin1 win1 tab1 out1 window1)
               (fnn-core-cold-values 'fn-ewz-codec-tick z input zin win tab out window)
             (declare (ignore decision))
             (setq z next zin zin1 win win1 tab tab1 out out1 window window1)))
          (:read
           ;; The core retains INPUT across codec quanta. Only its :READ
           ;; action authorizes overwriting the fixed input buffer.
           (let* ((effect (second action))
                  (io-status (fnn-extent-window-pread fd input (fifth effect) (sixth effect))))
             (destructuring-bind (answer next hash1 window1)
                 (fnn-core-cold-values 'fn-ewz-read effect io-status z input hash window)
               (declare (ignore answer))
               (setq z next hash hash1 window window1))))
          (:tick
           (destructuring-bind (answer next hash1)
               (fnn-core-cold-values 'fn-ewz-hash-tick z hash zin)
             (declare (ignore answer))
             (setq z next hash hash1)))
          ((:ready :refused) (return (list z window)))
          (otherwise (fnn-fault "invalid decoded window core action ~s" action)))))))

(defun fnn-extent-decoded-window-realize-octet (file eoff elen poff compressed trailer decoded dict i)
  "The actual scalar getter either borrows a returned decoded byte or throws
its full core-selected cold descriptor while the captured owner is held."
  (let* ((descriptor (fnn-core-cold-single 'fn-pwz-cold-descriptor
                       file eoff elen poff compressed trailer decoded dict i))
         (dict-id (fnn-core-cold-single 'fn-pwz-nth 8 descriptor)))
    (multiple-value-bind (word byte)
        (if *fnn-extent-window-worker*
            (fnn-extent-decoded-window-byte-at
              *fnn-extent-window-worker* *fnn-extent-window-token*
              file eoff elen poff compressed trailer decoded dict-id i)
          (values :unavailable nil))
      (cond ((eq word :byte) byte)
            ((member word '(:cancelled :stale-job))
             (throw 'fnn-extent-window-refused (values word nil nil nil)))
            ((eq word :unavailable) (throw 'fnn-extent-cold descriptor))
            (t (error 'fnn-extent-fault
                      :message "arena-extent-read: decoded window was not an authenticated returned result"))))))

(defun fn-durable-realize-lz-octet (file eoff elen poff compressed trailer decoded dict i)
  (if *fnn-extent-window-mode*
      (fnn-extent-decoded-window-realize-octet file eoff elen poff compressed trailer decoded dict i)
    (fnn-core 'fn-oct-nth i
      (fn-durable-realize-lz file eoff elen poff compressed trailer decoded dict))))

(defun acl2_*1*_acl2::fn-durable-realize-lz-octet (file eoff elen poff compressed trailer decoded dict i)
  (fn-durable-realize-lz-octet file eoff elen poff compressed trailer decoded dict i))
