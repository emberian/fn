;;; Load in the selected test image after host definitions, before opening it.
;;; One stream orders control, physical effects and the exact death ordinal.
;;; The existing physical recorder retains attempted and returned writes apart.
(in-package "ACL2")
(load "tests/native-device-effects-capture.lsp")
(defvar *fn2-device-cut-host* nil)
(defun fn2-device-cut-record (row)
  (sb-thread:with-mutex (*fn2-device-evidence-lock*)
    (fn2-device-evidence-record-locked row)))
(defun fn2-device-cut-host (host)
  (unless (fn2-nhost-trace host) (error "Cut correspondence requires full envelope capture"))
  (when (and *fn2-device-cut-host* (not (eq host *fn2-device-cut-host*)))
    (error "Cut capture cannot combine different hosts"))
  (setf *fn2-device-cut-host* host))
(let ((original (symbol-function 'fn2-init-executor)))
  (setf (symbol-function 'fn2-init-executor)
    (lambda (profile mode value core)
      (multiple-value-prog1 (funcall original profile mode value core)
        (unless (and (eq mode :echo) (null value))
          (error "Cut replay supports the selected existing-image initialization"))
        (fn2-device-cut-record (list :profile profile))))))
(let ((original (symbol-function 'fn2-boot-start)))
  (setf (symbol-function 'fn2-boot-start)
    (lambda (create size core)
      (multiple-value-bind (code after) (funcall original create size core)
        (fn2-device-cut-record (list :boot-start create size code))
        (values code after)))))
(let ((original (symbol-function 'fn2-n-record)))
  (setf (symbol-function 'fn2-n-record)
    (lambda (host entry)
      (fn2-device-cut-host host)
      (multiple-value-prog1 (funcall original host entry)
        (fn2-device-cut-record (list :control entry))))))
(setf *fn2-n-boundary-observer*
  (lambda (host ordinal label slot generation selected)
    (fn2-device-cut-host host)
    (if selected
        (progn
          ;; Freeze the evidence prefix until the actual boundary exits. A
          ;; concurrent already-begun syscall stays uncertain if no return was
          ;; recorded; this does not stop or retry its physical operation.
          (sb-thread:grab-mutex *fn2-device-evidence-lock*)
          (fn2-device-evidence-record-locked
           (list :boundary ordinal label slot generation selected)))
      (fn2-device-cut-record (list :boundary ordinal label slot generation selected)))))
