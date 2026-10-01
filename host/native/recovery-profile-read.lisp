;;; Finite primitive realizer for the early controller's exact issued effect.
;;; The image binding is preconstructed and obtained by the actual live getter.
;;; No constructor, identity, bounds, retry, EOF or cleanup decision lives here.
;;; The selected operation envelope must cover C-string lowering and first use.
(in-package "ACL2")

(defun fnn-recovery-profile-perform (effect binding)
  "Return primitive word, actual signed observation and retained descriptor.
BINDING is the actual image holder; its SAME backing and FD remain rooted."
  (handler-case
      (ecase (first effect)
        (:file-open
         (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :open-issued)
         (let ((opened
                 (sb-alien:alien-funcall
                  (sb-alien:extern-alien "open"
                    (function sb-alien:int sb-alien:c-string sb-alien:int))
                  (third effect) (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
           ; Store before any observation/return; negative observations are
           ; retained too and classified only by the actual core subject.
           (setf (fnn-runtime-profile-envelope-binding-fd binding) opened
                 (fnn-runtime-profile-envelope-binding-io-phase binding) :open-observed)
           (values :opened opened opened)))
        (:file-read
         (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :read-issued)
         (let* ((backing (fnn-runtime-profile-envelope-binding-workspace binding))
                (fd (fnn-runtime-profile-envelope-binding-fd binding))
                (got
                  (sb-sys:with-pinned-objects (backing)
                    (sb-alien:alien-funcall
                     (sb-alien:extern-alien "pread"
                       (function sb-alien:long sb-alien:int sb-alien:system-area-pointer
                                 sb-alien:unsigned-long sb-alien:long))
                     fd (sb-sys:sap+ (sb-sys:vector-sap backing) (third effect))
                     (fifth effect) (third effect)))))
           (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :read-observed)
           (values :read got fd)))
        (:file-close
         (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :close-issued)
         (let* ((fd (fnn-runtime-profile-envelope-binding-fd binding))
                (closed
                  (sb-alien:alien-funcall
                   (sb-alien:extern-alien "close" (function sb-alien:int sb-alien:int)) fd)))
           ; Definite and unknown close both retain the descriptor/source
           ; identity until the registered core completion has been recorded.
           (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :close-observed)
           (values :closed closed fd)))
      )
    (serious-condition (condition)
      (declare (ignore condition))
      (setf (fnn-runtime-profile-envelope-binding-io-phase binding) :fenced)
      ; A condition is not a fabricated syscall result. This explicit unknown
      ; observation fences the core while retaining the actual descriptor.
      ; Never render or rethrow it through the general command error path.
      (values :unknown 0 (fnn-runtime-profile-envelope-binding-fd binding)))))
