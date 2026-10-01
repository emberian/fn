;;; Finite primitive realizer for the early controller's exact issued effect.
;;; Caller retains the actual FD/result before recording it to the controller.
;;; No constructor, identity, bounds, retry, EOF or cleanup decision lives here.
;;; The selected operation envelope must cover C-string lowering and first use.
(in-package "ACL2")

(defun fnn-recovery-profile-perform (effect backing fd)
  "Return primitive word, actual signed observation and retained descriptor.
BACKING is the SAME image-registered RPF array, never a fresh workspace."
  (ecase (first effect)
    (:file-open
     (let ((opened
             (sb-alien:alien-funcall
              (sb-alien:extern-alien "open"
                (function sb-alien:int sb-alien:c-string sb-alien:int))
              (third effect) (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
       (values :opened opened opened)))
    (:file-read
     (let ((got
             (sb-sys:with-pinned-objects (backing)
               (sb-alien:alien-funcall
                (sb-alien:extern-alien "pread"
                  (function sb-alien:long sb-alien:int sb-alien:system-area-pointer
                            sb-alien:unsigned-long sb-alien:long))
                fd (sb-sys:sap+ (sb-sys:vector-sap backing) (third effect))
                (fifth effect) (third effect)))))
       (values :read got fd)))
    (:file-close
     (let ((closed
             (sb-alien:alien-funcall
              (sb-alien:extern-alien "close" (function sb-alien:int sb-alien:int)) fd)))
       ; Keep descriptor custody even for a definite close until the actual
       ; controller observation is retained. No host success/EOF comparison.
       (values :closed closed fd)))))
