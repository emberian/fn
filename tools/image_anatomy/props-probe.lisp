; tools/image_anatomy/props-probe.lisp -- loaded into a native image's core
; by derive.sh to make a RECORDING image (lane image-anatomy, 2026-09-26):
; every distinct (symbol property) pair any code reads from the ACL2 world
; through fgetprop or sgetprop is appended, the first time it is read, to
; $IA_PROPS_OUT.<pid>.  A measurement only: the recording image is never a
; release.
(in-package "ACL2")
(defvar *ia-props-seen* (make-hash-table :test 'equal))
(defvar *ia-props-lock* (sb-thread:make-mutex :name "ia-props"))
(defun ia-props-note (sym prop)
  (let ((key (cons sym prop)))
    (unless (gethash key *ia-props-seen*)
      (sb-thread:with-mutex (*ia-props-lock*)
        (unless (gethash key *ia-props-seen*)
          (setf (gethash key *ia-props-seen*) t)
          (let ((out (sb-ext:posix-getenv "IA_PROPS_OUT")))
            (when out
              (ignore-errors
               (with-open-file (s (format nil "~a.~d" out (sb-posix:getpid))
                                  :direction :output :if-exists :append
                                  :if-does-not-exist :create)
                 (let ((*print-pretty* nil) (*package* (find-package "ACL2")))
                   (format s "~s ~s~%" sym prop)))))))))))
(sb-int:encapsulate 'fgetprop 'ia-props
  (lambda (f sym prop &rest more) (ia-props-note sym prop) (apply f sym prop more)))
(sb-int:encapsulate 'sgetprop 'ia-props
  (lambda (f sym prop &rest more) (ia-props-note sym prop) (apply f sym prop more)))
