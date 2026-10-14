(setq *print-pretty* nil *print-length* nil *print-level* nil)
(defvar cl-user::*m20-log* (format nil "/tank/fn/scratch/m20/e1-~a.log" (sb-posix:getpid)))
(defun cl-user::m20-log (tag x)
  (with-open-file (s cl-user::*m20-log* :direction :output :if-exists :append :if-does-not-exist :create)
    (prin1 (list tag x) s) (terpri s)))
;; discovery only: the two startup twins the landing restates are passed; everything after them is observed
(sb-int:encapsulate 'acl2::fn-prstartup-protected 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :protected-original r) 0)))
(sb-int:encapsulate 'acl2::fn-prstartup-peer-native-grant 'm20
  (lambda (f &rest args)
    (cl-user::m20-log :peer-grant-original (apply f args))
    (let ((a (copy-list args))) (setf (nth 8 a) (list (expt 2 60))) (let ((r (apply f a))) (cl-user::m20-log :peer-grant-addr r) r))))
(sb-int:encapsulate 'acl2::fn-cbud-run-decide 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :cbud (list r args)) r)))
(sb-int:encapsulate 'acl2::fn-orv-startup-grant 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :orv (list r args)) r)))
(sb-int:encapsulate 'acl2::fn-adm-capacity-line 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :capline (cons r args)) r)))
