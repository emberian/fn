(setq *print-pretty* nil *print-length* nil *print-level* nil)
(defvar cl-user::*m20-log* (format nil "/tank/fn/scratch/m20/e2-~a.log" (sb-posix:getpid)))
(defun cl-user::m20-log (tag x)
  (with-open-file (s cl-user::*m20-log* :direction :output :if-exists :append :if-does-not-exist :create)
    (prin1 (list tag x) s) (terpri s)))
;; L-RUN-LAUNCH's startup semantics, applied by override: the protected runtime is the smaller of the
;; profile's and the launch's (LIMIT = least resident observation less the pools, here measured), the
;; peer grant against the address space only, the connection budget retired (the gate's C' decides).
(defvar cl-user::*m20-limit* (let ((e (sb-posix:getenv "M20_LIMIT"))) (and e (parse-integer e))))
(sb-int:encapsulate 'acl2::fn-prstartup-protected 'm20
  (lambda (f profile core nursery output mc observed)
    (let ((bound (funcall f profile core nursery output mc observed)))
      (if cl-user::*m20-limit*
          (min bound (+ (acl2::fn-mm-launch-dynamic cl-user::*m20-limit* core nursery)
                        (acl2::nfix (acl2::fn-crv-nth 0 output))))
        bound))))
(sb-int:encapsulate 'acl2::fn-prstartup-peer-native-grant 'm20
  (lambda (f &rest args)
    (let ((a (copy-list args))) (setf (nth 8 a) (list (expt 2 60))) (let ((r (apply f a))) (cl-user::m20-log :peer-grant r) r))))
(sb-int:encapsulate 'acl2::fn-cbud-run-decide 'm20
  (lambda (f capacity &rest args) (let ((r (apply f capacity args))) (cl-user::m20-log :cbud-retired r) (list :hold capacity))))
(sb-int:encapsulate 'acl2::fn-adm-capacity-line 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :capline r) r)))
(sb-int:encapsulate 'acl2::fn-prstartup-default-plan-with-peer 'm20
  (lambda (f &rest args) (let ((r (apply f args))) (cl-user::m20-log :plan (car r)) r)))
