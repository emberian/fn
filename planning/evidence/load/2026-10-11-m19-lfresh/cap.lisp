(setq *print-pretty* nil *print-length* nil *print-level* nil)
(sb-int:encapsulate (quote acl2::fn-adm-capacity-line) (quote m19) (lambda (f &rest args) (let ((r (apply f args))) (with-open-file (s (format nil "/tank/fn/scratch/m19/fresh/cap-args-~a.lisp" (sb-posix:getpid)) :direction :output :if-exists :supersede) (prin1 (cons r args) s)) r)))
