(setq *print-length* 40 *print-level* 6 *print-pretty* nil)
(trace acl2::fnn-call :condition (let ((n (symbol-name (sb-debug:arg 0)))) (or (search "HEAP" n) (search "EXTEND" n) (search "RESERV" n) (search "LXC" n))) :report trace)
