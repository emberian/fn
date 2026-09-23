; Certifiable host-call boundary for one TCPCL socket read.  The native host
; calls fn-tcl-host-drive and consumes this exact flat triple.
(in-package "ACL2")
(include-book "tcpcl-session")

(defun fn-tcl-host-triple (r)
  (list (fn-tcl-result-session r)
        (fn-tcl-result-events r)
        (fn-tcl-result-unconsumed r)))

(defun fn-tcl-host-drive (s buf now)
  (fn-tcl-host-triple (fn-tcl-drive s buf now)))
