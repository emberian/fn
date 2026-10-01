; Actual completion producer: the count is its cumulative ACK length.
(in-package "ACL2")
(include-book "../../books/tcpcl-received-count")
(include-book "../../books/tcpcl-session")
(defconst *tcl-count-complete* (fn-tcl-complete nil 7 3 3 '(65 66 67) 0))
(defconst *tcl-count-held*
 (list (cadr (car (fn-tcl-result-events *tcl-count-complete*)))))
(assert-event
 (and (equal (cadr (fn-tcl-result-events *tcl-count-complete*))
             '(:bundle-received 7 (65 66 67)))
      (equal (fn-tcl-final-held-count *tcl-count-held* 7) '(:counted 7 3))
      (equal (fn-tcl-final-count-value
               (fn-tcl-final-held-count *tcl-count-held* 7)) 3)))
(assert-event
 (and (not (fn-tcl-final-count-ready-p (fn-tcl-final-held-count *tcl-count-held* 8)))
      (not (fn-tcl-final-count-ready-p
             (fn-tcl-final-held-count (list (fn-tcl-make-xfer-ack 2 7 3)) 7)))
      (not (fn-tcl-final-count-ready-p (fn-tcl-final-held-count nil 7)))))
