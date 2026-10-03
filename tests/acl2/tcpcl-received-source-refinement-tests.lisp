(in-package "ACL2")
(include-book "../../books/tcpcl-received-source-refinement")
; Reach the transferring branch through actual open/contact/session-init.
(defconst *tcsr-local* (fn-tcl-make-params 10 10 1000 '(100 116 110 58 114) nil nil))
(defconst *tcsr-initial* (fn-tcl-initial-session :passive *tcsr-local* 0))
(defconst *tcsr-open* (fn-tcl-result-session (fn-tcl-open *tcsr-initial* 0)))
(defconst *tcsr-contact* (fn-tcl-result-session (fn-tcl-step *tcsr-open* (fn-tcl-make-contact 4 0) 0)))
(defconst *tcsr-up* (fn-tcl-result-session
 (fn-tcl-step *tcsr-contact* (fn-tcl-make-sess-init 10 10 1000 '(100 116 110 58 115) nil) 1)))
(defconst *tcsr-data* (fn-tcl-make-xfer-segment 3 7 nil '(65 66)))
(assert-event
 (and (fn-tcl-sessionp *tcsr-up*) (eq (fn-tcl-session-phase *tcsr-up*) :established)
      (fn-tcl-transferringp (fn-tcl-session-phase *tcsr-up*))
      (fn-tcl-session-negotiated *tcsr-up*)
      (fn-tcl-messagep *tcsr-data* (fn-tcl-segment-mru *tcsr-up*))
      (true-listp (fn-tcl-xfer-segment-data *tcsr-data*))
      (equal (fn-tcl-source-result-alpha (fn-tcl-recv-segment-source *tcsr-up* *tcsr-data* 2))
             (fn-tcl-recv-segment *tcsr-up* *tcsr-data* 2))
      (equal (cadr (fn-tcl-result-events (fn-tcl-step-source *tcsr-up* *tcsr-data* 2)))
             '(:bundle-segments-received 7 ((65 66)) 2))))
; Complete retained-hypothesis removal: the sole proper-data hypothesis fails
; and conclusion fails. Explicitly corrupted internal message, not live input.
(assert-event
 (with-guard-checking :none
 (let ((bad (fn-tcl-make-xfer-segment 3 7 nil '(65 . :broken))))
  (and (not (true-listp (fn-tcl-xfer-segment-data bad)))
       (not (equal (fn-tcl-source-result-alpha (fn-tcl-recv-segment-source *tcsr-up* bad 2))
                   (fn-tcl-recv-segment *tcsr-up* bad 2)))))))
