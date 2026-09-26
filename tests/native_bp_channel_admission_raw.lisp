;;; The shipped TCPCL boundary passes raw announced bytes and observed socket
;;; facts once to ACL2, which supplies the complete typed FNBS ingress.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defvar *admission-answer* nil)
(defvar *calls* nil)
(defun fnn-tclc-session (conn) (declare (ignore conn)) :session)
;; Since ec35b0d5 the caller passes the FNBS state itself (bp-node's live
;; state, or the initial state for bp-app receive): :fnbs stands for it.
(defun fnn-core (name &rest arguments)
  (case name
    (fn-tcl-session-negotiated
     (assert (equal arguments '(:session))) :negotiated)
    (fn-tcl-negotiated-peer-node-id
     (assert (equal arguments '(:negotiated))) '(100 116 110))
    (otherwise (error "unexpected core call ~s" name))))
(defun fnn-owner-core (name &rest arguments)
  (assert (eq name 'fn-owner-bp-tcpcl-ingress))
  (push (cons :admission arguments) *calls*)
  *admission-answer*)
(defun fnn-out (format-string &rest arguments)
  (push (list :log format-string arguments) *calls*))

(with-open-file (stream "host/native/bp-service.lisp")
  (let ((found nil))
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (eq (cadr form) 'fnn-bps-tcpcl-ingress))
            do (eval form) (setq found t) (return))
    (unless found (error "TCPCL ingress caller not found"))))

(let ((channel '(:tcp4 (127 0 0 1) 4556 (127 0 0 1)))
      (ingress '(:cl (1 . 3) 4 (:dtn 47 47 115 101 110 100 101 114 47)
                 (112 101 101 114) 9)))
  (setq *admission-answer* (list :admitted nil ingress)
        *calls* nil)
  (assert (equal (fnn-bps-tcpcl-ingress :fnbs :conn 3 4 :owner channel)
                 ingress))
  (assert (equal (reverse *calls*)
                 (list (cons :admission
                             (list :fnbs 3 4 channel '(100 116 110))))))
  (setq *admission-answer* (list :refused :eid-mismatch
                                 (list :cl '(1 . 3) 4
                                       '(:dtn 47 47 111 116 104 101 114 47)
                                       nil 0))
        *calls* nil)
  (assert (equal (fnn-bps-tcpcl-ingress :fnbs :conn 3 4 :owner channel)
                 (third *admission-answer*)))
  (assert (equal (reverse *calls*)
                 (list (cons :admission
                             (list :fnbs 3 4 channel '(100 116 110)))
                       (list :log "BP channel admission refused reason=~(~a~)"
                             '(:eid-mismatch))))))

(format t "native BP parsed channel admission: PASS~%")
