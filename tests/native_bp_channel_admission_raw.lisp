;;; The shipped TCPCL boundary must pass ACL2's parsed EID to the durable
;;; channel admission selector, while retaining the observed channel tuple.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defvar *admission-answer* nil)
(defvar *calls* nil)
(defun fnn-tclc-session (conn) (declare (ignore conn)) :session)
(defun fnn-bps-state (service) (declare (ignore service)) :fnbs)
(defun fnn-core (name &rest arguments)
  (case name
    (fn-tcl-session-negotiated
     (assert (equal arguments '(:session))) :negotiated)
    (fn-tcl-negotiated-peer-node-id
     (assert (equal arguments '(:negotiated))) '(100 116 110))
    (fn-bpn-host-eid
     (assert (equal arguments '((100 116 110))))
     '(:dtn 47 47 115 101 110 100 101 114 47))
    (fn-bpnf-tcpcl-ingress
     (push (cons :ingress arguments) *calls*) :ingress)
    (otherwise (error "unexpected core call ~s" name))))
(defun fnn-owner-core (name &rest arguments)
  (assert (eq name 'fn-owner-bp-session-principal))
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
      (eid '(:dtn 47 47 115 101 110 100 101 114 47)))
  (setq *admission-answer* '(:admitted (112 101 101 114) 9)
        *calls* nil)
  (assert (eq (fnn-bps-tcpcl-ingress :service :conn 3 4 :owner channel)
              :ingress))
  (assert (equal (reverse *calls*)
                 (list (cons :admission (list channel eid))
                       (cons :ingress
                             (list :fnbs 3 4 eid '(112 101 101 114) 9)))))
  (setq *admission-answer* '(:refused :eid-mismatch) *calls* nil)
  (fnn-bps-tcpcl-ingress :service :conn 3 4 :owner channel)
  (assert (equal (reverse *calls*)
                 (list (cons :admission (list channel eid))
                       (list :log "BP channel admission refused reason=~(~a~)"
                             '(:eid-mismatch))
                       (cons :ingress (list :fnbs 3 4 eid nil 0))))))

(format t "native BP parsed channel admission: PASS~%")
