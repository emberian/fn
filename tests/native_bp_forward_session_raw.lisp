;;; The shipped forward session (host/native/bp-node.lisp
;;; fnn-bpnode-forward-session) closes ACL2's session exactly once on every
;;; path that opened it (inspection sweep 2026-10-03 S027).  Before, a
;;; connection error after on-ready drove (:session ... t ...) but before
;;; the attempt was issued (nothing to send, or the hop reset first) only
;;; printed, so the session stayed open in the machine and
;;; fn-bpnrd-serve-rotation-due-p (no open session) never held again.
;;;
;;; The session, the socket and ACL2 are recording stubs; the function under
;;; test is the shipped body.  Cases: (1) a reset after SESS_INIT with
;;; nothing to send: open then close; (2) the normal path: open then close;
;;; (3) a reset after a durable attempt: open, result, close; (4) the socket
;;; shut failing after the close: still one close; (5) the connect failing:
;;; no session event at all.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-bps-outcome (service)
  (declare (ignorable service))
  (harness-stub-reached 'fnn-bps-outcome "host/native/bp-service.lisp"))
;;; ---- derived stubs: END ----

(define-condition fnn-os-error (error) ((errno :initarg :errno :initform 0)))
(defvar *fnn-bps-forward-send* nil)
(defconstant +fnn-tcl-keepalive+ 10)
(defconstant +fnn-tcl-segment-mru+ 65536)

(defstruct (fnn-bps (:conc-name fnn-bps-)) state (next-session 0) outcome root)
(defstruct (fnn-tcl-conn (:conc-name fnn-tclc-)) session pending outcome refusal)

(defvar *events* nil)
(defvar *case* nil)          ; :reset-nothing-sent :normal :reset-after-send :shut-fails :connect-fails

(defun fnn-out (control &rest arguments) (declare (ignore control arguments)))
(defun fnn-indeterminate (&rest arguments) (error "indeterminate ~s" arguments))
(defun fnn-core (name &rest arguments)
  (case name
    (fn-bpnf-epoch 7)
    (fn-tcl-session-negotiated :negotiated)
    (fn-tcl-negotiated-transfer-mtu 1000)
    (fn-tcl-negotiated-peer-node-id "ipn:2.0")
    (fn-bpnp-tcpcl-outcome (if (eq (first arguments) :connection-failed) :uncertain :sent))
    (t (error "unexpected fnn-core ~s" name))))
(defun fnn-bp-observation (wall wall-error) (list :obs wall wall-error))
(defun fnn-bpnode-budgeted (event) event)
(defun fnn-bps-foundation-step (bp event) (declare (ignore bp)) (push event *events*) event)
(defun fnn-bps-drive-effects (bp effects)
  (declare (ignore bp))
  ;; The open's effect is the attempt the host sends: one cl-send unless the
  ;; case has nothing to send.
  (when (and (eq (first effects) :session) (eq (fourth effects) t)
             (member *case* '(:normal :reset-after-send :shut-fails)))
    (funcall *fnn-bps-forward-send*
             (list :cl-send "peer" (third effects) :row :key :arrival '(1 2 3)))))
(defun fnn-bpnode-pause-at-durable-cut (&rest arguments) (declare (ignore arguments)))
(defun fnn-bpnode-forward-result (bp sent session-id result wall wall-error)
  (declare (ignore bp sent session-id wall wall-error))
  (push (list :forward-result result) *events*))
(defun fnn-tcl-params (&rest arguments) arguments)
(defun fnn-socket-fd (socket) socket)
(defun fnn-tcl-connect (host port)
  (declare (ignore host port))
  (when (eq *case* :connect-fails) (error 'fnn-os-error :errno 111))
  :socket)
(defun fnn-socket-shut (socket)
  (declare (ignore socket))
  (when (eq *case* :shut-fails) (error 'fnn-os-error :errno 54)))
(defun fnn-tcl-session (fd role params tag spool &key on-ready &allow-other-keys)
  (declare (ignore fd role params tag spool))
  (let ((conn (make-fnn-tcl-conn :session :s)))
    (funcall on-ready conn)
    (when (member *case* '(:reset-nothing-sent :reset-after-send))
      (error 'fnn-os-error :errno 54))
    (setf (fnn-tclc-outcome conn) :sent)
    conn))

(defun load-shipped (path names)
  (with-open-file (stream path)
    (dolist (wanted names)
      (file-position stream 0)
      (loop for form = (read stream nil :eof)
            when (eq form :eof) do (error "~a: ~s not found" path wanted)
            when (and (consp form) (eq (car form) 'defun) (eq (cadr form) wanted))
              do (eval form) (return)))))
(load-shipped "host/native/bp-node.lisp" '(fnn-bpnode-forward-session))

(defvar *failures* 0)
(defun run (case)
  (setq *case* case *events* nil)
  (let ((sent (ignore-errors
               (fnn-bpnode-forward-session (make-fnn-bps) "ipn:1.0" "peer" 1000 1 0
                                           "hop" "ipn:2.0" 4556 :table))))
    (declare (ignore sent))
    (mapcar (lambda (e) (if (eq (first e) :session) (list :session (fourth e)) e))
            (reverse *events*))))
(defun expect (case want)
  (let ((got (run case)))
    (unless (equal got want)
      (incf *failures*)
      (format t "FAIL ~s: ~s, want ~s~%" case got want))))

(expect :reset-nothing-sent '((:session t) (:session nil)))
(expect :normal '((:session t) (:forward-result :sent) (:session nil)))
(expect :reset-after-send '((:session t) (:forward-result :uncertain) (:session nil)))
(expect :shut-fails '((:session t) (:forward-result :sent) (:session nil)))
(expect :connect-fails '())

(if (zerop *failures*)
    (format t "native_bp_forward_session_raw: every opened session closes once: PASS~%")
    (progn (format t "native_bp_forward_session_raw: ~d failures: FAIL~%" *failures*)
           (sb-ext:exit :code 1)))
