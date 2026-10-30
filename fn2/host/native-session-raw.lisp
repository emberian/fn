;;; The raw half of fn2/tests/native-session.lsp (layer doc 4.1.4). Test-only.
(in-package "ACL2")
(load "fn2/host/ffi.lisp")
(load "fn2/host/adapter.lisp")

(defvar *fn2-ns-trace* nil)

(defun fn2-ns-serve (&optional (trace-capacity 4000000))
  "Bind 127.0.0.1:0, announce the port, serve until the stop control line."
  (let ((host (fn2-n-make-host *fn2-ns-profile* :control-fd 0 :trace-capacity trace-capacity)))
    (format t "@@FN2SS ready ~d 0 0@@~%" (fn2-nhost-listen-port host))
    (finish-output)
    (unwind-protect
         (let ((reason (fn2-n-run host)))
           (setf *fn2-ns-trace* (fn2-n-trace-list host))
           (format t "@@FN2SS served - 0 ~d@@~%" reason)
           (finish-output))
      (fn2-n-destroy host))))

(defun fn2-ns-verdicts (clients)
  "CLIENTS: (incarnation sent received closed port ident) per connection, the clients' own view.
WIRE per connection; ENVELOPE over the trace (a refusal is every connection's verdict)."
  (let ((env (fn2-envelope-check *fn2-ns-trace* clients *fn2-ns-profile*)))
    ;; A refusal names a port: print that connection's two sides for the record.
    (when (and (consp env) (member (car env) '(:receive-not-client :send-not-client :no-client)))
      (let* ((port (cadr env))
             (caps (cadr (fn2-envelope-replay *fn2-ns-trace* *fn2-ns-profile* nil)))
             (cap (find port caps :key (lambda (c) (nth 1 (cdr c)))))
             (cl (find port clients :key (lambda (c) (nth 4 c)))))
        (format t "@@FN2SS envelope-detail ~d rx=~s eof=~s tx-len=~d sent=~s received-len=~d closed=~s@@~%"
                port (map 'string #'code-char (reverse (nth 2 (cdr cap)))) (nth 4 (cdr cap))
                (length (nth 3 (cdr cap))) (map 'string #'code-char (nth 1 cl)) (length (nth 2 cl)) (nth 3 cl))))
    (dolist (c clients)
      (let ((v (if (eq env :pass) (fn2-wire-check (nth 1 c) (nth 2 c) (nth 3 c)) (list :envelope env))))
        (format t "@@FN2SS wire ~d ~s@@~%" (nth 5 c) v)))
    (format t "@@FN2SS stopped - 0 ~d@@~%" (length *fn2-ns-trace*))
    (finish-output)))
