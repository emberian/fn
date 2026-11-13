;;; The raw half of tests/native-session.lsp (layer doc 4.1.4). Test-only.
(in-package "ACL2")
(load "host/ffi.lisp")
(load "host/adapter.lisp")
(load "host/native-seed-fixture.lisp")

(defvar *fn2-ns-trace* nil)

(defun fn2-ns-install-fixture-image (host path)
  "Put the measurement's declared initial snapshot on its physical device.
This is test setup, before boundary recording and before any client. The
restart fixture separately exercises persisted genesis and the boot machine."
  (multiple-value-bind (fd size backend) (fn2-device-open path :create-size 33554432)
    (let ((device (%make-fn2-device :fd fd :size size :backend backend)) (transferred nil))
      (unwind-protect
          (progn
            (dolist (write (reverse *fn2-n-seed-store*))
              (let* ((bytes (make-array (length (cdr write)) :element-type '(unsigned-byte 8)
                                        :initial-contents (cdr write)))
                     (job (make-fn2-device-job :kind :write :bytes bytes :address 0
                                               :length (length bytes) :offset (car write))))
                (fn2-device-perform device job)
                (assert (= (fn2-device-job-result job) (length bytes)))))
            (assert (zerop (fn2-device-fence fd)))
            (setf (fn2-nhost-storage host)
                  (fn2-device-start fd size backend (length (fn2-nhost-ops host))
                    (lambda () (fn2-native-mux-signal (fn2-nhost-mux host)))
                    (lambda (label) (fn2-n-boundary host label))))
            (setf transferred t))
        (unless transferred (fn2-native-close fd))))))

(defun fn2-ns-serve (&optional (trace-capacity 4000000))
  "Bind 127.0.0.1:0, announce the port, serve until the stop control line."
  (let ((host (fn2-n-make-seeded-host *fn2-ss-profile* *fn2-ss-seeds*
                                   :control-fd 0 :trace-capacity trace-capacity)))
    (unwind-protect
         (progn
          (fn2-ns-install-fixture-image host
            (or (sb-ext:posix-getenv "FN2_SURFACE_IMAGE")
                (error "FN2_SURFACE_IMAGE must name a new measurement fixture image")))
          (format t "@@FN2SS ready ~d 0 0@@~%" (fn2-nhost-listen-port host))
          (finish-output)
          (let ((reason (fn2-n-run host)))
           (setf *fn2-ns-trace* (fn2-n-trace-list host))
           (format t "@@FN2SS served - 0 ~d@@~%" reason)
           (finish-output)))
      (fn2-n-destroy host))))

(defun fn2-ns-verdicts (clients)
  "CLIENTS: (incarnation sent received closed port ident) per connection, the clients' own view.
WIRE per connection; ENVELOPE over the trace replayed from the seeded store (a refusal is every connection's verdict)."
  (let ((env (fn2-ss-envelope-check *fn2-ns-trace* clients *fn2-ss-profile* *fn2-ss-seeds*)))
    ;; A refusal names a port: print that connection's two sides for the record.
    (when (and (consp env) (member (car env) '(:receive-not-client :send-not-client :no-client)))
      (let* ((port (cadr env))
             (caps (cadr (fn2-ss-replay *fn2-ns-trace* *fn2-ss-profile* *fn2-ss-seeds* nil)))
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
