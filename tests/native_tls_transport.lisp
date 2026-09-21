;;; Component/runtime test driver for host/native/tls.lisp.

(require :sb-posix)
(require :sb-bsd-sockets)
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(in-package "ACL2")

(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defconstant +fnn-max-read+ 65536)
(defun fnn-make-octets (n)
  (make-array n :element-type '(unsigned-byte 8) :initial-element 0))
(defun fnn-octets (sequence)
  (if (typep sequence 'fnn-octets) sequence
    (coerce sequence 'fnn-octets)))
(defvar *fnn-fd-waiter* #'sb-sys:wait-until-fd-usable)
(defvar *fnn-read-syscall*
  (lambda (fd buffer)
    (sb-sys:with-pinned-objects (buffer)
      (sb-unix:unix-read fd (sb-sys:vector-sap buffer) (length buffer)))))
(defun fnn-now () (get-internal-real-time))
(defun fnn-seconds-to-deadline (deadline)
  (max 0 (/ (- deadline (fnn-now)) (float internal-time-units-per-second))))
(defun fnn-eintr-p (errno) (and errno (= errno sb-posix:eintr)))
(defun fnn-would-block-p (errno)
  (and errno (or (= errno sb-posix:eagain) (= errno sb-posix:ewouldblock))))
(defun fnn-os-fail (errno) (error "native TLS test errno ~a" errno))
(defun fnn-read-fd (fd buffer deadline allow-would-block)
  (declare (ignore deadline))
  (loop
    (multiple-value-bind (count errno) (funcall *fnn-read-syscall* fd buffer)
      (cond (count (return count))
            ((fnn-eintr-p errno) nil)
            ((and allow-would-block (fnn-would-block-p errno))
             (return :would-block))
            (t (fnn-os-fail errno))))))
(defun fnn-test-nonblocking (fd)
  (sb-posix:fcntl fd sb-posix:f-setfl
                  (logior (sb-posix:fcntl fd sb-posix:f-getfl)
                          sb-posix:o-nonblock)))
(defun fnn-tls-test-check (truth description)
  (unless truth (error "native TLS test failed: ~a" description)))

(load "host/native/tls.lisp")

(let ((version (fnn-tls-version)))
  (fnn-tls-test-check (and (consp version)
                           (search "OpenSSL 3" (second version)))
                      "OpenSSL 3 loader/version"))

;; The sole-reader premise is checked at the host boundary: exact consumption
;; returns the peeked bytes, while EOF and changed bytes are connection faults.
(let ((source #(83 84 65 82 84 84 76 83 13 10))
      (offset 0))
  (let ((*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
        (*fnn-read-syscall*
          (lambda (fd buffer)
            (declare (ignore fd))
            (let ((count (min 3 (- (length source) offset) (length buffer))))
              (replace buffer source :start2 offset :end2 (+ offset count))
              (incf offset count)
              (values count nil)))))
    (fnn-tls-test-check
     (equalp (fnn-tls-consume-plaintext 9 source 1) source)
     "partial exact consume preserves the modeled prefix")))

(let ((*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
      (*fnn-read-syscall* (lambda (&rest ignored)
                            (declare (ignore ignored)) (values 0 nil))))
  (fnn-tls-test-check
   (handler-case (progn (fnn-tls-consume-plaintext 9 #(1) 1) nil)
     (fnn-tls-io-error () t))
   "short consume is a TLS I/O fault"))

(let ((*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
      (*fnn-read-syscall*
        (lambda (fd buffer)
          (declare (ignore fd)) (setf (aref buffer 0) 2) (values 1 nil))))
  (fnn-tls-test-check
   (handler-case (progn (fnn-tls-consume-plaintext 9 #(1) 1) nil)
     (fnn-tls-io-error () t))
   "changed consume is a TLS I/O fault"))

(let ((*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
      (*fnn-tls-peek-syscall*
        (lambda (fd buffer)
          (declare (ignore fd))
          (replace buffer #(1 2 3 4))
          (values 4 nil))))
  (fnn-tls-test-check (equalp (fnn-tls-peek-plaintext 9 1) #(1 2 3 4))
                      "MSG_PEEK seam leaves exact observed bytes"))

(let* ((certificate (sb-ext:posix-getenv "FN_TLS_TEST_CERT"))
       (private-key (sb-ext:posix-getenv "FN_TLS_TEST_KEY"))
       (wrong-key (sb-ext:posix-getenv "FN_TLS_TEST_WRONG_KEY")))
  (fnn-tls-test-check (and certificate private-key wrong-key)
                      "certificate/key test environment")
  (fnn-tls-test-check
   (handler-case
       (progn (fnn-tls-open-context certificate wrong-key) nil)
     (fnn-tls-config-error (condition)
       (search "mismatch" (fnn-tls-error-detail condition))))
   "certificate/private-key mismatch diagnostic")
  (let ((context (fnn-tls-open-context certificate private-key))
        (listener (make-instance 'sb-bsd-sockets:inet-socket
                                 :type :stream :protocol :tcp)))
    (unwind-protect
        (progn
          (sb-bsd-sockets:socket-bind listener #(127 0 0 1) 0)
          (sb-bsd-sockets:socket-listen listener 2)
          (multiple-value-bind (address port) (sb-bsd-sockets:socket-name listener)
            (declare (ignore address))
            (format t "PORT ~d~%" port)
            (finish-output))
          ;; First peer deliberately sends plaintext where a ClientHello is
          ;; required.  Its failure must leave the shared context usable.
          (let* ((socket (sb-bsd-sockets:socket-accept listener))
                 (fd (sb-bsd-sockets:socket-file-descriptor socket)))
            (fnn-test-nonblocking fd)
            (fnn-tls-test-check
             (handler-case (progn (fnn-tls-accept context fd 5) nil)
               (fnn-tls-handshake-error () t))
             "malformed handshake is isolated")
            (sb-bsd-sockets:socket-close socket)
            (format t "FAILURE-ISOLATED~%")
            (finish-output))
          ;; A later peer completes TLS and continues the NNTP byte path.
          (let* ((socket (sb-bsd-sockets:socket-accept listener))
                 (fd (sb-bsd-sockets:socket-file-descriptor socket)))
            (fnn-test-nonblocking fd)
            (let ((channel (fnn-tls-accept context fd 5)))
              (unwind-protect
                  (progn
                    (fnn-tls-test-check
                     (equalp (fnn-tls-read channel 5)
                             #(67 65 80 65 66 73 76 73 84 73 69 83 13 10))
                     "continued NNTP bytes after handshake")
                    (fnn-tls-send-all channel #(50 48 48 32 111 107 13 10) 5))
                (fnn-tls-close-channel channel)))
            (sb-bsd-sockets:socket-close socket)
            (format t "ROUNDTRIP-PASSED~%")
            (finish-output)))
      (fnn-tls-close-context context)
      (sb-bsd-sockets:socket-close listener))))

