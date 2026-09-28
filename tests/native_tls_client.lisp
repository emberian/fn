(require :sb-posix)
(require :sb-bsd-sockets)
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(in-package "ACL2")

(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defconstant +fnn-max-read+ 65536)
(defun fnn-make-octets (n) (make-array n :element-type '(unsigned-byte 8) :initial-element 0))
(defun fnn-octets (x) (if (typep x 'fnn-octets) x (coerce x 'fnn-octets)))
(defvar *fnn-fd-waiter* #'sb-sys:wait-until-fd-usable)
(defun fnn-now () (get-internal-real-time))
(defun fnn-seconds-to-deadline (deadline)
  (max 0 (/ (- deadline (fnn-now)) (float internal-time-units-per-second))))

(load "host/native/tls.lisp")

(let* ((port (parse-integer (sb-ext:posix-getenv "FN_TLS_CLIENT_PORT")))
       (anchor (sb-ext:posix-getenv "FN_TLS_CLIENT_CA"))
       (name (sb-ext:posix-getenv "FN_TLS_CLIENT_NAME"))
       (expect (sb-ext:posix-getenv "FN_TLS_CLIENT_EXPECT"))
       (socket (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp))
       (context nil) (channel nil))
  (unwind-protect
       (handler-case
           (progn
             (unless (handler-case
                         (progn (fnn-tls-open-client-context
                                 (list :pinned
                                       (coerce (list #\/ #\t #\m #\p (code-char 0)
                                                     #\/ #\c #\a) 'string)))
                                nil)
                       (fnn-tls-config-error () t))
               (error "embedded-NUL trust anchor reached OpenSSL"))
             (sb-bsd-sockets:socket-connect socket #(127 0 0 1) port)
             ;; The served and feed descriptors are nonblocking
             ;; (fnn-socket-fd); a blocking one would hide a WANT_READ.
             (let ((fd (sb-bsd-sockets:socket-file-descriptor socket)))
               (sb-posix:fcntl fd sb-posix:f-setfl
                               (logior (sb-posix:fcntl fd sb-posix:f-getfl)
                                       sb-posix:o-nonblock)))
             ;; PKT-613: FN_TLS_CLIENT_CA=system selects the library's default
             ;; roots (the test points SSL_CERT_FILE at its scratch CA).
             (setq context (fnn-tls-open-client-context
                            (if (string= anchor "system") '(:system-roots)
                              (list :pinned anchor))))
             (unless (handler-case
                         (progn (fnn-tls-connect
                                 context (sb-bsd-sockets:socket-file-descriptor socket)
                                 (coerce (list #\l #\o #\c #\a #\l (code-char 0)
                                               #\x) 'string) 5)
                                nil)
                       (fnn-tls-config-error () t))
               (error "embedded-NUL server name reached OpenSSL"))
             (setq channel (fnn-tls-connect context
                                            (sb-bsd-sockets:socket-file-descriptor socket)
                                            name 5))
             (if (string= expect "tickets")
                 ;; Defect M3: the server's TLS 1.3 NewSessionTicket records
                 ;; arrive before its greeting.  The feed's zero-second read
                 ;; on the nonblocking descriptor must answer :timeout for
                 ;; them (no application data yet), then the greeting.
                 (let ((deadline (+ (fnn-now) (* 5 internal-time-units-per-second)))
                       (timeouts 0))
                   (sleep 0.2)
                   (loop
                     (let ((incoming (fnn-tls-read channel 0 64)))
                       (cond ((eq incoming :timeout)
                              (incf timeouts)
                              (unless (< (fnn-now) deadline)
                                (error "no greeting after the tickets"))
                              (sleep 0.01))
                             ((equalp incoming (fnn-octets '(50 48 48 32 104 105 13 10)))
                              (return))
                             (t (error "unexpected bytes after the tickets: ~s"
                                       incoming)))))
                   (unless (plusp timeouts)
                     (error "the greeting was not delayed past the tickets"))
                   (format t "TLS-CLIENT-TICKETS-PASSED ~d~%" timeouts))
               (progn
                 (fnn-tls-send-all channel (fnn-octets '(80 73 78 71 13 10)) 5)
                 (let ((reply (fnn-tls-read channel 5 64)))
                   (unless (and (string= expect "success")
                                (equalp reply (fnn-octets '(80 79 78 71 13 10))))
                     (error "unexpected authenticated client result")))))
             (format t "TLS-CLIENT-PASSED~%"))
         (fnn-tls-error (condition)
           (unless (string= expect "failure") (error condition))
           (format t "TLS-CLIENT-REFUSED~%")))
    (when channel (ignore-errors (fnn-tls-close-channel channel)))
    (when context (fnn-tls-close-context context))
    (ignore-errors (sb-bsd-sockets:socket-close socket))))
