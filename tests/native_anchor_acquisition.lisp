;;; Component tests for host/native/anchor.lisp.
;;; The ACL2 calls are narrow stubs in this raw component test; certification
;;; of their real request/parser subjects is tests/acl2/anchor-wire-tests.lisp.

(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(in-package "ACL2")
(require :sb-posix)
(require :sb-bsd-sockets)

(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defun fnn-make-octets (n) (make-array n :element-type '(unsigned-byte 8) :initial-element 0))
(defun fnn-octets (x) (coerce x '(simple-array (unsigned-byte 8) (*))))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (o) (typep o '(unsigned-byte 8))) x)))
(define-condition fnn-store-error (error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-os-error (error) ())
(defconstant +fnn-exit-ok+ 0)
(defconstant +fnn-exit-refused+ 1)
(defconstant +fnn-exit-uncertain+ 3)
(defconstant +fnn-exit-fault+ 4)
(defun fnn-fault (control &rest args) (error (apply #'format nil control args)))
(defun fnn-out (&rest args) (declare (ignore args)) nil)
(defun fnn-err (&rest args) (declare (ignore args)) nil)
(defun make-fnn-store (&rest args) (declare (ignore args)) nil)
(defun fnn-acquire (store) (declare (ignore store)) nil)
(defun fnn-store-close (store) (declare (ignore store)) nil)
(defun fnn-open (path flags) (sb-posix:open path flags #o600))
(defun fnn-close (fd) (sb-posix:close fd))
(defun fnn-read-fd (fd buffer)
  (multiple-value-bind (count errno)
      (sb-sys:with-pinned-objects (buffer)
        (sb-unix:unix-read fd (sb-sys:vector-sap buffer) (length buffer)))
    (unless count (error "read failed: ~a" errno))
    count))
(defun fnn-socket-fd (socket) (sb-bsd-sockets:socket-file-descriptor socket))
(defun fnn-socket-shut (socket) (ignore-errors (sb-bsd-sockets:socket-close socket)))
(defun fnn-string-octets (x) (fnn-octets (map 'list #'char-code x)))
(defun fnn-register-verb (name function) (declare (ignore function)) name)

(load "host/native/crypto.lisp")

(defun fnn-anchor-test-hex (text)
  (let ((out (fnn-make-octets (/ (length text) 2))))
    (dotimes (i (length out) out)
      (setf (aref out i)
            (parse-integer text :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))
(defun fnn-anchor-test-check (truth message)
  (unless truth (error "native anchor acquisition test failed: ~a" message)))

(defparameter *fnn-anchor-test-nonce*
  (fnn-anchor-test-hex "95b3b3f850df64275c8448d870a859fb1e4e690ac6b44e16d83c12d78aa3a2c1"))
(defparameter *fnn-anchor-test-key*
  (fnn-anchor-test-hex "016e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1"))
(defparameter *fnn-anchor-test-delegate*
  (fnn-anchor-test-hex "70e193129ae59d61a2ab6af599a245d654e7ec9542324af3ea3bdf6fcfd623b9"))
(defparameter *fnn-anchor-test-delegation-signature*
  (fnn-anchor-test-hex
   (concatenate 'string
    "57e121e0f150dce10196855752731c2187f475f76ac99acf98e2dde127a9a1721"
    "71373898674f68a349c360b3d075c90af58d8b62d2f0990618a9170085dcf0f")))
(defparameter *fnn-anchor-test-signature*
  (fnn-anchor-test-hex
   (concatenate 'string
    "a7b00df8dc73597f85d9b95ffa3dd6d66f63b38af7e3bfabe79f776f13ded22a"
    "9b7bea3a201121071528529693e0e0e086e5d8ac2a600b9143aeca8cc1660503")))
(defparameter *fnn-anchor-test-root*
  (fnn-anchor-test-hex
   (concatenate 'string
    "fe528747bdbb53ab0d04b5e62a7bf2e5c6db7189ce27c618be0f101e3bfeef32"
    "e9011c2db03d4c53666c025323fb79521c1ca0f896972c95d478b5fc10aae47e")))
(defparameter *fnn-anchor-test-delegation-subject*
  (fnn-anchor-test-hex
   (concatenate 'string
    "526f75676854696d652076312064656c65676174696f6e207369676e61747572652d2d00"
    "0300000020000000280000005055424b4d494e544d415854"
    "70e193129ae59d61a2ab6af599a245d654e7ec9542324af3ea3bdf6fcfd623b9"
    "0000000000000000ffffffffffffffff")))
(defparameter *fnn-anchor-test-response-subject*
  (fnn-anchor-test-hex
   (concatenate 'string
    "526f75676854696d6520763120726573706f6e7365207369676e617475726500"
    "03000000040000000c000000524144494d494450524f4f54404b4c00e1e2bf39d75b0600"
    "fe528747bdbb53ab0d04b5e62a7bf2e5c6db7189ce27c618be0f101e3bfeef32"
    "e9011c2db03d4c53666c025323fb79521c1ca0f896972c95d478b5fc10aae47e")))
(defparameter *fnn-anchor-test-fields*
  (list (fnn-octet-list *fnn-anchor-test-key*)
        (fnn-octet-list *fnn-anchor-test-delegate*) 0 18446744073709551615
        (fnn-octet-list *fnn-anchor-test-delegation-signature*)
        1789829805236961 5000000 (fnn-octet-list *fnn-anchor-test-nonce*)
        (fnn-octet-list *fnn-anchor-test-signature*)
        (fnn-octet-list *fnn-anchor-test-root*)))
(defparameter *fnn-anchor-test-parsed*
  (list :parsed *fnn-anchor-test-fields* nil 0
        (fnn-octet-list *fnn-anchor-test-delegation-subject*)
        (fnn-octet-list *fnn-anchor-test-response-subject*) 1))

(defun fnn-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-anchor-wire-host-request
     (list :request (make-list 1024 :initial-element 0)))
    (fn-anchor-wire-host-parse *fnn-anchor-test-parsed*)
    (fn-anchor-server-host-select
     (list :server (map 'list #'char-code "127.0.0.1") 9
           (fnn-octet-list *fnn-anchor-test-key*)
           (list (fnn-octet-list *fnn-anchor-test-key*)) 32 1024 4096 1))
    (t (error "unexpected mock ACL2 call: ~s" name))))

(load "host/native/anchor.lisp")

(let ((nonce (fnn-anchor-csprng-nonce 32)))
  (fnn-anchor-test-check (= (length nonce) 32) "OS CSPRNG nonce width")
  (fnn-anchor-test-check (typep nonce 'fnn-octets) "OS CSPRNG octet vector"))

(fnn-anchor-test-check
(equal (fnn-anchor-acquire
         (list :server (map 'list #'char-code "127.0.0.1") 9
               (fnn-octet-list (subseq *fnn-anchor-test-key* 1))
               nil 32 1024 4096 1))
        '(:fault :pinned-key))
 "wrong pinned-key width faults before network acquisition")

(let ((observation (fnn-anchor-observe *fnn-anchor-test-parsed*
                                      *fnn-anchor-test-nonce*)))
  (fnn-anchor-test-check (eq (first observation) :observed) "observed tag")
  (fnn-anchor-test-check (eq (third observation) t) "both captured signatures")
  (fnn-anchor-test-check (eq (fourth observation) t) "captured leaf/root binding"))

(let* ((bad (copy-tree *fnn-anchor-test-parsed*))
       (fields (copy-list (second bad)))
       (signature (copy-list (ninth fields))))
  (setf (first signature) (logxor 1 (first signature)))
  (setf (ninth fields) signature (second bad) fields)
  (let ((observation (fnn-anchor-observe bad *fnn-anchor-test-nonce*)))
    (fnn-anchor-test-check (eq (first observation) :observed) "negative remains observation")
    (fnn-anchor-test-check (null (third observation)) "bad signature is false verdict")))

(defun fnn-anchor-test-server (reply thunk)
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket
                               :type :datagram :protocol :udp)))
    (unwind-protect
         (progn
           (sb-bsd-sockets:socket-bind socket #(127 0 0 1) 0)
           (multiple-value-bind (address port) (sb-bsd-sockets:socket-name socket)
             (declare (ignore address))
             (let ((thread
                     (sb-thread:make-thread
                      (lambda ()
                        (multiple-value-bind (buffer count peer-address peer-port)
                            (sb-bsd-sockets:socket-receive socket nil 2048)
                          (declare (ignore buffer count))
                          (sb-bsd-sockets:socket-send
                           socket (fnn-octets reply) nil
                           :address (list peer-address peer-port)))))))
               (unwind-protect (funcall thunk port)
                 (sb-thread:join-thread thread)))))
      (fnn-socket-shut socket))))

(fnn-anchor-test-server
 #(9 8 7)
 (lambda (port)
   (let ((packet (fnn-anchor-udp-exchange
                  "127.0.0.1" port (fnn-make-octets 1024) 1024 4096 2)))
     (fnn-anchor-test-check (equalp packet #(9 8 7))
                            "bounded connected UDP exchange"))))

; A datagram with a valid-looking 4096-octet prefix plus one extra byte is
; observed as overbound, never handed to the ACL2 parser as the prefix alone.
(fnn-anchor-test-server
 (make-array 4097 :element-type '(unsigned-byte 8) :initial-element 7)
 (lambda (port)
   (let ((packet (fnn-anchor-udp-exchange
                  "127.0.0.1" port (fnn-make-octets 1024) 1024 4096 2)))
     (fnn-anchor-test-check (eq packet :overbound)
                            "oversized UDP datagram is not truncated valid"))))

(fnn-anchor-test-server
 #(9 8 7)
 (lambda (port)
   (let ((outcome (fnn-anchor-acquire
                   (list :server (map 'list #'char-code "127.0.0.1") port
                         (fnn-octet-list *fnn-anchor-test-key*)
                         (list (fnn-octet-list *fnn-anchor-test-key*))
                         32 1024 4096 2))))
     (fnn-anchor-test-check (eq (first outcome) :observed)
                            "acquisition reaches ACL2 parse and crypto")
     ;; The actual nonce was fresh, so the captured ROOT cannot bind it.
     (fnn-anchor-test-check (null (fourth outcome))
                            "fresh request nonce stays load-bearing"))))

(format t "FN_NATIVE_ANCHOR_ACQUISITION_TEST passed library=~s version=~s~%"
        *fnn-crypto-library* *fnn-crypto-version*)
