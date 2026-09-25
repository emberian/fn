;;; Deterministic raw-native I/O boundary tests.  This loads the same
;;; host/native/io.lisp SBCL code that the saved image loads; no Python process
;;; or parser is part of the exercised path.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
;; Raw-I/O tests do not enter an ACL2 wrapper, but these names let SBCL compile
;; the full native adapter exactly once without warning about the image state.
(defvar *the-live-state* nil)
(defun f-get-global (name state)
  (declare (ignore name state))
  nil)
(load "host/native/io.lisp")

;; Native socketpair(2), used only to exercise the production descriptor and
;; readiness path without a Python process or a network listener.
(sb-alien:define-alien-routine ("socketpair" nio-%socketpair) sb-alien:int
  (domain sb-alien:int) (type sb-alien:int) (protocol sb-alien:int)
  (fds (* sb-alien:int)))

(defun nio-socketpair ()
  ;; AF_UNIX and SOCK_STREAM are both 1 on the supported POSIX targets.
  (sb-alien:with-alien ((fds (array sb-alien:int 2)))
    (when (< (nio-%socketpair 1 1 0 (sb-alien:cast fds (* sb-alien:int))) 0)
      (error "socketpair failed: errno ~d" (sb-alien:get-errno)))
    (values (sb-alien:deref fds 0) (sb-alien:deref fds 1))))

(defun nio-check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

(defun nio-expects (expected thunk)
  (handler-case (funcall thunk)
    (error (e)
      (unless (typep e expected)
        (error "expected ~a, got ~a" expected e))
      t)
    (:no-error (&rest values)
      (declare (ignore values))
      (error "expected ~a, got normal return" expected))))

(defun nio-wrong-condition-is-rejected ()
  (let ((rejected nil))
    (handler-case
        (nio-expects 'fnn-store-fault (lambda () (fnn-refuse "semantic refusal")))
      (error () (setq rejected t)))
    (nio-check rejected "test helper accepted refusal where a fault was required")))

(defun nio-read-eintr-then-data ()
  (let ((calls 0) (buffer (fnn-make-octets 3)))
    (let ((*fnn-read-syscall*
            (lambda (fd target)
              (declare (ignore fd))
              (incf calls)
              (if (= calls 1)
                  (values nil sb-posix:eintr)
                  (progn (setf (aref target 0) 42) (values 1 nil))))))
      (nio-check (= (fnn-read-fd 9 buffer) 1) "read did not return byte count")
      (nio-check (= calls 2) "read did not retry EINTR")
      (nio-check (= (aref buffer 0) 42) "read retry did not preserve buffer"))))

(defun nio-read-eof-remains-zero ()
  (let ((*fnn-read-syscall* (lambda (fd buffer)
                               (declare (ignore fd buffer))
                               (values 0 nil))))
    (nio-check (zerop (fnn-read-fd 9 (fnn-make-octets 2)))
               "EOF read was not preserved as zero")))

(defun nio-read-eagain-waits-again ()
  (let ((calls 0) (waits 0) (buffer (fnn-make-octets 2)))
    (let ((*fnn-fd-waiter* (lambda (&rest ignored)
                              (declare (ignore ignored))
                              (incf waits) t))
          (*fnn-read-syscall*
            (lambda (fd target)
              (declare (ignore fd))
              (incf calls)
              (if (= calls 1)
                  (values nil sb-posix:eagain)
                  (progn (setf (aref target 0) 7) (values 1 nil))))))
      (nio-check (equalp (fnn-recv 9 1) (fnn-octets '(7)))
                 "receive did not return data after EAGAIN")
      (nio-check (= waits 2) "receive retried EAGAIN without a second readiness wait")
      (nio-check (= calls 2) "receive did not retry EAGAIN"))))

(defun nio-zero-recv-polls-once ()
  (let ((waits nil) (calls 0))
    (let ((*fnn-monotonic-ticks* (lambda () 0))
          (*fnn-fd-waiter* (lambda (fd direction seconds)
                              (declare (ignore fd direction))
                              (push seconds waits) t))
          (*fnn-read-syscall* (lambda (fd target)
                                (declare (ignore fd))
                                (incf calls)
                                (setf (aref target 0) 8)
                                (values 1 nil))))
      (nio-check (equalp (fnn-recv 9 0) (fnn-octets '(8)))
                 "zero-time receive did not perform its readiness poll")
      (nio-check (equal waits '(0)) "zero-time receive used a nonzero or repeated poll")
      (nio-check (= calls 1) "zero-time receive did not issue one read"))))

(defun nio-zero-recv-eagain-does-not-spin ()
  (let ((waits 0) (calls 0))
    (let ((*fnn-monotonic-ticks* (lambda () 0))
          (*fnn-fd-waiter* (lambda (&rest ignored)
                              (declare (ignore ignored))
                              (incf waits) t))
          (*fnn-read-syscall* (lambda (&rest ignored)
                                (declare (ignore ignored))
                                (incf calls)
                                (values nil sb-posix:eagain))))
      (nio-check (eq (fnn-recv 9 0) :timeout)
                 "zero-time EAGAIN receive was not a timeout")
      (nio-check (= waits 1) "zero-time EAGAIN receive busy-spun readiness waits")
      (nio-check (= calls 1) "zero-time EAGAIN receive busy-spun syscalls"))))

(defun nio-recv-honors-caller-bound-before-read ()
  (let ((seen nil))
    (let ((*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
          (*fnn-read-syscall*
            (lambda (fd target)
              (declare (ignore fd))
              (setq seen (length target))
              (setf (aref target 0) 9)
              (values 1 nil))))
      (nio-check (equalp (fnn-recv 9 1 7) (fnn-octets '(9)))
                 "bounded receive did not return injected data")
      (nio-check (= seen 7) "receive allocated/read beyond caller bound")
      (nio-check (nio-expects 'fnn-store-fault (lambda () (fnn-recv 9 0 0)))
                 "zero receive maximum was accepted")
      (nio-check (nio-expects 'fnn-store-fault
                              (lambda () (fnn-recv 9 0 (+ +fnn-max-read+ 1))))
                 "oversized receive maximum was accepted"))))

(defun nio-connects-loopback-nonblocking ()
  "Exercise a real TCP handshake through FNN-CONNECT, not a socket mock."
  (let ((listener nil) (socket nil) (port nil))
    (unwind-protect
         (progn
           (multiple-value-setq (listener port) (fnn-listen 0))
           ;; The listener backlog is enough for TCP establishment; no raw
           ;; client parser or accept loop is involved in this boundary test.
           (setq socket (fnn-connect #(127 0 0 1) port :timeout 1))
           (let ((flags (sb-posix:fcntl (fnn-socket-fd socket) sb-posix:f-getfl)))
             (nio-check (not (zerop (logand flags sb-posix:o-nonblock)))
                        "successful TCP connect did not retain nonblocking mode")))
      (when socket (fnn-socket-shut socket))
      (when listener (fnn-socket-shut listener)))))

(defun nio-connect-preserves-refusal-errno ()
  "A kernel refusal must remain its errno, rather than a generic timeout."
  (let ((listener nil) (port nil))
    (unwind-protect
         (progn
           (multiple-value-setq (listener port) (fnn-listen 0))
           ;; Closing before the SYN leaves a loopback port with no listener.
           (fnn-socket-shut listener)
           (setq listener nil)
           (handler-case
               (progn
                 (fnn-connect #(127 0 0 1) port :timeout 1)
                 (error "closed loopback port unexpectedly connected"))
             (fnn-os-error (e)
               (nio-check (= (fnn-os-errno e) sb-posix:econnrefused)
                          "TCP refusal lost its real errno: ~s" (fnn-os-errno e)))))
      (when listener (fnn-socket-shut listener)))))

(defun nio-connect-pending-completion-and-deadline ()
  "The pending path has one output deadline and never repeats connect(2)."
  (let ((attempts 0) (waits nil) (socket nil))
    (let ((*fnn-monotonic-ticks* (lambda () 0))
          (*fnn-connect-attempt* (lambda (&rest ignored)
                                  (declare (ignore ignored))
                                  (incf attempts) :pending))
          (*fnn-fd-waiter* (lambda (fd direction seconds)
                             (declare (ignore fd))
                             (push (list direction seconds) waits) t))
          (*fnn-socket-pending-error* (lambda (&rest ignored)
                                        (declare (ignore ignored)) 0)))
      (setq socket (fnn-connect #(127 0 0 1) 9 :timeout 1))
      (nio-check (= attempts 1) "pending TCP connect repeated connect(2)")
      (nio-check (and (= (length waits) 1)
                      (eq (caar waits) :output)
                      (= (cadar waits) 1))
                 "pending TCP connect did not wait once with its original deadline")
      (fnn-socket-shut socket))))

(defun nio-connect-pending-timeout-does-not-reset-deadline ()
  (let ((ticks (list 0 0 internal-time-units-per-second)) (waits 0))
    (let ((*fnn-monotonic-ticks* (lambda () (pop ticks)))
          (*fnn-connect-attempt* (lambda (&rest ignored)
                                  (declare (ignore ignored)) :pending))
          (*fnn-fd-waiter* (lambda (&rest ignored)
                             (declare (ignore ignored)) (incf waits) t))
          (*fnn-socket-pending-error* (lambda (&rest ignored)
                                        (declare (ignore ignored)) sb-posix:einprogress)))
      (handler-case
          (progn (fnn-connect #(127 0 0 1) 9 :timeout 1)
                 (error "pending TCP connect outlived its absolute deadline"))
        (fnn-os-error (e)
          (nio-check (= (fnn-os-errno e) sb-posix:etimedout)
                     "pending TCP connect used wrong timeout errno")))
      (nio-check (= waits 1) "pending TCP connect reset its deadline after readiness"))))

(defun nio-zero-connect-poll-does-not-spin ()
  (let ((waits 0) (attempts 0))
    (let ((*fnn-monotonic-ticks* (lambda () 0))
          (*fnn-connect-attempt* (lambda (&rest ignored)
                                  (declare (ignore ignored)) (incf attempts) :pending))
          (*fnn-fd-waiter* (lambda (&rest ignored)
                             (declare (ignore ignored)) (incf waits) t))
          (*fnn-socket-pending-error* (lambda (&rest ignored)
                                        (declare (ignore ignored)) sb-posix:einprogress)))
      (handler-case
          (progn (fnn-connect #(127 0 0 1) 9 :timeout 0)
                 (error "zero-time pending connect unexpectedly succeeded"))
        (fnn-os-error (e)
          (nio-check (= (fnn-os-errno e) sb-posix:etimedout)
                     "zero-time pending connect used wrong outcome")))
      (nio-check (= attempts 1) "zero-time pending connect repeated connect(2)")
      (nio-check (= waits 1) "zero-time pending connect busy-spun readiness"))))

(defun nio-store-write-progress ()
  (let ((answers '(1 2 1)) (seen nil))
    (let ((*fnn-write-syscall*
            (lambda (fd octets offset count)
              (declare (ignore fd octets))
              (push (list offset count) seen)
              (values (pop answers) nil))))
      (fnn-write-all 9 (fnn-octets '(10 11 12 13)))
      (nio-check (equal (nreverse seen) '((0 4) (1 3) (3 1)))
                 "partial store writes did not resume at exact offsets")
      (nio-check (null answers) "store write did not consume every injected partial result"))))

(defun nio-with-transaction-scan-stubs (names thunk)
  (let* ((symbols '(fnn-list-directory fnn-list-directory-bounded
                    fnn-bridge-transaction-observation
                    fnn-lstat fnn-symlink-p fnn-regular-p))
         (saved (mapcar (lambda (symbol) (cons symbol (symbol-function symbol))) symbols)))
    (unwind-protect
         (progn
           ;; If fnn-transaction-files regresses to the unbounded helper this
           ;; test fails immediately instead of retaining a large list first.
           (setf (symbol-function 'fnn-list-directory) (lambda (&rest ignored)
                                                        (declare (ignore ignored))
                                                        (error "unbounded transaction enumeration"))
                 (symbol-function 'fnn-list-directory-bounded)
                 (lambda (path limit namespace)
                   (declare (ignore path namespace))
                   (when (> (length names) limit)
                     (fnn-fault "transaction namespace exceeds ACL2 observation bound"))
                   names)
                 (symbol-function 'fnn-bridge-transaction-observation)
                 (lambda (observed limit &optional (selected-lower 0))
                   (declare (ignore selected-lower))
                   (unless (and (= (length observed) (length names))
                                (>= limit (length observed)))
                     (fnn-fault "transaction observation lost its ACL2 bound"))
                   (loop for name in observed for sequence from 0
                         collect (cons sequence name)))
                 (symbol-function 'fnn-lstat) (lambda (&rest ignored)
                                                (declare (ignore ignored)) :regular)
                 (symbol-function 'fnn-symlink-p) (lambda (&rest ignored)
                                                    (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-regular-p) (lambda (st) (eq st :regular)))
           (funcall thunk))
      (dolist (pair saved)
        (setf (symbol-function (car pair)) (cdr pair))))))

(defun nio-transaction-enumeration-bound-is-exact ()
  ;; The bound is the profile's max-transactions, which ACL2 reads from the
  ;; persisted values (fn-store-profile-max-transactions).  This raw test
  ;; loads no ACL2, so the one wrapper the enumeration asks answers T = 3
  ;; here; the host's own fnn-profile-nat check and readdir bound still run.
  (let ((saved (symbol-function 'fnn-core))
        (profile (list :profile-with-max-transactions 3)))
    (unwind-protect
         (flet ((name (n) (format nil "~20,'0d.txn" n))
                (store () (%make-fnn-store :root "/native-io-test" :config profile)))
           (setf (symbol-function 'fnn-core)
                 (lambda (wrapper &rest args)
                   (unless (and (eq wrapper 'fn-store-profile-max-transactions)
                                (equal args (list profile)))
                     (error "unexpected ACL2 call ~a" wrapper))
                   3))
           (nio-with-transaction-scan-stubs
            (loop for n below 3 collect (name n))
            (lambda ()
              (nio-check (equal (mapcar #'car (fnn-transaction-files (store))) '(0 1 2))
                         "transaction enumeration changed accepted bound behavior")))
           (nio-with-transaction-scan-stubs
            (loop for n below 4 collect (name n))
            (lambda ()
              (nio-check (nio-expects 'fnn-store-fault
                                      (lambda () (fnn-transaction-files (store))))
                         "transaction enumeration did not reject the first excess entry"))))
      (setf (symbol-function 'fnn-core) saved))))

(defun nio-bounded-directory-actual-boundary ()
  "Exercise readdir(3), not a substituted name list, at the BP evidence bound."
  (let* ((limit 8192)
         (root (format nil "/tmp/fn-native-bounded-directory-~d-~d"
                       (sb-posix:getpid) (get-internal-real-time))))
    (unwind-protect
         (progn
           (fnn-mkdir root #o700)
           (loop for number below limit do
             (with-open-file (stream (fnn-join root (format nil "~5,'0d.entry" number))
                                     :direction :output :if-exists :error)
               (declare (ignore stream))))
           (nio-check (= (length (fnn-list-directory-bounded
                                  root limit "native I/O test namespace"))
                         limit)
                      "bounded directory rejected its exact physical limit")
           (with-open-file (stream (fnn-join root "beyond-limit.entry")
                                   :direction :output :if-exists :error)
             (declare (ignore stream)))
           (nio-check (nio-expects 'fnn-store-fault
                                   (lambda ()
                                     (fnn-list-directory-bounded
                                      root limit "native I/O test namespace")))
                      "bounded directory retained an entry beyond its physical limit"))
      (when (probe-file root)
        (dolist (name (ignore-errors (fnn-list-directory root)))
          (ignore-errors (fnn-unlink (fnn-join root name))))
        (ignore-errors (sb-posix:rmdir root))))))

;; This exercises the real initializer helper with only its syscall boundary
;; substituted.  It pins the EEXIST handler to link(2): a later directory
;; fence error, even a synthetic EEXIST, is ambiguous after the final link and
;; must exit as uncertain rather than take the retry branch.
(defun nio-with-initial-publish-stubs (link-action barrier-action thunk)
  (let* ((symbols '(fnn-open fnn-write-all fnn-fsync-file fnn-close fnn-link
                    fnn-fsync-dir fnn-unlink fnn-random-hex))
         (saved (mapcar (lambda (symbol) (cons symbol (symbol-function symbol))) symbols)))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-open) (lambda (&rest ignored)
                                               (declare (ignore ignored)) 7)
                 (symbol-function 'fnn-write-all) (lambda (&rest ignored)
                                                    (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-fsync-file) (lambda (&rest ignored)
                                                     (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-close) (lambda (&rest ignored)
                                               (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-link) (lambda (&rest ignored)
                                              (declare (ignore ignored))
                                              (funcall link-action))
                 (symbol-function 'fnn-fsync-dir) (lambda (&rest ignored)
                                                   (declare (ignore ignored))
                                                   (funcall barrier-action))
                 (symbol-function 'fnn-unlink) (lambda (&rest ignored)
                                                (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-random-hex) (lambda (&rest ignored)
                                                    (declare (ignore ignored)) "test"))
           (funcall thunk))
      (dolist (pair saved)
        (setf (symbol-function (car pair)) (cdr pair))))))

(defun nio-initial-publish-error-origins ()
  (flet ((store () (%make-fnn-store :root "/native-initial-publish"))
         (publish (store)
           (fnn-publish-initial-file store "/native-initial-publish/config.json"
                                     (fnn-octets '(1)))))
    (let ((links 0) (barriers 0))
      (nio-with-initial-publish-stubs
       (lambda () (incf links) (fnn-os-fail sb-posix:eexist))
       (lambda () (incf barriers))
       (lambda ()
         (nio-check (eq (publish (store)) :existing)
                    "link EEXIST did not retain the immutable-existing outcome")
         (nio-check (= links 1) "link EEXIST did not issue exactly one link")
         (nio-check (zerop barriers) "link EEXIST reached the directory barrier"))))
    (dolist (errno (list sb-posix:eexist sb-posix:eio))
      (let ((links 0) (barriers 0))
        (nio-with-initial-publish-stubs
         (lambda () (incf links) nil)
         (lambda () (incf barriers) (fnn-os-fail errno))
         (lambda ()
           (let ((code (handler-case
                           (progn (publish (store)) :returned)
                         (error (e) (fnn-exit-code-for e)))))
             (nio-check (= code +fnn-exit-uncertain+)
                        "post-link errno ~d did not remain uncertain" errno)
             (nio-check (= links 1) "post-link errno ~d did not issue link" errno)
             (nio-check (= barriers 1) "post-link errno ~d did not reach barrier" errno))))))))

(defun nio-initial-publish-linked-cut-is-uncertain ()
  "A named injected error after successful link is in the ambiguity window."
  (let ((links 0) (barriers 0))
    (nio-with-initial-publish-stubs
     (lambda () (incf links))
     (lambda () (incf barriers))
     (lambda ()
       (let* ((store (%make-fnn-store
                      :root "/native-initial-publish"
                      :fault-point :init-config-linked
                      :fault-class 'fnn-os-error))
              (code (handler-case
                        (progn
                          (fnn-publish-initial-file
                           store "/native-initial-publish/config.json"
                           (fnn-octets '(1)) "init-config-")
                          :returned)
                      (error (e) (fnn-exit-code-for e)))))
         (nio-check (eql code +fnn-exit-uncertain+)
                    "post-link named cut did not preserve uncertainty")
         (nio-check (= links 1) "post-link named cut did not issue link")
         (nio-check (zerop barriers) "post-link named cut reached barrier"))))))

(defun nio-zero-writes-fault ()
  (let ((*fnn-write-syscall* (lambda (&rest ignored)
                                (declare (ignore ignored))
                                (values 0 nil))))
    (nio-check (nio-expects 'fnn-store-fault
                            (lambda () (fnn-write-all 9 (fnn-octets '(1)))))
               "zero store write did not fault")))

(defun nio-send-retries-with-one-deadline ()
  (let ((ticks 0) (attempts 0) (waits nil) (writes nil))
    (let ((*fnn-monotonic-ticks* (lambda () (incf ticks 100)))
          (*fnn-fd-waiter* (lambda (fd direction seconds)
                              (declare (ignore fd direction))
                              (push seconds waits)
                              t))
          (*fnn-write-syscall*
            (lambda (fd octets offset count)
              (declare (ignore fd octets))
              (push (list offset count) writes)
              (incf attempts)
              (case attempts
                (1 (values nil sb-posix:eintr))
                (2 (values 1 nil))
                (3 (values 1 nil))))))
      (fnn-send-all 9 (fnn-octets '(1 2)) 1)
      (setq waits (nreverse waits))
      (nio-check (= attempts 3) "socket write did not retry EINTR and resume partial write")
      (nio-check (equal (nreverse writes) '((0 2) (0 2) (1 1)))
                 "socket partial write did not resume at the unwritten offset")
      (nio-check (= (length waits) 2) "unexpected socket wait count")
      (nio-check (< (second waits) (first waits))
                 "socket retry reset its deadline instead of consuming it"))))

(defun nio-zero-send-faults ()
  (let ((*fnn-monotonic-ticks* #'get-internal-real-time)
        (*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
        (*fnn-write-syscall* (lambda (&rest ignored)
                                (declare (ignore ignored))
                                (values 0 nil))))
    (nio-check (nio-expects 'fnn-store-fault
                            (lambda () (fnn-send-all 9 (fnn-octets '(1)) 1)))
               "zero socket write did not fault")))

(defun nio-send-eagain-waits-again ()
  (let ((calls 0) (waits 0))
    (let ((*fnn-fd-waiter* (lambda (&rest ignored)
                              (declare (ignore ignored))
                              (incf waits) t))
          (*fnn-write-syscall* (lambda (&rest ignored)
                                 (declare (ignore ignored))
                                 (incf calls)
                                 (if (= calls 1)
                                     (values nil sb-posix:eagain)
                                     (values 1 nil)))))
      (fnn-send-all 9 (fnn-octets '(1)) 1)
      (nio-check (= waits 2) "send retried EAGAIN without a second readiness wait")
      (nio-check (= calls 2) "send did not retry EAGAIN"))))

(defun nio-zero-send-eagain-does-not-spin ()
  (let ((waits 0) (calls 0))
    (let ((*fnn-monotonic-ticks* (lambda () 0))
          (*fnn-fd-waiter* (lambda (&rest ignored)
                              (declare (ignore ignored))
                              (incf waits) t))
          (*fnn-write-syscall* (lambda (&rest ignored)
                                 (declare (ignore ignored))
                                 (incf calls)
                                 (values nil sb-posix:eagain))))
      (nio-check (nio-expects 'fnn-os-error
                              (lambda () (fnn-send-all 9 (fnn-octets '(1)) 0)))
                 "zero-time EAGAIN send was not a timeout")
      (nio-check (= waits 1) "zero-time EAGAIN send busy-spun readiness waits")
      (nio-check (= calls 1) "zero-time EAGAIN send busy-spun syscalls"))))

(defun nio-actual-socketpair-peer-close-and-backpressure ()
  (multiple-value-bind (sender receiver) (nio-socketpair)
    (unwind-protect
         (progn
           (fnn-set-nonblocking sender)
           (fnn-set-nonblocking receiver)
           (let ((flags (sb-posix:fcntl sender sb-posix:f-getfl)))
             (nio-check (not (zerop (logand flags sb-posix:o-nonblock)))
                        "socket descriptor was not made nonblocking"))
           ;; A peer that has already closed is a real EOF, not a timeout or
           ;; refusal.  This uses the production unix-read and waiter seams.
           (fnn-close receiver)
           (setq receiver nil)
           (let ((received (fnn-recv sender 0.1)))
             (nio-check (and (typep received 'fnn-octets) (zerop (length received)))
                        "closed socketpair peer did not produce EOF")))
      (when sender (ignore-errors (fnn-close sender)))
      (when receiver (ignore-errors (fnn-close receiver)))))
  ;; A separate pair leaves its peer unread.  The production nonblocking
  ;; write eventually reaches EAGAIN and the readiness wait honors the single
  ;; deadline instead of blocking inside unix-write.
  (multiple-value-bind (sender receiver) (nio-socketpair)
    (unwind-protect
         (progn
           (fnn-set-nonblocking sender)
           (fnn-set-nonblocking receiver)
           (nio-check (nio-expects 'fnn-os-error
                                   (lambda ()
                                     (fnn-send-all sender
                                                   (fnn-make-octets (* 8 1024 1024))
                                                   0.1)))
                      "unread socketpair peer did not time out under backpressure"))
      (ignore-errors (fnn-close sender))
      (ignore-errors (fnn-close receiver)))))

(defun nio-send-eintr-obeys-deadline ()
  (let ((ticks 0))
    (let ((*fnn-monotonic-ticks* (lambda () (incf ticks 600000)))
          (*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
          (*fnn-write-syscall* (lambda (&rest ignored)
                                  (declare (ignore ignored))
                                  (values nil sb-posix:eintr))))
      (nio-check (nio-expects 'fnn-os-error
                              (lambda () (fnn-send-all 9 (fnn-octets '(1)) 1)))
                 "repeated EINTR bypassed the socket deadline"))))

(defun nio-recv-eintr-obeys-deadline ()
  (let ((ticks 0))
    (let ((*fnn-monotonic-ticks* (lambda () (incf ticks 600000)))
          (*fnn-fd-waiter* (lambda (&rest ignored) (declare (ignore ignored)) t))
          (*fnn-read-syscall* (lambda (&rest ignored)
                                (declare (ignore ignored))
                                (values nil sb-posix:eintr))))
      (nio-check (nio-expects 'fnn-os-error (lambda () (fnn-recv 9 1)))
                 "read EINTR retry bypassed the receive deadline"))))

(defun nio-core-boundary-faults ()
  (let ((old-counterpart (symbol-function 'fnn-counterpart))
        (old-call (symbol-function 'fnn-call)))
    (unwind-protect
         (progn
           (setf (symbol-function 'nio-core-boom) (lambda (&rest ignored)
                                                      (declare (ignore ignored))
                                                      (error "injected core error")))
           (setf (symbol-function 'fnn-counterpart) (lambda (name)
                                                       (declare (ignore name))
                                                       'nio-core-boom))
           (nio-check (nio-expects 'fnn-store-fault (lambda () (fnn-call 'nio-core)))
                      "thrown core condition was not a fault")
           (setf (symbol-function 'fnn-call) (lambda (&rest ignored)
                                                (declare (ignore ignored))
                                                (list t :bad-state)))
           (nio-check (nio-expects 'fnn-store-fault (lambda () (fnn-core-state 'nio-core)))
                      "core erp was not a fault")
           (nio-check (nio-expects 'fnn-store-fault (lambda () (fnn-nat :not-a-natural)))
                      "malformed natural result was not a fault")
           (nio-check (nio-expects 'fnn-store-fault (lambda () (fnn-as-octets '(256))))
                      "malformed octet result was not a fault")
           (nio-check (eq (fnn-action :refused) :refused)
                      "explicit semantic refusal was not preserved"))
      (setf (symbol-function 'fnn-counterpart) old-counterpart
            (symbol-function 'fnn-call) old-call))))

(defun nio-outcome-taxonomy ()
  (nio-check (= (fnn-exit-code-for
                 (make-condition 'fnn-store-indeterminate :message "test"))
                +fnn-exit-uncertain+)
             "indeterminate did not retain exit 3")
  (nio-check (= (fnn-exit-code-for
                 (make-condition 'fnn-store-fault :message "test"))
                +fnn-exit-fault+)
             "fault did not retain exit 4")
  (nio-check (= (fnn-exit-code-for
                 (make-condition 'fnn-store-error :message "test"))
                +fnn-exit-refused+)
             "semantic refusal did not retain exit 1"))

(defun nio-with-reader-stubs (thunk)
  (let* ((symbols '(fnn-socket-fd fnn-socket-shut fnn-send-all fnn-reader-reset
                    fnn-recv fnn-reader-chunk))
         (saved (mapcar (lambda (symbol) (cons symbol (symbol-function symbol))) symbols)))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-socket-fd) (lambda (socket)
                                                    (declare (ignore socket)) 9)
                 (symbol-function 'fnn-socket-shut) (lambda (socket)
                                                      (declare (ignore socket)) nil)
                 (symbol-function 'fnn-send-all) (lambda (&rest ignored)
                                                   (declare (ignore ignored)) t)
                 (symbol-function 'fnn-reader-reset) (lambda () (fnn-make-octets 0))
                 (symbol-function 'fnn-recv) (lambda (&rest ignored)
                                               (declare (ignore ignored))
                                               (fnn-octets '(65))))
           (funcall thunk))
      (dolist (pair saved)
        (setf (symbol-function (car pair)) (cdr pair))))))

(defun nio-reader-preserves-subtypes ()
  (flet ((serve (thunk)
           (nio-with-reader-stubs
            (lambda ()
              (setf (symbol-function 'fnn-reader-chunk)
                    (lambda (octets) (declare (ignore octets)) (funcall thunk)))
              (fnn-serve-client :test-socket)))))
    (nio-check (nio-expects 'fnn-store-indeterminate
                            (lambda () (serve (lambda () (fnn-indeterminate "test")))))
               "reader collapsed indeterminate into a connection refusal")
    (nio-check (nio-expects 'fnn-store-fault
                            (lambda () (serve (lambda () (fnn-fault "test")))))
               "reader collapsed fault into a connection refusal")
    (nio-check (null (serve (lambda () (fnn-refuse "test"))))
               "reader did not retain semantic refusal as a connection-only result")))

(nio-read-eintr-then-data)
(nio-read-eof-remains-zero)
(nio-read-eagain-waits-again)
(nio-zero-recv-polls-once)
(nio-zero-recv-eagain-does-not-spin)
(nio-recv-honors-caller-bound-before-read)
(nio-connects-loopback-nonblocking)
(nio-connect-preserves-refusal-errno)
(nio-connect-pending-completion-and-deadline)
(nio-connect-pending-timeout-does-not-reset-deadline)
(nio-zero-connect-poll-does-not-spin)
(nio-wrong-condition-is-rejected)
(nio-store-write-progress)
(nio-transaction-enumeration-bound-is-exact)
(nio-bounded-directory-actual-boundary)

(nio-initial-publish-error-origins)
(nio-initial-publish-linked-cut-is-uncertain)
(nio-zero-writes-fault)
(nio-send-retries-with-one-deadline)
(nio-zero-send-faults)
(nio-send-eagain-waits-again)
(nio-zero-send-eagain-does-not-spin)
(nio-send-eintr-obeys-deadline)
(nio-recv-eintr-obeys-deadline)
(nio-core-boundary-faults)
(nio-outcome-taxonomy)
(nio-reader-preserves-subtypes)
(nio-actual-socketpair-peer-close-and-backpressure)
(format t "native-io-progress: ok~%")

;; The configuration namespace test substitutes only the core decision and
;; syscalls.  It exercises the actual raw observer and rejects a regression to
;; the unbounded/suffix-filter helper before the bridge is reached.
(defun nio-with-config-observation-stubs (names thunk)
  (let* ((symbols '(fnn-list-directory fnn-list-directory-bounded
                    fnn-bridge-config-observation-limit
                    fnn-bridge-config-observation fnn-lstat fnn-symlink-p
                    fnn-regular-p fnn-read-regular-bounded))
         (saved (mapcar (lambda (symbol) (cons symbol (symbol-function symbol))) symbols)))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-list-directory)
                 (lambda (&rest ignored) (declare (ignore ignored))
                   (error "unbounded configuration enumeration"))
                 (symbol-function 'fnn-list-directory-bounded)
                 (lambda (path limit namespace)
                   (declare (ignore path))
                   (nio-check (string= namespace "configuration namespace")
                              "config observer used the wrong namespace label")
                   (when (> (length names) limit)
                     (fnn-fault "configuration namespace exceeds ACL2 observation bound"))
                   names)
                 (symbol-function 'fnn-bridge-config-observation-limit)
                 (lambda () 2)
                 (symbol-function 'fnn-lstat)
                 (lambda (&rest ignored) (declare (ignore ignored)) :regular)
                 (symbol-function 'fnn-symlink-p)
                 (lambda (&rest ignored) (declare (ignore ignored)) nil)
                 (symbol-function 'fnn-regular-p) (lambda (st) (eq st :regular))
                 (symbol-function 'fnn-read-regular-bounded)
                 (lambda (path limit)
                   (declare (ignore limit))
                   (fnn-octets (if (search "00000001.cfg" path) '(1) '(2))))
                 (symbol-function 'fnn-bridge-config-observation)
                 (lambda (observed &optional initializing)
                   (declare (ignore initializing))
                   (nio-check (= (length observed) (length names))
                              "config observer lost an observed entry")
                   ;; The raw code must consume this ACL2-issued ordering,
                   ;; not sort/filter names a second time.
                   (reverse observed)))
           (funcall thunk))
      (dolist (pair saved)
        (setf (symbol-function (car pair)) (cdr pair))))))

(defun nio-config-enumeration-is-bounded-and-core-ordered ()
  (let ((store (make-fnn-store "/native-config-observer")))
    (nio-with-config-observation-stubs
     '("00000001.cfg" "00000002.cfg")
     (lambda ()
       (nio-check (equal (mapcar #'car (fnn-config-record-observation store))
                         '("00000002.cfg" "00000001.cfg"))
                  "config observer did not consume ACL2 plan ordering")))
    (nio-with-config-observation-stubs
     '("00000001.cfg" "00000002.cfg" "00000003.cfg")
     (lambda ()
       (nio-check (nio-expects 'fnn-store-fault
                               (lambda () (fnn-config-record-observation store)))
                  "config observer accepted the first entry beyond its ACL2 bound")))))

(nio-config-enumeration-is-bounded-and-core-ordered)
(format t "native-config-observation: ok~%")
