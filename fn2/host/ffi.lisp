; A5r OS boundary (layer doc 4.1.3): raw SBCL, loaded only by a session
; script after the certified books. Byte arguments are SAPs into the pool's
; array or startup-allocated windows; no payload list or string crosses.
; Each wrapper returns the syscall's result and its errno; EINTR is retried
; a bounded number of times and every other errno is returned to the caller.
; Reviewed from the compost on fn2/a5-native-wip (6a6170a35): the storage,
; entropy and errno-to-reason pieces are gone (normalization is the logical
; fn2-host-result), accept keeps the peer's sockaddr, the listener binds port
; 0 and reports it, and the mux has a control slot for the session's stdin.
(in-package "ACL2")

(sb-alien:define-alien-routine ("socket" %fn2-native-socket) sb-alien:int
  (domain sb-alien:int) (kind sb-alien:int) (protocol sb-alien:int))
(sb-alien:define-alien-routine ("socketpair" %fn2-native-socketpair) sb-alien:int
  (domain sb-alien:int) (kind sb-alien:int) (protocol sb-alien:int)
  (fds sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("setsockopt" %fn2-native-setsockopt) sb-alien:int
  (fd sb-alien:int) (level sb-alien:int) (option sb-alien:int)
  (value sb-sys:system-area-pointer) (length sb-alien:unsigned-int))
(sb-alien:define-alien-routine ("bind" %fn2-native-bind) sb-alien:int
  (fd sb-alien:int) (address sb-sys:system-area-pointer) (length sb-alien:unsigned-int))
(sb-alien:define-alien-routine ("listen" %fn2-native-listen) sb-alien:int
  (fd sb-alien:int) (backlog sb-alien:int))
(sb-alien:define-alien-routine ("getsockname" %fn2-native-getsockname) sb-alien:int
  (fd sb-alien:int) (address sb-sys:system-area-pointer) (length sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("accept" %fn2-native-accept) sb-alien:int
  (fd sb-alien:int) (address sb-sys:system-area-pointer) (length sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("recv" %fn2-native-recv) sb-alien:long
  (fd sb-alien:int) (buffer sb-sys:system-area-pointer)
  (length sb-alien:unsigned-long) (flags sb-alien:int))
(sb-alien:define-alien-routine ("send" %fn2-native-send) sb-alien:long
  (fd sb-alien:int) (buffer sb-sys:system-area-pointer)
  (length sb-alien:unsigned-long) (flags sb-alien:int))
(sb-alien:define-alien-routine ("shutdown" %fn2-native-shutdown) sb-alien:int
  (fd sb-alien:int) (how sb-alien:int))
(sb-alien:define-alien-routine ("close" %fn2-native-close) sb-alien:int (fd sb-alien:int))
(sb-alien:define-alien-routine ("chmod" %fn2-native-chmod) sb-alien:int
  (path sb-sys:system-area-pointer) (mode sb-alien:unsigned-int))
(sb-alien:define-alien-routine ("unlink" %fn2-native-unlink) sb-alien:int
  (path sb-sys:system-area-pointer))
#+linux
(sb-alien:define-alien-routine ("getsockopt" %fn2-native-getsockopt) sb-alien:int
  (fd sb-alien:int) (level sb-alien:int) (option sb-alien:int)
  (value sb-sys:system-area-pointer) (length sb-sys:system-area-pointer))
#+darwin
(sb-alien:define-alien-routine ("getpeereid" %fn2-native-getpeereid) sb-alien:int
  (fd sb-alien:int) (uid sb-sys:system-area-pointer) (gid sb-sys:system-area-pointer))
;; &OPTIONAL marks C variadic arguments in SBCL's alien function type.
;; Darwin arm64 places them on the stack, unlike fixed prototype arguments.
(defun %fn2-native-fcntl (fd command argument)
  (sb-alien:alien-funcall
   (sb-alien:extern-alien "fcntl"
     (function sb-alien:int sb-alien:int sb-alien:int &optional sb-alien:long))
   fd command argument))
(sb-alien:define-alien-routine ("clock_gettime" %fn2-native-clock-gettime) sb-alien:int
  (clock-id sb-alien:int) (timespec sb-sys:system-area-pointer))
(sb-alien:define-alien-routine (#+linux "__errno_location" #+darwin "__error" %fn2-native-errno-pointer)
    sb-sys:system-area-pointer)
(sb-alien:define-alien-routine ("mmap" %fn2-native-mmap) sb-sys:system-area-pointer
  (address sb-sys:system-area-pointer) (length sb-alien:unsigned-long)
  (protection sb-alien:int) (flags sb-alien:int) (fd sb-alien:int) (offset sb-alien:long-long))
(sb-alien:define-alien-routine ("munmap" %fn2-native-munmap) sb-alien:int
  (address sb-sys:system-area-pointer) (length sb-alien:unsigned-long))
#+linux
(progn
  (sb-alien:define-alien-routine ("epoll_create1" %fn2-native-epoll-create) sb-alien:int (flags sb-alien:int))
  (sb-alien:define-alien-routine ("epoll_ctl" %fn2-native-epoll-ctl) sb-alien:int
    (epfd sb-alien:int) (operation sb-alien:int) (fd sb-alien:int) (event sb-sys:system-area-pointer))
  (sb-alien:define-alien-routine ("epoll_wait" %fn2-native-epoll-wait) sb-alien:int
    (epfd sb-alien:int) (events sb-sys:system-area-pointer)
    (capacity sb-alien:int) (timeout sb-alien:int)))
#+darwin
(sb-alien:define-alien-routine ("poll" %fn2-native-poll) sb-alien:int
  (fds sb-sys:system-area-pointer) (count sb-alien:unsigned-int) (timeout sb-alien:int))

(defun fn2-native-errno () (sb-sys:signed-sap-ref-32 (%fn2-native-errno-pointer) 0))
(defconstant +fn2-native-eintr-retries+ 8)
(defmacro fn2-native-syscall (form)
  ;; EINTR is retried at most +fn2-native-eintr-retries+ times; then the
  ;; caller sees it like any other errno (an op stays waiting).
  `(loop for tries from 0
         for result = ,form
         for error = (if (minusp result) (fn2-native-errno) 0)
         unless (and (= error 4) (< tries +fn2-native-eintr-retries+)) return (values result error)))
(defun fn2-native-required (result error operation)
  (when (minusp result) (error "fn2 host ~a failed: errno ~d" operation error))
  result)
(defmacro fn2-native-require-call (operation form)
  `(multiple-value-bind (result error) (fn2-native-syscall ,form)
     (fn2-native-required result error ,operation)))

(defun fn2-native-window (size)
  "Anonymous mmap is page aligned and zero filled; callers retain its size."
  (let ((sap (%fn2-native-mmap (sb-sys:int-sap 0) size 3
                         #+linux #x22 #+darwin #x1002 -1 0)))
    (when (= (sb-sys:sap-int sap) #xffffffffffffffff)
      (error "fn2 host mmap(~d) failed: errno ~d" size (fn2-native-errno)))
    sap))
(defun fn2-native-unmap (sap size)
  (fn2-native-syscall (%fn2-native-munmap sap size)))
(defun fn2-native-socket-option (fd option value)
  (sb-alien:with-alien ((v sb-alien:int value))
    (fn2-native-syscall (%fn2-native-setsockopt fd #+linux 1 #+darwin #xffff option
                                 (sb-alien:alien-sap (sb-alien:addr v)) 4))))
(defun fn2-native-configure-socket (fd)
  (multiple-value-bind (flags err) (fn2-native-syscall (%fn2-native-fcntl fd 3 0))
    (when (minusp flags) (return-from fn2-native-configure-socket (values flags err)))
    (multiple-value-bind (r e) (fn2-native-syscall (%fn2-native-fcntl fd 4 (logior flags #+linux #x800 #+darwin 4)))
      (when (minusp r) (return-from fn2-native-configure-socket (values r e)))))
  (multiple-value-bind (r e) (fn2-native-syscall (%fn2-native-fcntl fd 2 1))
    (when (minusp r) (return-from fn2-native-configure-socket (values r e))))
  #+darwin (fn2-native-socket-option fd #x1022 1)
  #+linux (values 0 0))

(defun fn2-native-listen (port &optional (address #x7f000001) (backlog 128))
  "Startup IPv4 TCP listener (PORT 0: the kernel chooses). Values: fd and the bound port."
  (let ((fd (fn2-native-require-call :socket (%fn2-native-socket 2 1 0))) (ok nil))
    (unwind-protect
         (sb-alien:with-alien ((address-bytes (array sb-alien:unsigned-char 16))
                               (length sb-alien:unsigned-int 16))
           (multiple-value-call #'fn2-native-required (fn2-native-configure-socket fd) :socket-options)
           (multiple-value-call #'fn2-native-required (fn2-native-socket-option fd #+linux 2 #+darwin 4 1) :reuseaddr)
           (let ((sap (sb-alien:alien-sap address-bytes)))
             (dotimes (i 16) (setf (sb-sys:sap-ref-8 sap i) 0))
             #+linux (setf (sb-sys:sap-ref-16 sap 0) 2)
             #+darwin (setf (sb-sys:sap-ref-8 sap 0) 16 (sb-sys:sap-ref-8 sap 1) 2)
             (setf (sb-sys:sap-ref-8 sap 2) (ldb (byte 8 8) port)
                   (sb-sys:sap-ref-8 sap 3) (ldb (byte 8 0) port))
             (dotimes (i 4) (setf (sb-sys:sap-ref-8 sap (+ 4 i)) (ldb (byte 8 (* 8 (- 3 i))) address)))
             (fn2-native-require-call :bind (%fn2-native-bind fd sap 16))
             (fn2-native-require-call :listen (%fn2-native-listen fd backlog))
             (fn2-native-require-call :getsockname
               (%fn2-native-getsockname fd sap (sb-alien:alien-sap (sb-alien:addr length))))
             (setf ok t)
             (values fd (+ (* 256 (sb-sys:sap-ref-8 sap 2)) (sb-sys:sap-ref-8 sap 3)))))
      (unless ok (fn2-native-syscall (%fn2-native-close fd))))))

;;; The owner-only Unix-domain listener at PATH (the profile's :listener-path,
;;; validated by fn2-host-listener-pathp: absolute, no NUL, at most 103
;;; octets). bind creates the socket file; chmod makes it 0600 before listen,
;;; so no connection is accepted while it is wider. An existing file at PATH
;;; is a named refusal (:local-bind with the errno): the node never removes a
;;; file it did not create. Values: fd.
(defun fn2-native-sockaddr-local (sap path)
  "sockaddr_un for PATH at SAP (zeroed, 110 octets). Value: its length."
  (dotimes (i 110) (setf (sb-sys:sap-ref-8 sap i) 0))
  (let ((at #+linux 2 #+darwin 2) (n (length path)))
    #+linux (setf (sb-sys:sap-ref-16 sap 0) 1)
    #+darwin (setf (sb-sys:sap-ref-8 sap 0) (+ at n 1) (sb-sys:sap-ref-8 sap 1) 1)
    (dotimes (i n) (setf (sb-sys:sap-ref-8 sap (+ at i)) (char-code (char path i))))
    (+ at n 1)))
(defun fn2-native-listen-local (path &optional (backlog 128))
  (let ((fd (fn2-native-require-call :local-socket (%fn2-native-socket 1 1 0))) (ok nil))
    (unwind-protect
         (sb-alien:with-alien ((address-bytes (array sb-alien:unsigned-char 112)))
           (let* ((sap (sb-alien:alien-sap address-bytes))
                  (length (fn2-native-sockaddr-local sap path)))
             (multiple-value-call #'fn2-native-required (fn2-native-configure-socket fd) :local-socket-options)
             (fn2-native-require-call :local-bind (%fn2-native-bind fd sap length))
             ;; From here the file is ours: a failure removes it.
             (unwind-protect
                  (progn
                    (fn2-native-require-call :local-chmod (%fn2-native-chmod (sb-sys:sap+ sap 2) #o600))
                    (fn2-native-require-call :local-listen (%fn2-native-listen fd backlog))
                    (setf ok t)
                    fd)
               (unless ok (fn2-native-syscall (%fn2-native-unlink (sb-sys:sap+ sap 2)))))))
      (unless ok (fn2-native-syscall (%fn2-native-close fd))))))
(defun fn2-native-unlink-local (path)
  "Remove the socket file this node's fn2-native-listen-local created."
  (sb-alien:with-alien ((address-bytes (array sb-alien:unsigned-char 112)))
    (let ((sap (sb-alien:alien-sap address-bytes)))
      (fn2-native-sockaddr-local sap path)
      (fn2-native-syscall (%fn2-native-unlink (sb-sys:sap+ sap 2))))))

;;; accept(2) with the peer's sockaddr. Values: fd (or -1), errno, family
;;; (:inet :inet6 :local :none), port, w0..w3 (network order, most
;;; significant first). Families by the kernel's numbering per platform.
(defun fn2-native-sap-word (sap at)
  (logior (ash (sb-sys:sap-ref-8 sap at) 24) (ash (sb-sys:sap-ref-8 sap (+ at 1)) 16)
          (ash (sb-sys:sap-ref-8 sap (+ at 2)) 8) (sb-sys:sap-ref-8 sap (+ at 3))))
(defun fn2-native-accept (fd)
  (sb-alien:with-alien ((peer (array sb-alien:unsigned-char 128))
                        (length sb-alien:unsigned-int 128))
    (let ((sap (sb-alien:alien-sap peer)))
      (multiple-value-bind (new error)
          (fn2-native-syscall (%fn2-native-accept fd sap (sb-alien:alien-sap (sb-alien:addr length))))
        (if (minusp new) (values new error :none 0 0 0 0 0)
          (multiple-value-bind (r e) (fn2-native-configure-socket new)
            (if (minusp r)
                (progn (fn2-native-syscall (%fn2-native-close new)) (values r e :none 0 0 0 0 0))
              (let ((family #+linux (sb-sys:sap-ref-16 sap 0) #+darwin (sb-sys:sap-ref-8 sap 1))
                    (port (+ (* 256 (sb-sys:sap-ref-8 sap 2)) (sb-sys:sap-ref-8 sap 3))))
                (cond ((= family 2) (values new 0 :inet port (fn2-native-sap-word sap 4) 0 0 0))
                      ((= family #+linux 10 #+darwin 30)
                       (values new 0 :inet6 port (fn2-native-sap-word sap 8) (fn2-native-sap-word sap 12)
                               (fn2-native-sap-word sap 16) (fn2-native-sap-word sap 20)))
                      ((= family 1) (values new 0 :local 0 0 0 0 0))
                      (t (values new 0 :none 0 0 0 0 0)))))))))))
;;; accept(2) on the Unix-domain listener: the peer is its credentials, read
;;; from the kernel (getpeereid on Darwin, SO_PEERCRED on Linux), never from
;;; the sockaddr (an unnamed client has none). Values as fn2-native-accept:
;;; fd (or -1), errno, :local, port 0, w0 = uid, w1 = gid, 0, 0. A failed
;;; credential read closes the connection and is the accept's failure.
(defun fn2-native-peer-credentials (fd)
  "Values: result, errno, uid, gid."
  #+darwin
  (sb-alien:with-alien ((uid sb-alien:unsigned-int 0) (gid sb-alien:unsigned-int 0))
    (multiple-value-bind (r e)
        (fn2-native-syscall (%fn2-native-getpeereid fd (sb-alien:alien-sap (sb-alien:addr uid))
                                                    (sb-alien:alien-sap (sb-alien:addr gid))))
      (values r e uid gid)))
  #+linux
  (sb-alien:with-alien ((cred (array sb-alien:unsigned-int 3)) (length sb-alien:unsigned-int 12))
    (multiple-value-bind (r e)
        (fn2-native-syscall (%fn2-native-getsockopt fd 1 17 (sb-alien:alien-sap cred)
                                                    (sb-alien:alien-sap (sb-alien:addr length))))
      (values r e (sb-alien:deref cred 1) (sb-alien:deref cred 2)))))
(defun fn2-native-accept-local (fd)
  (sb-alien:with-alien ((peer (array sb-alien:unsigned-char 112))
                        (length sb-alien:unsigned-int 112))
    (multiple-value-bind (new error)
        (fn2-native-syscall (%fn2-native-accept fd (sb-alien:alien-sap peer) (sb-alien:alien-sap (sb-alien:addr length))))
      (if (minusp new) (values new error :none 0 0 0 0 0)
        (multiple-value-bind (r e) (fn2-native-configure-socket new)
          (if (minusp r)
              (progn (fn2-native-syscall (%fn2-native-close new)) (values r e :none 0 0 0 0 0))
            (multiple-value-bind (r e uid gid) (fn2-native-peer-credentials new)
              (if (minusp r)
                  (progn (fn2-native-syscall (%fn2-native-close new)) (values r e :none 0 0 0 0 0))
                (values new 0 :local 0 uid gid 0 0)))))))))
(defun fn2-native-recv (fd sap length) (fn2-native-syscall (%fn2-native-recv fd sap length 0)))
(defun fn2-native-send (fd sap length)
  (fn2-native-syscall (%fn2-native-send fd sap length #+linux #x4000 #+darwin 0)))
(defun fn2-native-shutdown (fd) (fn2-native-syscall (%fn2-native-shutdown fd 1)))
(defun fn2-native-close (fd)
  ;; Executor is single threaded: no descriptor can be reused during EINTR.
  (fn2-native-syscall (%fn2-native-close fd)))
(defun fn2-native-abort-socket (fd)
  (sb-alien:with-alien ((linger (array sb-alien:int 2)))
    (setf (sb-alien:deref linger 0) 1 (sb-alien:deref linger 1) 0)
    (fn2-native-syscall (%fn2-native-setsockopt fd #+linux 1 #+darwin #xffff
                                 #+linux 13 #+darwin #x80 (sb-alien:alien-sap linger) 8))))

(defun fn2-native-clock (monotonicp)
  "Microseconds (the clock mailbox's unit; DATE reads realtime in microseconds)."
  (sb-alien:with-alien ((ts (array sb-alien:long 2)))
    (fn2-native-require-call :clock
      (%fn2-native-clock-gettime (if monotonicp #+linux 1 #+darwin 6 0) (sb-alien:alien-sap ts)))
    (+ (* 1000000 (sb-alien:deref ts 0)) (floor (sb-alien:deref ts 1) 1000))))

#+linux
(defconstant +fn2-native-epoll-event-size+ #+x86-64 12 #-x86-64 16)
#+linux
(defconstant +fn2-native-epoll-data-offset+ #+x86-64 4 #-x86-64 8)

;;; One registered descriptor per capability. The adapter folds simultaneous
;;; interests into the mask, and unregisters before closing/reusing the fd.
;;; Buffers/arrays allocate at startup only. mask uses POLLIN=1 / POLLOUT=4.
(defstruct (fn2-native-mux (:constructor %make-fn2-native-mux))
  (capacity 0) (fd -1) fds masks ready events control
  (wake-read -1) (wake-write -1) wake-buffer)
(declaim (ftype (function (t t t t) t) fn2-native-mux-interest))
(defun make-fn2-native-mux (capacity)
  ;; Slots: CAPACITY capabilities, then the listener's second socket (the
  ;; Unix-domain one, capability 0's), then the signal wake, then the control fd.
  (let* ((total (+ 3 capacity))
         (mux (%make-fn2-native-mux
          :capacity total :fd #+linux (fn2-native-require-call :epoll-create (%fn2-native-epoll-create #x80000)) #+darwin -1
          :fds (make-array total :element-type 'fixnum :initial-element -1)
          :masks (make-array total :element-type '(unsigned-byte 32) :initial-element 0)
          :ready (make-array total :element-type '(unsigned-byte 32) :initial-element 0)
          :events (fn2-native-window (* total #+linux +fn2-native-epoll-event-size+ #+darwin 8))
          :control #+linux (fn2-native-window +fn2-native-epoll-event-size+) #+darwin nil
          :wake-buffer (fn2-native-window 256))))
    #+darwin
    (dotimes (i total)
      (setf (sb-sys:signed-sap-ref-32 (fn2-native-mux-events mux) (* i 8)) -1))
    (sb-alien:with-alien ((pair (array sb-alien:int 2)))
      (fn2-native-require-call :signal-socketpair
        (%fn2-native-socketpair 1 1 0 (sb-alien:alien-sap pair)))
      (setf (fn2-native-mux-wake-read mux) (sb-alien:deref pair 0)
            (fn2-native-mux-wake-write mux) (sb-alien:deref pair 1)))
    (multiple-value-call #'fn2-native-required
      (fn2-native-configure-socket (fn2-native-mux-wake-read mux)) :signal-reader)
    (multiple-value-call #'fn2-native-required
      (fn2-native-configure-socket (fn2-native-mux-wake-write mux)) :signal-writer)
    ;; This permanent internal slot closes the signal-before-poll race.
    (fn2-native-mux-interest mux (1+ capacity) (fn2-native-mux-wake-read mux) 1)
    mux))
(defun fn2-native-mux-local-index (mux) (- (fn2-native-mux-capacity mux) 3))
(defun fn2-native-mux-signal (mux)
  "Handler wake transport, not an operation completion. The sticky bit is set
before this call. EAGAIN means an earlier wake byte is already unread. No core
function runs here, and a failed wake send never manufactures a completion."
  (let ((saved-errno (fn2-native-errno)))
    (unwind-protect
         (fn2-native-send (fn2-native-mux-wake-write mux) (fn2-native-mux-wake-buffer mux) 1)
      ;; A signal can arrive between a data syscall and errno capture.
      (setf (sb-sys:signed-sap-ref-32 (%fn2-native-errno-pointer) 0) saved-errno))))
(defun fn2-native-mux-interest (mux index fd mask)
  (let ((previous-fd (aref (fn2-native-mux-fds mux) index))
        (previous-mask (aref (fn2-native-mux-masks mux) index)))
    (unless (and (= previous-fd fd) (= previous-mask mask))
      #+linux
      (let ((control (fn2-native-mux-control mux)))
        (when (and (plusp previous-mask) (or (zerop mask) (/= previous-fd fd)))
          (fn2-native-require-call :epoll-delete
            (%fn2-native-epoll-ctl (fn2-native-mux-fd mux) 2 previous-fd (sb-sys:int-sap 0))))
        (when (plusp mask)
          ;; Linux packs epoll_event on x86_64; other 64-bit ABIs align data.
          (setf (sb-sys:sap-ref-32 control 0) mask
                (sb-sys:sap-ref-64 control +fn2-native-epoll-data-offset+) index)
          (fn2-native-require-call :epoll-interest
            (%fn2-native-epoll-ctl (fn2-native-mux-fd mux)
                            (if (and (plusp previous-mask) (= previous-fd fd)) 3 1)
                            fd control))))
      #+darwin
      (let ((offset (* index 8)) (events (fn2-native-mux-events mux)))
        (setf (sb-sys:signed-sap-ref-32 events offset) (if (zerop mask) -1 fd)
              (sb-sys:sap-ref-16 events (+ offset 4)) mask
              (sb-sys:sap-ref-16 events (+ offset 6)) 0))
      (setf (aref (fn2-native-mux-fds mux) index) fd
            (aref (fn2-native-mux-masks mux) index) mask))))
(defun fn2-native-mux-wait (mux timeout-ms)
  "Only the executor calls this, using the core's idle deadline. EINTR returns
:INTERRUPTED, without a core completion: the sticky signal is harvested next.
Re-entering with a fresh core deadline avoids resetting a timeout on EINTR."
  (fill (fn2-native-mux-ready mux) 0)
  (let* ((n #+linux (%fn2-native-epoll-wait (fn2-native-mux-fd mux) (fn2-native-mux-events mux)
                                    (fn2-native-mux-capacity mux) timeout-ms)
            #+darwin (%fn2-native-poll (fn2-native-mux-events mux) (fn2-native-mux-capacity mux) timeout-ms))
         (error (if (minusp n) (fn2-native-errno) 0)))
    (when (= error 4) (return-from fn2-native-mux-wait :interrupted))
    (fn2-native-required n error :wait)
    #+linux
    (dotimes (i n)
      (let* ((offset (* i +fn2-native-epoll-event-size+))
             (index (sb-sys:sap-ref-64 (fn2-native-mux-events mux) (+ offset +fn2-native-epoll-data-offset+))))
        (setf (aref (fn2-native-mux-ready mux) index) (sb-sys:sap-ref-32 (fn2-native-mux-events mux) offset))))
    #+darwin
    (dotimes (i (fn2-native-mux-capacity mux))
      (setf (aref (fn2-native-mux-ready mux) i) (sb-sys:sap-ref-16 (fn2-native-mux-events mux) (+ (* i 8) 6))))
    (when (plusp (aref (fn2-native-mux-ready mux) (- (fn2-native-mux-capacity mux) 2)))
      ;; One bounded drain. More signals leave the fd readable for the next
      ;; turn; the one sticky shutdown bit represents all of these wakes.
      (fn2-native-recv (fn2-native-mux-wake-read mux) (fn2-native-mux-wake-buffer mux) 256))
    n))
(defun fn2-native-mux-ready-p (mux index mask)
  (not (zerop (logand (aref (fn2-native-mux-ready mux) index) (logior mask 8 16 32)))))
(defun fn2-native-mux-destroy (mux)
  #+linux (progn (fn2-native-close (fn2-native-mux-fd mux)) (fn2-native-unmap (fn2-native-mux-control mux) +fn2-native-epoll-event-size+))
  (fn2-native-close (fn2-native-mux-wake-read mux))
  (fn2-native-close (fn2-native-mux-wake-write mux))
  (fn2-native-unmap (fn2-native-mux-wake-buffer mux) 256)
  (fn2-native-unmap (fn2-native-mux-events mux) (* (fn2-native-mux-capacity mux) #+linux +fn2-native-epoll-event-size+ #+darwin 8)))

(defun fn2-native-mux-watch-control (mux fd)
  "Watch FD (the session's control input) for readability in the last slot."
  (fn2-native-mux-interest mux (1- (fn2-native-mux-capacity mux)) fd 1))
(defun fn2-native-mux-control-ready-p (mux)
  (plusp (aref (fn2-native-mux-ready mux) (1- (fn2-native-mux-capacity mux)))))
(sb-alien:define-alien-routine ("read" %fn2-native-read) sb-alien:long
  (fd sb-alien:int) (buffer sb-sys:system-area-pointer) (length sb-alien:unsigned-long))
