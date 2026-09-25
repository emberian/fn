;;; host/native/io.lisp -- the fn native host's raw-Lisp I/O adapter.
;;;
;;; TRUST BOUNDARY.  Every form in this file is raw Common Lisp, loaded into
;;; the ACL2 world under the trust tag :fn-native-host by host/native/build.lisp
;;; (progn! (set-raw-mode t) (load "host/native/io.lisp")).  Nothing here is
;;; proved.  This file is part of the raw surface of the native host: SBCL's
;;; sb-posix, sb-unix, sb-alien and sb-bsd-sockets contribs, the diagnostic
;;; SHA-256 CLI below, and the socket loop.  specs/host.md lists the surface
;;; function by function.
;;;
;;; Calls into ACL2 go through `fnn-call`, which applies the executable
;;; counterpart (ACL2_*1*_ACL2) of the selected wrapper or logical function.
;;; This does not prove that every inner call rechecks its guards. In particular,
;;; :program host wrappers are not guard-verified caller proofs; their raw
;;; execution can rely on arguments/global state satisfying a callee's guards.
;;; The adapter must establish external-input bounds and maintain the state
;;; invariant required by the called transition's preservation theorem. That
;;; host/model correspondence is an assurance obligation, not a consequence of
;;; the saved image having guard-checking-on = t. See specs/host.md and the
;;; native store guard review/disposition in planning/evidence/.
;;;
;;; SOCKET SURFACE.  host/native/tcpcl.lisp (the DTN wave, planning/lanes/
;;; HANDOFF-w4-tcpcl.md "Proposed host surface") builds its convergence layer
;;; on exactly these entry points and opens no socket and makes no syscall of
;;; its own:
;;;
;;;   (fnn-listen port &key family backlog) -> (values socket bound-port)
;;;   (fnn-connect host port &key family timeout) -> socket, an active open
;;;                                            after one nonblocking connect
;;;                                            deadline (DNS is separate)
;;;   (fnn-accept-loop listener handler once) -> one handler call per client
;;;   (fnn-socket-fd socket)                -> a nonblocking descriptor the three below take
;;;   (fnn-socket-shut socket)              -> close, errors swallowed
;;;   (fnn-recv fd seconds &optional maximum) -> octets, an empty vector at end
;;;                                            of input, or :timeout; at most
;;;                                            MAXIMUM (default +fnn-max-read+)
;;;                                            octets per call
;;;   (fnn-send-all fd octets seconds)      -> t, partial writes resumed
;;;   (fnn-graceful-close fd)               -> FIN, then a bounded input drain
;;;
;;; and into the core: `fnn-call', `fnn-core', `fnn-core-state', `fnn-global',
;;; with the outcome codes above (`+fnn-exit-refused+' 1,
;;; `+fnn-exit-uncertain+' 3, `+fnn-exit-fault+' 4).
;;;
;;; The host's decisions are the Python host's decisions, in the same order,
;;; with the same messages, so that the two can be compared byte for byte.
;;; The bounded directory grammar and errno classes remain host boundary
;;; checks.  ACL2 owns metadata framing, profile values, frontier decoding and
;;; successor selection; this file only moves those octets.

(in-package "ACL2")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-posix)
  (require :sb-bsd-sockets))

;;; ---------------------------------------------------------------------------
;;; Outcomes.  Uncertain, refused, accepted and fault stay distinct to the exit
;;; code (specs/host.md "CLI exit codes").

(defconstant +fnn-exit-ok+ 0)
(defconstant +fnn-exit-refused+ 1)
(defconstant +fnn-exit-uncertain+ 3)
(defconstant +fnn-exit-fault+ 4)
(defconstant +fnn-exit-usage+ 5)

(define-condition fnn-store-error (error)
  ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-input-overbound (fnn-store-fault) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
;; A Store write that failed before publication, after which ACL2 consumed the
;; reservation as a known failure: nothing was stored.  It is a refusal (exit
;; 1, like its parent), and the owner relays its kind as :storage-failed so
;; the wire names the reason (books/nntp-post.lisp fn-post-store-refusal-line).
(define-condition fnn-store-io-refusal (fnn-store-error) ())
(define-condition fnn-usage-error (fnn-store-error) ())

;; One POSIX failure, reported the way Python's OSError prints itself.
(define-condition fnn-os-error (error)
  ((errno :initarg :errno :reader fnn-os-errno)
   (path :initarg :path :initform nil :reader fnn-os-path))
  (:report (lambda (c s)
             (format s "[Errno ~d] ~a~@[: '~a'~]"
                     (fnn-os-errno c) (sb-int:strerror (fnn-os-errno c))
                     (fnn-os-path c)))))

(defun fnn-refuse (control &rest args)
  (error 'fnn-store-error :message (apply #'format nil control args)))
(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))
(defun fnn-overbound (control &rest args)
  (error 'fnn-input-overbound :message (apply #'format nil control args)))
(defun fnn-refuse-io (control &rest args)
  (error 'fnn-store-io-refusal :message (apply #'format nil control args)))
(defun fnn-indeterminate (control &rest args)
  (error 'fnn-store-indeterminate :message (apply #'format nil control args)))
(defun fnn-os-fail (errno &optional path)
  (error 'fnn-os-error :errno errno :path path))

(defun fnn-exit-code-for (condition)
  (typecase condition
    (fnn-store-indeterminate +fnn-exit-uncertain+)
    (fnn-store-fault +fnn-exit-fault+)
    (fnn-usage-error +fnn-exit-usage+)
    (fnn-store-error +fnn-exit-refused+)
    (fnn-os-error +fnn-exit-fault+)
    (t +fnn-exit-fault+)))

;;; ---------------------------------------------------------------------------
;;; Octets, text, hex.

(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))

(defun fnn-make-octets (n)
  (make-array n :element-type '(unsigned-byte 8) :initial-element 0))

(defun fnn-octets (sequence)
  (if (typep sequence 'fnn-octets)
      sequence
      (let ((out (fnn-make-octets (length sequence))))
        (replace out sequence)
        out)))

(defun fnn-octet-list (octets)
  (coerce octets 'list))

(defun fnn-octet-list-p (x)
  (and (listp x)
       (every (lambda (o) (and (integerp o) (<= 0 o 255))) x)))

(defun fnn-string-octets (string)
  (sb-ext:string-to-octets string :external-format :utf-8))

(defun fnn-octets-string (octets)
  (sb-ext:octets-to-string (fnn-octets octets) :external-format :utf-8))

(defun fnn-ascii-octet-list (string)
  (map 'list #'char-code string))

(defun fnn-hex (octets)
  (with-output-to-string (s)
    (map nil (lambda (o) (format s "~(~2,'0x~)" o)) octets)))

(defun fnn-concat (&rest strings)
  (apply #'concatenate 'string strings))

;;; ---------------------------------------------------------------------------
;;; SHA-256 has one owner, and it is ACL2.  `books/sha256-stobj.lisp'
;;; computes FIPS 180-4 over a word stobj: `fn-sha256-stobj' is what
;;; books/crypto-attach.lisp attaches to the digest seams, and
;;; `fn-sha256-of-string' reads a string in place.  This host used to carry
;;; a SHA-256 of its own for the diagnostic `sha256' verb, a second
;;; implementation of a decision ACL2 owns; the verb now hands ACL2 the file
;;; as a string.  tools/fn_native.py `sha256-selftest' checks the verb
;;; against hashlib, which is now a check of ACL2's digest through the host.

(defun fnn-octet-string (octets)
  "A byte array as an ACL2 string of the same character codes: the concrete
input the core's string entries read in place, with no list in between."
  (map '(simple-array character (*)) #'code-char octets))

;;; ---------------------------------------------------------------------------
;;; POSIX.  Every syscall failure becomes fnn-os-error with its errno; the
;;; callers classify exactly as tools/run_store.py classifies OSError.

(defconstant +fnn-o-nofollow+ sb-posix:o-nofollow)
(defconstant +fnn-o-directory+ sb-posix:o-directory)
;; Darwin: F_FULLFSYNC asks the device to flush its own cache; fsync(2) alone
;; hands data to the drive.  sb-posix does not name the command; 51 is the
;; value in <sys/fcntl.h> on this platform.
(defconstant +fnn-f-fullfsync+ 51)
;; errno values after which Python falls back to fsync(2): ENOTTY, ENOTSUP
;; (45 on Darwin; sb-posix has no symbol for it), EOPNOTSUPP, EINVAL, EPERM.
(defparameter +fnn-fullfsync-unsupported+
  (list sb-posix:enotty 45 sb-posix:eopnotsupp sb-posix:einval sb-posix:eperm))
(defconstant +fnn-lock-sh+ 1)
(defconstant +fnn-lock-ex+ 2)
(defconstant +fnn-lock-nb+ 4)
(defconstant +fnn-lock-un+ 8)
(defconstant +fnn-shut-wr+ 1)
(defconstant +fnn-shut-rdwr+ 2)

(sb-alien:define-alien-routine ("flock" fnn-%flock) sb-alien:int
  (fd sb-alien:int) (operation sb-alien:int))
(sb-alien:define-alien-routine ("shutdown" fnn-%shutdown) sb-alien:int
  (fd sb-alien:int) (how sb-alien:int))

(defmacro fnn-posix ((&optional path) &body body)
  "Run BODY; translate an sb-posix syscall-error into fnn-os-error."
  `(handler-case (progn ,@body)
     (sb-posix:syscall-error (e)
       (fnn-os-fail (sb-posix:syscall-errno e) ,path))))

(defun fnn-open (path flags &optional (mode #o600))
  (fnn-posix (path) (sb-posix:open path flags mode)))
(defun fnn-close (fd)
  (fnn-posix () (sb-posix:close fd)))
(defun fnn-fstat (fd)
  (fnn-posix () (sb-posix:fstat fd)))
(defun fnn-lstat (path)
  "The lstat of PATH, or NIL when it does not exist."
  (handler-case (sb-posix:lstat path)
    (sb-posix:syscall-error (e)
      (if (= (sb-posix:syscall-errno e) sb-posix:enoent)
          nil
          (fnn-os-fail (sb-posix:syscall-errno e) path)))))
(defun fnn-regular-p (st) (sb-posix:s-isreg (sb-posix:stat-mode st)))
(defun fnn-directory-p (st) (sb-posix:s-isdir (sb-posix:stat-mode st)))
(defun fnn-symlink-p (st) (sb-posix:s-islnk (sb-posix:stat-mode st)))

(defun fnn-durable-barrier (fd)
  "The strongest durability barrier this platform offers on FD.

specs/host.md 'Durability barriers by platform': F_FULLFSYNC on darwin, with
fsync(2) after the listed unsupported errnos; fsync(2) elsewhere.  Neither is a
power-loss qualification."
  #+darwin
  (handler-case (progn (sb-posix:fcntl fd +fnn-f-fullfsync+)
                       (return-from fnn-durable-barrier nil))
    (sb-posix:syscall-error (e)
      (unless (member (sb-posix:syscall-errno e) +fnn-fullfsync-unsupported+)
        (fnn-os-fail (sb-posix:syscall-errno e)))))
  (fnn-posix () (sb-posix:fsync fd))
  nil)

(defun fnn-fsync-dir (path)
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-directory+))))
    (unwind-protect (fnn-durable-barrier fd)
      (fnn-close fd))))

(defun fnn-fsync-file (fd)
  (fnn-durable-barrier fd))

(defun fnn-fsync-regular (path)
  "Barrier one verified regular file without following a replacement link."
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (unwind-protect
         (progn
           (unless (fnn-regular-p (fnn-fstat fd))
             (fnn-fault "refusing non-regular store file: ~a" path))
           (fnn-durable-barrier fd))
      (fnn-close fd))))

(defvar *fnn-read-syscall*
  (lambda (fd buffer)
    (sb-sys:with-pinned-objects (buffer)
      (sb-unix:unix-read fd (sb-sys:vector-sap buffer) (length buffer))))
  "Raw read seam.  Tests bind this to inject POSIX results; production uses unix-read.")

(defvar *fnn-write-syscall*
  (lambda (fd octets offset count)
    (sb-unix:unix-write fd octets offset count))
  "Raw write seam.  Tests bind this to inject POSIX results; production uses unix-write.")

(defvar *fnn-fd-waiter* #'sb-sys:wait-until-fd-usable
  "Raw wait seam.  Tests bind it; production waits on the actual descriptor.")

(defvar *fnn-monotonic-ticks* #'get-internal-real-time
  "Monotonic clock seam for bounded retry tests and no other policy decision.")

(defun fnn-now () (funcall *fnn-monotonic-ticks*))

(defun fnn-seconds-to-deadline (deadline)
  (max 0 (/ (- deadline (fnn-now)) (float internal-time-units-per-second))))

(defun fnn-eintr-p (errno)
  (and (integerp errno) (= errno sb-posix:eintr)))

(defun fnn-would-block-p (errno)
  "Whether ERRNO asks a nonblocking socket to wait for readiness again."
  (and (integerp errno)
       (or (= errno sb-posix:eagain)
           (= errno sb-posix:ewouldblock))))

(defun fnn-set-nonblocking (fd)
  "Make socket descriptor FD nonblocking, preserving its existing flags.

Every fd exposed by FNN-SOCKET-FD goes through this boundary before the
deadline-aware recv/send helpers use it.  FNN-CONNECT also uses it before its
single connect(2) attempt; DNS resolution remains outside every socket
deadline contract."
  (fnn-posix ()
    (let ((flags (sb-posix:fcntl fd sb-posix:f-getfl)))
      (sb-posix:fcntl fd sb-posix:f-setfl
                      (logior flags sb-posix:o-nonblock))))
  fd)

(defun fnn-retry-eintr (call &optional deadline)
  "Run CALL until it returns a result other than an interrupted syscall.

CALL returns the SBCL unix-read/unix-write pair (COUNT, ERRNO).  It does not
choose an outcome for a non-EINTR error; callers retain their read/write
semantics, including EOF's legitimate zero read.  A deadline bounds retry
loops; it cannot make a blocking syscall itself interruptible."
  (loop
    (multiple-value-bind (count errno) (funcall call)
      (if (and (null count) (fnn-eintr-p errno))
          ;; A socket send has one deadline across all waits and retries.  A
          ;; regular-file write has no timeout contract and passes NIL.
          (when (and deadline (<= (fnn-seconds-to-deadline deadline) 0))
            (fnn-os-fail sb-posix:etimedout))
          (return (values count errno))))))

(defun fnn-write-progress (call remaining context &optional deadline allow-would-block)
  "One write's positive progress, retrying EINTR without changing its deadline.

When ALLOW-WOULD-BLOCK is true, a nonblocking socket's EAGAIN/EWOULDBLOCK is
reported to its readiness loop as :WOULD-BLOCK.  Store file writes still turn
every such syscall failure into an OS error."
  (multiple-value-bind (count errno) (fnn-retry-eintr call deadline)
    (cond ((and (null count) allow-would-block (fnn-would-block-p errno))
           :would-block)
          ((null count) (fnn-os-fail errno))
          ((not (and (integerp count) (> count 0) (<= count remaining)))
           (fnn-fault "~a write made no valid progress" context))
          (t count))))

(defun fnn-write-all (fd octets)
  (let ((data (fnn-octets octets)) (offset 0))
    (loop while (< offset (length data)) do
      (let ((remaining (- (length data) offset)))
        (incf offset
              (fnn-write-progress
               (lambda () (funcall *fnn-write-syscall* fd data offset remaining))
               remaining "store"))))))

(defun fnn-read-fd (fd buffer &optional deadline allow-would-block)
  "Read into BUFFER; the octet count, 0 at end of file.  EINTR is retried.

For a nonblocking socket ALLOW-WOULD-BLOCK returns :WOULD-BLOCK so its caller
can wait again under the same deadline.  Regular-file callers leave it NIL and
receive an OS error for every failed read."
  (multiple-value-bind (count errno)
      (fnn-retry-eintr (lambda () (funcall *fnn-read-syscall* fd buffer)) deadline)
    (cond ((and (null count) allow-would-block (fnn-would-block-p errno))
           :would-block)
          ((null count) (fnn-os-fail errno))
          ((not (and (integerp count) (<= 0 count) (<= count (length buffer))))
           (fnn-fault "read returned an invalid count"))
          (t count))))

(defun fnn-read-bounded-fd (fd maximum)
  "Read at most MAXIMUM octets from one already validated descriptor."
  (let ((chunks nil) (remaining (+ maximum 1)) (total 0))
             (loop while (> remaining 0) do
               (let* ((buffer (fnn-make-octets (min 65536 remaining)))
                      (count (fnn-read-fd fd buffer)))
                 (when (zerop count) (return))
                 (push (subseq buffer 0 count) chunks)
                 (incf total count)
                 (decf remaining count)))
             (when (> total maximum)
      (fnn-overbound "file exceeds ACL2-owned bound"))
             (let ((data (fnn-make-octets total)) (at 0))
               (dolist (chunk (nreverse chunks))
                 (replace data chunk :start1 at)
                 (incf at (length chunk)))
      data)))

(defun fnn-read-regular-bounded (path maximum)
  "Read one regular, non-symlink file through a no-follow descriptor."
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (unwind-protect
         (let ((info (fnn-fstat fd)))
           (unless (fnn-regular-p info)
             (fnn-fault "refusing non-regular store file: ~a" path))
           (when (> (sb-posix:stat-size info) maximum)
             (fnn-overbound "store file exceeds bound: ~a" path))
           (fnn-read-bounded-fd fd maximum))
      (fnn-close fd))))

(defun fnn-check-regular (path)
  "The lstat of a regular file, NIL when absent, a fault for anything else."
  (let ((st (fnn-lstat path)))
    (cond ((null st) nil)
          ((or (fnn-symlink-p st) (not (fnn-regular-p st)))
           (fnn-fault "refusing non-regular path: ~a" path))
          (t st))))

(defun fnn-list-directory (path)
  "Entry names of PATH other than . and .., in directory order."
  (let ((dir (fnn-posix (path) (sb-posix:opendir path))) (names nil))
    (unwind-protect
         (loop
           (let ((entry (fnn-posix (path) (sb-posix:readdir dir))))
             (when (sb-alien:null-alien entry) (return))
             (let ((name (sb-posix:dirent-name entry)))
               (unless (or (string= name ".") (string= name ".."))
                 (push name names)))))
      (fnn-posix (path) (sb-posix:closedir dir)))
    (nreverse names)))

(defun fnn-list-directory-bounded (path limit &optional namespace)
  "Entry names of PATH, or a fault before an unbounded list is retained.

The caller gets LIMIT from an ACL2 policy wrapper.  We read at most LIMIT plus
one directory entry, so an untrusted namespace cannot turn recovery into an
unbounded allocation or a partial cleanup.  NAMESPACE is only a diagnostic
label; it does not select a policy."
  (unless (and (integerp limit) (>= limit 0))
    (fnn-fault "invalid ACL2 directory observation limit"))
  (let ((dir (fnn-posix (path) (sb-posix:opendir path))) (names nil) (entry-count 0))
    (unwind-protect
         (loop
           (let ((entry (fnn-posix (path) (sb-posix:readdir dir))))
             (when (sb-alien:null-alien entry) (return))
             (let ((name (sb-posix:dirent-name entry)))
               (unless (or (string= name ".") (string= name ".."))
                 (when (>= entry-count limit)
                   (fnn-fault "~a exceeds ACL2 observation bound"
                              (or namespace "directory")))
                 (push name names)
                 (incf entry-count)))))
      (fnn-posix (path) (sb-posix:closedir dir)))
    (nreverse names)))

;; The staging sweep's enumeration.  Unlike the bounded listing above, a
;; directory larger than LIMIT is not a fault here: the sweep is decided in
;; rounds (books/store-sweep.lisp, fn-sn-sweep-round), so one round retains at
;; most LIMIT names and reports only that the directory held another.  Which
;; names are retained is directory order, sorted afterwards; nothing here
;; classifies a name.
(defun fnn-list-directory-window (path limit)
  "Up to LIMIT entry names of PATH, and whether PATH held a further entry."
  (unless (and (integerp limit) (> limit 0))
    (fnn-fault "invalid ACL2 directory observation limit"))
  (let ((dir (fnn-posix (path) (sb-posix:opendir path))) (names nil) (entry-count 0)
        (more nil))
    (unwind-protect
         (loop
           (let ((entry (fnn-posix (path) (sb-posix:readdir dir))))
             (when (sb-alien:null-alien entry) (return))
             (let ((name (sb-posix:dirent-name entry)))
               (unless (or (string= name ".") (string= name ".."))
                 (when (>= entry-count limit)
                   (setq more t)
                   (return))
                 (push name names)
                 (incf entry-count)))))
      (fnn-posix (path) (sb-posix:closedir dir)))
    (values (nreverse names) more)))

(defun fnn-link (old new) (fnn-posix (new) (sb-posix:link old new)))
(defun fnn-replace (old new) (fnn-posix (new) (sb-posix:rename old new)))
(defun fnn-unlink (path) (fnn-posix (path) (sb-posix:unlink path)))
(defun fnn-mkdir (path mode) (fnn-posix (path) (sb-posix:mkdir path mode)))
(defun fnn-chmod (path mode) (fnn-posix (path) (sb-posix:chmod path mode)))

(defun fnn-flock (fd operation)
  (let ((result (fnn-%flock fd operation)))
    (when (< result 0) (fnn-os-fail (sb-alien:get-errno)))))

(defvar *fnn-random-state* (sb-ext:seed-random-state t))
(defun fnn-random-hex (octets)
  (format nil "~(~v,'0x~)" (* 2 octets) (random (ash 1 (* 8 octets)) *fnn-random-state*)))

;;; Paths, as Python's pathlib joins and parents them.

(defun fnn-join (directory name)
  (if (and (> (length directory) 0) (char= (char directory (1- (length directory))) #\/))
      (fnn-concat directory name)
      (fnn-concat directory "/" name)))

(defun fnn-parent (path)
  (let* ((trimmed (string-right-trim "/" path))
         (slash (position #\/ trimmed :from-end t)))
    (cond ((string= trimmed "") "/")
          ((null slash) ".")
          ((zerop slash) "/")
          (t (subseq trimmed 0 slash)))))

(defun fnn-absolute (path)
  (if (and (> (length path) 0) (char= (char path 0) #\/))
      (string-right-trim "/" path)
      (fnn-join (string-right-trim "/" (sb-posix:getcwd)) (string-right-trim "/" path))))

;;; ---------------------------------------------------------------------------
;;; Streams.  Output goes through two binary fd streams the host owns.

(defvar *fnn-stdout* nil)
(defvar *fnn-stderr* nil)

(defun fnn-open-streams ()
  (setq *fnn-stdout* (sb-sys:make-fd-stream 1 :output t :element-type '(unsigned-byte 8)
                                              :buffering :full))
  (setq *fnn-stderr* (sb-sys:make-fd-stream 2 :output t :element-type '(unsigned-byte 8)
                                              :buffering :full)))

(defun fnn-emit (stream text)
  (write-sequence (fnn-string-octets text) stream)
  (finish-output stream))

(defun fnn-out (control &rest args)
  (fnn-emit *fnn-stdout* (fnn-concat (apply #'format nil control args) (string #\Newline))))

(defun fnn-err (control &rest args)
  (fnn-emit *fnn-stderr* (fnn-concat (apply #'format nil control args) (string #\Newline))))
;;; The service log.  `fn operator CONFIG run' opens `[log] path' append-only
;;; before the store (host/native/operator.lisp) and leaves its descriptor
;;; here; NIL means stderr.  Every line is ACL2's (books/owner-log.lisp); this
;;; writes its octets and one LF and decides nothing.  A failed write is
;;; reported on stderr and stops nothing: the log is an operator's record,
;;; never evidence of durable acceptance.
(defvar *fnn-owner-log-fd* nil)

(defun fnn-log-line (line)
  "Write the ACL2-rendered octet list LINE and one LF to the service log."
  (unless (fnn-octet-list-p line)
    (fnn-fault "ACL2 returned a malformed log line"))
  (let ((octets (concatenate 'fnn-octets (fnn-octets line) (fnn-octets (list 10)))))
    (if *fnn-owner-log-fd*
        (handler-case (fnn-write-all *fnn-owner-log-fd* octets)
          (error (condition)
            (fnn-err "service log write failed: ~a" condition)))
      (when *fnn-stderr*
        (write-sequence octets *fnn-stderr*)
        (finish-output *fnn-stderr*)))))

(defun fnn-exit (code)
  (when *fnn-stdout* (finish-output *fnn-stdout*))
  (when *fnn-stderr* (finish-output *fnn-stderr*))
  (finish-output *standard-output*)
  (sb-ext:exit :code code :abort t))

;;; ---------------------------------------------------------------------------
;;; Calls into the certified core: the executable counterpart of each host
;;; wrapper, exactly as the interpreted bridge evaluates it.

(defun fnn-counterpart (name)
  (let ((symbol (find-symbol (symbol-name name) "ACL2_*1*_ACL2")))
    (unless (and symbol (fboundp symbol))
      (fnn-fault "ACL2 executable counterpart missing: ~a" name))
    symbol))

(defun fnn-call (name &rest args)
  "Apply NAME's executable counterpart to ARGS.

An explicit core result such as :REFUSED remains a semantic result for its
wrapper to handle.  A thrown condition or escaped raw evaluation is an
execution-boundary fault, never a claim that the core refused an input."
  (let ((outcome :thrown) (values nil))
    (setq values
          (catch 'raw-ev-fncall
            (handler-case
                (prog1 (multiple-value-list (apply (fnn-counterpart name) args))
                  (setq outcome :ok))
              (serious-condition (c)
                (setq outcome (princ-to-string c))
                nil))))
    (case outcome
      (:ok values)
      (:thrown (fnn-fault "ACL2 error in ~(~a~): ~a" name
                           (handler-case (princ-to-string values) (error () "guard violation"))))
      (t (fnn-fault "ACL2 error in ~(~a~): ~a" name outcome)))))

(defun fnn-core (name &rest args)
  "A state-free wrapper's single value."
  (first (apply #'fnn-call name args)))

(defun fnn-core-state (name &rest args)
  "A `state`-returning wrapper's value; its error flag is a core fault."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (list *the-live-state*)))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

(defun fnn-global (name)
  (f-get-global name *the-live-state*))

;;; Result whitelists, as tools/run_store.py accepts them.

(defparameter +fnn-actions+
  '(:ready :prepared :durable :aborted :indeterminate :duplicate :conflict :absent :invalid
    :refused :fault :recovering :frontier-staged :frontier-data-durable :frontier-attempted
    :record-staged :record-data-durable :record-attempted :reserved :aborting :completing
    :fenced-frontier :fenced-record :fenced-recovery))

(defun fnn-action (value)
  (unless (member value +fnn-actions+)
    (fnn-fault "unexpected ACL2 action: ~s" value))
  value)

(defun fnn-nat (value)
  (unless (and (integerp value) (>= value 0))
    (fnn-fault "ACL2 returned a non-natural"))
  value)

(defun fnn-as-octets (value)
  (unless (fnn-octet-list-p value)
    (fnn-fault "ACL2 returned a non-octet list"))
  (fnn-octets value))

;;; Durable metadata is one certified interface.  These functions deliberately
;;; mirror tools/frame_bridge.py's wrappers: the raw host neither frames nor
;;; parses a field, and it does not restate the frontier domain or successor.

(defun fnn-metadata-config-frame (profile)
  (let ((value (fnn-core 'fn-store-metadata-config-frame profile)))
    (when (or (null value) (not (fnn-octet-list-p value)))
      (fnn-fault "ACL2 returned malformed metadata profile frame"))
    (fnn-octets value)))

(defun fnn-metadata-config-decode (octets)
  "ACL2's decoded store profile: a format-8 profile, or a format-7 tuple the
store runs under by its translation.  The host keeps the value opaque and
reads every field through an ACL2 accessor."
  (let ((value (fnn-core 'fn-store-metadata-config-decode
                         (fnn-octet-list octets))))
    (unless (and value (fnn-core 'fn-store-profile-admittedp value))
      (fnn-fault "ACL2 rejected durable configuration frame"))
    value))

(defun fnn-metadata-frontier-frame (frontier)
  (let ((value (fnn-core 'fn-store-metadata-frontier-frame frontier)))
    (when (or (null value) (not (fnn-octet-list-p value)))
      (fnn-fault "ACL2 returned malformed allocation frontier frame"))
    (fnn-octets value)))

(defun fnn-metadata-frontier-decode (octets)
  (let ((value (fnn-core 'fn-store-metadata-frontier-decode
                         (fnn-octet-list octets))))
    (unless (and (integerp value) (>= value 0))
      (fnn-fault "ACL2 rejected durable allocation frontier frame"))
    value))

(defun fnn-metadata-frontier-next (frontier)
  (let ((value (fnn-core 'fn-store-metadata-frontier-next frontier)))
    (unless (or (null value) (and (integerp value) (>= value 0)))
      (fnn-fault "ACL2 returned malformed allocation frontier successor"))
    value))

(defun fnn-transaction-name (sequence)
  (let ((value (fnn-core 'fn-store-txn-name sequence)))
    (unless (and (stringp value) (> (length value) 0)
                 (null (position #\/ value)))
      (fnn-fault "ACL2 refused transaction filename"))
    value))

;;; ---------------------------------------------------------------------------
;;; The store bridge: fixed calls into host/store-node-host.lisp.

(defun fnn-bridge-reset () (fnn-action (fnn-core-state 'fn-store-sn-reset)))
(defun fnn-bridge-record-sequence (record)
  (fnn-nat (fnn-core 'fn-store-record-sequence (fnn-octet-list record))))
(defun fnn-bridge-record-txid (record)
  (fnn-nat (fnn-core 'fn-store-record-txid (fnn-octet-list record))))
(defun fnn-bridge-recover (records frontier config-records)
  "Replay the configuration history and then the article history.

The core (host/store-node-host.lisp `fn-store-sn-recover') replays
`config-records' with the article records through `fn-cpr-replay', takes the
allocation domain and the capacity from the configured node, and opens the
observed store through `fn-cpo-open-observed'; a store with no configuration record never reaches
here.  The host supplies octets and decides nothing about them."
  (fnn-action (fnn-core-state 'fn-store-sn-recover
                              (mapcar #'fnn-octet-list records) frontier
                              (mapcar #'fnn-octet-list config-records))))
(defun fnn-bridge-config-observation-limit ()
  "The config reader consumes an ACL2-owned bound before readdir retains names."
  (fnn-nat (fnn-core 'fn-store-config-observation-limit)))

(defun fnn-bridge-config-observation (observed &optional initializing)
  "Return ACL2-issued (canonical basename . octets) config history entries.

OBSERVED is a bounded physical list.  The core decodes each octet record,
derives its generation, checks the writer codec's exact basename, and returns
only the sorted contiguous plan.  The membership check below validates the
returned representation; it is not a second filename policy."
  (let ((value
          (fnn-core (if initializing 'fn-store-config-initial-observation
                        'fn-store-config-observation)
                    (mapcar (lambda (entry)
                              (list (fnn-octet-list (fnn-string-octets (car entry)))
                                    (fnn-octet-list (cdr entry))))
                            observed))))
    (unless (and (true-listp value) (= (length value) 3)
                 (eq (first value) :ok) (null (second value))
                 (listp (third value)))
      (fnn-fault "ACL2 refused configuration namespace observation"))
    (mapcar (lambda (entry)
              (unless (and (true-listp entry) (= (length entry) 2)
                           (stringp (first entry))
                           (fnn-octet-list-p (second entry))
                           (null (position #\/ (first entry)))
                           (find (first entry) observed :key #'car :test #'string=))
                (fnn-fault "ACL2 returned malformed configuration namespace entry"))
              (cons (first entry) (fnn-octets (second entry))))
            (third value))))

(defun fnn-bridge-transaction-observation (observed limit selected-lower)
  "Return ACL2-issued (sequence . filename) pairs for one bounded scan.

The host passes observed names as octets and receives their canonical sequence
binding.  It performs no filename parser, decimal conversion, or gap policy."
  (let ((value (fnn-core 'fn-store-txn-observation-selected
                         (mapcar (lambda (name)
                                   (fnn-octet-list (fnn-string-octets name)))
                                 observed)
                         limit selected-lower)))
    (unless (and (listp value) (eq (first value) :ok)
                 (integerp (second value)) (>= (second value) 0)
                 (listp (third value)))
      (fnn-fault "ACL2 refused transaction namespace observation"))
    (values
     (mapcar (lambda (pair)
              (unless (and (true-listp pair) (= (length pair) 2)
                           (integerp (first pair)) (>= (first pair) 0)
                           (stringp (second pair)))
                (fnn-fault "ACL2 returned malformed transaction namespace pair"))
              ;; fn-store-txn-observation has already decoded the observed
              ;; UTF-8 octets and compared this string to fn-bs-txn-name.
              (cons (first pair) (second pair)))
             (third value))
     (second value))))

(defun fnn-bridge-staging-observation-limit ()
  "The ACL2-owned maximum number of staging names recovery may observe."
  (let ((value (fnn-core-state 'fn-store-sn-staging-observation-limit)))
    (unless (and (integerp value) (> value 0))
      (fnn-fault "ACL2 returned a non-positive staging observation limit"))
    value))

(defun fnn-bridge-sweep-round (observed more)
  "Ask the recovery model what one bounded staging observation decides.

OBSERVED came from one bounded directory enumeration and MORE says whether the
directory held a further entry.  The answer is (values ACTION REMOVALS):
:DONE, :AGAIN or :REFUSED, books/store-sweep.lisp fn-sn-sweep-round.  The
native adapter marshals the observation and verifies the returned
representation; it does not repeat the staging-prefix, held-name, phase or
round policy."
  (let ((value (fnn-core-state 'fn-store-sn-sweep-round
                               (mapcar (lambda (name)
                                         (fnn-octet-list (fnn-string-octets name)))
                                       observed)
                               (if more t nil)
                               nil)))
    (unless (and (consp value) (member (first value) '(:done :again :refused))
                 (consp (rest value)) (null (cddr value))
                 (listp (second value)) (every #'fnn-octet-list-p (second value)))
      (fnn-fault "ACL2 returned a malformed staging sweep round"))
    (values (first value)
            (mapcar (lambda (octets)
                      (handler-case (fnn-octets-string (fnn-octets octets))
                        (error () (fnn-fault "ACL2 returned a non-UTF-8 staging name"))))
                    (second value)))))
(defun fnn-bridge-io (operation result)
  (fnn-action (fnn-core-state 'fn-store-sn-io operation result)))

(defconstant +fnn-owner-wall-error-ms+ 1000)
(defconstant +fnn-owner-unix-dtn-offset-seconds+
  (- (encode-universal-time 0 0 0 1 1 2000 0)
     (encode-universal-time 0 0 0 1 1 1970 0)))

(defun fnn-owner-wall-milliseconds ()
  "One gettimeofday reading since 2000-01-01; the second value says if usable."
  (handler-case
      (multiple-value-bind (seconds microseconds) (sb-ext:get-time-of-day)
        (let ((wall (+ (* 1000 (- seconds +fnn-owner-unix-dtn-offset-seconds+))
                       (floor microseconds 1000))))
          (if (minusp wall) (values 0 nil) (values wall t))))
    (error () (values 0 nil))))

(defun fnn-store-prepare-observation ()
  (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
    (fnn-core 'fn-clock-observation
              (floor (* (get-internal-real-time) 1000)
                     internal-time-units-per-second)
              wall +fnn-owner-wall-error-ms+ has-wall)))

(defun fnn-bridge-prepare (msgid payload codes obligation subject evidence charge)
  (fnn-action (fnn-core-state 'fn-store-sn-prepare (fnn-octet-list msgid) (fnn-octet-list payload)
                              codes (fnn-octet-list obligation) (fnn-octet-list subject)
                              (fnn-octet-list evidence) charge
                              (fnn-store-prepare-observation))))
(defun fnn-bridge-existing-action (msgid payload codes)
  (fnn-action (fnn-core-state 'fn-store-sn-existing-action (fnn-octet-list msgid)
                              (fnn-octet-list payload) codes)))
(defun fnn-bridge-pending-record ()
  (let ((value (fnn-core-state 'fn-store-sn-pending-octets)))
    (if (null value) (fnn-make-octets 0) (fnn-as-octets value))))
(defun fnn-bridge-known-abort () (fnn-action (fnn-core-state 'fn-store-sn-known-abort)))
(defun fnn-bridge-refuse-reservation ()
  (fnn-action (fnn-core-state 'fn-store-sn-refuse-reservation)))
(defun fnn-bridge-finish () (fnn-action (fnn-core-state 'fn-store-sn-finish)))

;; The standalone store binds neither variable.  A composed native owner may
;; dynamically bind these two delivery callbacks to its own state machine so
;; it reuses the exact file/barrier program without calling the store-node
;; completion subject a second time.
(defvar *fnn-observe-callback* #'fnn-bridge-io)
(defvar *fnn-finish-callback* #'fnn-bridge-finish)
; Developer fault cut, dynamically scoped to one canonical Store publication.
; NIL in normal operation.  The cut runs after the final link and before its
; directory barrier, so an injected EIO is an uncertain publication.
(defvar *fnn-record-directory-fault-observer* nil)
; host/native/checkpoint.lisp installs this callback after it loads.  A build
; without that optional layer retains authoritative full replay and reports
; no selected checkpoint.
(defvar *fnn-checkpoint-recover-callback*
  (lambda (store records) (declare (ignore store records)) '(:none)))
; A selected lossless prefix pack may reconstruct records before the one
; generic decoder/replay call.  Without the optional pack layer this is the
; identity function.
(defvar *fnn-pack-recover-callback*
  (lambda (store records sequences actual-lower)
    (declare (ignore store sequences actual-lower)) records))
(defvar *fnn-pack-lower-bound-callback*
  (lambda (store) (declare (ignore store)) 0))

(defun fnn-bridge-article-count () (fnn-nat (fnn-core-state 'fn-store-sn-article-count)))
(defun fnn-bridge-next-txid () (fnn-nat (fnn-core-state 'fn-store-sn-next-txid)))
(defun fnn-bridge-group-next (code) (fnn-nat (fnn-core-state 'fn-store-sn-group-next code)))
(defun fnn-bridge-pin-count () (fnn-nat (fnn-core-state 'fn-store-sn-pin-count)))
(defun fnn-bridge-reserved () (fnn-nat (fnn-core-state 'fn-store-sn-reserved)))
(defun fnn-bridge-lookup (msgid)
  (let ((value (fnn-core-state 'fn-store-sn-lookup (fnn-octet-list msgid))))
    (if (null value) (fnn-make-octets 0) (fnn-as-octets value))))
(defun fnn-bridge-config-generation ()
  (fnn-nat (fnn-core-state 'fn-store-cfg-generation)))

(defun fnn-decode-joined-names (octets)
  "Decode only the ACL2-owned LF join of a group-name table."
    (unless (fnn-octet-list-p octets) (fnn-fault "ACL2 returned a non-octet list"))
    (let ((names nil) (current nil))
      (dolist (octet octets)
        (if (= octet 10)
            (progn (push (fnn-octets-string (fnn-octets (nreverse current))) names)
                   (setq current nil))
            (push octet current)))
      (when current (push (fnn-octets-string (fnn-octets (nreverse current))) names))
      (nreverse names)))

(defun fnn-bridge-config-names (wrapper)
  "A replayed name table: the core joins the names with LF, which no group
name contains (`fn-store-cfg-join-names', host/store-node-host.lisp)."
  (fnn-decode-joined-names (fnn-core-state wrapper)))

(defun fnn-bridge-config-initial (names)
  "Generation 1 of a fresh store, built and admitted by the core."
  (let ((value (fnn-core 'fn-cfg-host-initial-octets
                         (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) names))))
    (when (or (keywordp value) (not (fnn-octet-list-p value)))
      (fnn-refuse "refused initial group table"))
    (fnn-octets value)))

(defun fnn-bridge-lookup-found-p (msgid)
  (let ((value (fnn-core-state 'fn-store-sn-lookup-foundp (fnn-octet-list msgid))))
    (cond ((eq value t) t) ((null value) nil)
          (t (fnn-fault "ACL2 returned a non-boolean")))))

;;; The frame session: tools/frame_bridge.py, with SHA-256 from above.

(defvar *fnn-constants* nil)

(defun fnn-constants ()
  (or *fnn-constants*
      (let ((values (fnn-core 'fn-store-frame-constants))
            (names '(:header :trailer :overhead :max-store :max-workflow :max-receipt
                     :max-inbound :max-text :max-blob :max-identity)))
        (unless (and (listp values) (= (length values) (length names))
                     (every #'integerp values))
          (fnn-fault "ACL2 returned an unexpected constant vector"))
        (let ((table (mapcar #'cons names values)))
          ;; The two slice constants the store host still holds, checked
          ;; against the ACL2 grammar at session open as frame_bridge does.
          (unless (= (cdr (assoc :trailer table)) 32)
            (fnn-refuse "host store trailer is 32 but the model says ~d" (cdr (assoc :trailer table))))
          (unless (= (cdr (assoc :header table)) 10)
            (fnn-refuse "host store header is 10 but the model says ~d" (cdr (assoc :header table))))
          (setq *fnn-constants* table)))))

(defun fnn-constant (name) (cdr (assoc name (fnn-constants))))

(defun fnn-trailer (prefix)
  "The integrity trailer over a protected prefix, computed by ACL2.

`books/frame-trailer.lisp' owns it: `fn-frame-trailer' is `fn-frame-digest',
realised by `fn-sha256' through `books/crypto-attach.lisp'.  This host used
to run `fnn-sha256' here, which made three separate SHA-256s the owners of
one decision -- the other two being `tools/frame_bridge.py' and
`tools/run_owner.py' -- and that is what AGENTS.md's one-owner rule forbids.
The diagnostic `sha256' verb asks ACL2 too (`fn-sha256-of-string'); this
host has no SHA-256 of its own."
  (let ((value (fnn-core 'fn-frame-trailer (fnn-octet-list prefix))))
    (when (eq value :bad)
      (fnn-fault "ACL2 refused to trail a protected prefix"))
    (fnn-as-octets value)))

(defun fnn-seal (prefix)
  (concatenate 'fnn-octets (fnn-octets prefix) (fnn-trailer prefix)))

(defun fnn-digest-of (framed)
  (if (< (length framed) (fnn-constant :trailer))
      nil
      (fnn-octet-list (fnn-trailer (subseq framed 0 (- (length framed) (fnn-constant :trailer)))))))

(defun fnn-frame (record)
  "ACL2 builds the protected prefix; the host appends the integrity trailer."
  (let ((value (fnn-core 'fn-store-frame-store-protected (fnn-octet-list record))))
    (when (or (keywordp value) (not (fnn-octet-list-p value)))
      (fnn-fault "ACL2 refused to frame a transaction record"))
    (fnn-seal value)))

(defun fnn-unframe (raw)
  "ACL2 parses the frame and compares the trailer with the host digest."
  (let ((value (fnn-core 'fn-store-frame-store-decode (fnn-octet-list raw) (fnn-digest-of raw))))
    (unless (and (consp value) (eq (first value) :ok))
      (let ((reason (if (and (consp value) (consp (cdr value))) (second value) :unknown)))
        (fnn-fault "frame refused: ~(~a~)" reason)))
    (fnn-as-octets (second value))))

(defun fnn-subject-id (payload)
  "Content identity v1 (books/identity), derived end to end in ACL2.
`books/crypto-attach.lisp' attaches SHA-256 to `fn-frame-digest', so the
preimage AND the digest are ACL2's; this host no longer hashes for identity,
because a second SHA-256 here would be a second owner of the derivation.
Hashing the bare payload is the v0 profile and derives a different identity,
which `fn-store-sn-prepare' then refuses."
  (fnn-as-octets (fnn-core 'fn-store-subject-id-of-payload
                           (fnn-octet-list payload))))

(defun fnn-obligation-id (msgid subject)
  "Obligation identity v1, preimage and digest both ACL2's.  See FNN-SUBJECT-ID."
  (fnn-as-octets (fnn-core 'fn-store-obligation-id-of
                           (fnn-octet-list msgid) (fnn-octet-list subject))))

(defun fnn-post-boundary (profile msgid payload-length group-count charge)
  "ACL2's POST boundary verdict under PROFILE, the values ACL2 decoded at open."
  (let ((value (fnn-core 'fn-sbud-post-boundary profile (fnn-octet-list msgid)
                         payload-length group-count charge)))
    (unless (keywordp value) (fnn-fault "ACL2 returned an unexpected boundary verdict"))
    value))

(defun fnn-pending-sequence (value)
  "The staged record's sequence as ACL2 returned it (fn-sbud-pending-sequence)."
  (unless (and (integerp value) (>= value 0))
    (fnn-fault "ACL2 returned no staged record sequence"))
  value)

(defun fnn-charge (length)
  (let ((value (fnn-core 'fn-store-charge length)))
    (unless (and (integerp value) (> value 0)) (fnn-fault "ACL2 returned a non-positive charge"))
    value))

(defun fnn-group-codes (names domain)
  "Codes in the replayed allocation domain the core handed the store at open.
There is no compiled group table to compare against: `fn-store-group-codes'
resolves the names against `domain' and the host carries that list verbatim."
  (let ((value (fnn-core 'fn-store-group-codes
                         (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) names)
                         (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) domain))))
    (when (or (keywordp value) (not (listp value)) (/= (length value) (length names)))
      (fnn-refuse "unknown or duplicate configured group"))
    value))

;;; ---------------------------------------------------------------------------
;;; The store: tools/run_store.py's Store, decision for decision.

(defconstant +fnn-config-record-bytes+ 65538)
;; tools/run_store.py's `init --group` default, an operator default and not a
;; group table: what a store serves is what the core admits and replays.
(defparameter +fnn-default-groups+ (list "fn.letters" "fn.test"))

(defstruct (fnn-store (:constructor %make-fnn-store))
  root writable lock-fd config frontier fenced (orphans nil) (orphans-more nil)
  (completion-pending nil)
  ;; The checkpoint layer runs only after authoritative full replay.  It keeps
  ;; its diagnostic outcome here and never replaces the live store-node state.
  (checkpoint-outcome '(:none))
  ;; P3: how the last open reached the Store state: (:checkpoint S K) or
  ;; (:full-replay REASON).  `operator status' prints it.
  (open-mode '(:full-replay :absent))
  ;; The replayed configuration the core hands back at recover.  The host
  ;; stores it and passes it back; it derives no name, code or generation.
  (config-generation nil) (config-served nil) (config-domain nil)
  ;; The one scripted fault point, or NIL: tools/run_store.py's ScriptedFaults.
  (fault-point nil) (fault-class nil) (fault-message nil))

(defun fnn-profile-nat (name store)
  (let ((value (fnn-core name (fnn-store-config store))))
    (unless (and (integerp value) (> value 0))
      (fnn-fault "ACL2 returned a malformed profile field from ~(~a~)" name))
    value))
;; The operator's article bound A and transaction bound T of the profile the
;; store runs under (books/byte-store-frame.lisp accessors).
(defun fnn-config-max-payload (store)
  (fnn-profile-nat 'fn-store-profile-max-article-octets store))
(defun fnn-config-max-transactions (store)
  (fnn-profile-nat 'fn-store-profile-max-transactions store))

(defun make-fnn-store (root &key writable fault)
  (let ((store (%make-fnn-store :root (fnn-absolute root) :writable writable)))
    (when fault
      (destructuring-bind (point class message) fault
        (setf (fnn-store-fault-point store) point
              (fnn-store-fault-class store) class
              (fnn-store-fault-message store) message)))
    store))

(defun fnn-at (store point)
  "Production has no injection branch; a scripted point raises its outcome."
  (when (eq point (fnn-store-fault-point store))
    (cond ((eq (fnn-store-fault-class store) 'fnn-os-error)
           (fnn-os-fail sb-posix:eio))
          ;; Only a developer-image selector arms this class
          ;; (fnn-post-entry-fault, fnn-recovery-test-fault,
          ;; fnn-init-test-fault).  SIGKILL is
          ;; deliberate: unlike an exception it cannot run unwind-protect
          ;; cleanup, so the next command tests an actual new process.
          ((eq (fnn-store-fault-class store) :fnn-test-kill)
           (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
           (fnn-fault "test SIGKILL did not terminate the process"))
          ;; Developer-only physical-fault harness handoff.  The process is
          ;; stopped at :frontier-attempted or :record-attempted, after the
          ;; authority rename/link and before its directory barrier.  Its
          ;; driver must resume or terminate the exact PID it started.
          ((eq (fnn-store-fault-class store) :fnn-test-stop)
           (sb-posix:kill (sb-posix:getpid) sb-unix:sigstop))
          ;; A test-only setup action.  fnn-config-record-names invokes this
          ;; immediately before its real fnn-list-directory call, so that call
          ;; itself returns EACCES.  A handler that turned its error into NIL
          ;; would make the regression test below falsely succeed.
          ((eq (fnn-store-fault-class store) :fnn-test-config-no-read)
           (fnn-chmod (fnn-config-dir store) #o000))
          (t
           (error (fnn-store-fault-class store) :message (fnn-store-fault-message store))))))

(defun fnn-config-path (s) (fnn-join (fnn-store-root s) "config.json"))
(defun fnn-transactions (s) (fnn-join (fnn-store-root s) "transactions"))
(defun fnn-staging (s) (fnn-join (fnn-store-root s) "staging"))
(defun fnn-lock-path (s) (fnn-join (fnn-store-root s) "writer.lock"))
(defvar *fnn-clone-activation* nil)

; The one ACL2-owned path-component decoder.  It lives here, not in
; checkpoint.lisp, because every Store open decodes the clone fence name with
; it, and host/native/build-dtn.lisp loads io.lisp without checkpoint.lisp.
(defun fnn-checkpoint-name-result (value description)
  "Validate and decode one ACL2-owned path component."
  (unless (and (fnn-octet-list-p value) value
               (every (lambda (octet) (< octet 128)) value)
               (not (member (char-code #\/) value))
               (not (member 0 value)))
    (fnn-fault "ACL2 returned invalid ~a" description))
  (fnn-octets-string (fnn-octets value)))

(defun fnn-clone-fence-path (s)
  (fnn-join (fnn-store-root s)
            (fnn-checkpoint-name-result
             (fnn-core 'fn-store-checkpoint-clone-fence-name)
             "clone fence name")))

(defun fnn-require-clone-activated (s)
  (when (and (fnn-lstat (fnn-clone-fence-path s))
             (not *fnn-clone-activation*))
    (fnn-refuse "clone is fenced pending durable incarnation rollover")))
(defun fnn-frontier-path (s) (fnn-join (fnn-store-root s) "allocation-frontier.json"))
(defun fnn-history-marker-path (s) (fnn-join (fnn-store-root s) "committed-history.json"))
(defun fnn-config-dir (s) (fnn-join (fnn-store-root s) "config"))
(defun fnn-config-record-name (generation)
  "The one persistent configuration filename renderer is ACL2's fixed-width
codec.  Directory enumeration remains a separate, bounded-recovery successor;
this function never formats a generation in raw Lisp."
  (let ((name (fnn-core 'fn-native-admin-host-config-name generation)))
    (unless (and (stringp name) (= (length name) 12)
                 (null (position #\/ name)))
      (fnn-refuse "ACL2 refused configuration record generation ~a" generation))
    name))
(defun fnn-config-record-path (s generation)
  (fnn-join (fnn-config-dir s) (fnn-config-record-name generation)))

(defun fnn-config-record-observation (store &optional test-fault-point initializing)
  "One bounded physical config history observation, ordered by ACL2's plan.

Every observed name is checked as a regular non-symlink and read under the
record byte bound before ACL2 decodes its generation and compares the native
writer codec name.  A malformed/gapped namespace remains a fault; no suffix
filter turns it into an absent or shorter history."
  (when test-fault-point (fnn-at store test-fault-point))
  (let* ((limit (fnn-bridge-config-observation-limit))
         (names (handler-case
                    (sort (fnn-list-directory-bounded (fnn-config-dir store) limit
                                                      "configuration namespace")
                          #'string<)
                  (fnn-os-error () (fnn-fault "cannot enumerate configuration history"))))
         (observed
           (mapcar (lambda (name)
                     (let ((path (fnn-join (fnn-config-dir store) name)))
                       ;; This is deliberately before the ACL2 call: a
                       ;; symlink/non-file is a physical observation fault.
                       (fnn-check-regular path)
                       (cons name
                             (fnn-read-regular-bounded path +fnn-config-record-bytes+))))
                   names)))
    (fnn-bridge-config-observation observed initializing)))

(defun fnn-config-record-names (store &optional test-fault-point initializing)
  "Canonical config basenames from one bounded ACL2-bound observation."
  (mapcar #'car (fnn-config-record-observation store test-fault-point initializing)))

(defun fnn-config-records-from-observation (observation)
  (unless observation
    (fnn-fault "refusing store with no durable configuration record"))
  (mapcar #'cdr observation))

(defun fnn-config-records (store)
  "The exact config octets paired with ACL2's canonical contiguous names."
  (fnn-config-records-from-observation (fnn-config-record-observation store)))

(defun fnn-open-lock (store exclusive create)
  (let ((flags (logior (if exclusive sb-posix:o-rdwr sb-posix:o-rdonly)
                       (if create sb-posix:o-creat 0)
                       +fnn-o-nofollow+))
        (fd nil))
    (handler-case (setq fd (fnn-open (fnn-lock-path store) flags #o600))
      (fnn-os-error (e)
        (if (= (fnn-os-errno e) sb-posix:eloop)
            (fnn-fault "refusing writer-lock symlink")
            (fnn-fault "cannot open writer lock: ~a" e))))
    (handler-case
        (unless (fnn-regular-p (fnn-fstat fd))
          (fnn-fault "refusing non-regular writer lock"))
      (error (e) (fnn-close fd) (error e)))
    (handler-case (fnn-flock fd (logior (if exclusive +fnn-lock-ex+ +fnn-lock-sh+) +fnn-lock-nb+))
      (fnn-os-error ()
        (fnn-close fd)
        (fnn-refuse "store is already locked")))
    fd))

(defun fnn-init-cut (store label)
  "One test seam after a named fresh-initializer durable syscall."
  (fnn-at store (intern (string-upcase label) :keyword)))

(defun fnn-safe-directory (path &optional create initializer-store mkdir-cut parent-cut)
  (let ((st (fnn-lstat path)))
    (when (null st)
      (unless create (fnn-fault "missing store directory: ~a" path))
      (fnn-mkdir path #o700)
      (when initializer-store (fnn-init-cut initializer-store mkdir-cut))
      (fnn-fsync-dir (fnn-parent path))
      (when initializer-store (fnn-init-cut initializer-store parent-cut))
      (setq st (fnn-lstat path)))
    (when (or (null st) (not (fnn-directory-p st)) (fnn-symlink-p st))
      (fnn-fault "refusing non-directory store path: ~a" path))
    st))

(defun fnn-publish-initial-file (store final contents &optional initializer-prefix)
  "Stage, barrier, then immutably publish one initialization metadata file.

The return is :PUBLISHED after a new final name, or :EXISTING after link(2)
reported EEXIST.  An error other than EEXIST at link is indeterminate: the
kernel may have issued the namespace operation even when it reports failure."
  (let* ((stage (fnn-join (fnn-staging store)
                          (format nil ".init-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (when initializer-prefix (fnn-init-cut store (fnn-concat initializer-prefix "created")))
    (unwind-protect (progn (fnn-write-all fd contents)
                           (when initializer-prefix
                             (fnn-init-cut store (fnn-concat initializer-prefix "written")))
                           (fnn-fsync-file fd)
                           (when initializer-prefix
                             (fnn-init-cut store (fnn-concat initializer-prefix "file-fenced"))))
      (fnn-close fd))
    (unwind-protect
         ;; Catch EEXIST only from link(2).  Directory fencing and the test
         ;; seam below retain their own error/cut origin.
         (let ((publication
                 (handler-case
                     (progn (fnn-link stage final) :published)
                   (fnn-os-error (e)
                     (if (= (fnn-os-errno e) sb-posix:eexist)
                         :existing
                       (fnn-indeterminate
                        "initial immutable-link outcome is indeterminate: ~a" e))))))
           (case publication
             (:published
              ;; Link succeeded, so a later directory-barrier error cannot
              ;; be retried as EEXIST.  The final name may be visible; surface
              ;; either errno as uncertain for recovery.
              (handler-case
                  (progn
                    (when initializer-prefix
                      (fnn-init-cut store (fnn-concat initializer-prefix "linked")))
                    (fnn-fsync-dir (fnn-store-root store))
                    (when initializer-prefix
                      (fnn-init-cut store (fnn-concat initializer-prefix "root-fenced")))
                    :published)
                (fnn-os-error (e)
                  (fnn-indeterminate
                   "initial immutable-link directory fence is indeterminate: ~a" e))))
             (:existing
              ;; This cut is after link(2)'s EEXIST return and before cleanup
              ;; of the separately staged candidate.
              (when initializer-prefix
                (fnn-init-cut store (fnn-concat initializer-prefix "link-eexist")))
              :existing)))
      (ignore-errors (fnn-unlink stage))
      ;; Keep the real best-effort unlink policy above.  The test seam is
      ;; deliberately outside that handler so its selected outcome is visible.
      (when initializer-prefix (fnn-init-cut store (fnn-concat initializer-prefix "stage-unlinked"))))))

(defun fnn-transaction-files (store &optional (selected-lower 0))
  "ACL2-bound final namespace pairs, each path verified regular by the host."
  (let* ((limit (fnn-config-max-transactions store))
         ;; This is the physical resource boundary: readdir stops before an
         ;; unbounded name list is retained.  Sorting only stabilizes the
         ;; observed representation; ACL2 owns filename grammar and sequence.
         (observed (handler-case
                       (sort (fnn-list-directory-bounded (fnn-transactions store)
                                                         limit "transaction namespace")
                             #'string<)
                     (fnn-os-error () (fnn-fault "cannot enumerate transactions"))))
         (answer (multiple-value-list
                  (fnn-bridge-transaction-observation observed limit selected-lower)))
         (pairs (first answer)) (actual-lower (second answer)))
    (values (mapcar (lambda (pair)
              (let* ((sequence (car pair))
                     (name (cdr pair))
                     (path (fnn-join (fnn-transactions store) name))
                     (st (fnn-lstat path)))
                (when (or (null st) (fnn-symlink-p st) (not (fnn-regular-p st)))
                  (fnn-fault "refusing transaction symlink or non-file"))
                ;; SEQUENCE came from fn-store-txn-observation, whose exact
                ;; filename comparison is the byte-store codec.  Durable
                ;; record decoding below binds this value again before replay.
                (cons sequence path)))
                    pairs)
            actual-lower)))

(defun fnn-staging-observation (store)
  "One bounded physical observation for the ACL2 staging policy.

The answer is (values NAMES MORE): at most the ACL2 limit of sorted names, and
whether the directory held another entry."
  (let ((limit (fnn-bridge-staging-observation-limit)))
    (handler-case
        (multiple-value-bind (names more) (fnn-list-directory-window (fnn-staging store) limit)
          (values (sort names #'string<) more))
      (fnn-os-error () (fnn-fault "cannot enumerate staging")))))

(defun fnn-staging-orphans (store)
  "The bounded report after a recovery policy decision or a read-only open.

A shared-lock reader does not sweep; it reports one observation and says when
the directory held more than it shows."
  (multiple-value-bind (names more) (fnn-staging-observation store)
    (setf (fnn-store-orphans-more store) more)
    names))

(defun fnn-sweep-staging (store)
  "Apply the ACL2-owned recovery policy, one bounded observation per round.

Each round enumerates at most the ACL2 limit, asks fn-sn-sweep-round, and
unlinks what it returns.  :AGAIN promises the round removed a name, so the next
enumeration is of a strictly smaller directory
(fn-sn-sweep-rounds-collect-every-orphan); :REFUSED is a directory holding more
names than one observation, none of which the model may remove, and it is a
refusal, not a fault.  The core's removals must be observed names; that check
is representation validation at the host boundary, not a second staging
policy.  ENOENT means a concurrent external removal won the race; any other
unlink error is uncertain because the name may or may not still be present
after the syscall."
  (let ((removed nil))
    (loop
      (multiple-value-bind (observed more) (fnn-staging-observation store)
        (multiple-value-bind (action removals) (fnn-bridge-sweep-round observed more)
          (dolist (name removals)
            (unless (member name observed :test #'string=)
              (fnn-fault "ACL2 returned a staging removal outside the observation"))
            (handler-case
                (progn
                  (fnn-unlink (fnn-join (fnn-staging store) name))
                  ;; Developer-only source-pinned recovery seam.  It runs after the
                  ;; real unlink, so EIO here is a post-success observation and
                  ;; SIGKILL is process death before the next directory observation.
                  (fnn-at store :recovery-stage-unlinked))
              (fnn-os-error (e)
                (if (= (fnn-os-errno e) sb-posix:enoent)
                    nil
                    (fnn-indeterminate "cannot collect staging orphan ~a: ~a" name e))))
            (push name removed))
          (case action
            (:again nil)
            (:done (return))
            (:refused
             (fnn-refuse "staging namespace holds more than ~d names recovery may not remove"
                         (length observed)))
            (otherwise (fnn-fault "ACL2 returned an invalid staging sweep action"))))))
    (setf (fnn-store-orphans store) (fnn-staging-orphans store))
    (nreverse removed)))

(defun fnn-load-config (store)
  (fnn-check-regular (fnn-config-path store))
  (let ((raw (handler-case
                 (fnn-read-regular-bounded (fnn-config-path store) 16384)
               (fnn-os-error (e) (fnn-fault "invalid durable config: ~a" e)))))
    ;; Format 5 is deliberately retained.  Opening never rewrites it into a
    ;; format-6 FNSM frame; migration is a separate offline operation.
    (when (and (> (length raw) 0) (= (aref raw 0) (char-code #\{)))
      (fnn-fault "legacy JSON metadata is retained in place; explicit offline migration is required"))
    (setf (fnn-store-config store) (fnn-metadata-config-decode raw))))

(defun fnn-load-frontier (store)
  (fnn-check-regular (fnn-frontier-path store))
  (let ((raw (handler-case
                 (fnn-read-regular-bounded (fnn-frontier-path store) 4096)
               (fnn-os-error (e)
                 (fnn-fault "invalid durable allocation frontier: ~a" e)))))
    (when (and (> (length raw) 0) (= (aref raw 0) (char-code #\{)))
      (fnn-fault "legacy JSON allocator is retained in place; explicit offline migration is required"))
    (setf (fnn-store-frontier store) (fnn-metadata-frontier-decode raw))))

;; The committed-history boundary (books/store-history-marker).  The open
;; reads the marker once and ACL2 (fn-hm-open-verdict) compares it with the
;; length of the record list replay is handed: pack events plus suffix files.
(defun fnn-history-marker-observation (store)
  "(:absent) or (:present OCTETS): one bounded read of committed-history.json."
  (let ((path (fnn-history-marker-path store)))
    (if (null (fnn-check-regular path))
        (list :absent)
        (list :present
              (fnn-octet-list
               (handler-case (fnn-read-regular-bounded path 4096)
                 (fnn-os-error (e)
                   (fnn-fault "cannot read the committed-history marker: ~a" e))))))))

(defun fnn-check-history-marker (store record-count)
  "Refuse an open whose committed history is short of its marker.

A refusal is detected damage to committed data (specs/storage.md STO-005):
a fault naming ACL2's reason, never a silent rollback to the shorter history."
  (let* ((verdict (fnn-core 'fn-hm-open-verdict
                            (fnn-history-marker-observation store) record-count))
         (word (and (consp verdict) (first verdict))))
    (case word
      (:admitted verdict)
      (:refused
       (fnn-fault "committed history refused at open: ~(~a~)~@[ marker=~d~] records=~d"
                  (second verdict) (third verdict) record-count))
      (otherwise (fnn-fault "ACL2 returned a malformed committed-history verdict")))))

(defun fnn-mark-committed (store sequence)
  "Replace the committed-history marker after record SEQUENCE is durable.

Every caller runs this after fnn-publish returned :durable and before
fnn-finish, so a record the node acknowledges is below a durable marker, and
nothing else (a reservation, an abort, a refusal, recovery) writes it.  The
bytes are ACL2's (fn-hm-after-commit); the steps are fn-hm-marker-program's,
and each cut is an `fnn-at' site named in fn-hm-marker-cut-names.  The stage
uses the `.stage-' prefix the recovery sweep collects.  Any OS error is
uncertain: the record is durable and the marker may or may not be replaced,
so the store stays fenced and recovery decides; the transaction is never
acknowledged without its marker."
  (fnn-require-writer store)
  (let ((frame (fnn-core 'fn-hm-after-commit sequence))
        (stage (fnn-join (fnn-staging store)
                         (format nil ".stage-marker-~d-~a" (sb-posix:getpid) (fnn-random-hex 12)))))
    (setf (fnn-store-fenced store) t)
    (unless (fnn-octet-list-p frame)
      (fnn-indeterminate "ACL2 returned no committed-history marker for sequence ~d" sequence))
    (handler-case
        (progn
          (fnn-write-staged-at store stage (fnn-octets frame) :marker-created :marker-written)
          (fnn-at store :marker-staged-durable)
          (fnn-replace stage (fnn-history-marker-path store))
          (fnn-at store :marker-replaced)
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-at store :marker-durable)
          :marked)
      (fnn-os-error (e)
        (fnn-indeterminate "committed-history marker update after durable sequence ~d is uncertain: ~a"
                           sequence e)))))

(defun fnn-initialize (store &optional (groups +fnn-default-groups+) (profile :development))
  ;; One durable configuration record at generation 1, built and admitted by
  ;; the core from the operator's group names.
  (fnn-safe-directory (fnn-store-root store) t store
                      "init-root-mkdir" "init-root-parent-fenced")
  (fnn-require-clone-activated store)
  (let ((lock-fd (fnn-open-lock store t t)))
    (unwind-protect
         (progn
           (fnn-init-cut store "init-lock-created")
           (fnn-safe-directory (fnn-transactions store) t store
                               "init-transactions-mkdir" "init-transactions-parent-fenced")
           (fnn-safe-directory (fnn-staging store) t store
                               "init-staging-mkdir" "init-staging-parent-fenced")
           (fnn-safe-directory (fnn-config-dir store) t store
                               "init-config-dir-mkdir" "init-config-dir-parent-fenced")
           (let ((config (fnn-metadata-config-frame profile)))
             (if (eq (fnn-publish-initial-file store (fnn-config-path store) config "init-config-")
                     :published)
                 (setf (fnn-store-config store) (fnn-metadata-config-decode config))
                 (fnn-load-config store)))
           (when (null (fnn-config-record-names store :init-config-records-first-enumerate t))
             (when (eq (fnn-publish-initial-file store (fnn-config-record-path store 1)
                                              (fnn-bridge-config-initial groups) "init-history-")
                       :existing)
               ;; The exclusive writer lock does not authorize an external
               ;; writer.  Preserve this conflicting durable evidence for
               ;; recovery instead of silently accepting a racing history.
               (fnn-indeterminate "configuration history appeared during initialization"))
             (fnn-fsync-dir (fnn-config-dir store))
             (fnn-init-cut store "init-config-history-fenced"))
           ;; A missing allocator alongside committed history would permit
           ;; reuse of an aborted ID.  It is a fault, never an implicit 0.
           (when (and (null (fnn-check-regular (fnn-frontier-path store)))
                      (fnn-transaction-files store))
             (fnn-fault "refusing missing allocator frontier with committed history"))
           (if (eq (fnn-publish-initial-file store (fnn-frontier-path store)
                                             (fnn-metadata-frontier-frame 0) "init-frontier-")
                   :published)
               (setf (fnn-store-frontier store) 0)
               (fnn-load-frontier store))
           (fnn-fsync-regular (fnn-config-path store))
           (fnn-init-cut store "init-final-config-file-fenced")
           (dolist (name (fnn-config-record-names store :init-config-records-final-enumerate))
             (fnn-fsync-regular (fnn-join (fnn-config-dir store) name))
             ;; The fresh branch has generation 1 only.  Existing history is
             ;; intentionally outside this packet.
             (fnn-init-cut store "init-final-config-record-file-fenced"))
           (fnn-fsync-regular (fnn-frontier-path store))
           (fnn-init-cut store "init-final-frontier-file-fenced")
           (fnn-fsync-dir (fnn-transactions store))
           (fnn-init-cut store "init-transactions-fenced")
           (fnn-fsync-dir (fnn-store-root store))
           (fnn-init-cut store "init-root-fenced")
           (fnn-fsync-dir (fnn-parent (fnn-store-root store)))
           (fnn-init-cut store "init-parent-fenced"))
      (ignore-errors (fnn-flock lock-fd +fnn-lock-un+))
      (fnn-close lock-fd))))

(defun fnn-acquire (store)
  (fnn-safe-directory (fnn-store-root store))
  (fnn-require-clone-activated store)
  (fnn-safe-directory (fnn-transactions store))
  (fnn-safe-directory (fnn-staging store))
  (handler-case
      (progn
        (setf (fnn-store-lock-fd store)
              (fnn-open-lock store (fnn-store-writable store) (fnn-store-writable store)))
        (fnn-load-config store)
        (fnn-load-frontier store))
    (error (e) (fnn-store-close store) (error e))))

(defun fnn-store-close (store)
  (setf (fnn-store-completion-pending store) nil)
  (let ((fd (fnn-store-lock-fd store)))
    (when fd
      (setf (fnn-store-lock-fd store) nil)
      (unwind-protect (fnn-flock fd +fnn-lock-un+)
        (fnn-close fd)))))

(defun fnn-durable-records (store &optional (selected-lower 0))
  (let ((records nil) (sequences nil) (aggregate 0)
        ;; One bounded read per file, at the persisted profile's record
        ;; ceiling plus the frame overhead (ACL2's figure,
        ;; host/store-host.lisp `fn-store-profile-read-bound').
        (bound (fnn-core 'fn-store-profile-read-bound (fnn-store-config store))))
    (multiple-value-bind (files actual-lower)
        (fnn-transaction-files store selected-lower)
      (loop for (sequence . path) in files do
        (fnn-check-regular path)
        (let ((record (fnn-unframe (fnn-read-regular-bounded path bound))))
          (incf aggregate (length record))
          ;; ACL2's bound (fn-profile-replay-within-boundp, monotone under a
          ;; profile upgrade: fn-profile-upgrade-keeps-replay-bound).
          (unless (fnn-core 'fn-store-profile-replay-within-bound
                            (fnn-store-config store) aggregate)
            (fnn-fault "transaction recovery input exceeds configured bound"))
          (unless (= (fnn-bridge-record-sequence record) sequence)
            (fnn-fault "record sequence does not match immutable filename"))
          (push sequence sequences)
          (push record records)))
      (values (nreverse records) actual-lower (nreverse sequences)))))

(defun fnn-observe (store operation &optional (result :ok))
  "Submit one already-observed filesystem result and keep failure fenced."
  (handler-case (funcall *fnn-observe-callback* operation result)
    ((or fnn-store-error fnn-os-error) ()
      (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil)
      (fnn-indeterminate "ACL2 could not record ~(~a~) observation" operation))))

;;; ---------------------------------------------------------------------------
;;; P3: open from the state checkpoint (books/store-checkpoint-open.lisp,
;;; books/store-checkpoint-codec.lisp, the byte program fn-bs-scp-program).
;;; The file is a sequence of segment frames read range by range on one
;;; descriptor under the store lock (A-HOST-EXCLUSIVE-READ,
;;; fn-bs-read-ranges-concatenate).  A missing, refused or unusable
;;; checkpoint falls back to today's full replay, which stays authoritative;
;;; the open reports which one it did.

(defun fnn-state-checkpoint-name ()
  "The rename target of fn-bs-scp-program: ACL2's name, not the host's."
  (let ((name (fnn-core 'fn-store-sco-file-name)))
    (unless (and (stringp name) (> (length name) 0) (null (position #\/ name)))
      (fnn-fault "ACL2 returned an invalid state checkpoint name"))
    name))

(defun fnn-state-checkpoint-path (store)
  (fnn-join (fnn-store-root store) (fnn-state-checkpoint-name)))

(defun fnn-read-exact-fd (fd count)
  "COUNT octets from FD, or NIL when end of file comes first."
  (let ((data (fnn-make-octets count)) (at 0))
    (loop while (< at count) do
      (let* ((buffer (fnn-make-octets (min 65536 (- count at))))
             (got (fnn-read-fd fd buffer)))
        (when (zerop got) (return-from fnn-read-exact-fd nil))
        (replace data buffer :start1 at :end2 got)
        (incf at got)))
    data))

(defun fnn-state-checkpoint-segments (store)
  "(values :absent NIL), (values :ok SEGMENTS) or (values :refused REASON).

One descriptor, consecutive ranges: a segment header, then the rest of that
segment as `fn-scc-segment-extent' sizes it, until end of file.  Each read is
at most one segment, which the profile's R bounds (fn-store-sco-segment-read-bound)."
  (let ((path (fnn-state-checkpoint-path store)))
    (unless (fnn-check-regular path)
      (return-from fnn-state-checkpoint-segments (values :absent nil)))
    (let ((header-octets (fnn-core 'fn-store-sco-segment-header-octets))
          (bound (fnn-core 'fn-store-sco-segment-read-bound (fnn-store-config store)))
          (fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
          (segments nil))
      (unless (and (integerp header-octets) (> header-octets 0)
                   (integerp bound) (>= bound header-octets))
        (fnn-close fd)
        (fnn-fault "ACL2 returned an invalid checkpoint segment bound"))
      (unwind-protect
           (progn
             (unless (fnn-regular-p (fnn-fstat fd))
               (return-from fnn-state-checkpoint-segments (values :refused :not-regular)))
             (loop
               (let ((first (make-array 1 :element-type '(unsigned-byte 8))))
                 (when (zerop (fnn-read-fd fd first)) (return))
                 (let ((rest (fnn-read-exact-fd fd (1- header-octets))))
                   (unless rest
                     (return-from fnn-state-checkpoint-segments (values :refused :truncated)))
                   (let* ((header (concatenate '(vector (unsigned-byte 8)) first rest))
                          (extent (fnn-core 'fn-scc-segment-extent (fnn-octet-list header))))
                     (unless (and (integerp extent) (>= extent header-octets) (<= extent bound))
                       (return-from fnn-state-checkpoint-segments (values :refused :segment-header)))
                     (let ((body (fnn-read-exact-fd fd (- extent header-octets))))
                       (unless body
                         (return-from fnn-state-checkpoint-segments (values :refused :truncated)))
                       (push (fnn-octet-list (concatenate '(vector (unsigned-byte 8)) header body))
                             segments))))))
             (values :ok (nreverse segments)))
        (fnn-close fd)))))

(defun fnn-state-checkpoint-load (store)
  "Decode the checkpoint into ACL2's global: (values STATUS S) with STATUS
:absent, :refused or :ok, the vocabulary of fn-sco-select."
  (multiple-value-bind (status value)
      (handler-case (fnn-state-checkpoint-segments store)
        (fnn-os-error () (values :refused :io)))
    (case status
      (:absent (fnn-core-state 'fn-store-sco-clear) (values :absent 0))
      (:refused (fnn-core-state 'fn-store-sco-clear) (values :refused 0))
      (t (let ((answer (fnn-core-state 'fn-store-sco-decode value)))
           (if (and (consp answer) (eq (first answer) :ok)
                    (integerp (second answer)) (>= (second answer) 0))
               (values :ok (second answer))
               (values :refused 0)))))))

(defun fnn-recover-full-replay (store config-records &optional (reason nil))
  "Today's open: every durable record, then one full replay."
  (let ((records nil))
    (multiple-value-bind (physical-records actual-lower physical-sequences)
        (fnn-durable-records
         store (funcall *fnn-pack-lower-bound-callback* store))
      (setq records (funcall *fnn-pack-recover-callback*
                             store physical-records physical-sequences
                             actual-lower)))
    (fnn-check-history-marker store (length records))
    (unless (eq (fnn-bridge-recover records (fnn-store-frontier store) config-records)
                :recovering)
      (fnn-fault "ACL2 replay rejected committed transaction history or configuration history"))
    (when reason
      (setf (fnn-store-open-mode store) (list :full-replay reason)))
    records))

(defun fnn-read-suffix-records (store pairs)
  "Read the transaction files PAIRS ((sequence . path) ...) as fnn-durable-records does."
  (let ((records nil) (aggregate 0)
        (bound (fnn-core 'fn-store-profile-read-bound (fnn-store-config store))))
    (loop for (sequence . path) in pairs do
      (fnn-check-regular path)
      (let ((record (fnn-unframe (fnn-read-regular-bounded path bound))))
        (incf aggregate (length record))
        (unless (fnn-core 'fn-store-profile-replay-within-bound
                          (fnn-store-config store) aggregate)
          (fnn-fault "transaction recovery input exceeds configured bound"))
        (unless (= (fnn-bridge-record-sequence record) sequence)
          (fnn-fault "record sequence does not match immutable filename"))
        (push record records)))
    (nreverse records)))

(defun fnn-recover-from-state-checkpoint (store config-records)
  "The records of the history when the checkpoint opened the Store, else NIL
after recording why not in open-mode (the caller then replays in full)."
  (multiple-value-bind (status sequence) (fnn-state-checkpoint-load store)
    (let* ((lower (funcall *fnn-pack-lower-bound-callback* store))
           (pairs (if (eq status :ok) (fnn-transaction-files store lower) nil))
           (count (if (eq status :ok)
                      (fnn-core 'fn-store-sco-observed-count (mapcar #'car pairs) lower)
                      0))
           (choice (fnn-core 'fn-store-sco-select status sequence count
                             (fnn-store-config store))))
      (unless (and (consp choice) (member (first choice) '(:checkpoint :full-replay)))
        (fnn-fault "ACL2 returned a malformed checkpoint selection"))
      (when (eq (first choice) :full-replay)
        (setf (fnn-store-open-mode store) (list :full-replay (second choice)))
        (return-from fnn-recover-from-state-checkpoint nil))
      (let* ((s (second choice))
             (suffix
               (if (>= s lower)
                   ;; Only the files at or after S are read.
                   (let ((drop (fnn-core 'fn-store-sco-covered-count (mapcar #'car pairs) s)))
                     (fnn-read-suffix-records store (nthcdr drop pairs)))
                   ;; A selected pack covers names past S: the pack is read
                   ;; (one file) and the records before S are dropped.
                   (multiple-value-bind (physical actual-lower sequences)
                       (fnn-durable-records store lower)
                     (nthcdr s (funcall *fnn-pack-recover-callback*
                                        store physical sequences actual-lower))))))
        (fnn-check-history-marker store (+ s (length suffix)))
        (unless (eq (fnn-action
                     (fnn-core-state 'fn-store-sn-recover-from-checkpoint
                                     (mapcar #'fnn-octet-list suffix)
                                     (fnn-store-frontier store)
                                     (mapcar #'fnn-octet-list config-records)))
                    :recovering)
          ;; Full replay is authoritative and decides; the checkpoint is
          ;; derived.  Never serve a refused checkpoint open.
          (fnn-core-state 'fn-store-sco-clear)
          (fnn-bridge-reset)
          (setf (fnn-store-open-mode store) (list :full-replay :checkpoint-open-refused))
          (return-from fnn-recover-from-state-checkpoint nil))
        (setf (fnn-store-open-mode store) (list :checkpoint s (length suffix)))
        (append (mapcar #'fnn-as-octets (fnn-core-state 'fn-store-sco-prefix-octets))
                suffix)))))

(defun fnn-open-report (store)
  (let ((mode (fnn-store-open-mode store)))
    (case (first mode)
      (:checkpoint (format nil "open=checkpoint:~d suffix=~d" (second mode) (third mode)))
      (t (format nil "open=full-replay reason=~(~a~)" (second mode))))))

(defparameter +fnn-state-checkpoint-model-cuts+
  '("state-checkpoint-created" "state-checkpoint-written"
    "state-checkpoint-staged-durable" "state-checkpoint-replaced"
    "state-checkpoint-durable"))

(defun fnn-state-checkpoint-test-fault ()
  "Developer-only FN_NATIVE_STATE_CHECKPOINT_FAULT=MODEL-CUT:eio|kill selector
for fn-bs-scp-program's five cuts."
  (let ((raw (fnn-developer-selector "FN_NATIVE_STATE_CHECKPOINT_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_STATE_CHECKPOINT_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (member label +fnn-state-checkpoint-model-cuts+ :test #'string=)
            (fnn-fault "unknown FN_NATIVE_STATE_CHECKPOINT_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_STATE_CHECKPOINT_FAULT action: ~a" action)))
                "developer-only native state-checkpoint fault"))))))

(defun fnn-state-checkpoint-write (store octets)
  "P-STATE-CHECKPOINT, books fn-bs-scp-program: stage, fence, rename onto
the checkpoint name, fence the root.  Before the rename a failure is known
(exit 1): the old checkpoint, or none, stays.  At or after it the outcome is
uncertain (exit 3): the next open reads the old or the new file, never a
torn one (fn-bs-scp-program-crash-is-old-or-new), and a corrupt or missing
one falls back to full replay."
  (let ((stage (fnn-join (fnn-staging store)
                         (format nil ".stage-checkpoint-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
        (attempted nil))
    (handler-case
        (progn
          (fnn-write-staged-at store stage octets
                               :state-checkpoint-created :state-checkpoint-written)
          (fnn-at store :state-checkpoint-staged-durable)
          (setq attempted t)
          (fnn-replace stage (fnn-state-checkpoint-path store))
          (fnn-at store :state-checkpoint-replaced)
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-at store :state-checkpoint-durable))
      (fnn-os-error (e)
        (if attempted
            (fnn-indeterminate "state checkpoint replacement is indeterminate: ~a" e)
            (fnn-refuse-io "known failure before the state checkpoint replacement: ~a" e))))))

(defun fnn-command-state-checkpoint (root)
  "Publish the exact-state checkpoint of the recovered Store (P3).

The store opens as `recover' does (the exclusive writer lock, so a running
owner refuses this).  ACL2 extends the checkpoint the open used over the
records after it, or captures the whole history after a full replay
(fn-store-sco-publish-octets), and returns the file; the host writes it."
  (multiple-value-bind (store records)
      (fnn-open-live-store root t (fnn-state-checkpoint-test-fault))
    (unwind-protect
         (let* ((segment (fnn-profile-nat 'fn-store-profile-max-record-octets store))
                (answer (fnn-core-state 'fn-store-sco-publish-octets segment)))
           (when (eq answer :unencodable)
             (fnn-refuse "the recovered Store state is not encodable as a checkpoint"))
           (unless (and (consp answer) (fnn-octet-list-p (first answer)) (first answer)
                        (integerp (second answer)) (= (second answer) (length records)))
             (fnn-fault "ACL2 returned a malformed state checkpoint"))
           (let ((octets (fnn-octets (first answer))))
             (fnn-state-checkpoint-write store octets)
             (fnn-out "checkpoint sequence=~d octets=~d ~a"
                      (second answer) (length octets) (fnn-open-report store))
             +fnn-exit-ok+))
      (fnn-store-close store))))

(defun fnn-recover (store)
  (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil
        (fnn-store-open-mode store) '(:full-replay :absent))
  (let ((records nil))
    (handler-case
        (progn
          (fnn-load-frontier store)
          (let ((config-records (fnn-config-records store)))
            (setq records (or (fnn-recover-from-state-checkpoint store config-records)
                              (fnn-recover-full-replay store config-records))))
          (setf (fnn-store-config-generation store) (fnn-bridge-config-generation)
                (fnn-store-config-served store) (fnn-bridge-config-names 'fn-store-cfg-served)
                (fnn-store-config-domain store) (fnn-bridge-config-names 'fn-store-cfg-domain)))
      ((or fnn-store-fault fnn-store-indeterminate) (e)
        (setf (fnn-store-fenced store) t)
        (error e))
      (fnn-store-error (e)
        (setf (fnn-store-fenced store) t)
        (fnn-fault "cannot reconstruct committed history: ~a" e)))
    (fnn-at store :recover-replayed)
    (handler-case
        (let ((phase nil))
          (loop for barrier in (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
                                 (lambda () (fnn-fsync-regular (fnn-frontier-path store)))
                                 (lambda () (fnn-fsync-dir (fnn-transactions store)))
                                 (lambda () (fnn-fsync-dir (fnn-store-root store)))
                                 (lambda () (fnn-fsync-dir (fnn-parent (fnn-store-root store)))))
                for ordinal from 1 do
            (handler-case (funcall barrier)
              (fnn-os-error (e)
                (fnn-observe store :recovery-barrier :uncertain)
                (error e)))
            (setq phase (fnn-observe store :recovery-barrier :ok))
            (unless (member phase '(:recovering :ready))
              (fnn-fault "ACL2 rejected recovered barrier ordering"))
            (fnn-at store (intern (format nil "RECOVER-BARRIER-~d" ordinal) :keyword)))
          (unless (eq phase :ready)
            (fnn-fault "ACL2 did not complete all recovery barriers")))
      (fnn-os-error ()
        (setf (fnn-store-fenced store) t)
        (fnn-indeterminate "cannot establish recovered namespace frontier")))
    ;; The model's sweep transition is enabled only after the fifth recovery
    ;; observation reached :ready.  A shared-lock reader may report its
    ;; bounded observation, but it does not mutate a namespace it does not
    ;; exclusively own.
    (handler-case
        (if (fnn-store-writable store)
            (fnn-sweep-staging store)
            (setf (fnn-store-orphans store) (fnn-staging-orphans store)))
      ((or fnn-store-fault fnn-store-indeterminate) (e)
        (setf (fnn-store-fenced store) t)
        (error e)))
    ; Full journal replay above remains authoritative.  The checkpoint layer
    ; restores into separate ACL2 globals and compares that image with
    ; fn-store-sn; it cannot reset or replace the live node.
    (setf (fnn-store-checkpoint-outcome store)
          (funcall *fnn-checkpoint-recover-callback* store records))
    (setf (fnn-store-fenced store) nil)
    records))

(defun fnn-require-writer (store)
  (unless (and (fnn-store-writable store) (fnn-store-lock-fd store))
    (fnn-refuse "mutation requires a live exclusive store owner")))

(defun fnn-write-staged (stage contents)
  (let ((fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (unwind-protect (progn (fnn-write-all fd contents) (fnn-fsync-file fd))
      (fnn-close fd))))

(defun fnn-write-staged-at (store stage contents created written)
  "fnn-write-staged with the byte programs' two staging cuts between its calls.

The Store's frontier and record writers call this rather than
fnn-write-staged, so that fn-bs-frontier-program's `frontier-created' and
`frontier-written' (and fn-bs-record-program's `record-created' and
`record-written') are `fnn-at' sites: after the O_EXCL create and after
write_all, before fsync(fd).  An EIO there is a pre-publication failure of
the same arm as a failing write; SIGKILL leaves a staging file the
recovery sweep owns."
  (let ((fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (unwind-protect (progn (fnn-at store created)
                           (fnn-write-all fd contents)
                           (fnn-at store written)
                           (fnn-fsync-file fd))
      (fnn-close fd))))

(defun fnn-advance-frontier (store current-txid)
  "Report each allocator observation to the file kernel in order."
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  (unless (eql current-txid (fnn-store-frontier store))
    (setf (fnn-store-fenced store) t)
    (fnn-fault "ACL2 allocator and durable frontier disagree"))
  (let* ((next (fnn-metadata-frontier-next current-txid))
         (contents (and next (fnn-metadata-frontier-frame next)))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".allocation-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (attempted nil))
    (when (null next)
      (fnn-refuse "finite transaction-ID domain exhausted"))
    (handler-case
        (progn
          (unless (eq (fnn-observe store :start-frontier) :frontier-staged)
            (setf (fnn-store-fenced store) t)
            (fnn-fault "ACL2 rejected allocator start"))
          (fnn-write-staged-at store stage contents :frontier-created :frontier-written)
          (setf (fnn-store-fenced store) t)
          (unless (eq (fnn-observe store :frontier-file :ok) :frontier-data-durable)
            (fnn-fault "ACL2 rejected durable allocator file"))
          (fnn-at store :frontier-staged-durable)
          (setq attempted t)
          (setf (fnn-store-fenced store) t)
          (handler-case (fnn-replace stage (fnn-frontier-path store))
            (fnn-os-error (e) (fnn-observe store :frontier-replace :error) (error e)))
          (fnn-at store :frontier-replaced)
          (unless (eq (fnn-observe store :frontier-replace :ok) :frontier-attempted)
            (fnn-indeterminate "ACL2 rejected allocator replacement after the namespace attempt"))
          (fnn-at store :frontier-attempted)
          (setf (fnn-store-fenced store) t)
          (handler-case (progn (fnn-at store :frontier-barrier)
                               (fnn-fsync-dir (fnn-store-root store)))
            (fnn-os-error (e) (fnn-observe store :frontier-directory :error) (error e)))
          (fnn-at store :frontier-durable)
          (unless (eq (fnn-observe store :frontier-directory :ok) :reserved)
            (fnn-indeterminate "ACL2 rejected durable allocator frontier after its barrier"))
          (setf (fnn-store-fenced store) nil (fnn-store-frontier store) next)
          (fnn-at store :frontier-reserved)
          next)
      (fnn-os-error (e)
        (when attempted
          (setf (fnn-store-fenced store) t)
          (fnn-indeterminate "allocation-frontier update is indeterminate"))
        (fnn-observe store :frontier-file :known-fail)
        (fnn-refuse-io "known pre-publication allocator failure: ~a" e)))))

(defun fnn-log-staging-cleanup (step stage sequence condition)
  "Log the swallowed error CONDITION of fnn-publish's staging cleanup STEP.

The line is ACL2's (books/owner-log.lisp fn-olog-staging-cleanup-line): the
step, the sequence of the durable record, the stage path, the errno when the
condition is an OS error, and the condition's report as SBCL gives it.  If
rendering or writing the line fails, stderr says so and names both errors;
the record is durable either way and the caller's outcome does not change."
  (handler-case
      (fnn-log-line
       (fnn-core 'fn-olog-staging-cleanup-line
                 step
                 (fnn-octet-list (fnn-string-octets stage))
                 sequence
                 (and (typep condition 'fnn-os-error) (fnn-os-errno condition))
                 (fnn-octet-list (fnn-string-octets (princ-to-string condition)))))
    (error (failure)
      (ignore-errors
       (fnn-err "service log line for a swallowed staging cleanup error failed: ~a; the swallowed error: ~a"
                failure condition)))))

(defun fnn-publish (store sequence record)
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  ; This is a final assertion after preparation.  Normal resource refusal was
  ; already decided from the ACL2 kind ceiling before allocator reservation.
  (unless (eq (fnn-core 'fn-store-publication-admissibility
                        (fnn-store-config store) sequence (length record))
              :admissible)
    (fnn-refuse "prepared Store transaction exceeds persisted profile"))
  (let* ((final (fnn-join (fnn-transactions store) (fnn-transaction-name sequence)))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".stage-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (data (fnn-frame record))
         (attempted nil))
    (handler-case
        (progn
          (fnn-write-staged-at store stage data :record-created :record-written)
          (setf (fnn-store-fenced store) t)
          (unless (eq (fnn-observe store :record-file :ok) :record-data-durable)
            (fnn-fault "ACL2 rejected durable record file"))
          (setf (fnn-store-fenced store) nil)
          (fnn-at store :record-staged-durable)
          (setq attempted t)
          (setf (fnn-store-fenced store) t)
          (handler-case (fnn-link stage final)
            (fnn-os-error (e) (fnn-observe store :record-link :error) (error e)))
          (fnn-at store :record-linked)
          (unless (eq (fnn-observe store :record-link :ok) :record-attempted)
            (setf (fnn-store-fenced store) t)
            (fnn-indeterminate "ACL2 rejected record publication after the final-name attempt"))
          (fnn-at store :record-attempted)
          (handler-case (progn (fnn-at store :record-barrier)
                               (when *fnn-record-directory-fault-observer*
                                 (funcall *fnn-record-directory-fault-observer*
                                          final))
                               (fnn-fsync-dir (fnn-transactions store)))
            (fnn-os-error (e) (fnn-observe store :record-directory :error) (error e)))
          (fnn-at store :record-durable)
          (unless (eq (fnn-observe store :record-directory :ok) :completing)
            (fnn-indeterminate "ACL2 rejected record directory barrier after publication"))
          (setf (fnn-store-completion-pending store) t)
          (fnn-at store :record-completing)
          ;; Best-effort cleanup: an error here is swallowed, as the model's
          ;; P-RECORD says, and that includes an EIO selected at the
          ;; `record-stage-unlinked' cut between the unlink and its barrier.
          ;; Swallowed, not silent: each such error leaves one service-log
          ;; line (fnn-log-staging-cleanup), and nothing that line does can
          ;; change the outcome, since the `ignore-errors' holds it too.
          (let ((step :unlink))
            (ignore-errors
             (handler-case (progn (fnn-unlink stage)
                                  (setq step :directory-barrier)
                                  (fnn-at store :record-stage-unlinked)
                                  (fnn-fsync-dir (fnn-staging store)))
               (error (e) (fnn-log-staging-cleanup step stage sequence e)))))
          (fnn-at store :record-staging-cleaned)
          :durable)
      (fnn-os-error (e)
        (when attempted
          (setf (fnn-store-fenced store) t)
          (fnn-indeterminate "transaction publication outcome is indeterminate"))
        (fnn-refuse-io "known pre-publication store failure: ~a" e)))))

(defun fnn-finish (store)
  "Open the writer gate only after exact fn-sn durable completion."
  (fnn-require-writer store)
  (unless (and (fnn-store-fenced store) (fnn-store-completion-pending store))
    (fnn-indeterminate "durable completion was not pending"))
  (setf (fnn-store-completion-pending store) nil)
  ;; Both cut points lie after publication: the record is durable.  An OS
  ;; error at either is therefore never a refusal (campaign W2, 2026-09-24:
  ;; one escaped to the owner's refusal clause and a durable article was
  ;; answered `441 ... refused').  At :finish-consumed ACL2 has not consumed
  ;; the completion; at :finish-durable it has, and the owner then renders any
  ;; word but :durable as uncertain (fn-own-consumed-completion-is-240-or-
  ;; uncertain).  Either way the store is fenced and recovery decides.
  (handler-case (fnn-at store :finish-consumed)
    (fnn-os-error (e)
      (setf (fnn-store-fenced store) t)
      (fnn-indeterminate "completion interrupted after publication: ~a" e)))
  (let ((completion (handler-case (funcall *fnn-finish-callback*)
                      ((or fnn-store-error fnn-os-error) ()
                        (setf (fnn-store-fenced store) t)
                        (fnn-indeterminate "ACL2 completion failed after publication")))))
    (unless (eq completion :durable)
      (setf (fnn-store-fenced store) t)
      (fnn-indeterminate "ACL2 rejected durable completion after publication"))
    (setf (fnn-store-fenced store) nil)
    (handler-case (fnn-at store :finish-durable)
      (fnn-os-error (e)
        (setf (fnn-store-fenced store) t)
        (fnn-indeterminate "writer reopening interrupted after the consumed completion: ~a" e)))
    completion))

(defun fnn-identity-text (identity)
  "The one rendering of a canonical identity where a string is forced: a
store record metadata field, a journal record and an NNTP header all carry
text, and ACL2 decides what that text is.  A record field holds this, never
the canonical octets, which are not `fn-store-text-octetsp'."
  (fnn-as-octets (fnn-core 'fn-store-identity-text (fnn-octet-list identity))))

(defun fnn-provenance-post ()
  "The durable provenance for a locally injected article, decided by ACL2
from the live configuration generation and path identity."
  (let ((value (fnn-core-state 'fn-store-prov-post)))
    (unless (fnn-octet-list-p value)
      (fnn-fault "ACL2 returned invalid local-post provenance"))
    (fnn-as-octets value)))

(defun fnn-metadata (msgid payload)
  "Content identity and provenance, derived in ACL2.
The obligation binds the CANONICAL subject identity octets; what comes back
is each identity's text.  `fn-store-prov-post' selects the durable evidence
from the live ACL2 configuration; the native host does not name a provenance."
  (let* ((subject (handler-case (fnn-subject-id payload)
                    (fnn-store-indeterminate (e) (error e))
                    (fnn-store-fault (e) (error e))
                    (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity"))))
         (obligation (handler-case (fnn-obligation-id msgid subject)
                       (fnn-store-indeterminate (e) (error e))
                       (fnn-store-fault (e) (error e))
                       (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity")))))
    (values (fnn-identity-text obligation) (fnn-identity-text subject)
            (fnn-provenance-post))))

(defun fnn-group-codes-for (store groups)
  (when (null groups) (fnn-refuse "provide one or more distinct configured groups"))
  (fnn-group-codes groups (fnn-store-config-domain store)))

(defun fnn-validate-post-boundary (verdict)
  "Relay ACL2's POST boundary VERDICT (fn-sbud-post-boundary) as a refusal.

The developer `store post' asks it over the profile it opened
(fnn-post-boundary); the served owner over the profile it was handed
(fn-owner-post-boundary).  The host compares no bound of its own."
  (case verdict
    (:ok nil)
    (:bad-message-id (fnn-refuse "Message-ID is not a valid RFC 5536 message identifier"))
    (:payload-bound (fnn-refuse "payload exceeds the modelled bound"))
    (:group-bound (fnn-refuse "group count exceeds codec bound"))
    (:charge-bound (fnn-refuse "charge must be a positive uint32"))
    (t (fnn-refuse "ACL2 refused the post boundary: ~(~a~)" verdict))))

(defun fnn-open-live-store (root writable &optional fault)
  (let ((store (make-fnn-store root :writable writable :fault fault)))
    (fnn-acquire store)
    (handler-case
        (progn
          (fnn-bridge-reset)
          (values store (fnn-recover store)))
      (error (e) (fnn-store-close store) (error e)))))

(defun fnn-orphan-report (store)
  (if (null (fnn-store-orphans store))
      "staging-orphans=0"
      (format nil "staging-orphans=~d~:[~;+~] [~{~a~^ ~}]" (length (fnn-store-orphans store))
              (fnn-store-orphans-more store) (fnn-store-orphans store))))

(defun fnn-checkpoint-report (store)
  (let ((outcome (fnn-store-checkpoint-outcome store)))
    (case (first outcome)
      (:none "checkpoint=none")
      (:ok (format nil "checkpoint=ok generation=~d suffix-from=~d differential=~a auxiliary=~a"
                   (second outcome) (third outcome)
                   (if (fourth outcome) "equal" "DIFFERENT")
                   (case (fifth outcome)
                     (:equal-v2 "equal-v2")
                     (:equal-v1 "equal-v1")
                     (otherwise "unknown"))))
      (:corrupt (format nil "checkpoint=corrupt reason=~a" (second outcome)))
      (otherwise (fnn-fault "invalid checkpoint recovery outcome")))))

;;; Commands.

(defparameter +fnn-init-model-cuts+
  '("init-root-mkdir" "init-root-parent-fenced" "init-lock-created"
    "init-transactions-mkdir" "init-transactions-parent-fenced"
    "init-staging-mkdir" "init-staging-parent-fenced"
    "init-config-dir-mkdir" "init-config-dir-parent-fenced"
    "init-config-created" "init-config-written" "init-config-file-fenced"
    "init-config-linked" "init-config-link-eexist" "init-config-root-fenced" "init-config-stage-unlinked"
    "init-history-created" "init-history-written" "init-history-file-fenced"
    "init-history-linked" "init-history-link-eexist" "init-history-root-fenced" "init-history-stage-unlinked"
    "init-config-history-fenced"
    "init-frontier-created" "init-frontier-written" "init-frontier-file-fenced"
    "init-frontier-linked" "init-frontier-link-eexist" "init-frontier-root-fenced" "init-frontier-stage-unlinked"
    "init-final-config-file-fenced" "init-final-config-record-file-fenced"
    "init-final-frontier-file-fenced" "init-transactions-fenced"
    "init-root-fenced" "init-parent-fenced"))

;; These controls are intentionally outside fn-bsi-current-init-program: they
;; fail *before* a directory enumeration to verify the host does not confuse
;; an OS error with an empty configuration history.
(defparameter +fnn-init-test-controls+
  '("init-config-records-first-enumerate" "init-config-records-final-enumerate"))

(defun fnn-init-test-fault ()
  "Developer-only FN_NATIVE_INIT_FAULT=MODEL-CUT:eio|kill|eacces selector.

This is intentionally not a command-line option or an operator configuration
field.  The external native fidelity test uses it to stop one child process at
a source-pinned post-syscall cut."
  (let ((raw (fnn-developer-selector "FN_NATIVE_INIT_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_INIT_FAULT (expected MODEL-CUT:eio|kill|eacces)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (or (member label +fnn-init-model-cuts+ :test #'string=)
                      (member label +fnn-init-test-controls+ :test #'string=))
            (fnn-fault "unknown FN_NATIVE_INIT_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      ((string= action "eacces") :fnn-test-config-no-read)
                      (t (fnn-fault "invalid FN_NATIVE_INIT_FAULT action: ~a" action)))
                "developer-only native initializer fault"))))))

;; In the order fnn-recover reaches them.  `recover-replayed' and
;; `recover-barrier' are fn-bs-recover-program's own cuts
;; (books/byte-store-programs.lisp); `recover-barrier-N' selects each of the
;; five model cuts.  `recovery-stage-unlinked' is
;; fn-bs-recover-stage-cleanup-program's cut, and that program runs once per
;; removed orphan AFTER fn-bs-recover-program has completed: fnn-recover
;; sweeps only once the fifth barrier observation has reached :ready.
(defparameter +fnn-recovery-model-cuts+
  '("recover-replayed" "recover-barrier-1" "recover-barrier-2"
    "recover-barrier-3" "recover-barrier-4" "recover-barrier-5"
    "recovery-stage-unlinked"))

(defun fnn-recovery-test-fault ()
  "Developer-only FN_NATIVE_RECOVERY_FAULT=MODEL-CUT:eio|kill selector.

This is not an operator option.  It selects one of fnn-recover's `fnn-at'
cuts: after replay, after a recovery barrier, or after the real unlink of a
staging orphan.  A subsequent command is a fresh process rather than an
in-process retry."
  (let ((raw (fnn-developer-selector "FN_NATIVE_RECOVERY_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_RECOVERY_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (member label +fnn-recovery-model-cuts+ :test #'string=)
            (fnn-fault "unknown FN_NATIVE_RECOVERY_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_RECOVERY_FAULT action: ~a" action)))
                "developer-only native recovery fault"))))))

(defun fnn-command-init (root groups &optional (profile :development))
  (let ((store (make-fnn-store root :writable t :fault (fnn-init-test-fault))))
    (unwind-protect
         (progn (fnn-initialize store (or groups +fnn-default-groups+) profile)
                (fnn-acquire store)
                (fnn-out "initialized ~a" (fnn-store-root store)))
      (fnn-store-close store))
    +fnn-exit-ok+))

;; The offline profile upgrade's cuts, in the order
;; `fnn-upgrade-profile-write' reaches them: fn-bs-profile-program's
;; (books/byte-store-profile-program.lisp) five `:cut' steps.
(defparameter +fnn-profile-model-cuts+
  '("profile-created" "profile-written" "profile-staged-durable"
    "profile-replaced" "profile-durable"))

(defun fnn-profile-test-fault ()
  "Developer-only FN_NATIVE_PROFILE_FAULT=MODEL-CUT:eio|kill selector.

Not an operator option: it selects one `fnn-at' cut of the profile upgrade's
byte program.  kill is SIGKILL at the cut, so the next command is a new
process; eio raises the host's EIO there."
  (let ((raw (fnn-developer-selector "FN_NATIVE_PROFILE_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_PROFILE_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (member label +fnn-profile-model-cuts+ :test #'string=)
            (fnn-fault "unknown FN_NATIVE_PROFILE_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_PROFILE_FAULT action: ~a" action)))
                "developer-only native profile-upgrade fault"))))))

(defun fnn-upgrade-profile-write (store octets)
  "P-PROFILE, books/byte-store-profile-program.lisp `fn-bs-profile-program'.

Stage OCTETS under a `.stage-' name (the recovery sweep's), fence it, rename
it onto config.json, fence the root.  Before the rename a failure is known:
config.json is the old frame and the stage is an orphan the next open sweeps
(exit 1).  At or after it the outcome is uncertain (exit 3): the next open
reads whichever frame the directory holds, old or new, never a torn one
(fn-bs-profile-program-crash-is-old-or-new)."
  (let ((stage (fnn-join (fnn-staging store) (format nil ".stage-profile-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
        (attempted nil))
    (handler-case
        (progn
          (fnn-write-staged-at store stage octets :profile-created :profile-written)
          (fnn-at store :profile-staged-durable)
          (setq attempted t)
          (fnn-replace stage (fnn-config-path store))
          (fnn-at store :profile-replaced)
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-at store :profile-durable))
      (fnn-os-error (e)
        (if attempted
            (fnn-indeterminate "store profile replacement is indeterminate: ~a" e)
            (fnn-refuse-io "known failure before the profile replacement: ~a" e))))))

(defun fnn-command-upgrade-profile (root profile)
  "Offline: replace the store's profile by PROFILE when ACL2 calls it an upgrade.

The store is opened as `recover' opens it: the exclusive writer lock (so a
running owner refuses this with `store is already locked'), the old profile's
bounds, full replay and recovery barriers.  ACL2's verdict
(`fn-profile-upgrade-verdict') decides and supplies the frame; the host only
writes it.  Same profile and anything but an upgrade are refused (exit 1) and
write nothing."
  (multiple-value-bind (store records) (fnn-open-live-store root t (fnn-profile-test-fault))
    (unwind-protect
         (let ((verdict (fnn-core 'fn-store-profile-upgrade-verdict
                                  (fnn-store-config store) profile)))
           (unless (and (consp verdict) (member (first verdict) '(:upgrade :refused)))
             (fnn-fault "ACL2 returned a malformed profile verdict"))
           (if (eq (first verdict) :refused)
               (fnn-refuse "store profile upgrade refused: ~(~a~)~@[ ~a~]"
                           (second verdict) (third verdict))
               (destructuring-bind (octets old-budget new-budget) (rest verdict)
                 (unless (and (fnn-octet-list-p octets) octets
                              (integerp old-budget) (integerp new-budget))
                   (fnn-fault "ACL2 returned a malformed profile frame"))
                 (fnn-upgrade-profile-write store (fnn-octets octets))
                 (fnn-out "upgraded profile=~(~a~) transactions-used=~d transactions-budget=~d previous-budget=~d"
                          (if (symbolp profile) profile (first profile))
                          (length records) new-budget old-budget)
                 (fnn-out-profile (fnn-metadata-config-decode octets))
                 +fnn-exit-ok+)))
      (fnn-store-close store))))

(defparameter +fnn-cli-faults+
  (list (cons "prepublish" (list :record-staged-durable 'fnn-store-error
                                 "injected known abort before publication"))
        (cons "postpublish" (list :record-attempted 'fnn-store-indeterminate
                                  "indeterminate injected failure after final publication"))
        (cons "frontierbarrier" (list :frontier-barrier 'fnn-os-error
                                      "injected allocator directory barrier failure"))
        (cons "recordbarrier" (list :record-barrier 'fnn-os-error
                                    "injected transaction directory barrier failure"))))

(defparameter +fnn-post-model-cuts+
  '(:frontier-created :frontier-written
    :frontier-staged-durable :frontier-replaced :frontier-attempted
    :frontier-durable :frontier-reserved
    :record-created :record-written :record-staged-durable
    :record-linked :record-attempted :record-durable :record-completing
    :record-stage-unlinked :record-staging-cleaned
    ;; fnn-mark-committed: fn-bs-marker-program (books/byte-store-marker-program),
    ;; whose names are fn-hm-marker-cut-names.
    :marker-created :marker-written :marker-staged-durable
    :marker-replaced :marker-durable
    :finish-consumed :finish-durable))

(defun fnn-post-test-fault ()
  "Developer-only FN_NATIVE_POST_FAULT=MODEL-CUT:eio|kill selector.

The frontier-attempted:stop and record-attempted:stop variants park the process
for an isolated block fault test. They resume at the same cut and do not inject
an ACL2 outcome.

The point is one of fnn-advance-frontier/fnn-publish/fnn-finish's actual
fnn-at boundaries.  SIGKILL cannot run unwind-protect, so the next command
observes a genuine new-process image."
  (let ((raw (fnn-developer-selector "FN_NATIVE_POST_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_POST_FAULT (expected MODEL-CUT:eio|kill)"))
        (let* ((label (subseq raw 0 colon))
               (point (intern (string-upcase label) :keyword))
               (action (subseq raw (1+ colon))))
          (unless (or (member point +fnn-post-model-cuts+)
                      ;; The committed-history marker's cuts are ACL2's
                      ;; table (books/store-history-marker).
                      (member (string-downcase label)
                              (fnn-core 'fn-hm-marker-cut-names) :test #'string=))
            (fnn-fault "unknown FN_NATIVE_POST_FAULT cut: ~a" label))
          (list point
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      ((and (string= action "stop")
                            (member point '(:frontier-attempted
                                            :record-attempted))) :fnn-test-stop)
                      (t (fnn-fault
                          "invalid FN_NATIVE_POST_FAULT action: ~a" action)))
                "developer-only native post fault"))))))

(defun fnn-post-entry-fault (inject)
  "The one store fault a posting entry arms, or NIL.

Both posting entries call this: `store ROOT post' (fnn-command-post) and the
served owner (fnn-owner-run-normalized, fnn-command-owner in owner.lisp).  So
both read the same selectors, from the same tables, into the same store slot
that `fnn-at' tests; the cut sites themselves are in fnn-recover,
fnn-advance-frontier, fnn-publish and fnn-finish, which both entries call.

INJECT is the positional `store post' FAULT argument (one of
+fnn-cli-faults+).  FN_NATIVE_POST_FAULT selects a post cut and
FN_NATIVE_RECOVERY_FAULT a recovery cut.  A store has one fault slot, so two
selections at once are a usage error rather than one silently winning.  On a
production image the environment selectors read as NIL (the startup gate
`fnn-developer-selector-gate' has already refused them) and INJECT is a usage
error for the same reason."
  (when (and inject (not (fnn-developer-image-p)))
    (error 'fnn-usage-error
           :message "the store post FAULT argument requires a developer image"))
  (let* ((positional
           (when inject
             (or (cdr (assoc inject +fnn-cli-faults+ :test #'string=))
                 (error 'fnn-usage-error :message "unknown fault point"))))
         (selected (remove nil (list positional (fnn-post-test-fault)
                                     (fnn-recovery-test-fault)))))
    (when (cdr selected)
      (error 'fnn-usage-error
             :message "select at most one of the FAULT argument, FN_NATIVE_POST_FAULT and FN_NATIVE_RECOVERY_FAULT"))
    (first selected)))

(defun fnn-command-post (root message-id payload-path charge-text inject groups)
  ;; This direct guard also protects callers of the raw function outside the
  ;; CLI dispatcher.  The startup gate below rejects the CLI before dispatch.
  (unless (fnn-developer-image-p)
    (error 'fnn-usage-error
           :message "store post is available only in the developer image"))
  (let* ((msgid (fnn-octets (fnn-ascii-octet-list message-id)))
         (fault (fnn-post-entry-fault inject)))
    (let ((store (fnn-open-live-store root t fault)))
      (unwind-protect
           (let* ((payload (fnn-read-regular-bounded
                            ;; One octet past the profile's A, so that a longer
                            ;; payload reaches ACL2's boundary and is refused
                            ;; there by name (`:payload-bound'), not by the read.
                            payload-path (1+ (fnn-config-max-payload store))))
                  (codes (fnn-group-codes-for store groups))
                  (charge (if charge-text (parse-integer charge-text) (fnn-charge (length payload))))
                  (sequence nil))
             (fnn-validate-post-boundary
              (fnn-post-boundary (fnn-store-config store) msgid (length payload)
                                 (length codes) charge))
             (let ((existing (fnn-bridge-existing-action msgid payload codes)))
               (when (eq existing :duplicate)
                 (fnn-out "duplicate")
                 (return-from fnn-command-post +fnn-exit-ok+))
               (when (eq existing :conflict)
                 (fnn-refuse "conflicting immutable Message-ID")))
             (unless (eq (fnn-core-state 'fn-store-sn-publication-verdict
                                         (fnn-store-config store) :article)
                         :admissible)
               (fnn-refuse "transaction count has reached configured bound"))
             (fnn-advance-frontier store (fnn-bridge-next-txid))
             (multiple-value-bind (obligation subject evidence) (fnn-metadata msgid payload)
               (let ((action (fnn-bridge-prepare msgid payload codes obligation subject evidence charge)))
                 (unless (eq action :prepared)
                   (setf (fnn-store-fenced store) t)
                   (unless (eq (fnn-bridge-refuse-reservation) :refused)
                     (fnn-indeterminate "ACL2 could not consume refused reservation"))
                   (fnn-refuse "ACL2 refused post: ~(~a~)" action))))
             (let ((record (fnn-bridge-pending-record)))
               (setq sequence (fnn-pending-sequence
                               (fnn-core-state 'fn-store-sn-pending-sequence)))
               (handler-case (fnn-publish store sequence record)
                 (fnn-store-indeterminate (e) (error e))
                 (fnn-store-error (e)
                   (unless (fnn-store-fenced store)
                     (setf (fnn-store-fenced store) t)
                     (unless (eq (fnn-bridge-known-abort) :aborted)
                       (fnn-indeterminate "ACL2 rejected known pre-publication abort")))
                   (error e))))
             (fnn-mark-committed store sequence)
             (setf (fnn-store-fenced store) t)
             (fnn-finish store)
             (fnn-out "committed sequence=~d charge=~d" sequence charge)
             +fnn-exit-ok+)
        (fnn-store-close store)))))

(defun fnn-regular-path-p (path)
  (handler-case (fnn-regular-p (sb-posix:lstat path))
    (sb-posix:syscall-error () nil)))

(defun fnn-anchor-report (store)
  "The freshness question, answered the way tools/run_store.py answers it.

A store that never recorded an anchor has nothing to be stale against, and
`anchor=none' says exactly that.  A store that holds one cannot be answered by
this image: it has no pinned Roughtime client, so the answer is uncertain --
never `none', which would report a possibly stale store as a fresh one.  The
record itself is books/anchor's (host/anchor-host.lisp is in the image now);
this reads only whether there is one."
  (if (fnn-regular-path-p (fnn-join (fnn-store-root store) "anchor.fnan"))
      (values "anchor=uncertain [no anchor source in the native host]"
              +fnn-exit-uncertain+)
      (values "anchor=none" +fnn-exit-ok+)))

(defun fnn-command-recover (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t (fnn-recovery-test-fault))
    (unwind-protect
         (multiple-value-bind (report code) (fnn-anchor-report store)
           (fnn-out "recovered transactions=~d articles=~d ~a ~a ~a"
                    (length records) (fnn-bridge-article-count)
                    (fnn-orphan-report store) report
                    (fnn-checkpoint-report store))
           (fnn-out "~a" (fnn-open-report store))
           (if (and (= code +fnn-exit-ok+)
                    (eq (first (fnn-store-checkpoint-outcome store)) :corrupt))
               +fnn-exit-fault+
             code))
      (fnn-store-close store))))

(defun fnn-out-profile (values)
  "Print the store profile ACL2 reports: its persisted format and every
field by its operator name (books/byte-store-frame.lisp `fn-bs-profile-report')."
  (let ((report (fnn-core 'fn-store-profile-report values)))
    (unless (and (consp report)
                 (every (lambda (entry)
                          (and (consp entry) (stringp (car entry))
                               (integerp (cdr entry)) (>= (cdr entry) 0)))
                        report))
      (fnn-fault "ACL2 returned a malformed profile report"))
    (fnn-out "profile~{ ~a=~d~}"
             (loop for (name . value) in report collect name collect value))))

(defun fnn-out-headroom (store)
  "Print ACL2's headroom for the open Store: transactions used of the
profile's budget, committed record octets of its history bound, and the
retention ledger's reserved charge of its capacity."
  (let ((headroom (fnn-core-state 'fn-store-sn-headroom (fnn-store-config store))))
    (unless (and (listp headroom) (= (length headroom) 6)
                 (every (lambda (n) (and (integerp n) (>= n 0))) headroom))
      (fnn-fault "ACL2 returned malformed headroom"))
    (destructuring-bind (used budget bytes-used history reserved capacity) headroom
      (fnn-out-profile (fnn-store-config store))
      (fnn-out "headroom transactions-used=~d transactions-budget=~d bytes-used=~d history-bound=~d charge-reserved=~d charge-capacity=~d"
               used budget bytes-used history reserved capacity))))

(defun fnn-store-observation (store)
  "What this process observed at its own open, which the status report names:
the staging orphans, whether their listing stopped at its bound, and how
the Store was opened (checkpoint or full replay, and why)."
  (list (fnn-store-orphans store) (fnn-store-orphans-more store)
        (fnn-store-open-mode store)))

(defun fnn-write-report (report)
  "Write the octets of one ACL2 status report; render nothing."
  (unless (fnn-octet-list-p report)
    (fnn-fault "ACL2 returned a malformed status report"))
  (when report
    (write-sequence (fnn-octets report) *fnn-stdout*)
    (finish-output *fnn-stdout*)))

(defun fnn-command-live-report (root kind)
  "The status report of KIND over the Store at ROOT, opened read-only.

books/native-live-status.lisp `fn-nls-offline-report' renders every word;
the running owner answers the same report of the state it carries
(`fn-nls-live-report-is-the-offline-report').  The shared lock refuses while
an owner holds the Store: `operator CONFIG status' asks that owner instead."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (progn
           (fnn-write-report
            (fnn-core 'fn-native-live-status-host-offline kind
                      (fnn-store-config store) (fnn-store-observation store)
                      *the-live-state*))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-status (root)
  (fnn-command-live-report root :status))

(defun fnn-command-retention (root)
  "Report the replayed ACL2 ledger's pin count and reserved charge."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (progn
           (fnn-out "pins=~d reserved=~d"
                    (fnn-bridge-pin-count) (fnn-bridge-reserved))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-config (root)
  "The replayed configuration: generation, served table, domain."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (progn (fnn-out "generation=~d served=~{~a~^,~} domain=~{~a~^,~}"
                         (fnn-store-config-generation store)
                         (fnn-store-config-served store)
                         (fnn-store-config-domain store))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-inspect (root message-id)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (let ((msgid (progn
                        ;; Python encodes the Message-ID after opening the
                        ;; store, so a non-ASCII identifier is a usage error
                        ;; only once the store itself opened.
                        (unless (every (lambda (c) (< (char-code c) 128)) message-id)
                          (error 'fnn-usage-error :message "Message-ID is not ASCII"))
                        (fnn-octets (fnn-ascii-octet-list message-id)))))
           (cond ((not (fnn-bridge-lookup-found-p msgid)) +fnn-exit-refused+)
                 (t (write-sequence (fnn-bridge-lookup msgid) *fnn-stdout*)
                    (finish-output *fnn-stdout*)
                    +fnn-exit-ok+)))
      (fnn-store-close store))))

(defun fnn-command-probe (root count)
  "tests/store_capacity_probe.py's sequence in-process: commit COUNT maximum
payloads, close, reopen, and report both timings as JSON on stdout."
  (let* ((started (get-internal-real-time))
         (store (make-fnn-store root :writable t))
         (payload nil))
    (fnn-initialize store)
    (fnn-acquire store)
    (fnn-bridge-reset)
    (fnn-recover store)
    (setq payload (make-array (fnn-config-max-payload store)
                              :element-type '(unsigned-byte 8)
                              :initial-element (char-code #\x)))
    (let ((codes (fnn-group-codes-for store +fnn-default-groups+)))
      (dotimes (sequence count)
        (let ((msgid (fnn-octets (fnn-ascii-octet-list
                                  (format nil "<capacity-~d@example.invalid>" sequence)))))
          (multiple-value-bind (obligation subject evidence) (fnn-metadata msgid payload)
            (fnn-advance-frontier store (fnn-bridge-next-txid))
            (unless (eq (fnn-bridge-prepare msgid payload codes obligation subject evidence
                                            (fnn-charge (length payload)))
                        :prepared)
              (fnn-fault "probe prepare refused"))
            (let ((pending (fnn-pending-sequence
                            (fnn-core-state 'fn-store-sn-pending-sequence))))
              (unless (eq (fnn-publish store pending (fnn-bridge-pending-record))
                          :durable)
                (fnn-fault "probe publish refused"))
              (fnn-mark-committed store pending))
            (unless (eq (fnn-finish store) :durable) (fnn-fault "probe finish refused"))))))
    (let ((commit-seconds (/ (- (get-internal-real-time) started)
                             (float internal-time-units-per-second 1d0))))
      (fnn-store-close store)
      (let ((before (get-internal-real-time)))
        (multiple-value-bind (reopened records) (fnn-open-live-store root nil)
          (let ((reopen-seconds (/ (- (get-internal-real-time) before)
                                   (float internal-time-units-per-second 1d0))))
            (unwind-protect
                 (progn
                   (unless (and (= (length records) count) (= (fnn-bridge-article-count) count)
                                (= (fnn-bridge-pin-count) count)
                                (= (fnn-bridge-group-next 0) (1+ count))
                                (= (fnn-bridge-group-next 1) (1+ count))
                                (equalp (fnn-bridge-lookup
                                         (fnn-octets (fnn-ascii-octet-list "<capacity-0@example.invalid>")))
                                        payload)
                                (= (fnn-bridge-reserved) (* count (fnn-charge (length payload)))))
                     (fnn-fault "probe reopen state mismatch"))
                   (fnn-out "{\"host\":\"native\",\"transactions\":~d,\"payload_bytes\":~d,~
                             \"commit_seconds\":~,4f,\"reopen_seconds\":~,4f,\"status\":\"passed\"}"
                            count (fnn-config-max-payload reopened)
                            commit-seconds reopen-seconds))
              (fnn-store-close reopened)))))
      +fnn-exit-ok+)))

;;; ---------------------------------------------------------------------------
;;; The reader: tools/run_reader.py's loopback listener over fn-wire-next and
;;; fn-nntp-step through host/reader-host.lisp.

(defconstant +fnn-max-read+ 512)

(define-condition fnn-reader-bridge-fault (error)
  ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))

(defun fnn-reader-select (with-store)
  ;; The operator's posting permission is pinned into the connection at open
  ;; by fn-reader-reset, so a served step reads it from the connection and
  ;; never from a global.  This host serves read-only until it owns a writer
  ;; lock as well: it is set to nil explicitly, never left unbound.
  (fnn-core-state 'fn-reader-set-posting nil)
  (let ((selection (fnn-core-state (if with-store 'fn-reader-use-store 'fn-reader-use-seed))))
    (unless (member selection '(:ready :refused))
      (fnn-fault "unexpected ACL2 archive-selection result"))
    (unless (eq selection :ready)
      (fnn-refuse "reader archive is not NNTP-projectable"))))

(defun fnn-reader-octets-of (value)
  (unless (fnn-octet-list-p value) (fnn-fault "unexpected ACL2 octet-list result"))
  (fnn-octets value))

(defun fnn-reader-octets (global)
  (let ((value (fnn-global global)))
    (unless (fnn-octet-list-p value) (fnn-fault "unexpected ACL2 octet-list result"))
    value))

(defun fnn-model-chunks (path)
  "The chunk list of a length-prefixed file: a decimal count, LF, that many
octets, repeated.  Parsed here digit by digit; external data never reaches the
Lisp reader."
  (let ((data (fnn-read-regular-bounded path (ash 1 22)))
        (at 0) (chunks nil))
    (loop while (< at (length data)) do
      (let ((eol (position 10 data :start at)) (count 0))
        (unless eol (fnn-refuse "chunk file: unterminated length"))
        (when (= eol at) (fnn-refuse "chunk file: empty length"))
        (loop for index from at below eol do
          (let ((digit (- (aref data index) 48)))
            (unless (<= 0 digit 9) (fnn-refuse "chunk file: non-decimal length"))
            (setq count (+ (* count 10) digit))))
        (when (> (+ eol 1 count) (length data)) (fnn-refuse "chunk file: truncated chunk"))
        (push (subseq data (+ eol 1) (+ eol 1 count)) chunks)
        (setq at (+ eol 1 count))))
    (nreverse chunks)))

(defun fnn-reader-reset ()
  (fnn-core-state 'fn-reader-reset)
  (fnn-octets (fnn-reader-octets 'fn-reader-output)))

(defun fnn-reader-chunk (octets)
  "One socket read, consumed whole by one certified call: (values reply closing).

`fn-served-step' (books/served.lisp) is a fold of fn-wire-feed-byte with
fn-nntp-post-step run on each framed event before the next byte, with the
reply concatenation; article mode is wire state inside the connection, so a
POST and its article are the same one call per read.  It consumes the entire
chunk, so there is no unconsumed suffix to hand back and no wire loop in this
file: `fn-served-run-is-the-concatenated-step' says the cut points the network
chose are invisible, and tests/native_differential.py is the evidence that
this host obeys it."
  (if (null octets)
      (values (fnn-make-octets 0) nil)
      (progn
        (fnn-core-state 'fn-reader-chunk octets)
        (let ((closing (fnn-global 'fn-reader-closep)))
          (unless (member closing '(t nil)) (fnn-fault "unexpected ACL2 boolean result"))
          (values (fnn-octets (fnn-reader-octets 'fn-reader-output)) closing)))))

(defun fnn-reader-submission ()
  "The article a served step injected, or NIL.  ACL2 produced every octet."
  (let ((octets (fnn-global 'fn-reader-submit-octets)))
    (and octets
         (progn
           (unless (fnn-octet-list-p octets) (fnn-fault "unexpected ACL2 octet-list result"))
           (list (fnn-octets (fnn-reader-octets 'fn-reader-submit-msgid))
                 (fnn-octets octets))))))

(defun fnn-reader-outcome (completion)
  "One durable outcome, served: ACL2 writes the 240 or the 441, never this file."
  (fnn-core-state 'fn-reader-outcome completion)
  (fnn-octets (fnn-reader-octets 'fn-reader-output)))

(defun fnn-recv (fd seconds &optional (maximum +fnn-max-read+))
  "Read at most MAXIMUM octets, an empty vector at end of input, or :timeout.

SECONDS bounds every readiness wait and interrupted/nonblocking retry as one
absolute deadline.  MAXIMUM is a caller-supplied ACL2 projection when a
protocol admits a tighter retained-input bound; it is validated before the
buffer allocation and syscall.  FD must have passed through FNN-SOCKET-FD,
which makes it nonblocking: a readiness race therefore returns EAGAIN and
waits again rather than starting an unbounded blocking read.  A zero-second
call performs one zero-time poll; it never spins after an EAGAIN race."
  (when (< seconds 0) (fnn-fault "negative socket receive timeout"))
  (unless (and (integerp maximum) (<= 1 maximum) (<= maximum +fnn-max-read+))
    (fnn-fault "invalid socket receive maximum: ~s" maximum))
  (let ((deadline (+ (fnn-now) (* seconds internal-time-units-per-second)))
        (zero-poll-p (zerop seconds)))
    (loop
      (let ((remaining (fnn-seconds-to-deadline deadline)))
        (when (and (<= remaining 0) (not zero-poll-p))
          (return :timeout))
        (unless (funcall *fnn-fd-waiter* fd :input remaining)
          (return :timeout))
        (setq zero-poll-p nil)
        (let* ((buffer (fnn-make-octets maximum))
               (count (fnn-read-fd fd buffer deadline t)))
          (cond ((eq count :would-block)
                 ;; The descriptor is nonblocking.  Go back through the
                 ;; readiness waiter instead of polling the syscall in a loop.
                 nil)
                (t (return (subseq buffer 0 count)))))))))

(defun fnn-send-all (fd octets seconds)
  "Write OCTETS with one deadline for readiness waits and EINTR retries.

FD must have passed through FNN-SOCKET-FD, which makes it nonblocking.  A
partial write resumes at its unwritten offset; EAGAIN/EWOULDBLOCK returns to
the readiness waiter under the same absolute deadline.  A zero-second call
performs one zero-time output poll and cannot busy-spin after a race."
  (when (< seconds 0) (fnn-fault "negative socket send timeout"))
  (let ((data (fnn-octets octets))
        (offset 0)
        (deadline (+ (fnn-now) (* seconds internal-time-units-per-second)))
        (zero-poll-p (zerop seconds)))
    (loop while (< offset (length data)) do
      (let ((remaining (fnn-seconds-to-deadline deadline)))
        (when (and (<= remaining 0) (not zero-poll-p))
          (fnn-os-fail sb-posix:etimedout))
        (unless (funcall *fnn-fd-waiter* fd :output remaining)
          (fnn-os-fail sb-posix:etimedout))
        (setq zero-poll-p nil)
        (let ((unwritten (- (length data) offset)))
          (let ((progress
                  (fnn-write-progress
                   (lambda () (funcall *fnn-write-syscall* fd data offset unwritten))
                   unwritten "socket" deadline t)))
            ;; A readiness notification can race another reader.  The next
            ;; iteration waits again, so EAGAIN cannot become a busy loop.
            (unless (eq progress :would-block)
              (incf offset progress))))))))

(defun fnn-graceful-close (fd)
  "End a connection after its final reply without a reset: shutdown the
output side, then drain the peer's input for at most one second."
  (when (< (fnn-%shutdown fd +fnn-shut-wr+) 0) (return-from fnn-graceful-close nil))
  (let ((deadline (+ (get-internal-real-time) internal-time-units-per-second)))
    (handler-case
        (loop while (< (get-internal-real-time) deadline) do
          (let* ((remaining (/ (- deadline (get-internal-real-time))
                               (float internal-time-units-per-second)))
                 (received (fnn-recv fd (max 0.05 remaining))))
            (when (or (eq received :timeout) (zerop (length received)))
              (return))))
      (fnn-os-error () nil))))

;;; The socket surface host/native/tcpcl.lisp builds its convergence layer on
;;; (planning/lanes/HANDOFF-w4-tcpcl.md).  Nothing above this point opens a
;;; socket, and the reader below opens none of its own either.

(defun fnn-socket-fd (socket)
  "The nonblocking descriptor used by the deadline-aware socket helpers."
  (fnn-set-nonblocking (sb-bsd-sockets:socket-file-descriptor socket)))

(defun fnn-socket-shutdown (socket)
  "Wake socket I/O without closing its descriptor.

The worker that owns SOCKET performs the later close, so a stop hook cannot
close a descriptor that another worker has cached and the kernel may reuse."
  (ignore-errors (sb-bsd-sockets:socket-shutdown socket :direction :io))
  nil)

(defun fnn-socket-shut (socket)
  (ignore-errors (sb-bsd-sockets:socket-close socket))
  nil)

(defun fnn-socket-class (family)
  (if (eq family :inet6) 'sb-bsd-sockets:inet6-socket 'sb-bsd-sockets:inet-socket))

(defun fnn-loopback (family)
  (if (eq family :inet6) #(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1) #(127 0 0 1)))

(defun fnn-listen (port &key (family :inet) (backlog 1) (address nil))
  "A bound, listening socket and the port the kernel chose.  ADDRESS defaults
to loopback: a listener reachable off the box is the operator's decision, made
by passing one, not this file's default.

BACKLOG is the kernel's accept queue.  The default of 1 suits a listener that
serves one client at a time and accepts the next only when that one is gone --
fnn-command-reader, the diagnostic reader, is the caller it is written for.  A
service whose accept thread hands each connection to a worker must pass a
depth: with 1, a client arriving while the accept thread is launching the
previous worker is dropped.  The owner passes
+fnn-owner-listen-backlog+ (host/native/owner.lisp)."
  (let ((listener (make-instance (fnn-socket-class family) :type :stream :protocol :tcp)))
    (handler-case
        (progn
          (setf (sb-bsd-sockets:sockopt-reuse-address listener) t)
          (sb-bsd-sockets:socket-bind listener (or address (fnn-loopback family)) port)
          (sb-bsd-sockets:socket-listen listener backlog)
          (multiple-value-bind (bound-address bound-port) (sb-bsd-sockets:socket-name listener)
            (declare (ignore bound-address))
            (values listener bound-port)))
      (error (e) (fnn-socket-shut listener) (error e)))))

(defvar *fnn-connect-attempt*
  (lambda (socket address port)
    "Return :CONNECTED or :PENDING from one nonblocking connect(2) attempt."
    (handler-case
        (progn (sb-bsd-sockets:socket-connect socket address port) :connected)
      (sb-bsd-sockets:operation-in-progress () :pending)))
  "Raw connect seam.  Tests use :PENDING without inventing a second transport.")

(defvar *fnn-socket-pending-error* #'sb-bsd-sockets:sockopt-error
  "Raw SO_ERROR seam.  Zero establishes a pending TCP connection.")

(defun fnn-connect-address (host)
  "Resolve HOST before starting the TCP deadline.

getaddrinfo through SBCL's GET-HOST-BY-NAME is synchronous and can block.
This intentionally remains a separate availability boundary: no raw thread
termination is used to pretend that DNS has the TCP deadline."
  (if (stringp host)
      (sb-bsd-sockets:host-ent-address (sb-bsd-sockets:get-host-by-name host))
    host))

(defun fnn-connect-complete (socket fd deadline zero-poll-p)
  "Wait for one pending nonblocking connect under DEADLINE, then inspect SO_ERROR."
  (loop
    (let ((remaining (fnn-seconds-to-deadline deadline)))
      (when (and (<= remaining 0) (not zero-poll-p))
        (fnn-os-fail sb-posix:etimedout))
      (unless (funcall *fnn-fd-waiter* fd :output remaining)
        (fnn-os-fail sb-posix:etimedout))
      (setq zero-poll-p nil)
      (let ((errno (funcall *fnn-socket-pending-error* socket)))
        (cond ((zerop errno) (return socket))
              ;; A readiness indication can race a pending state change.
              ;; Re-enter the same absolute-deadline wait, never connect(2).
              ((or (= errno sb-posix:einprogress) (= errno sb-posix:ealready)) nil)
              (t (fnn-os-fail errno)))))))

(defun fnn-connect (host port &key (family :inet) (timeout 10))
  "An active TCP open with one nonblocking connect deadline.

HOST is an address vector or a name resolved before the TCP attempt.  TIMEOUT
is a nonnegative host observation in seconds; callers that have a protocol
policy must obtain it from ACL2.  On success the returned socket is already
nonblocking and belongs solely to the caller.  A timeout or real SO_ERROR
closes the private socket before signalling FNN-OS-ERROR.  DNS resolution is
intentionally not timed by this function."
  (unless (and (realp timeout) (>= timeout 0))
    (fnn-fault "invalid TCP connect timeout: ~s" timeout))
  ;; Resolve first so the TCP deadline says only what it can actually bound.
  (let* ((address (fnn-connect-address host))
         (socket (make-instance (fnn-socket-class family) :type :stream :protocol :tcp))
         (completed nil))
    (unwind-protect
         (let* ((fd (fnn-socket-fd socket))
                (deadline (+ (fnn-now) (* timeout internal-time-units-per-second))))
           (case (funcall *fnn-connect-attempt* socket address port)
             (:connected (setq completed t) socket)
             (:pending (prog1 (fnn-connect-complete socket fd deadline (zerop timeout))
                         (setq completed t)))
             (otherwise (fnn-fault "connect boundary returned an invalid status"))))
      (unless completed (fnn-socket-shut socket)))))

(defun fnn-accept-observe (listener seconds)
  "Return one accepted socket or :TIMEOUT after a bounded readiness wait.

The listener is nonblocking so shutdown(2) need not wake a blocking accept(2)
on every supported host.  Socket and syscall conditions remain conditions for
the caller to classify against its own stop and fault state."
  (let ((fd (fnn-socket-fd listener)))
    (if (funcall *fnn-fd-waiter* fd :input seconds)
        (sb-bsd-sockets:socket-accept listener)
      :timeout)))

(defun fnn-accept-loop (listener handler &optional once)
  "Run HANDLER on each accepted connection; HANDLER owns and closes its socket."
  (loop
    (funcall handler (sb-bsd-sockets:socket-accept listener))
    (when once (return))))

(defun fnn-serve-client (socket)
  "Serve one connection; a broken peer cannot end the listener.  A core
failure that leaves the reader unable to correlate replies is a bridge fault."
  (let ((fd (fnn-socket-fd socket)))
    (unwind-protect
         (handler-case
             (progn
               (fnn-send-all fd (fnn-reader-reset) 10)
               (loop
                 (let ((incoming (fnn-recv fd 10)))
                   (when (or (eq incoming :timeout) (zerop (length incoming)))
                     (return))
                   ;; One read, one certified step.  The loop that used to
                   ;; live here re-fed an unconsumed suffix and so computed
                   ;; fn-wire-drive in this file; books/served.lisp owns that
                   ;; loop now.
                   (multiple-value-bind (reply closing)
                       (handler-case (fnn-reader-chunk (fnn-octet-list incoming))
                         ;; A recovery fence and a malformed core result are
                         ;; process outcomes, not a peer's ordinary refusal.
                         (fnn-store-indeterminate (e) (error e))
                         (fnn-store-fault (e) (error e))
                         (fnn-store-error ()
                           ;; A semantic refusal is not a protocol reply; this
                           ;; connection's input is dropped while the listener
                           ;; remains usable.
                           (return-from fnn-serve-client nil)))
                     (when (> (length reply) 0) (fnn-send-all fd reply 10))
                     (when (fnn-reader-submission)
                       ;; The step submitted an injected article.  This host
                       ;; holds a shared lock, so the durable attempt is not
                       ;; its to make: the completion is refused -- distinct
                       ;; from durable and from uncertain -- and goes back as
                       ;; one more served input, which ACL2 turns into the
                       ;; reply.  The owner process lane replaces the constant.
                       (let ((outcome (fnn-reader-outcome :refused)))
                         (when (> (length outcome) 0) (fnn-send-all fd outcome 10))))
                     (when closing
                       (fnn-graceful-close fd)
                       (return-from fnn-serve-client nil))))))
           (fnn-os-error () nil)
           (sb-bsd-sockets:socket-error () nil)
           ;; Keep the three core outcomes distinct.  A semantic refusal costs
           ;; this connection; a fault or recovery fence reaches the one-shot
           ;; command and preserves its 4 or 3 exit code.
           (fnn-store-indeterminate (e) (error e))
           (fnn-store-fault (e) (error e))
           (fnn-store-error () nil)
           (fnn-reader-bridge-fault (e) (error e))
           (serious-condition (e)
             (error 'fnn-reader-bridge-fault
                    :message (format nil "ACL2 bridge failed: ~a" e))))
      (fnn-socket-shut socket))))

(defun fnn-reader-prepare (store-root)
  "Select the archive a served connection reads, and return the open store.

STORE-ROOT NIL is the seeded archive constant.  A store is fixed under a
shared lock: posting needs the incompatible exclusive writer lock, so the
served POST path here is refused rather than silently unowned."
  (let ((store nil))
    (when store-root
      (setq store (make-fnn-store store-root :writable nil))
      (handler-case
          (progn (fnn-acquire store) (fnn-bridge-reset) (fnn-recover store))
        (error (e) (fnn-store-close store) (error e))))
    (handler-case (fnn-reader-select (not (null store-root)))
      (error (e) (when store (fnn-store-close store)) (error e)))
    store))

(defun fnn-command-model (chunk-path store-root)
  "The reply stream `fn-served-run' produces for the chunk list in CHUNK-PATH.

The model side of tests/test_native_served_differential.py: the same octets
the socket carries, through the certified fold in one call, with the open
reply first, exactly as the connection sends it.  This file frames nothing --
`fn-reader-model-octets' (host/native/reader-model-host.lisp) opens the same
connection `fn-reader-reset' opens and projects with
`fn-served-reply-octets'."
  (let ((store (fnn-reader-prepare store-root)))
    (unwind-protect
         (let ((octets (fnn-reader-octets-of
                        (fnn-core-state 'fn-reader-model-octets
                                        (mapcar #'fnn-octet-list
                                                (fnn-model-chunks chunk-path))))))
           (write-sequence octets *fnn-stdout*)
           (finish-output *fnn-stdout*)
           +fnn-exit-ok+)
      (when store (fnn-store-close store)))))

(defun fnn-command-reader (port once store-root)
  (let ((store nil) (listener nil))
    (unwind-protect
         (progn
           (setq store (fnn-reader-prepare store-root))
           (multiple-value-bind (bound bound-port) (fnn-listen port)
             (setq listener bound)
             (fnn-out "LISTENING ~d" bound-port))
           (handler-case (fnn-accept-loop listener #'fnn-serve-client once)
             (fnn-reader-bridge-fault (fault)
               ;; Fail closed rather than answer the next client from a core
               ;; whose replies can no longer be matched to commands.
               (fnn-err "reader: ~a" fault)
               (return-from fnn-command-reader +fnn-exit-fault+)))
           +fnn-exit-ok+)
      (when listener (fnn-socket-shut listener))
      (when store (fnn-store-close store)))))

;;; ---------------------------------------------------------------------------
;;; Entry.  tools/fn_native.py validates the command line with the Python
;;; parsers and hands over a fixed positional protocol after "--fn":
;;;   store ROOT init [GROUP...] | recover | status | retention | config
;;;   store ROOT post MESSAGE-ID PAYLOAD CHARGE|- FAULT|- GROUP...
;;;   store ROOT inspect MESSAGE-ID
;;;   store ROOT probe COUNT
;;;   reader PORT ONCE(0|1) STORE-ROOT|-
;;;   model CHUNK-FILE STORE-ROOT|-
;;;   tcpcl listen PORT [ONCE SPOOL NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU REPLY-FILE TRACE]
;;;   tcpcl send HOST PORT BUNDLE-FILE [SPOOL NODE-ID PEER KEEPALIVE
;;;                      SEGMENT-MRU TRANSFER-MRU EXPECT TRACE]
;;;   tcpcl replay TRACE-FILE [ROLE NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU]
;;;   sha256 PATH
;;; `FN_NATIVE_INIT_FAULT=MODEL-CUT:eio|kill|eacces` is a developer-only test seam;
;;; it is intentionally absent from this command protocol and normal CLI.

;;; Verbs a layer above this file owns.  host/native/tcpcl.lisp registers
;;; "tcpcl" when it loads; naming its dispatcher here instead made this file
;;; unloadable on its own and made the two files order-dependent in both
;;; directions.  An unregistered verb is an unknown verb, which is what a
;;; host built without that layer should say.

(defvar *fnn-verbs* nil)
(defvar *fnn-image-profile* :production)
(defvar *fnn-sigterm-owner-active* nil)
(defvar *fnn-sigterm-requested* nil)
(defvar *fnn-sigterm-wakeup-fd* nil)

(defun fnn-register-verb (verb handler)
  (push (cons verb handler) *fnn-verbs*)
  verb)

(defun fnn-unregister-verb (verb)
  "Withdraw VERB while a build script constructs the image, before it is saved."
  (setq *fnn-verbs* (remove verb *fnn-verbs* :key #'car :test #'string=))
  verb)

;;; The surfaces a build script left out of its image.  The DTN build
;;; (host/native/build-dtn.lisp) loads the owner and the operator for the BP
;;; node, but not the NNTP service, credential administration or the control
;;; socket; it names those here, and the operator refuses an ACL2 plan whose
;;; action needs one as an unsupported entry (usage, exit 5) instead of
;;; calling a function the image does not have.  The default image names none.
(defvar *fnn-image-omitted-surfaces* nil)

(defun fnn-image-omits-p (surface)
  (and (member surface *fnn-image-omitted-surfaces*) t))

(defun fnn-select-image-profile
    (&optional (name (or (sb-ext:posix-getenv "FN_NATIVE_PROFILE")
                         "production")))
  "Select the entry surface once while constructing the saved image.

The default and deployment profile is production.  Developer images opt in
before diagnostic modules are loaded; a process environment cannot change the
serialized profile when the saved image later starts."
  (setq *fnn-image-profile*
        (cond ((string= name "production") :production)
              ((string= name "developer") :developer)
              (t (error "unknown native image profile ~s" name)))))

(defun fnn-developer-image-p ()
  (eq *fnn-image-profile* :developer))

(defun fnn-dash-nil (text) (if (string= text "-") nil text))

;;; Developer selectors: one table, one gate.
;;;
;;; Each name below arms a developer-only cut or fault: a process death, an
;;; injected EIO, a stop, a pause.  A developer image honours them.  A
;;; production image refuses to START with any of them in its environment, or
;;; with a `store post' FAULT argument: `fnn-main' calls
;;; `fnn-developer-selector-gate' before `fnn-dispatch', so the refusal is a
;;; usage exit (5) naming the variable, and no store, socket or request is
;;; ever reached.  Readers go through `fnn-developer-selector', which answers
;;; NIL on a production image, so no reader has a production branch of its own
;;; and no refusal can arrive in the middle of a request as an outcome it is
;;; not (review of the dabebb84 campaign, F4 to F6).
(defparameter +fnn-developer-selectors+
  '("FN_NATIVE_INIT_FAULT" "FN_NATIVE_RECOVERY_FAULT" "FN_NATIVE_POST_FAULT"
    "FN_NATIVE_PROFILE_FAULT" "FN_NATIVE_STATE_CHECKPOINT_FAULT"
    "FN_NATIVE_CONTROL_FAULT" "FN_NATIVE_CONTROL_TEST_STOP"
    "FN_NATIVE_AUTH_ADMIN_FAULT"
    "FN_NATIVE_OWNER_TEST_SIGTERM" "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP"
    "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT"
    "FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER" "FN_BP_TEST_DELIVER_FAULT"
    "FN_BP_SERVICE_TEST_FAIL_SECOND_LIFECYCLE_ENUMERATION"
    "FN_BP_CLOCK_DOMAIN_TEST_FAIL"
    "FN_BP_SERVICE_TEST_SEND_FAULT" "FN_BP_APP_TEST_PAUSE_AFTER_DECISION"
    "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN" "FN_BP_NODE_TEST_APP_BUSY"
    "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE"
    "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_TEN"
    "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT"
    "FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX"
    "FN_BP_NODE_TEST_PAUSE_AFTER_REPORT_OUTBOX"
    "FN_BP_ROTATION_TEST_STOP"
    "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT"
    "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_SUBMIT"
    "FN_TCPCL_TEST_FAIL_STAGING_UNLINK" "FN_TCPCL_TEST_FAIL_STAGING_BARRIER"
    "FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA"
    "FN_CHECKPOINT_TEST_FAIL" "FN_CHECKPOINT_TEST_STOP_AFTER"
    "FN_CHECKPOINT_TEST_STOP" "FN_CHECKPOINT_TEST_MISMATCH"
    "FN_APP_JOURNAL_TEST_OBSERVER"
    "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE"
    "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE"
    "FN_APP_JOURNAL_TEST_FENCE_STORE" "FN_APP_JOURNAL_TEST_READ_ONLY_STORE"
    "FN_APP_JOURNAL_TEST_FAIL" "FN_IMMUTABLE_PUBLISH_TEST_FAIL"))

(defun fnn-developer-selector (name)
  "The value of developer selector NAME on a developer image, else NIL."
  (unless (member name +fnn-developer-selectors+ :test #'string=)
    (fnn-fault "~a is not a registered developer selector" name))
  (and (fnn-developer-image-p) (sb-ext:posix-getenv name)))

(defun fnn-store-post-fault-argument (argv)
  "The positional FAULT of `store ROOT post MSGID PAYLOAD CHARGE FAULT ...'."
  (and (>= (length argv) 7)
       (string= (first argv) "store")
       (string= (third argv) "post")
       (fnn-dash-nil (nth 6 argv))))

(defun fnn-developer-selector-refusal (argv)
  "NIL, or what a production image finds that only a developer image honours."
  (unless (fnn-developer-image-p)
    (or (dolist (name +fnn-developer-selectors+)
          (when (sb-ext:posix-getenv name) (return name)))
        (and (fnn-store-post-fault-argument argv)
             "the store post FAULT argument")
        (and (>= (length argv) 3)
             (string= (first argv) "store")
             (string= (third argv) "post")
             "store post"))))

(defun fnn-developer-selector-gate (argv)
  "Refuse, before any store is opened, a production start that names a cut."
  (let ((found (fnn-developer-selector-refusal argv)))
    (when found
      (error 'fnn-usage-error
             :message (format nil "~a is a developer-image selector; this production image does not start with it"
                              found)))))

(defun fnn-register-developer-verb (verb handler)
  "Register a diagnostic entry only in an explicitly selected developer image."
  (when (fnn-developer-image-p)
    (fnn-register-verb verb handler))
  verb)

(defun fnn-verb-handler (verb)
  (cdr (assoc verb *fnn-verbs* :test #'string=)))


(defun fnn-dispatch (args)
  (flet ((need (n) (when (< (length args) n) (error 'fnn-usage-error :message "missing arguments"))))
    (need 1)
    (let ((verb (first args)))
      (cond
        ((string= verb "store")
         (need 3)
         (let ((root (second args)) (command (third args)) (rest (cdddr args)))
           (cond ((string= command "init") (fnn-command-init root rest))
                 ((string= command "recover") (fnn-command-recover root))
                 ((string= command "status") (fnn-command-status root))
                 ((string= command "upgrade-profile")
                  (need 4)
                  (fnn-command-upgrade-profile
                   root (fnn-core 'fn-store-profile-word
                                  (fnn-octet-list (fnn-string-octets (first rest))))))
                 ((string= command "checkpoint") (fnn-command-state-checkpoint root))
                 ((string= command "retention") (fnn-command-retention root))
                 ((string= command "config") (fnn-command-config root))
                 ((string= command "inspect") (need 4) (fnn-command-inspect root (first rest)))
                 ((string= command "probe") (need 4) (fnn-command-probe root (parse-integer (first rest))))
                 ((string= command "post")
                  (need 8)
                  (fnn-command-post root (first rest) (second rest) (fnn-dash-nil (third rest))
                                    (fnn-dash-nil (fourth rest)) (cddddr rest)))
                 (t (error 'fnn-usage-error :message (format nil "unknown store command ~a" command))))))
        ((string= verb "reader")
         (unless (fnn-developer-image-p)
           (error 'fnn-usage-error
                  :message "reader is available only in the developer image"))
         (need 4)
         (fnn-command-reader (parse-integer (second args)) (string= (third args) "1")
                             (fnn-dash-nil (fourth args))))
        ((string= verb "model")
         (need 3)
         (fnn-command-model (second args) (fnn-dash-nil (third args))))
        ;; A registered verb: the TCPCLv4 convergence layer
        ;; (host/native/tcpcl.lisp) is the one today.  Its own positional
        ;; protocol, because its arguments are a peer and a session and not
        ;; a store, so a handler takes a command and the rest.
        ((fnn-verb-handler verb)
         (need 2)
         (funcall (fnn-verb-handler verb) (second args) (cddr args)))
        ((string= verb "sha256")
         (need 2)
         ;; The file reaches ACL2 as a string, read in place by
         ;; `fn-sha256-of-string' (books/sha256-stobj.lisp): no octet list.
         (fnn-out "~a" (fnn-hex (fnn-as-octets
                                 (fnn-core 'fn-sha256-of-string
                                           (fnn-octet-string
                                            (fnn-read-regular-bounded (second args) (ash 1 26)))))))
         +fnn-exit-ok+)
        (t (error 'fnn-usage-error :message (format nil "unknown verb ~a" verb)))))))

(defun fnn-main ()
  (fnn-open-streams)
  ;; A peer that closed first must surface as EPIPE, never as a signal that
  ;; ends the listener; Python ignores SIGPIPE at interpreter start.
  (sb-sys:enable-interrupt sb-unix:sigpipe :ignore)
  (sb-sys:enable-interrupt sb-unix:sigterm
                           (lambda (signal info context)
                             (declare (ignore signal info context))
                             ;; Owner mode keeps one captured listener fd open
                             ;; through all cleanup. Signal context sets one
                             ;; monotonic global and performs raw shutdown(2);
                             ;; it invokes no callback, mutex, allocator or
                             ;; semantic core call.
                             (if *fnn-sigterm-owner-active*
                                 (progn
                                   (setq *fnn-sigterm-requested* t)
                                   (when *fnn-sigterm-wakeup-fd*
                                     (fnn-%shutdown *fnn-sigterm-wakeup-fd*
                                                    +fnn-shut-rdwr+)))
                               (fnn-exit (+ 128 sb-unix:sigterm)))))
  (let* ((argv (cdr (member "--fn" sb-ext:*posix-argv* :test #'string=)))
         (reader-p (and argv (string= (first argv) "reader")))
         (code
           (handler-case
               (progn
                 (fnn-developer-selector-gate argv)
                 (unless (eq (fnn-global 'guard-checking-on) t)
                   (fnn-fault "guard-checking-on is not t in the saved image"))
                 (fnn-dispatch argv))
             (fnn-usage-error (e)
               (fnn-err "fn-host: error: ~a" e)
               +fnn-exit-usage+)
             ((or fnn-store-indeterminate fnn-store-fault fnn-store-error fnn-os-error) (e)
              ;; Socket loss is consumed by fnn-serve-client.  A store/core
              ;; condition that escapes reader setup or the client handler
              ;; keeps the same 3/4/1 outcome as every other native command.
              (fnn-err "~a: ~a" (if reader-p "reader" "store") e)
              (fnn-exit-code-for e))
             (serious-condition (e)
               (fnn-err "~a: internal error: ~a" (if reader-p "reader" "store") e)
               +fnn-exit-fault+))))
    (fnn-exit code)))

;; The saved image's facility checks (the crypto, TLS and ML-DSA OpenSSL pair
;; revalidated per process, host/native/build.lisp fn-native-entry) run before
;; fnn-main and so outside its handlers.  An error there used to reach SBCL's
;; --disable-debugger hook, whose non-aborting exit ACL2's loop caught: the
;; process printed the ACL2 prompt and waited on stdin (native-subsets
;; 47bdb9a4, failure 5).  A start the image cannot make is a refusal of this
;; invocation: its reason on stderr and exit 5, never a prompt.
(defun fnn-native-startup (checks)
  (handler-case (funcall checks)
    (serious-condition (e)
      (fnn-open-streams)
      (fnn-err "fn-host: error: refused start: ~a" e)
      (fnn-exit +fnn-exit-usage+))))

;; The ACL2-visible entry that host/native/build.lisp defines in :program
;; mode is redefined here in raw Lisp, so that save-exec's :return-from-lp
;; form (fn-native-entry state) reaches fnn-main.
(defun fn-native-entry (st)
  (declare (ignore st))
  (fnn-main)
  (values nil :exited *the-live-state*))
