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
;;; code (specs/host.md "CLI exit codes", HST-009).  The numbers are ACL2's:
;;; each constant is the fn-wide map's code for its class
;;; (books/outcome-class.lisp fn-outcome-code, PRF-143), read once when the
;;; image is built, which is after every book is included (host/native/
;;; build.lisp).  The host writes no exit number of its own.

(defconstant +fnn-exit-ok+ (fn-outcome-code :accepted))
(defconstant +fnn-exit-refused+ (fn-outcome-code :refused))
(defconstant +fnn-exit-uncertain+ (fn-outcome-code :fenced))
(defconstant +fnn-exit-fault+ (fn-outcome-code :fault))
(defconstant +fnn-exit-usage+ (fn-outcome-code :usage))

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
;; A Store open ACL2 refused by name (books/store-open-pre-c1.lisp): a
;; refusal (exit 1) that recovery passes through unchanged, never the
;; generic "cannot reconstruct committed history" fault.
(define-condition fnn-store-open-refusal (fnn-store-error) ())
;; The open's named refusal of a saved profile (PKT-471, D34,
;; books/store-profile-open.lisp): a profile the poll reply cannot carry, or a
;; store of another format; the line names the reinstall and import.
(define-condition fnn-store-profile-refusal (fnn-store-open-refusal) ())

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
  "ACL2's code for the condition that ended a command: the host names the
condition's type (an observation) and books/outcome-class.lisp
fn-outcome-host-condition-exit-code classifies it (PRF-143,
fn-outcome-host-condition-fences-iff-indeterminate).  It runs in handlers,
so it calls the guard-t function directly rather than through fnn-core,
whose own failure would raise a new condition here."
  (fn-outcome-host-condition-exit-code
   (typecase condition
     (fnn-store-indeterminate :indeterminate)
     (fnn-store-fault :fault)
     (fnn-usage-error :usage)
     (fnn-store-error :refusal)
     (t :fault))))

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
;;; The octet buffer (books/octets-stobj.lisp, D27 boundary 6).  `fn-octets'
;;; is an abstract stobj whose logical value is an octet list and whose
;;; executable is a resizable byte array with a fill count; the live object
;;; is the state's user-stobj-alist entry, a two-slot vector (the array, the
;;; count).  `fnn-octets-fill' is the host boundary of that book: one
;;; `replace' of a byte vector into the array, then the count, so the core
;;; reads the bytes in place and no list is built.  It stands at the same
;;; trust as `fnn-octet-list' handing a list to the core (A-HOST): the host
;;; asserts the buffer's logical value is the list of the bytes it wrote,
;;; and nothing else reaches the array.  One buffer, one owner thread: the
;;; served attempt fills it and reads it under the service mutex
;;; (host/native/owner.lisp fnn-owner-attempt).

(defvar *fnn-octets* nil)

(defun fnn-live-octets ()
  (or *fnn-octets*
      (setq *fnn-octets*
            (or (cdr (assoc 'fn-octets (user-stobj-alist *the-live-state*)))
                (fnn-fault "the octet buffer stobj is not in this image")))))

(defun fnn-octets-fill (vector)
  "Make VECTOR's bytes the buffer's contents; return the live stobj."
  (let* ((st (fnn-live-octets)) (n (length vector)))
    (fn-octets$c-reserve n st)
    (replace (the fnn-octets (svref st 0)) vector)
    (setf (svref st 1) n)
    st))

(defun fnn-octets-clear ()
  "Empty the buffer (the fill count to 0; the array is kept)."
  (setf (svref (fnn-live-octets) 1) 0))

;;; The PUBLICATION buffer: `fn-octets-pub' (books/owner-checkpoint-stream.lisp),
;;; a second abstract stobj congruent to `fn-octets' with its own live
;;; object.  The owner's checkpoint thread (host/native/owner.lisp
;;; fnn-owner-publish-captured) runs OFF the service mutex and encodes the
;;; checkpoint into this one; the served attempt's buffer above is never
;;; touched off the mutex.  One buffer, one thread, per buffer.

(defvar *fnn-octets-pub* nil)

(defun fnn-live-octets-pub ()
  (or *fnn-octets-pub*
      (setq *fnn-octets-pub*
            (or (cdr (assoc 'fn-octets-pub (user-stobj-alist *the-live-state*)))
                (fnn-fault "the publication buffer stobj is not in this image")))))

(defun fnn-octets-release ()
  "Empty the buffer and give its array back: after the state checkpoint's
load the array holds the whole file, which the served attempts (one request
each) never need again; they regrow it to one request's size.  A bound on
retained memory only (the logical value, the empty list, is unchanged by the
array's size); it decides nothing ACL2 decides."
  (let ((st (fnn-live-octets)))
    (setf (svref st 1) 0)
    (setf (svref st 0) (make-array 0 :element-type '(unsigned-byte 8)))
    st))

(defun fnn-octets-pub-release ()
  "Empty the publication buffer and give its array back after a checkpoint's
publication (the verb's or the owner's thread): the array grew to the
largest step the publication wrote and nothing needs it until the next
publication, which regrows it (per-record-state PKT-PRS-2: 8.4 MB kept at
10,000 records).  A bound on retained memory only; the logical value, the
empty list, is unchanged, and it decides nothing ACL2 decides."
  (let ((st (fnn-live-octets-pub)))
    (setf (svref st 1) 0)
    (setf (svref st 0) (make-array 0 :element-type '(unsigned-byte 8)))
    st))

(defun fnn-octets-reserve (n)
  "Grow the buffer's array so that N octets fit; contents and count unchanged."
  (fn-octets$c-reserve n (fnn-live-octets)))

(defun fnn-octets-append-vector (vector)
  "Append VECTOR's bytes at the buffer's fill point (the same boundary as
`fnn-octets-fill': the host asserts the cells it wrote hold these bytes);
return the index the bytes begin at."
  (let* ((st (fnn-live-octets)) (fill (svref st 1)) (n (length vector)))
    (fn-octets$c-reserve (+ fill n) st)
    (replace (the fnn-octets (svref st 0)) vector :start1 fill)
    (setf (svref st 1) (+ fill n))
    fill))

;;; The PAYLOAD ARENA (books/payload-arena.lisp; the records flip,
;;; books/store-intern.lisp): `fn-arena' is the abstract stobj whose logical
;;; value is the list of sealed payloads and whose executable is the byte
;;; array books/payload-arena-attach.lisp attached (one byte per payload
;;; octet).  The Store's rows carry handles into it; the live object is the
;;; state's user-stobj-alist entry, found as `fnn-live-octets' finds the
;;; buffer's.  The host never reads or writes it: every call below hands it
;;; to an ACL2 entry (the intern at the open, the POST's seal, the reads by
;;; handle), and one thread owns it, as it owns the Store.

(defvar *fnn-arena* nil)
(defvar *fnn-cat* nil)

(defun fnn-live-arena ()
  (or *fnn-arena*
      (setq *fnn-arena*
            (or (cdr (assoc 'fn-arena (user-stobj-alist *the-live-state*)))
                (fnn-fault "the payload arena stobj is not in this image")))))

;;; The trailing stobjs of a state-returning entry: the live payload arena
;;; and catalog (books/payload-arena.lisp fn-arena, books/catalog.lisp fn-cat)
;;; when the entry's STOBJS-IN end in (fn-arena state) or (fn-arena fn-cat
;;; state): the served readers read an article's bytes through the arena
;;; (books/nntp-session.lisp fn-nntp-article-bytes; lane served-readers) and
;;; the catalog's served chain and maintenance take both.  Read off the
;;; entry's own STOBJS-IN (a property the image keeps: host/native/
;;; strip-world.lisp), once per name, so a wrapper never carries a list that
;;; could go stale.
(defvar *fnn-trailing-stobjs* (make-hash-table :test 'eq))

(defun fnn-live-cat ()
  (or *fnn-cat*
      (setq *fnn-cat*
            (or (cdr (assoc 'fn-cat (user-stobj-alist *the-live-state*)))
                (fnn-fault "the catalog stobj is not in this image")))))

(defun fnn-trailing-kind (name)
  (multiple-value-bind (known found) (gethash name *fnn-trailing-stobjs*)
    (if found
        known
      (setf (gethash name *fnn-trailing-stobjs*)
            (let ((ins (stobjs-in name (w *the-live-state*))))
              (cond ((and (>= (length ins) 3) (eq (car (last ins)) 'state)
                          (eq (car (last ins 2)) 'fn-cat)
                          (eq (car (last ins 3)) 'fn-arena))
                     :arena-cat)
                    ((and (>= (length ins) 2) (eq (car (last ins)) 'state)
                          (eq (car (last ins 2)) 'fn-arena))
                     :arena)
                    (t nil)))))))

(defun fnn-arena-then-state (name)
  "The trailing stobj arguments of the state-returning entry NAME."
  (case (fnn-trailing-kind name)
    (:arena-cat (list (fnn-live-arena) (fnn-live-cat) *the-live-state*))
    (:arena (list (fnn-live-arena) *the-live-state*))
    (t (list *the-live-state*))))

(defun fnn-core-arena-state (name &rest args)
  "A wrapper over the arena and state, the live arena passed before state:
its value.  An entry that seals returns (mv erp val fn-arena state) and a
reader (mv erp val state); the arena is updated in place either way."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (list (fnn-live-arena) *the-live-state*)))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

(defun fnn-core-buffer-arena-state (name &rest args)
  "A wrapper over the octet buffer, the arena and state (in that order, after
ARGS): its value.  The owner's POST entries read the payload from the buffer
and seal it into the arena (host/owner-host.lisp fn-owner-prepare-buffer)."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (list (fnn-live-octets) (fnn-live-arena)
                                                *the-live-state*)))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

(defun fnn-core-buffer-state (name &rest args)
  "A `state`-returning wrapper over the buffer, (mv erp value state) with the
live buffer passed before state: its value."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (cons (fnn-live-octets) (fnn-arena-then-state name))))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

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

(defun fnn-write-range (fd data start end)
  "fnn-write-all of the byte vector DATA's cells START..END, in place."
  (let ((offset start))
    (loop while (< offset end) do
      (let ((remaining (- end offset)))
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

(defun fnn-read-bounded-fd (fd maximum &optional size)
  "Read at most MAXIMUM octets from one already validated descriptor.
SIZE, the descriptor's fstat size when the caller has it, sizes the first
read's buffer exactly and the next read is a one-octet probe for end of file,
so a file that did not change is read into one vector with no copy; the reads
still go to end of file, and past MAXIMUM is refused whatever SIZE said."
  (let ((chunks nil) (remaining (+ maximum 1)) (total 0)
        (next (if (and size (> size 0)) size 65536)))
    (loop while (> remaining 0) do
      (let* ((buffer (fnn-make-octets (min next remaining)))
             (count (fnn-read-fd fd buffer)))
        (when (zerop count) (return))
        (push (if (= count (length buffer)) buffer (subseq buffer 0 count)) chunks)
        (incf total count)
        (decf remaining count)
        ;; After the hinted read, one octet asks whether the file ended.
        (setq next (if (and size (= total size)) 1 65536))))
    (when (> total maximum)
      (fnn-overbound "file exceeds ACL2-owned bound"))
    (if (and chunks (null (cdr chunks)))
        (car chunks)
        (let ((data (fnn-make-octets total)) (at 0))
          (dolist (chunk (nreverse chunks))
            (replace data chunk :start1 at)
            (incf at (length chunk)))
          data))))

(defun fnn-read-regular-bounded (path maximum)
  "Read one regular, non-symlink file through a no-follow descriptor."
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (unwind-protect
         (let ((info (fnn-fstat fd)))
           (unless (fnn-regular-p info)
             (fnn-fault "refusing non-regular store file: ~a" path))
           (when (> (sb-posix:stat-size info) maximum)
             (fnn-overbound "store file exceeds bound: ~a" path))
           (fnn-read-bounded-fd fd maximum (sb-posix:stat-size info)))
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

;;; The state behind every staged name's random suffix, seeded from the OS's
;;; entropy (`seed-random-state t': /dev/urandom) by the first draw of each
;;; process.  A saved image must not carry it: a state seeded while the image
;;; was built gave every process of that image the same sequence, so `init'
;;; and `import', whose stage names carry no PID, staged under the same
;;; ROOT.init-77b60431a1de in every run (PKT-819).  The save hook drops it
;;; before `save-lisp-and-die'; a restarted image seeds its own.
(defvar *fnn-random-state* nil)
(defvar *fnn-random-state-lock* (sb-thread:make-mutex :name "fn native random state"))

(defun fnn-random-state ()
  (or *fnn-random-state*
      (sb-thread:with-mutex (*fnn-random-state-lock*)
        (or *fnn-random-state*
            (setq *fnn-random-state* (sb-ext:seed-random-state t))))))

(defun fnn-random-state-forget ()
  (setq *fnn-random-state* nil))
(pushnew 'fnn-random-state-forget sb-ext:*save-hooks*)

(defun fnn-random-hex (octets)
  (format nil "~(~v,'0x~)" (* 2 octets) (random (ash 1 (* 8 octets)) (fnn-random-state))))

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

;;; PKT-712: a report piped to `head' (or any reader that leaves early).
;;; SIGPIPE is ignored (fnn-main), so a write to a closed stdout raises
;;; EPIPE as a stream error inside whatever verb is printing, which printed
;;; `fault operator health Couldn't write to ...' or, at the exit's final
;;; flush outside every handler, SBCL's BROKEN-PIPE backtrace.  Standard
;;; output is therefore one stream that cannot fail: the first error on it
;;; marks it lost and every later write is dropped, so the verb finishes what
;;; it was doing (a report's reader leaving changes nothing the node does)
;;; and the process exits quietly: with the verb's own code when that is not
;;; 0, else 141, the shell's code for a writer ended by SIGPIPE, so a lost
;;; report is never reported as a success (fnn-exit).
(defvar *fnn-stdout-lost* nil)

(defclass fnn-stdout-stream (sb-gray:fundamental-binary-output-stream)
  ((target :initarg :target :reader fnn-stdout-target)))

(defmacro fnn-stdout-guard (stream &body body)
  `(unless *fnn-stdout-lost*
     (handler-case (progn ,@body)
       (stream-error ()
         (setq *fnn-stdout-lost* t)
         ;; Drop what the fd-stream still buffers, so no later flush
         ;; raises the same error again.
         (ignore-errors (clear-output (fnn-stdout-target ,stream)))))))

(defmethod stream-element-type ((stream fnn-stdout-stream))
  '(unsigned-byte 8))

(defmethod sb-gray:stream-write-byte ((stream fnn-stdout-stream) byte)
  (fnn-stdout-guard stream (write-byte byte (fnn-stdout-target stream)))
  byte)

(defmethod sb-gray:stream-write-sequence ((stream fnn-stdout-stream) sequence
                                          &optional (start 0) end)
  (fnn-stdout-guard stream
    (write-sequence sequence (fnn-stdout-target stream) :start start :end end))
  sequence)

(defmethod sb-gray:stream-finish-output ((stream fnn-stdout-stream))
  (fnn-stdout-guard stream (finish-output (fnn-stdout-target stream)))
  nil)

(defmethod sb-gray:stream-force-output ((stream fnn-stdout-stream))
  (fnn-stdout-guard stream (force-output (fnn-stdout-target stream)))
  nil)

(defun fnn-open-streams ()
  (setq *fnn-stdout*
        (make-instance 'fnn-stdout-stream
                       :target (sb-sys:make-fd-stream 1 :output t
                                                        :element-type '(unsigned-byte 8)
                                                        :buffering :full)))
  (setq *fnn-stderr* (sb-sys:make-fd-stream 2 :output t :element-type '(unsigned-byte 8)
                                              :buffering :full)))

(defun fnn-emit (stream text)
  (write-sequence (fnn-string-octets text) stream)
  (finish-output stream))

(defun fnn-out (control &rest args)
  (fnn-emit *fnn-stdout* (fnn-concat (apply #'format nil control args) (string #\Newline))))

(defun fnn-err (control &rest args)
  ;; PKT-508: while the owner's log writer runs, a diagnostic is offered to
  ;; its queue like a log line (fnn-log-offer), so a serving thread never
  ;; blocks on stderr; otherwise (every offline command) it is written here.
  (let ((text (fnn-concat (apply #'format nil control args) (string #\Newline))))
    (unless (fnn-log-offer :stderr (fnn-string-octets text))
      (fnn-emit *fnn-stderr* text))))
;;; The service log.  `fn operator CONFIG run' opens `[log] path' append-only
;;; before the store (host/native/operator.lisp) and leaves its descriptor
;;; here; NIL means stderr.  Every line is ACL2's (books/owner-log.lisp); this
;;; writes its octets and one LF and decides nothing.  A failed write is
;;; reported on stderr and stops nothing: the log is an operator's record,
;;; never evidence of durable acceptance.
(defvar *fnn-owner-log-fd* nil)
;;; PKT-101: the `[log] path' the run opened (NIL for stderr), the SIGHUP
;;; count the signal handler advances (the handler does nothing else), and
;;; the mutex under which a line is written and the descriptor is swapped,
;;; so a line goes whole to the old file or whole to the new one.
(defvar *fnn-owner-log-path* nil)
(defvar *fnn-sighup-count* 0)
(defvar *fnn-owner-log-mutex* (sb-thread:make-mutex :name "fn service log"))

(defun fnn-csprng-octets (width what)
  "Exactly WIDTH octets from the OS CSPRNG as an octet list; short or failed
entropy is a host fault.  WIDTH is ACL2's."
  (unless (and (integerp width) (< 0 width))
    (fnn-fault "ACL2 returned an invalid ~a width" what))
  (let ((fd (fnn-open "/dev/urandom" sb-posix:o-rdonly))
        (answer (fnn-make-octets width))
        (offset 0))
    (unwind-protect
         (progn
           (loop while (< offset width) do
             (let* ((chunk (fnn-make-octets (- width offset)))
                    (count (fnn-read-fd fd chunk)))
               (when (zerop count)
                 (fnn-fault "OS CSPRNG ended before one ~a" what))
               (replace answer chunk :start1 offset :end2 count)
               (incf offset count)))
           (fnn-octet-list answer))
      (fnn-close fd))))

;;; PKT-508 (PRF-187): the served path never waits on the log.  While the
;;; owner runs (host/native/operator.lisp starts and stops the writer around
;;; `fnn-control-owner-run-normalized'), a line or diagnostic is OFFERED:
;;; ACL2 decides :queue or :drop over the sink it returns
;;; (books/log-sink.lisp fn-log-sink-offer, counted, never silent: `health'
;;; prints `log-sink pending= dropped= written='), and the thread that
;;; decided it returns.  One writer thread (`fnn-log-writer-loop') takes the
;;; queue's head and writes it whole with blocking writes, holding no owner
;;; lock and not the queue mutex, and reports the outcome back
;;; (fn-log-sink-take).  The queue mutex is held only for an ACL2 call and a
;;; list update, never across I/O, so a sink that stops draining costs the
;;; serving threads nothing: its backlog stops at ACL2's bound and later lines
;;; are dropped and counted.  `[log] path' reopen (SIGHUP) swaps the
;;; descriptor through the same queue, in order.
(defvar *fnn-log-queue-mutex* (sb-thread:make-mutex :name "fn log queue"))
(defvar *fnn-log-queue-ready* (sb-thread:make-waitqueue :name "fn log queue ready"))
;; FIFO of (DESTINATION . OCTETS), DESTINATION :log or :stderr; (:swap . FD);
;; (:stop).  Read and written under the queue mutex only.
(defvar *fnn-log-queue-head* nil)
(defvar *fnn-log-queue-tail* nil)
;; ACL2's sink (PENDING-OCTETS PENDING-LINES DROPPED WRITTEN OFFERED), NIL
;; when no writer runs.
(defvar *fnn-log-sink* nil)
(defvar *fnn-log-writer* nil)

(defun fnn-log-queue-push (item)
  "Append ITEM; the caller holds the queue mutex."
  (let ((cell (list item)))
    (if *fnn-log-queue-tail*
        (setf (cdr *fnn-log-queue-tail*) cell)
        (setq *fnn-log-queue-head* cell))
    (setq *fnn-log-queue-tail* cell)
    (sb-thread:condition-notify *fnn-log-queue-ready*)))

(defun fnn-log-sink-accept (sink what)
  (unless (and (listp sink) (= (length sink) 5)
               (every (lambda (n) (and (integerp n) (<= 0 n))) sink))
    (fnn-fault "ACL2 returned a malformed log sink after ~a" what))
  (setq *fnn-log-sink* sink))

(defun fnn-log-offer (destination octets)
  "Offer one whole line.  NIL when no writer runs (the caller writes it);
otherwise T, the line queued or dropped as ACL2 decided."
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (when *fnn-log-writer*
      (let ((answer (fnn-core 'fn-log-sink-offer *fnn-log-sink* (length octets)
                              (fnn-core 'fn-log-sink-pending-bound))))
        (unless (and (consp answer) (member (first answer) '(:queue :drop)))
          (fnn-fault "ACL2 returned a malformed log sink decision"))
        (fnn-log-sink-accept (second answer) "an offer")
        (when (eq (first answer) :queue)
          (fnn-log-queue-push (cons destination octets)))
        t))))

(defun fnn-log-sink-snapshot ()
  "The sink ACL2 last returned, for `health' (fn-nh-log-sink-line); NIL when
no writer runs."
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    *fnn-log-sink*))

(defun fnn-log-write-item (destination octets)
  "Write one whole line: :written, or :failed (ACL2 counts it dropped)."
  (handler-case
      (cond ((and (eq destination :log) *fnn-owner-log-fd*)
             (fnn-write-all *fnn-owner-log-fd* octets)
             :written)
            (*fnn-stderr*
             (write-sequence octets *fnn-stderr*)
             (finish-output *fnn-stderr*)
             :written)
            (t :failed))
    (error () :failed)))

(defun fnn-log-writer-loop ()
  (loop
    (let ((item (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                  (loop until *fnn-log-queue-head*
                        do (sb-thread:condition-wait *fnn-log-queue-ready*
                                                     *fnn-log-queue-mutex*))
                  (prog1 (pop *fnn-log-queue-head*)
                    (unless *fnn-log-queue-head*
                      (setq *fnn-log-queue-tail* nil))))))
      (case (car item)
        (:stop (return))
        (:swap
         ;; Only this thread writes the descriptor while it runs.
         (let ((old *fnn-owner-log-fd*))
           (setq *fnn-owner-log-fd* (cdr item))
           (when old (ignore-errors (fnn-close old)))))
        (t
         (let ((outcome (fnn-log-write-item (car item) (cdr item))))
           (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
             (fnn-log-sink-accept
              (fnn-core 'fn-log-sink-take *fnn-log-sink* (length (cdr item)) outcome)
              "a write"))))))))

(defun fnn-log-writer-start ()
  "Start the owner's log writer with ACL2's empty sink (fn-log-sink-init)."
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (unless *fnn-log-writer*
      (fnn-log-sink-accept (fnn-core 'fn-log-sink-init) "init")
      (setq *fnn-log-queue-head* nil
            *fnn-log-queue-tail* nil
            *fnn-log-writer*
            (sb-thread:make-thread #'fnn-log-writer-loop
                                   :name "fn service log writer")))))

(defun fnn-log-writer-stop ()
  "Ask the writer to drain and stop, and wait for it at most ACL2's
fn-log-sink-close-wait-seconds.  A writer still blocked on its sink then is
left running (lines keep being offered and dropped, never waited on) and the
process exits without it: what it had queued, a wedged sink would lose
anyway."
  (let ((thread (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
                  (when *fnn-log-writer*
                    (fnn-log-queue-push (list :stop))
                    *fnn-log-writer*))))
    (when thread
      (multiple-value-bind (value outcome)
          (sb-thread:join-thread thread
                                 :timeout (fnn-core 'fn-log-sink-close-wait-seconds)
                                 :default :timeout)
        (declare (ignore value))
        (unless (eq outcome :timeout)
          (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
            (setq *fnn-log-writer* nil
                  *fnn-log-queue-head* nil
                  *fnn-log-queue-tail* nil)))))))

(defun fnn-log-swap-fd (fd)
  "Install FD as the service log: through the writer's queue while it runs
(in order after the lines before it), else under the log mutex."
  (unless (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
            (when *fnn-log-writer*
              (fnn-log-queue-push (cons :swap fd))
              t))
    (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
      (let ((old *fnn-owner-log-fd*))
        (setq *fnn-owner-log-fd* fd)
        (when old (ignore-errors (fnn-close old)))))))

(defun fnn-log-line (line)
  "Write the ACL2-rendered octet list LINE and one LF to the service log:
offered to the writer while the owner runs (PKT-508), else written here."
  (unless (fnn-octet-list-p line)
    (fnn-fault "ACL2 returned a malformed log line"))
  (let ((octets (concatenate 'fnn-octets (fnn-octets line) (fnn-octets (list 10)))))
    (unless (fnn-log-offer :log octets)
      (sb-thread:with-recursive-lock (*fnn-owner-log-mutex*)
        (if *fnn-owner-log-fd*
            (handler-case (fnn-write-all *fnn-owner-log-fd* octets)
              (error (condition)
                (fnn-err "service log write failed: ~a" condition)))
          (when *fnn-stderr*
            (write-sequence octets *fnn-stderr*)
            (finish-output *fnn-stderr*)))))))

(defun fnn-exit (code)
  (when *fnn-stdout* (finish-output *fnn-stdout*))
  (when *fnn-stderr* (ignore-errors (finish-output *fnn-stderr*)))
  (ignore-errors (finish-output *standard-output*))
  ;; PKT-712: a report whose reader left is never a success.
  (sb-ext:exit :code (if (and *fnn-stdout-lost* (eql code 0)) 141 code)
               :abort t))

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
      (apply #'fnn-call name (append args (fnn-arena-then-state name)))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

(defun fnn-global (name)
  (f-get-global name *the-live-state*))

(defvar *fnn-pack-memo-depth* 0)
(defmacro fnn-with-pack-memo (&body body)
  "Run BODY with ACL2's pack-link memo scope open (host/checkpoint-host.lisp
`fn-store-pack-memo-scope', books/checkpoint-pack-chain-once.lisp): each
chain link BODY walks is decoded once; the memo is dropped when the outermost
scope ends, however it ends."
  `(progn
     (when (= *fnn-pack-memo-depth* 0) (fnn-core-state 'fn-store-pack-memo-scope t))
     (let ((*fnn-pack-memo-depth* (1+ *fnn-pack-memo-depth*)))
       (unwind-protect (progn ,@body)
         (when (= *fnn-pack-memo-depth* 1)
           (fnn-core-state 'fn-store-pack-memo-scope nil))))))

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
  "ACL2's decoded store profile: a format-9 profile (the one format, D34).  The host keeps the value opaque and
reads every field through an ACL2 accessor.  The verdict is ACL2's open
(books/store-profile-open.lisp fn-spo-config-open): a saved profile whose
record bound the poll reply cannot carry, a profile frame of another
format, or a fn-store-8 profile frame of another release's layout (PKT-705:
`reason=older-release' / `newer-release', naming both field counts) is
refused by name, exit 1, with ACL2's line (PKT-471, D34); a frame that is no
saved profile stays a fault."
  (let ((verdict (fnn-core 'fn-store-metadata-config-open
                           (fnn-octet-list octets))))
    (cond ((and (consp verdict) (eq (first verdict) :opened)
                (fnn-core 'fn-store-profile-admittedp (second verdict)))
           (second verdict))
          ((and (consp verdict) (eq (first verdict) :refused))
           (let ((text (fnn-core 'fn-store-metadata-config-refusal-text verdict)))
             (unless (stringp text)
               (fnn-fault "ACL2 refused the store profile without naming a reason"))
             (error 'fnn-store-profile-refusal :message text)))
          ((equal verdict '(:rejected))
           (fnn-fault "ACL2 rejected durable configuration frame"))
          (t (fnn-fault "ACL2 returned a malformed profile open verdict")))))

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
(defun fnn-bridge-recover (next-chunk frontier config-records)
  "Replay the configuration history and then the article history.

The core replays `config-records' with the article records through
`fn-cpr-replay', takes the allocation domain and the capacity from the
configured node, and opens the observed store through `fn-cpo-open-observed'
(host/store-node-host.lisp `fn-store-sn-recover-rows'); a store with no
configuration record never reaches here.

The history goes over in CHUNKS (PKT-823; books/store-recover-stream.lisp).
NEXT-CHUNK answers ACL2's decode of the next chunk, or :END: the file reader
(`fnn-recover-file-chunks') answers `fn-srs-checked-decode' of a numbered
chunk, the pack path (`fnn-recover-record-chunks') `fn-store-decode-records'
(`fn-srs-decode') of a chunk of records already checked.  Per chunk the
guard-verified `fn-srs-intern-step' interns it into the arena, accumulating
the rows; the arena is cleared first and updated only by those direct calls,
so no :program entry updates it (invariant-risk: flip-L6-2).  KEYSTONES
fn-srs-steps-are-one-step-of-the-concatenation (every chunking gives the rows
and arena one step over the whole history gives) and
fn-srs-checked-step-is-the-step (a numbered chunk's two calls are the step
over its records).  The host supplies octets, passes ACL2's values back
unread, and decides nothing about them.

A chunk source over a format-9 log's full replay answers, as second and
third values, the chunk's records and, per record, its log entry's (FILE
START N TRAILER) (fnn-log-scan-segments): then the chunk goes to
`fn-arx-intern-step' (books/payload-extent.lisp), and a record whose entry
holds its payload is sealed as an EXTENT, no octets on the heap (PRF-281;
KEYSTONE fn-arx-intern-step-refines: the same rows and arena as
fn-srs-intern-step when each record's octets are its entry's durable octets,
A-DURABLE-EXTENT)."
  (let ((configs (mapcar #'fnn-octet-list config-records))
        (arena (fnn-live-arena))
        (acc nil))
    (fnn-call 'fn-arena-clear arena)
    (loop
      (multiple-value-bind (decoded chunk places) (funcall next-chunk)
        (when (eq decoded :end) (return))
        (when (eq decoded :sequence)
          (fnn-fault "record sequence does not match immutable filename"))
        (setq acc (first (if (some #'identity places)
                             (fnn-call 'fn-arx-intern-step acc decoded chunk places arena)
                           (fnn-call 'fn-srs-intern-step acc decoded arena))))
        (when (eq acc :bad)
          (return-from fnn-bridge-recover :fault))))
    (fnn-action (fnn-core-state 'fn-store-sn-recover-rows
                                (fnn-core 'fn-srs-rows acc) frontier configs))))

(defun fnn-recover-record-chunks (records &optional positions)
  "A chunk source over RECORDS (octet vectors, or octet lists: the log
kernel's committed records, taken as they are; checked already): each call
converts the next chunk to octet lists and answers ACL2's decode of it; a
chunk closes where ACL2 says (`fn-srs-chunk-fullp', a work quantum: one
record is always taken first, so no record is refused or split for its size).
With POSITIONS (per record its log entry's place, fnn-log-scan-segments) it
also answers the chunk and its places (fnn-bridge-recover seals extents)."
  (lambda ()
    (if (null records)
        :end
        (let ((chunk nil) (places nil) (octets 0))
          (loop while (and records (not (fnn-core 'fn-srs-chunk-fullp octets))) do
            (let ((record (pop records)))
              (incf octets (length record))
              (push (pop positions) places)
              (push (fnn-octet-list record) chunk)))
          (let ((chunk (nreverse chunk)))
            (values (fnn-core 'fn-store-decode-records chunk) chunk (nreverse places)))))))

(defun fnn-bridge-config-observation-limit (store)
  "The config reader consumes an ACL2-owned bound before readdir retains names:
the operator's max-config-generations of the profile STORE opened."
  (let ((value (fnn-core 'fn-store-config-observation-limit
                         (fnn-store-config store))))
    (unless (and (integerp value) (> value 0))
      (fnn-fault "ACL2 returned a malformed configuration generation bound"))
    value))

(defun fnn-bridge-config-observation (observed limit &optional initializing)
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
                            observed)
                    limit)))
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

(defun fnn-seal-octets (octets)
  "The arena update a prepare names: seal OCTETS (the octet list the core
answered with) through the guard-verified `fn-arena-seal-list'
(books/payload-arena.lisp).  The core entries only READ the arena: an entry
that also sealed would carry ACL2's invariant-risk and run through its *1*
body, checking every callee's guard (the whole history, per POST)."
  (fnn-call 'fn-arena-seal-list octets (fnn-live-arena))
  t)

(defun fnn-seal-live-buffer ()
  "The arena update the owner's buffer prepare names (:seal-buffer): seal the
octet buffer's payload through the guard-verified `fn-arena-seal-buffer'
(books/payload-arena.lisp); see FNN-SEAL-OCTETS."
  (fnn-call 'fn-arena-seal-buffer (fnn-live-octets) (fnn-live-arena))
  t)

(defun fnn-bridge-prepare (msgid payload codes obligation subject evidence charge)
  "The standalone POST's prepare: ACL2 decides (fn-store-sn-prepare) and names
the payload to seal as (:seal OCTETS); the host seals exactly those octets
(books/store-prepare-carried.lisp
`fn-store-prepare-interned-carried-is-next-then-seal')."
  (let ((value (fnn-core-arena-state 'fn-store-sn-prepare (fnn-octet-list msgid)
                                     (fnn-octet-list payload)
                                     codes (fnn-octet-list obligation) (fnn-octet-list subject)
                                     (fnn-octet-list evidence) charge
                                     (fnn-store-prepare-observation))))
    (if (and (consp value) (eq (first value) :seal))
        (progn
          (unless (and (consp (rest value)) (null (cddr value))
                       (fnn-octet-list-p (second value)))
            (fnn-fault "ACL2 returned a malformed seal"))
          (fnn-seal-octets (second value))
          :prepared)
      (fnn-action value))))
(defun fnn-bridge-existing-action (msgid payload codes)
  (fnn-action (fnn-core-arena-state 'fn-store-sn-existing-action (fnn-octet-list msgid)
                                    (fnn-octet-list payload) codes)))
(defun fnn-bridge-pending-record ()
  (let ((value (fnn-core-arena-state 'fn-store-sn-pending-octets)))
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
  (lambda (store count) (declare (ignore store count)) '(:none)))
; A selected lossless prefix pack may reconstruct records before the one
; generic decoder/replay call.  Without the optional pack layer this is the
; identity function.
(defvar *fnn-pack-recover-callback*
  (lambda (store records sequences actual-lower)
    (declare (ignore store sequences actual-lower)) records))
(defvar *fnn-pack-lower-bound-callback*
  (lambda (store) (declare (ignore store)) 0))
; True when a selected pack reconstructs the history's prefix, so the open
; reads the history through `fnn-committed-history' (the pack's
; reconstruction and the suffix files) rather than streaming the files.
(defvar *fnn-pack-selected-callback*
  (lambda (store) (declare (ignore store)) nil))
(defvar *fnn-pack-status-callback* nil)

(defun fnn-bridge-article-count () (fnn-nat (fnn-core-state 'fn-store-sn-article-count)))
(defun fnn-bridge-next-txid () (fnn-nat (fnn-core-state 'fn-store-sn-next-txid)))
(defun fnn-bridge-group-next (code) (fnn-nat (fnn-core-state 'fn-store-sn-group-next code)))
(defun fnn-bridge-pin-count () (fnn-nat (fnn-core-state 'fn-store-sn-pin-count)))
(defun fnn-bridge-reserved () (fnn-nat (fnn-core-state 'fn-store-sn-reserved)))
(defun fnn-bridge-lookup (msgid)
  (let ((value (fnn-core-arena-state 'fn-store-sn-lookup (fnn-octet-list msgid))))
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
  ;; PKT-665: the record carries this host's clock (DTN seconds), the
  ;; creation time of every initial group.
  (let ((value (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
                 (fnn-core 'fn-cfg-host-initial-octets-at
                           (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) names)
                           (floor (* (get-internal-real-time) 1000)
                                  (* 1000 internal-time-units-per-second))
                           (if has-wall (floor wall 1000) 0)))))
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

(defun fnn-unframe-list (raw)
  "FNN-UNFRAME answering ACL2's octet list of the record itself: the streaming
open hands it to the step as it is (fnn-recover-file-chunks), so the record is
not made a vector and then a list again.  The file goes over as one octet list
of its protected prefix and the trailer's octets (the frame's trailer size is
ACL2's constant, as fnn-digest-of splits it): ACL2 digests the prefix itself
and answers the payload as the prefix's tail, with no copy
(host/store-host.lisp fn-store-unframe-split, books/store-recover-stream.lisp
KEYSTONE fn-srs-unframe-is-the-frame-decode).  A file shorter than a trailer
goes over whole, as fnn-unframe sends it."
  (let* ((cut (- (length raw) (fnn-constant :trailer)))
         (value (if (< cut 0)
                    (fnn-core 'fn-store-frame-store-decode (fnn-octet-list raw) nil)
                    (fnn-core 'fn-store-unframe-split
                              (loop for i below cut collect (aref raw i))
                              (loop for i from cut below (length raw) collect (aref raw i))))))
    (unless (and (consp value) (eq (first value) :ok))
      (let ((reason (if (and (consp value) (consp (cdr value))) (second value) :unknown)))
        (fnn-fault "frame refused: ~(~a~)" reason)))
    (second value)))

(defun fnn-subject-id (payload)
  "Content identity v1 (books/identity), derived end to end in ACL2.
`books/crypto-attach.lisp' attaches SHA-256 to `fn-frame-digest', so the
preimage AND the digest are ACL2's; this host no longer hashes for identity,
because a second SHA-256 here would be a second owner of the derivation.
Hashing the bare payload is the v0 profile and derives a different identity,
which `fn-store-sn-prepare' then refuses."
  (fnn-as-octets (fnn-core 'fn-store-subject-id-of-payload
                           (fnn-octet-list payload))))

(defun fnn-subject-id-buffer ()
  "FNN-SUBJECT-ID of the payload in the octet buffer, digested in place.
books/sha256-buffer.lisp `fn-shb-subject-id-bounded', guard-verified with
guard T, so the call runs the compiled stobj code and ACL2 raises no
invariant-risk warning on standard output (qual-e747dbcc A4): the subject
preimage's fixed head is a short list and the payload is read from the
buffer by index, so no octet list of the payload is built for the digest
(D27 wave C; the served POST, host/native/owner.lisp fnn-owner-attempt)."
  (fnn-as-octets (fnn-core 'fn-shb-subject-id-bounded (fnn-live-octets))))

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

;;; Lane commit-onto-log: bound to T while the owner runs one batch of
;;; members in one quantum (host/native/owner.lisp fnn-owner-commit-batch):
;;; fnn-publish then puts each member's record into the log's open batch and
;;; leaves the append and the barrier to the batch's end.  NIL everywhere
;;; else: a commit is a batch of one.
(defvar *fnn-log-batch* nil)

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
  ;; D31: the committed-history frame this open writes before it returns
  ;; (fn-hmr-catch-up), or NIL.  Set by fnn-check-history-marker, written by
  ;; fnn-recover after its barriers, only by a writable open.
  (marker-catch-up nil)
  ;; The one scripted fault point, or NIL: tools/run_store.py's ScriptedFaults.
  (fault-point nil) (fault-class nil) (fault-message nil)
  ;; The open answers the history's record COUNT and keeps no records
  ;; (PKT-823); a verb that needs them reads them after the open
  ;; (fnn-history-records).  On format 9 the open records here how the log
  ;; holds the history (fnn-recover-log): (PREFIXP CLOSED GENESIS ACTIVE):
  ;; whether a checkpoint covers dropped segments (the prefix is then its
  ;; rows'), the closed segments scanned and the genesis the scan started
  ;; from, and the active segment's index (fnn-log-history-records).
  (log-history nil)
  ;; Lane commit-onto-log: the commit route ACL2 names from the profile
  ;; (fn-store-profile-logp: format 9) and, on that route, the open record
  ;; log (an fnn-log: the segment's descriptor and the log kernel).
  (logp nil) (log nil))

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
  "Production has no injection branch; a scripted point raises its outcome.
A named CLI fault may arm one point per commit route (a list: the per-file
route's point and the record log's, lane commit-onto-log)."
  (when (let ((armed (fnn-store-fault-point store)))
          (if (consp armed) (member point armed) (eq point armed)))
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
;; The record log's directory and its one segment (format 9).  The name is
;; ACL2's (books/owner-log-route.lisp fn-olr-segment-name).
(defun fnn-journal-dir (s) (fnn-join (fnn-store-root s) "journal"))
(defun fnn-segment-path (s)
  (let ((name (fnn-core 'fn-store-log-segment-name)))
    (unless (and (stringp name) (> (length name) 0) (null (position #\/ name)))
      (fnn-fault "ACL2 returned an invalid log segment name"))
    (fnn-join (fnn-journal-dir s) name)))

(defun fnn-segment-path-at (s k)
  "journal/NAME of segment K (books/store-log-segments.lisp fn-lgs-segment-name)."
  (let ((name (fnn-core 'fn-lgs-segment-name k)))
    (unless (and (stringp name) (> (length name) 0) (null (position #\/ name))
                 (eql (fnn-core 'fn-lgs-segment-index name) k))
      (fnn-fault "ACL2 returned an invalid log segment name"))
    (fnn-join (fnn-journal-dir s) name)))
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
  (let* ((limit (fnn-bridge-config-observation-limit store))
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
    (fnn-bridge-config-observation observed limit initializing)))

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

(defun fnn-store-owner-observation (root)
  "What a non-blocking shared flock sees of ROOT's writer lock: :held (a
process holds it exclusively: a running owner), :free, :absent (no lock
file), or :unknown when the probe itself failed.  An observation only; what
it means for the operator is ACL2's (fn-native-auth-admin-effect-word)."
  (handler-case
      (let ((path (fnn-lock-path (make-fnn-store root))))
        (if (null (fnn-lstat path))
            :absent
            (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+) 0)))
              (unwind-protect
                   (handler-case
                       (progn (fnn-flock fd (logior +fnn-lock-sh+ +fnn-lock-nb+))
                              (fnn-flock fd +fnn-lock-un+)
                              :free)
                     (fnn-os-error (e)
                       (if (= (fnn-os-errno e) sb-posix:ewouldblock) :held :unknown)))
                (fnn-close fd)))))
    (error () :unknown)))

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
    ;; JSON metadata (format 5 and older) is another store format (D34): the
    ;; open refuses it by ACL2's name, and never rewrites it.
    (when (and (> (length raw) 0) (= (aref raw 0) (char-code #\{)))
      (error 'fnn-store-profile-refusal
             :message (fnn-core 'fn-store-metadata-config-refusal-text
                                '(:refused :store-format))))
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

;; The committed-history boundary (books/store-history-marker,
;; books/store-history-required).  The open reads the marker once and ACL2
;; (fn-hmr-open-verdict, under the profile's history-marker requirement)
;; compares it with the length of the record list replay is handed: pack
;; events plus suffix files.
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
  "Refuse an open whose committed history is short of its marker, or whose
required marker is missing; remember the frame the open must write.

A refusal is detected damage to committed data (specs/storage.md STO-005):
a fault naming ACL2's reason, never a silent rollback to the shorter history.
An admitted open records ACL2's catch-up frame (fn-hmr-catch-up): the marker
of the reconstructed count when the marker is absent or behind it, which
fnn-recover writes before the open returns (D31 case 2)."
  (let* ((observation (fnn-history-marker-observation store))
         (verdict (fnn-core 'fn-hmr-open-verdict
                            (fnn-store-config store) observation record-count))
         (word (and (consp verdict) (first verdict))))
    (case word
      (:admitted
       (let ((frame (fnn-core 'fn-hmr-catch-up
                              (fnn-store-config store) observation record-count)))
         (unless (or (null frame) (fnn-octet-list-p frame))
           (fnn-fault "ACL2 returned a malformed committed-history catch-up"))
         (setf (fnn-store-marker-catch-up store) frame))
       verdict)
      (:refused
       (fnn-fault "committed history refused at open: ~(~a~)~@[ marker=~d~] records=~d"
                  (second verdict) (third verdict) record-count))
      (otherwise (fnn-fault "ACL2 returned a malformed committed-history verdict")))))

(defun fnn-mark-committed (store sequence &optional catch-up)
  "Replace the committed-history marker after record SEQUENCE is durable.

With CATCH-UP (ACL2's fn-hmr-catch-up frame, SEQUENCE NIL) it is fnn-recover's
catch-up: the same program and cuts, run after the recovery barriers made the
reconstructed records durable and before the open returns.

Every caller runs this after fnn-publish returned :durable and before
fnn-finish, so a record the node acknowledges is below a durable marker, and
nothing else (a reservation, an abort, a refusal, recovery) writes it.  The
bytes are ACL2's (fn-hm-after-commit); the steps are fn-hm-marker-program's,
and each cut is an `fnn-at' site named in fn-hm-marker-cut-names.  The stage
uses the `.stage-' prefix the recovery sweep collects.  Any OS error is
uncertain: the record is durable and the marker may or may not be replaced,
so the store stays fenced and recovery decides; the transaction is never
acknowledged without its marker."
  ;; A format-9 store has no marker object: M := D, the log's last complete
  ;; entry is the committed history (design 2026-09-27 section 3.4).
  (when (fnn-store-logp store)
    (return-from fnn-mark-committed nil))
  (fnn-require-writer store)
  (let ((frame (or catch-up (fnn-core 'fn-hm-after-commit sequence)))
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
  ;; the core from the operator's group names.  The program is ACL2's by the
  ;; profile's route: format 8 books/byte-store-initializer.lisp
  ;; fn-bsi-current-init-program; format 9 (fn-store-profile-logp)
  ;; books/byte-store-log-initializer.lisp fn-bsi-log-init-program (journal/
  ;; and the segment in place of transactions/ and the allocator file).
  (let ((logp (fnn-core 'fn-store-profile-logp
                        (fnn-metadata-config-decode (fnn-metadata-config-frame profile)))))
    (fnn-safe-directory (fnn-store-root store) t store
                        "init-root-mkdir" "init-root-parent-fenced")
    (fnn-require-clone-activated store)
    (let ((lock-fd (fnn-open-lock store t t)))
      (unwind-protect
           (progn
             (fnn-init-cut store "init-lock-created")
             (unless logp
               (fnn-safe-directory (fnn-transactions store) t store
                                   "init-transactions-mkdir" "init-transactions-parent-fenced"))
             (fnn-safe-directory (fnn-staging store) t store
                                 "init-staging-mkdir" "init-staging-parent-fenced")
             (fnn-safe-directory (fnn-config-dir store) t store
                                 "init-config-dir-mkdir" "init-config-dir-parent-fenced")
             (when logp
               (fnn-safe-directory (fnn-journal-dir store) t store
                                   "init-journal-mkdir" "init-journal-parent-fenced"))
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
             (cond
               (logp
                ;; fn-bsi-log-segment-steps.
                (fnn-log-init-segment store))
               (t
                ;; A missing allocator alongside committed history would permit
                ;; reuse of an aborted ID.  It is a fault, never an implicit 0.
                (when (and (null (fnn-check-regular (fnn-frontier-path store)))
                           (fnn-transaction-files store))
                  (fnn-fault "refusing missing allocator frontier with committed history"))
                (if (eq (fnn-publish-initial-file store (fnn-frontier-path store)
                                                  (fnn-metadata-frontier-frame 0) "init-frontier-")
                        :published)
                    (setf (fnn-store-frontier store) 0)
                    (fnn-load-frontier store))))
             (fnn-fsync-regular (fnn-config-path store))
             (fnn-init-cut store "init-final-config-file-fenced")
             (dolist (name (fnn-config-record-names store :init-config-records-final-enumerate))
               (fnn-fsync-regular (fnn-join (fnn-config-dir store) name))
               ;; The fresh branch has generation 1 only.  Existing history is
               ;; intentionally outside this packet.
               (fnn-init-cut store "init-final-config-record-file-fenced"))
             (unless logp
               (fnn-fsync-regular (fnn-frontier-path store))
               (fnn-init-cut store "init-final-frontier-file-fenced")
               (fnn-fsync-dir (fnn-transactions store))
               (fnn-init-cut store "init-transactions-fenced"))
             (fnn-fsync-dir (fnn-store-root store))
             (fnn-init-cut store "init-root-fenced")
             (fnn-fsync-dir (fnn-parent (fnn-store-root store)))
             (fnn-init-cut store "init-parent-fenced"))
        (ignore-errors (fnn-flock lock-fd +fnn-lock-un+))
        (fnn-close lock-fd)))))

(defun fnn-acquire (store)
  (fnn-safe-directory (fnn-store-root store))
  (fnn-require-clone-activated store)
  ;; PKT-579: the store root is on the filesystem its record names, or the
  ;; open is refused by name before anything else is read.
  (fnn-check-filesystem-identity store)
  (fnn-safe-directory (fnn-staging store))
  (handler-case
      (progn
        (setf (fnn-store-lock-fd store)
              (fnn-open-lock store (fnn-store-writable store) (fnn-store-writable store)))
        (fnn-load-config store)
        ;; The commit route is ACL2's reading of the profile (format 9: the
        ;; record log); the host keeps the answer and decides nothing.
        (setf (fnn-store-logp store)
              (and (fnn-core 'fn-store-profile-logp (fnn-store-config store)) t))
        (cond ((fnn-store-logp store)
               ;; The frontier is derived from the log at recovery
               ;; (fnn-recover-log); there is no frontier file to read.
               (fnn-safe-directory (fnn-journal-dir store)))
              (t
               (fnn-safe-directory (fnn-transactions store))
               (fnn-load-frontier store))))
    (error (e) (fnn-store-close store) (error e))))

(defun fnn-store-close (store)
  (setf (fnn-store-completion-pending store) nil)
  (let ((log (fnn-store-log store)))
    (when log
      (setf (fnn-store-log store) nil)
      (ignore-errors (fnn-close (fnn-log-fd log)))))
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
          ;; ACL2's bound (fn-profile-replay-within-boundp).
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

(defun fnn-state-checkpoint-plan (store)
  "(values :absent NIL), (values :ok PLAN) or (values :refused REASON), REASON
one of :not-regular, :truncated, :header, :exceeds-bound.

One descriptor, consecutive reads: a segment header (37 octets), then ACL2's
admission of that segment against the profile's segment bound and file bound
given the octets read so far (fn-store-sco-segment-admit, books
fn-sccr-admit-segment), then the chunk and the trailer.  Each chunk's bytes
are appended into the live octet buffer in file order and the plan holds, per
segment, (HEADER A B TRAILER): the header and the trailer as octet lists, the
chunk as the buffer's cells A..B, the frames contiguous.  No octet list of
the file is built (rep-wave-d-3): the decoder reads the buffer by index
(books/store-checkpoint-reader.lisp fn-sccr-decode-plan)."
  (let ((path (fnn-state-checkpoint-path store)))
    (unless (fnn-check-regular path)
      (return-from fnn-state-checkpoint-plan (values :absent nil)))
    (let ((header-octets (fnn-core 'fn-store-sco-segment-header-octets))
          (trailer-octets (fnn-core 'fn-store-sco-trailer-octets))
          (profile (fnn-store-config store))
          (fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
          (frames nil) (total 0) (at 0))
      (unless (and (integerp header-octets) (> header-octets 0)
                   (integerp trailer-octets) (> trailer-octets 0))
        (fnn-close fd)
        (fnn-fault "ACL2 returned an invalid checkpoint frame size"))
      (unwind-protect
           (let ((st (fnn-fstat fd)))
             (unless (fnn-regular-p st)
               (return-from fnn-state-checkpoint-plan (values :refused :not-regular)))
             (fnn-octets-clear)
             ;; One allocation for the chunks of the whole file, never past
             ;; what ACL2 would admit.
             (let ((bound (fnn-core 'fn-store-sco-file-read-bound profile)))
               (when (and (integerp bound) (> bound 0))
                 (fnn-octets-reserve (min (max 0 (sb-posix:stat-size st)) bound))))
             (loop
               (let ((first (make-array 1 :element-type '(unsigned-byte 8))))
                 (when (zerop (fnn-read-fd fd first)) (return))
                 (let ((rest (fnn-read-exact-fd fd (1- header-octets))))
                   (unless rest
                     (return-from fnn-state-checkpoint-plan (values :refused :truncated)))
                   (let* ((header (fnn-octet-list
                                   (concatenate '(vector (unsigned-byte 8)) first rest)))
                          (admission (fnn-core 'fn-store-sco-segment-admit
                                               header total profile)))
                     (unless (and (consp admission)
                                  (member (first admission) '(:ok :refused)))
                       (fnn-fault "ACL2 returned a malformed checkpoint segment admission"))
                     (when (eq (first admission) :refused)
                       (return-from fnn-state-checkpoint-plan
                         (values :refused (second admission))))
                     (let ((extent (second admission)) (chunk-octets (third admission)))
                       (unless (and (integerp extent) (integerp chunk-octets)
                                    (>= chunk-octets 0)
                                    (= extent (+ header-octets chunk-octets trailer-octets)))
                         (fnn-fault "ACL2 returned a malformed checkpoint segment extent"))
                       (let ((chunk (fnn-read-exact-fd fd chunk-octets)))
                         (unless chunk
                           (return-from fnn-state-checkpoint-plan (values :refused :truncated)))
                         (let ((trailer (fnn-read-exact-fd fd trailer-octets)))
                           (unless trailer
                             (return-from fnn-state-checkpoint-plan
                               (values :refused :truncated)))
                           (let ((a (fnn-octets-append-vector chunk)))
                             (unless (= a at)
                               (fnn-fault "the octet buffer moved under the checkpoint reader"))
                             (push (list header a (+ a chunk-octets) (fnn-octet-list trailer))
                                   frames)
                             (incf at chunk-octets)
                             (incf total extent)))))))))
             (values :ok (nreverse frames)))
        (fnn-close fd)))))

(defun fnn-state-checkpoint-load (store)
  "Decode the checkpoint into ACL2's global: (values STATUS S) with STATUS
:absent, :refused, :exceeds-bound, :schema (a file of another schema, D34:
the journal replays, `status' says reason=checkpoint-schema), :arena (a file
without the arena run: reason=checkpoint-arena) or :ok, the vocabulary of
fn-scka-select-named."
  (multiple-value-bind (status value)
      (handler-case (fnn-state-checkpoint-plan store)
        (fnn-os-error () (values :refused :io)))
    (case status
      (:absent (fnn-core-state 'fn-store-sco-clear) (values :absent 0))
      (:refused (fnn-core-state 'fn-store-sco-clear)
       (values (case value (:exceeds-bound :exceeds-bound) (:schema :schema) (t :refused)) 0))
      (t (let ((answer (fnn-core-buffer-state 'fn-store-sco-decode value)))
           (if (and (consp answer) (eq (first answer) :arena) (= (length answer) 4)
                    (every (lambda (x) (and (integerp x) (>= x 0))) (rest answer)))
               (fnn-state-checkpoint-load-arena (second answer) (third answer)
                                                (fourth answer))
               ;; A file without the arena run (tables-only, written before
               ;; the flip) is refused by name: reason=checkpoint-arena.
               (values (if (equal answer '(:refused :arena)) :arena :refused) 0)))))))

(defconstant +fnn-checkpoint-load-batch-payloads+ 1024
  "Payloads sealed into the arena per call while a state checkpoint loads
(fn-scka-seal-n): a work bound per call, never a bound on the store; the
arena is the same at every value (fn-scka-seal-n-compose).")

(defun fnn-state-checkpoint-load-arena (start end count)
  "The checkpoint's arena run is verified (fn-store-sco-decode answered
(:arena START END COUNT)): empty the arena, seal the COUNT payloads of the
buffer's [START, END) through the guard-verified fn-scka-seal-n a bounded
number per call, then read the four tables (fn-store-sco-decode-finish).
The three calls are fn-scka-load (books/store-checkpoint-arena-load.lisp,
KEYSTONE fn-scka-load-of-written-file).  No :program entry updates the
arena (invariant-risk; host/store-node-host.lisp fn-store-sco-decode's note).
A refusal leaves a partial arena that nothing reads: the full replay
empties it first (fnn-bridge-recover)."
  (let ((arena (fnn-live-arena)) (octets (fnn-live-octets)) (i start) (left count))
    (fnn-call 'fn-arena-clear arena)
    (loop while (> left 0) do
      (let* ((k (min left +fnn-checkpoint-load-batch-payloads+))
             (answer (fnn-call 'fn-scka-seal-n i end k octets arena)))
        (unless (and (consp answer) (first answer) (integerp (second answer)))
          (fnn-core-state 'fn-store-sco-clear)
          (fnn-octets-release)
          (return-from fnn-state-checkpoint-load-arena (values :refused 0)))
        (setq i (second answer))
        (decf left k)))
    (let ((answer (fnn-core-buffer-state 'fn-store-sco-decode-finish i end)))
      ;; The file is read; the buffer's array (the whole file) is given back.
      (fnn-octets-release)
      (if (and (consp answer) (eq (first answer) :ok)
               (integerp (second answer)) (>= (second answer) 0))
          (values :ok (second answer))
          (values :refused 0)))))

(defun fnn-recover-file-chunks (store files)
  "A chunk source over the transaction FILES ((sequence . path) ...): each call
reads the next chunk's files, unframes each (fnn-unframe-list), checks the
aggregate against ACL2's replay bound as it goes, and answers ACL2's
`fn-srs-checked-decode' of the numbered chunk ((SEQUENCE . RECORD) ...): the
chunk's decode, or :sequence when a record's sequence is not its file's
number (KEYSTONE fn-srs-checked-decode-is-the-per-file-check: the per-file
check `fnn-durable-records' makes, in the one decode).  One bounded read per
file, at the persisted profile's record ceiling plus the frame overhead
(host/store-host.lisp `fn-store-profile-read-bound').  Only the chunk being
decoded is in memory: the files are read as the replay takes them."
  (let ((aggregate 0)
        (bound (fnn-core 'fn-store-profile-read-bound (fnn-store-config store))))
    (lambda ()
      (if (null files)
          :end
          (let ((chunk nil) (octets 0))
            (loop while (and files (not (fnn-core 'fn-srs-chunk-fullp octets))) do
              (destructuring-bind (sequence . path) (pop files)
                (fnn-check-regular path)
                (let* ((record (fnn-unframe-list (fnn-read-regular-bounded path bound)))
                       (length (length record)))
                  (incf aggregate length)
                  (incf octets length)
                  ;; ACL2's bound (fn-profile-replay-within-boundp).
                  (unless (fnn-core 'fn-store-profile-replay-within-bound
                                    (fnn-store-config store) aggregate)
                    (fnn-fault "transaction recovery input exceeds configured bound"))
                  (push (cons sequence record) chunk))))
            (fnn-core 'fn-srs-checked-decode (nreverse chunk)))))))

(defun fnn-recover-full-replay (store config-records &optional (reason nil))
  "Today's open: every durable record, then one full replay, taken in chunks;
answers the history's record count.  Without a selected pack the transaction
files are read a chunk at a time as the replay takes them
(`fnn-recover-file-chunks'), so the history is never in memory at once
besides the arena; with one, the pack reconstructs the prefix first
(`fnn-committed-history', which checks the marker) and the records go over in
chunks.  A caller that needs the records' octets reads them with
`fnn-committed-history'."
  (let* ((count nil)
         (next (if (funcall *fnn-pack-selected-callback* store)
                   (let ((records (fnn-committed-history store)))
                     (setq count (length records))
                     (fnn-recover-record-chunks records))
                   (let ((files (fnn-transaction-files
                                 store (funcall *fnn-pack-lower-bound-callback* store))))
                     (setq count (length files))
                     (fnn-check-history-marker store (length files))
                     (fnn-recover-file-chunks store files)))))
    (let ((action (fnn-bridge-recover next (fnn-store-frontier store) config-records)))
      ;; A named refusal of the open (books/store-open-pre-c1.lisp
      ;; fn-sopc-classified-open): ACL2 renders the line.
      (when (eq action :refused)
        (let ((text (fnn-core-state 'fn-store-open-refusal-text)))
          (unless (stringp text)
            (fnn-fault "ACL2 refused the open without naming a reason"))
          (error 'fnn-store-open-refusal :message text)))
      (unless (eq action :recovering)
        (fnn-fault "ACL2 replay rejected committed transaction history or configuration history")))
    (when reason
      (setf (fnn-store-open-mode store) (list :full-replay reason)))
    count))

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

(defun fnn-recover-suffix-rows (store suffix config-records)
  "The open from the loaded checkpoint: the suffix decoded
(fn-store-sn-recover-records), interned ON TOP of the arena the load left by
the guard-verified fn-intern-events (records nil 0: the canonical handles
continue from the checkpoint's payload count), then the open over the rows
(fn-store-sn-recover-from-checkpoint).  The three calls are
fn-scka-recover-rows over the host's extension (books/store-checkpoint-
arena.lisp, KEYSTONE fn-scka-recover-from-checkpoint-is-full-recover)."
  (let* ((configs (mapcar #'fnn-octet-list config-records))
         (decoded (fnn-core 'fn-store-sn-recover-records
                            (mapcar #'fnn-octet-list suffix) configs)))
    (if (eq decoded :bad)
        :fault
        (let ((rows (first (fnn-call 'fn-intern-events decoded nil 0 (fnn-live-arena)))))
          (fnn-action (fnn-core-state 'fn-store-sn-recover-from-checkpoint
                                      rows (fnn-store-frontier store) configs))))))

(defun fnn-recover-from-state-checkpoint (store config-records)
  "The history's record COUNT when the checkpoint opened the Store, else :FULL
after recording why not in open-mode (the caller then replays in full).  The
covered prefix is not re-encoded (PKT-823): a caller that needs the records
reads them after the open (`fnn-history-records')."
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
        (return-from fnn-recover-from-state-checkpoint :full))
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
        (unless (eq (fnn-recover-suffix-rows store suffix config-records) :recovering)
          ;; Full replay is authoritative and decides; the checkpoint is
          ;; derived.  Never serve a refused checkpoint open.
          (fnn-core-state 'fn-store-sco-clear)
          (fnn-bridge-reset)
          (setf (fnn-store-open-mode store) (list :full-replay :checkpoint-open-refused))
          (return-from fnn-recover-from-state-checkpoint :full))
        (setf (fnn-store-open-mode store) (list :checkpoint s (length suffix)))
        ;; The history's count; a caller that needs the records reads them
        ;; (fnn-committed-history), so the prefix is not re-encoded here.
        (+ s (length suffix))))))

(defun fnn-open-report (store)
  (let ((mode (fnn-store-open-mode store)))
    (case (first mode)
      (:checkpoint (format nil "open=checkpoint:~d suffix=~d" (second mode) (third mode)))
      (t (format nil "open=full-replay reason=~(~a~)" (second mode))))))

(defun fnn-state-checkpoint-file-observation (store)
  "The newest published checkpoint file's lstat, (OCTETS MODIFIED), or NIL
when there is none.  The status report (books/native-live-status.lisp
`fn-nls-checkpoint-file-words') renders it."
  (handler-case
      (let ((st (sb-posix:lstat (fnn-state-checkpoint-path store))))
        (list (sb-posix:stat-size st) (max 0 (sb-posix:stat-mtime st))))
    (sb-posix:syscall-error () nil)))

(defparameter +fnn-state-checkpoint-model-cuts+
  '("state-checkpoint-created" "state-checkpoint-written"
    "state-checkpoint-staged-durable" "state-checkpoint-replaced"
    "state-checkpoint-durable"))

(defun fnn-checkpoint-budget-test-override (budget)
  "Developer-only FN_NATIVE_CHECKPOINT_BUDGET_TEST=N: the checkpoint budget
the owner's automatic publication is decided against, in place of the
profile's (tests.test_native_checkpoint_auto's deferral case), else BUDGET
(the owner passes nil, and host/owner-host.lisp fn-owner-sco-budget takes
the profile's when it is not a natural).  The decision stays ACL2's:
fn-ock-publication-stream compares the file's length with what it is handed
and names both."
  (let ((raw (fnn-developer-selector "FN_NATIVE_CHECKPOINT_BUDGET_TEST")))
    (if raw
        (let ((value (ignore-errors (parse-integer raw))))
          (unless (and (integerp value) (>= value 0))
            (fnn-fault "invalid FN_NATIVE_CHECKPOINT_BUDGET_TEST (expected a natural)"))
          value)
      budget)))

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

(defun fnn-plan-p (plan &optional (st (fnn-live-octets)))
  "A state checkpoint plan (books/store-checkpoint-buffer.lisp fn-sccb-plan):
a nonempty list of (HEADER A B TRAILER), header and trailer nonempty octet
lists, 0 <= A <= B <= the fill of the buffer ST (the served buffer, or the
publication buffer fnn-live-octets-pub)."
  (let ((fill (svref st 1)))
    (and (consp plan)
         (every (lambda (frame)
                  (and (consp frame) (= (length frame) 4)
                       (fnn-octet-list-p (first frame)) (first frame)
                       (integerp (second frame)) (integerp (third frame))
                       (<= 0 (second frame) (third frame) fill)
                       (fnn-octet-list-p (fourth frame)) (fourth frame)))
                plan))))

(defun fnn-plan-write-all (fd plan st)
  "Write the frames' octets (fn-sccb-plan-octets: per frame the header, the
buffer ST's cells A..B, the trailer) to FD straight from ST's array: no
vector of the file is built.  Both checkpoint entries call this once per
pipeline step (fnn-checkpoint-write-steps) inside the staged file's writer
handed to fnn-state-checkpoint-write."
  (let ((buffer (the fnn-octets (svref st 0))))
    (dolist (frame plan)
      (let ((header (fnn-octets (first frame))) (a (second frame)) (b (third frame))
            (trailer (fnn-octets (fourth frame))))
        (fnn-write-range fd header 0 (length header))
        (fnn-write-range fd buffer a b)
        (fnn-write-range fd trailer 0 (length trailer))))))

;; PKT-169: the compaction's temporary space is checked against the disk.
;; The host observes the free octets of the store's filesystem (statvfs:
;; f_bavail blocks of f_frsize octets, what an unprivileged writer may use)
;; and ACL2 decides (books/store-compact-verb.lisp `fn-cverb-disk-admitsp').
;; NIL when the call fails or the platform's layout is not known here; ACL2
;; then refuses :temporary-space by name.  A developer image honours
;; FN_NATIVE_DISK_FREE=N, which caps the observation at N octets (a small
;; disk for the native case; the production image refuses to start with it).
(sb-alien:define-alien-routine ("statvfs" fnn-%statvfs) sb-alien:int
  (path sb-alien:c-string) (buffer (* (sb-alien:unsigned 8))))

(defun fnn-statvfs-free-octets (path)
  (let ((buffer (sb-alien:make-alien (sb-alien:unsigned 8) 256)))
    (unwind-protect
         (when (zerop (fnn-%statvfs path buffer))
           (let ((sap (sb-alien:alien-sap buffer)))
             (declare (ignorable sap))
             ;; f_frsize at 8 and f_bavail at 32: the Linux x86-64 and the
             ;; OpenBSD amd64 struct statvfs (sys/statvfs.h, 7.9) agree.
             #+(and (or linux openbsd) x86-64)
             (* (sb-sys:sap-ref-64 sap 8) (sb-sys:sap-ref-64 sap 32))
             #+darwin
             (* (sb-sys:sap-ref-64 sap 8) (sb-sys:sap-ref-32 sap 24))
             #-(or (and (or linux openbsd) x86-64) darwin)
             nil))
      (sb-alien:free-alien buffer))))

(defun fnn-disk-free-octets (store)
  (let ((free (fnn-statvfs-free-octets (fnn-store-root store)))
        (cap (fnn-developer-selector "FN_NATIVE_DISK_FREE")))
    (if (and free cap)
        (let ((n (ignore-errors (parse-integer cap))))
          (unless (and (integerp n) (>= n 0))
            (fnn-fault "invalid FN_NATIVE_DISK_FREE (expected octets)"))
          (min free n))
        free)))

;;; PKT-579: the filesystem a Store lives on (books/store-mount-identity.lisp,
;;; PRF-232).  `init' records the identity of the filesystem the store root
;;; is on; every open (fnn-acquire) observes it again and ACL2 decides:
;;; opened, or refused by name (unobserved, unrecorded, record invalid,
;;; changed).  The owner's start (fnn-owner-install) also asks the store's
;;; durability policy (PKT-648): refused by name when the store requires
;;; durable storage and the mount observably disables it.  The host reads
;;; statfs and /proc/self/mountinfo and hands ACL2 the facts; the mount table
;;; is parsed and the containing mount selected in ACL2
;;; (fn-smid-mountinfo-step), never here.

(defun fnn-filesystem-record-path (store)
  (fnn-join (fnn-store-root store) "filesystem-identity.fnmi"))

(sb-alien:define-alien-routine
    (#+(and darwin x86-64) "statfs$INODE64" #-(and darwin x86-64) "statfs"
     fnn-%statfs)
    sb-alien:int
  (path sb-alien:c-string) (buffer (* (sb-alien:unsigned 8))))

(defun fnn-statfs-octets (path)
  "The raw struct statfs of PATH as octets (4096 is larger than every layout
below: Linux 120, OpenBSD 568, macOS 2168), or NIL when statfs fails."
  (let ((buffer (sb-alien:make-alien (sb-alien:unsigned 8) 4096)))
    (unwind-protect
         (when (zerop (fnn-%statfs path buffer))
           (let ((out (fnn-make-octets 4096)) (sap (sb-alien:alien-sap buffer)))
             (dotimes (i 4096 out)
               (setf (aref out i) (sb-sys:sap-ref-8 sap i)))))
      (sb-alien:free-alien buffer))))

(defun fnn-statfs-field (raw start width)
  "The octets of the NUL-terminated char[WIDTH] at START."
  (let* ((end (+ start width))
         (nul (or (position 0 raw :start start :end end) end)))
    (fnn-octet-list (subseq raw start nul))))

(defun fnn-realpath (path)
  "realpath(3) of PATH as octets, or NIL."
  (let ((result (sb-alien:alien-funcall
                 (sb-alien:extern-alien "realpath"
                                        (function (* sb-alien:char) sb-alien:c-string (* sb-alien:char)))
                 path nil)))
    (unless (sb-alien:null-alien result)
      (unwind-protect
           (let ((sap (sb-alien:alien-sap result)) (octets nil))
             (loop for i from 0
                   for b = (sb-sys:sap-ref-8 sap i)
                   until (zerop b) do (push b octets))
             (nreverse octets))
        (sb-alien:alien-funcall
         (sb-alien:extern-alien "free" (function sb-alien:void (* sb-alien:char))) result)))))

(defun fnn-mountinfo-best (path)
  "Fold /proc/self/mountinfo line by line through ACL2's selection.  A line
longer than ACL2's bound is handed over as :overlong, never truncated."
  (let* ((fd (fnn-open "/proc/self/mountinfo" sb-posix:o-rdonly))
         (limit (fnn-core 'fn-smid-mountinfo-line-max))
         (line (make-array 256 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
         (overlong nil) (best nil)
         (buffer (fnn-make-octets 65536)))
    (flet ((flush ()
             (when (or overlong (plusp (fill-pointer line)))
               (setq best (fnn-core 'fn-smid-mountinfo-step best
                                    (if overlong :overlong (coerce line 'list))
                                    path)))
             (setf (fill-pointer line) 0 overlong nil)))
      (unwind-protect
           (loop
             (let ((count (fnn-read-fd fd buffer)))
               (when (zerop count) (flush) (return best))
               (dotimes (i count)
                 (let ((b (aref buffer i)))
                   (cond ((= b 10) (flush))
                         (overlong nil)
                         ((>= (fill-pointer line) limit) (setq overlong t))
                         (t (vector-push-extend b line)))))))
        (fnn-close fd)))))

(defun fnn-filesystem-observation (root)
  "What statfs and the mount table say about the filesystem ROOT is on:
ACL2's observation, (:observed ...) or (:unobserved)."
  (handler-case
      (let ((raw (fnn-statfs-octets root)))
        (if (null raw)
            (list :unobserved)
            #+linux
            (let ((path (fnn-realpath root)))
              (if (null path)
                  (list :unobserved)
                  ;; f_fsid at 56 (struct statfs, x86-64).
                  (fnn-core 'fn-smid-linux-observation
                            (fnn-octet-list (subseq raw 56 64))
                            (fnn-mountinfo-best path))))
            ;; OpenBSD amd64 7.9: f_fsid 96, f_fstypename 120[16],
            ;; f_mntonname 136[90], f_mntfromname 226[90].
            #+openbsd
            (fnn-core 'fn-smid-statfs-observation
                      (fnn-octet-list (subseq raw 96 104))
                      (fnn-statfs-field raw 120 16)
                      (fnn-statfs-field raw 136 90)
                      (fnn-statfs-field raw 226 90))
            ;; macOS (64-bit inode): f_fsid 48, f_fstypename 72[16],
            ;; f_mntonname 88[1024], f_mntfromname 1112[1024].
            #+darwin
            (fnn-core 'fn-smid-statfs-observation
                      (fnn-octet-list (subseq raw 48 56))
                      (fnn-statfs-field raw 72 16)
                      (fnn-statfs-field raw 88 1024)
                      (fnn-statfs-field raw 1112 1024))
            #-(or linux openbsd darwin)
            (list :unobserved)))
    (fnn-os-error () (list :unobserved))))

(defun fnn-filesystem-record-observation (store)
  "(:absent), or (:present OCTETS DIGEST): the record file's octets and ACL2's
trailer over its protected prefix.  A file past ACL2's bound is a record that
does not decode."
  (let ((path (fnn-filesystem-record-path store)))
    (if (null (fnn-check-regular path))
        (list :absent)
        (let ((raw (handler-case
                       (fnn-read-regular-bounded
                        path (fnn-core 'fn-smid-record-frame-limit))
                     (fnn-input-overbound () nil))))
          (if (null raw)
              (list :present nil nil)
              (list :present (fnn-octet-list raw) (fnn-digest-of raw)))))))

(defun fnn-filesystem-text (octets)
  (unless (fnn-octet-list-p octets)
    (fnn-fault "ACL2 returned a malformed filesystem line"))
  (fnn-octets-string (fnn-octets octets)))

(defun fnn-filesystem-durability-warn (root &optional observation)
  "PKT-648: print ACL2's warning when the filesystem under ROOT observably
disables durability (nobarrier, barrier=0, tmpfs, ramfs); nothing otherwise.
The owner's start and `status'/`health' call it, not every open."
  (let ((warning (fnn-core 'fn-smid-durability-warning
                           (or observation (fnn-filesystem-observation root)))))
    (when warning (fnn-err "~a" (fnn-filesystem-text warning)))))

(defun fnn-check-filesystem-identity (store &optional start)
  "The open's decision (ACL2 fn-smid-open-verdict), or with START the owner
start's (fn-smid-start-verdict): refused by name, never opened elsewhere.
A start that proceeds prints the durability warning."
  (let* ((observation (fnn-filesystem-observation (fnn-store-root store)))
         (record (fnn-filesystem-record-observation store))
         (verdict (if start
                      (fnn-core 'fn-smid-start-verdict record observation)
                      ;; CONFIGURED: config.json is a regular file here (a
                      ;; store made before the record opens offline with a
                      ;; warning; an empty root is refused).
                      (fnn-core 'fn-smid-open-decision record observation
                                (if (fnn-check-regular (fnn-config-path store)) t nil)))))
    (when (and (not start) (consp verdict) (eq (first verdict) :open-unrecorded))
      (fnn-err "~a" (fnn-filesystem-text
                     (fnn-core 'fn-smid-unrecorded-warning verdict)))
      (return-from fnn-check-filesystem-identity verdict))
    (unless (equal verdict (if start '(:start) '(:open)))
      (let ((text (fnn-core 'fn-smid-refusal-text verdict)))
        (unless text
          (fnn-fault "ACL2 returned no text for a filesystem refusal"))
        (error 'fnn-store-open-refusal :message (fnn-filesystem-text text))))
    (when start
      (fnn-filesystem-durability-warn (fnn-store-root store) observation))
    verdict))

(defun fnn-publish-filesystem-record (store protected)
  "Replace the record by PROTECTED sealed with ACL2's trailer: stage, fsync,
rename, fsync the root.  The caller holds the writer lock.  A failure before
the rename is a known failure (the stage is removed, or left to the staging
sweep under its .stage- prefix); after it, uncertain."
  (unless (fnn-octet-list-p protected)
    (fnn-fault "ACL2 returned a malformed filesystem record"))
  (let ((stage (fnn-join (fnn-staging store)
                         (format nil ".stage-filesystem-~d-~a"
                                 (sb-posix:getpid) (fnn-random-hex 12)))))
    (handler-case (fnn-write-staged stage (fnn-seal protected))
      (fnn-os-error (e)
        (ignore-errors (fnn-unlink stage))
        (fnn-refuse-io "cannot stage the filesystem record: ~a" e)))
    (handler-case
        (progn (fnn-replace stage (fnn-filesystem-record-path store))
               (fnn-fsync-dir (fnn-store-root store)))
      (fnn-os-error (e)
        (fnn-indeterminate "filesystem record replacement is uncertain: ~a" e)))
    :published))

(defun fnn-record-filesystem-at-init (store profile &optional policy)
  "After fnn-initialize: record the identity under POLICY (1 or 0, the init's
--storage-require-durable) or else the preset's policy, once.
An existing record is kept (a repeated `init' over an existing store); the
open that follows checks it."
  (when (eq (first (fnn-filesystem-record-observation store)) :absent)
    (let ((lock-fd (fnn-open-lock store t t)))
      (setf (fnn-store-lock-fd store) lock-fd)
      (unwind-protect
           (let ((plan (fnn-core 'fn-smid-record-plan
                                 (fnn-filesystem-observation (fnn-store-root store))
                                 (or policy (fnn-core 'fn-smid-init-policy nil)))))
             (unless (and (consp plan) (member (first plan) '(:record :refused)))
               (fnn-fault "ACL2 returned a malformed filesystem record plan"))
             (when (eq (first plan) :refused)
               (error 'fnn-store-open-refusal
                      :message (fnn-filesystem-text
                                (fnn-core 'fn-smid-refusal-text plan))))
             (when (eq (first (fnn-filesystem-record-observation store)) :absent)
               (fnn-publish-filesystem-record store (second plan))))
        (setf (fnn-store-lock-fd store) nil)
        (ignore-errors (fnn-flock lock-fd +fnn-lock-un+))
        (fnn-close lock-fd)))))

(defun fnn-command-rebind-filesystem (root requested)
  "`store ROOT rebind-filesystem [on|off]': record the filesystem the store
is on now, for a deliberate move or a restored backup.  The store's writer
lock is taken (a running owner refuses this) and its profile and frontier
load, but the identity is not checked: that is what this replaces.
REQUESTED is 1, 0 or NIL (keep the store's policy)."
  (let ((store (make-fnn-store root :writable t)))
    (fnn-safe-directory (fnn-store-root store))
    (fnn-safe-directory (fnn-staging store))
    (setf (fnn-store-lock-fd store) (fnn-open-lock store t nil))
    (unwind-protect
         (progn
           (fnn-load-config store)
           (fnn-load-frontier store)
           (let* ((record (fnn-filesystem-record-observation store))
                  (observation (fnn-filesystem-observation (fnn-store-root store)))
                  (plan (fnn-core 'fn-smid-rebind-plan record observation requested)))
             (unless (and (consp plan) (member (first plan) '(:record :refused)))
               (fnn-fault "ACL2 returned a malformed rebind plan"))
             (when (eq (first plan) :refused)
               (error 'fnn-store-open-refusal
                      :message (fnn-filesystem-text
                                (fnn-core 'fn-smid-refusal-text plan))))
             (fnn-publish-filesystem-record store (second plan))
             (fnn-out "~a" (fnn-filesystem-text
                            (fnn-core 'fn-smid-rebind-text record observation requested)))))
      (fnn-store-close store))
    +fnn-exit-ok+))

;;; The batch loop both entries run (host/native/owner.lisp
;;; fnn-owner-publish-captured on its thread; the verb below): ACL2's
;;; fn-ockp-step over the publication buffer, each step's frames written to
;;; FD before the next step (fnn-plan-write-all, straight from the buffer's
;;; array), until the four tables are written.  The buffer holds one step's
;;; rows and one segment's residue, never the file
;;; (books/owner-checkpoint-pipeline.lisp).  A refused frame (one the reader
;;; would refuse) abandons the staged file as a known failure before the
;;; rename.  The developer selector FN_NATIVE_CHECKPOINT_BATCH_FAULT=K:kill
;;; kills the process after the K-th step's frames were written (the
;;; `created' cut's verdict: the next open reads the old checkpoint, the
;;; staged file is swept).

(defconstant +fnn-checkpoint-batch-rows+ 1024
  "Rows of a table per pipeline step: a work bound per scheduling step (D27),
never a bound on the store; the file is the same at every batch size.")

(defconstant +fnn-checkpoint-batch-octets+ (* 4 1024 1024)
  "Octets per pipeline step: the step ends after the row that brings the
publication buffer's fill to this (fn-ockp-encode-batch), so a step's
residency is under this plus one row plus one segment's residue whatever the
rows' sizes (gpt-6, review 2026-09-26 section 2: one record can be large).
A work bound per step, never a bound on the store; the file is the same at
every value.")

(defun fnn-checkpoint-revision ()
  "The writer's source revision for the checkpoint's F row: the recorded one
(fnn-source-revision), or \"unknown\" on an image that records none (a
scratch image): provenance, never a refusal."
  (or (ignore-errors (fnn-source-revision)) "unknown"))

(defun fnn-checkpoint-batch-fault ()
  "Developer-only FN_NATIVE_CHECKPOINT_BATCH_FAULT=K:kill: the step after
which the process is killed, or NIL."
  (let ((raw (fnn-developer-selector "FN_NATIVE_CHECKPOINT_BATCH_FAULT")))
    (when raw
      (let ((colon (position #\: raw)))
        (unless (and colon (string= (subseq raw (1+ colon)) "kill"))
          (fnn-fault "invalid FN_NATIVE_CHECKPOINT_BATCH_FAULT (expected K:kill)"))
        (let ((k (ignore-errors (parse-integer (subseq raw 0 colon)))))
          (unless (and (integerp k) (>= k 0))
            (fnn-fault "invalid FN_NATIVE_CHECKPOINT_BATCH_FAULT (expected K:kill)"))
          k)))))

(defun fnn-checkpoint-walk (records)
  "The walk of the owner's captured RECORDS: each canonical payload's length
and source (books/store-checkpoint-arena-writer.lisp fn-scka-srcs-n), a
bounded number of rows per call (+fnn-checkpoint-batch-rows+; the calls are
one walk: fn-scka-srcs-n-compose).  READS the arena.  The last state,
(ROWS' LACC SACC), ROWS' empty."
  (let ((walk (list records nil nil)) (arena (fnn-live-arena)))
    (loop
      (when (atom (first walk)) (return walk))
      (setq walk (fnn-core 'fn-scka-srcs-n (first walk) +fnn-checkpoint-batch-rows+
                           (second walk) (third walk) arena))
      (unless (and (consp walk) (= (length walk) 3))
        (fnn-fault "ACL2 returned a malformed checkpoint walk")))))

(defun fnn-checkpoint-write-arena-steps (fd arun sequence segment-bound file-bound st fault)
  "Write the arena run's frames to FD step by step (fn-scka-write-step: step 0
the head, each later step one batch of whole canonical payloads read through
the arena, framed and admitted by the reader's rule); the number of steps.
ARUN is (N COUNT STATE0) from fn-store-sco-publish-setup or the owner's
capture.  KEYSTONE fn-scka-write-run-is-run-segments
(books/store-checkpoint-arena-writer.lisp): the frames' octets, in order,
are the arena run the load reads.  The step READS the arena and updates only
the publication buffer ST."
  (destructuring-bind (n count state) arun
    (let ((steps 0) (arena (fnn-live-arena)))
      (loop
        (when (fnn-core 'fn-scka-write-donep state count) (return steps))
        (let ((answer (fnn-call 'fn-scka-write-step state n count sequence
                                segment-bound file-bound arena st)))
          (unless (and (consp answer) (>= (length answer) 3))
            (fnn-fault "ACL2 returned a malformed checkpoint arena step"))
          (destructuring-bind (verdict frames next &rest stobj) answer
            (declare (ignore stobj))
            (unless (eq verdict :ok)
              (fnn-refuse-io "the checkpoint arena run refused by name: ~a" verdict))
            (unless (fnn-plan-p frames st)
              (fnn-fault "ACL2 returned a malformed checkpoint arena step"))
            (fnn-plan-write-all fd frames st)
            (setq state next)
            (incf steps)
            (when (and fault (= steps (1+ fault)))
              (sb-posix:kill (sb-posix:getpid) sb-posix:sigkill))))))))

(defun fnn-checkpoint-write-steps (fd setup segment sequence profile st arun)
  "Write the file's frames to FD step by step: the arena run ARUN first
(fnn-checkpoint-write-arena-steps), then the four tables (fn-ockp-step); the
number of steps."
  (let* ((segment-bound (fnn-core 'fn-store-sco-segment-read-bound profile))
         (file-bound (fnn-core 'fn-store-sco-file-read-bound profile))
         (fault (fnn-checkpoint-batch-fault))
         (steps (fnn-checkpoint-write-arena-steps fd arun sequence segment-bound
                                                  file-bound st fault))
         (state (fnn-core 'fn-ockp-initial-state (second setup) st)))
    (loop
      (when (fnn-core 'fn-ockp-donep state) (return steps))
      (let ((answer (fnn-call 'fn-ockp-step setup state +fnn-checkpoint-batch-rows+
                              +fnn-checkpoint-batch-octets+
                              segment sequence segment-bound file-bound st)))
        ;; fnn-call answers the multiple-value list: VERDICT FRAMES STATE'
        ;; and the stobj.
        (unless (and (consp answer) (>= (length answer) 3))
          (fnn-fault "ACL2 returned a malformed checkpoint step"))
        (destructuring-bind (verdict frames next &rest stobj) answer
          (declare (ignore stobj))
          (unless (eq verdict :ok)
            ;; (:refused REASON): a frame the open would refuse; :unencodable:
            ;; a row the codec cannot write (unreachable after a setup that
            ;; did not say so: fn-ockp-setup-not-unencodable-never-refuses-a-row)
            (fnn-refuse-io "the checkpoint pipeline refused by name: ~a" verdict))
          (unless (or (null frames) (fnn-plan-p frames st))
            (fnn-fault "ACL2 returned a malformed checkpoint step"))
          (fnn-plan-write-all fd frames st)
          (setq state next)
          (incf steps)
          (when (and fault (= steps (1+ fault)))
            (sb-posix:kill (sb-posix:getpid) sb-posix:sigkill)))))))

(defun fnn-state-checkpoint-publish-steps (store count)
  "Publish the exact-state checkpoint of the recovered STORE (P3) and return
the report line.  ACL2 extends the checkpoint the open used over the
records after it, or captures the whole history after a full replay,
builds the schema-3 tables of it and decides by name before anything is
allocated (fn-store-sco-publish-setup, books/owner-checkpoint-pipeline.lisp:
the estimate against the profile's checkpoint budget and the free space);
then the same batch loop as the owner's thread writes the file through the
publication buffer, one step's rows at a time.  On a format-9 store the log
is rotated first (fnn-log-rotate: the checkpoint's F row names the new
segment and its genesis), and once the checkpoint is installed the segments
it covers are dropped (fnn-log-drop; T8)."
  (let* ((profile (fnn-store-config store))
         ;; the writer's segment: ACL2's choice under the record bound
         ;; (fn-ockp-segment-octets: the smaller of R and a quarter of
         ;; the step's octets); the same derivation as the owner's thread
         (segment (fnn-core 'fn-ockp-segment-octets
                            (fnn-profile-nat 'fn-store-profile-max-record-octets store)
                            +fnn-checkpoint-batch-octets+))
         (budget (fnn-core 'fn-ock-capture-budget profile))
         (position (and (fnn-store-logp store) (fnn-log-rotate store)))
         ;; one walk of the live rows, a bounded number per call: each
         ;; canonical payload's length and source (fn-store-sco-pass-step)
         (walked (progn
                   (fnn-core-state 'fn-store-sco-pass-begin)
                   (loop until (fnn-core-arena-state 'fn-store-sco-pass-step
                                                     +fnn-checkpoint-batch-rows+))
                   t))
         (answer (fnn-core-arena-state 'fn-store-sco-publish-setup segment budget
                                       (fnn-disk-free-octets store)
                                       (fnn-checkpoint-revision) position)))
    (declare (ignore walked))
    (unless (and (consp answer) (= (length answer) 3)
                 (consp (first answer)) (integerp (second answer))
                 (= (second answer) count))
      (fnn-fault "ACL2 returned a malformed state checkpoint setup"))
    (let* ((setup (first answer)) (sequence (second answer))
           (arun (third answer))
           (verdict (first setup)))
      (cond
        ((eq verdict :unencodable)
         (fnn-refuse "the recovered Store state is not encodable as a checkpoint"))
        ((and (consp verdict) (eq (first verdict) :deferred))
         (fnn-refuse "checkpoint deferred reason=~(~a~) estimate=~d budget=~d"
                     (second verdict) (third verdict) (fourth verdict)))
        ((and (consp verdict) (eq (first verdict) :plan) (integerp (second verdict)))
         (let ((st (fnn-live-octets-pub)) (steps 0) (dropped 0))
           (unwind-protect
                (fnn-state-checkpoint-write
                 store
                 (lambda (fd)
                   (setq steps (fnn-checkpoint-write-steps fd setup segment sequence
                                                           profile st arun))))
             (fnn-octets-pub-release))
           (when position
             (handler-case
                 (setq dropped (fnn-log-drop store (fnn-log-covered-indices store (first position))))
               (fnn-os-error (e)
                 (fnn-indeterminate "the drop of covered log segments is uncertain: ~a" e))))
           (format nil "checkpoint sequence=~d octets=~d steps=~d~@[ segment=~d~]~:[~; dropped=~d~] ~a"
                   sequence (second verdict) steps (first position) position dropped
                   (fnn-open-report store))))
        (t (fnn-fault "ACL2 returned a malformed checkpoint verdict"))))))

(defun fnn-command-state-checkpoint (root)
  "`store checkpoint': open the store as `recover' does (the exclusive writer
lock, so a running owner refuses this) and publish its exact-state checkpoint
(fnn-state-checkpoint-publish-steps)."
  (multiple-value-bind (store count)
      (fnn-open-live-store root t (fnn-state-checkpoint-test-fault))
    (unwind-protect
         (progn (fnn-out "~a" (fnn-state-checkpoint-publish-steps store count))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-recover (store)
  "Open STORE: the history replayed (from the state checkpoint or in full),
the recovery barriers, the staging sweep and the marker catch-up.  Answers
the history's record COUNT; the records themselves are not kept (PKT-823): a
caller that needs their octets reads them with `fnn-committed-history'."
  (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil
        (fnn-store-marker-catch-up store) nil
        (fnn-store-open-mode store) '(:full-replay :absent))
  (when (fnn-store-logp store)
    (return-from fnn-recover (fnn-recover-log store)))
  (let ((count nil))
    (handler-case
        (progn
          (fnn-load-frontier store)
          (let ((config-records (fnn-config-records store)))
            (setq count (fnn-with-pack-memo
                            (let ((opened (fnn-recover-from-state-checkpoint
                                           store config-records)))
                              (if (eq opened :full)
                                  (fnn-recover-full-replay store config-records)
                                  opened)))))
          (setf (fnn-store-config-generation store) (fnn-bridge-config-generation)
                (fnn-store-config-served store) (fnn-bridge-config-names 'fn-store-cfg-served)
                (fnn-store-config-domain store) (fnn-bridge-config-names 'fn-store-cfg-domain)))
      ((or fnn-store-fault fnn-store-indeterminate fnn-store-open-refusal) (e)
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
    ;; D31 case 2: the marker catches up here, after the fifth barrier made
    ;; every reconstructed record durable and before the open returns, so a
    ;; record this process later answers as stored (a retry resolved as
    ;; already stored, with no later commit) is below a durable marker.  A
    ;; reader under the shared lock writes nothing and answers no submission.
    ;; An error in the marker program is uncertain (exit 3); the next open
    ;; catches up again.
    (let ((frame (fnn-store-marker-catch-up store)))
      (when (and frame (fnn-store-writable store))
        (fnn-mark-committed store nil frame)
        (setf (fnn-store-marker-catch-up store) nil)))
    ; Full journal replay above remains authoritative.  The checkpoint layer
    ; restores into separate ACL2 globals and compares that image with
    ; fn-store-sn; it cannot reset or replace the live node.
    (setf (fnn-store-checkpoint-outcome store)
          (funcall *fnn-checkpoint-recover-callback* store count))
    (setf (fnn-store-fenced store) nil)
    count))

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
                           ;; CONTENTS is a byte vector, or a writer the
                           ;; caller hands in (the owner's checkpoint plan,
                           ;; fnn-plan-write-all: the file's bytes straight
                           ;; from the publication buffer, no vector of the
                           ;; file), written between the same two cuts.
                           (if (functionp contents)
                               (funcall contents fd)
                             (fnn-write-all fd contents))
                           (fnn-at store written)
                           (fnn-fsync-file fd))
      (fnn-close fd))))

(defun fnn-advance-frontier (store current-txid)
  "Report each allocator observation to the file kernel in order."
  (when (fnn-store-logp store)
    (return-from fnn-advance-frontier (fnn-log-reserve store current-txid)))
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
  (when (fnn-store-logp store)
    (return-from fnn-publish (fnn-log-publish store sequence record)))
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
    ;; A batch of one (every commit outside the owner's batch quantum): the
    ;; member's record is fenced already, so the log kernel acknowledges it
    ;; now (fn-lgk-finish-one).  Inside a batch the committer acknowledges
    ;; each member after the batch's barrier (fnn-log-batch-finish).
    (when (and (fnn-store-logp store) (not *fnn-log-batch*))
      (fnn-log-ack (fnn-store-log store) 1))
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

(defun fnn-metadata-buffer (msgid)
  "FNN-METADATA with the payload in the octet buffer (the served POST): the
subject identity is FNN-SUBJECT-ID-BUFFER, the rest as FNN-METADATA."
  (let* ((subject (handler-case (fnn-subject-id-buffer)
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
(fn-owner-post-boundary).  The host compares no bound of its own and keeps
no text of its own: `fn-sbud-post-boundary-refusal' (books/store-budget-
naming.lisp) renders the refusal, NIL exactly when the boundary admits
(fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted), and the host
prints its octets."
  (let ((text (fnn-core 'fn-sbud-post-boundary-refusal verdict)))
    (cond ((null text) nil)
          ((fnn-octet-list-p text) (fnn-refuse "~a" (fnn-octets-string text)))
          (t (fnn-fault "ACL2 returned a malformed POST boundary refusal")))))

(defun fnn-open-live-store (root writable &optional fault)
  "Acquire and open ROOT: the store and the history's record COUNT (PKT-823);
the records are read after the open by the verbs that need them
(`fnn-history-records')."
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
    "init-root-fenced" "init-parent-fenced"
    ;; books/byte-store-log-initializer.lisp fn-bsi-log-init-program (format 9).
    "init-journal-mkdir" "init-journal-parent-fenced"
    "init-segment-created" "init-segment-written" "init-segment-file-fenced"
    "init-journal-segment-fenced"))

;; These controls are intentionally outside fn-bsi-current-init-program: they
;; fail *before* a directory enumeration to verify the host does not confuse
;; an OS error with an empty configuration history.
(defparameter +fnn-init-test-controls+
  '("init-config-records-first-enumerate" "init-config-records-final-enumerate"))

;; books/store-init-publication.lisp fn-bs-init-pub-program's cuts: the
;; import's program with init's names, in program order.
(defparameter +fnn-init-publication-cuts+
  '("init-stage-created" "init-subdir-created" "init-file-created"
    "init-file-written" "init-file-durable" "init-subdir-durable"
    "init-staged-durable" "init-validated" "init-published" "init-durable"))

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
                      (member label +fnn-init-publication-cuts+ :test #'string=)
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
          ;; The recovery's marker catch-up runs the marker program, whose
          ;; cuts are ACL2's table (books/store-history-marker).
          (unless (or (member label +fnn-recovery-model-cuts+ :test #'string=)
                      (member label (fnn-core 'fn-hm-marker-cut-names) :test #'string=))
            (fnn-fault "unknown FN_NATIVE_RECOVERY_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_RECOVERY_FAULT action: ~a" action)))
                "developer-only native recovery fault"))))))

;;; SEC-006 (PRF-210): the node's key files (books/node-secret.lisp).  The
;;; store directory is the node's persistent private state (D34); the key
;;; files live in STORE/keys/ (mode 0700), each 0600:
;;;
;;;   node-secret.key     the CURRENT epoch's entry (fn-ns-file-render)
;;;   node-secret-E.key   each retained older epoch E, kept by a rotation so
;;;                       posts locked under it stay cancellable
;;;
;;; Every value in a file is ACL2's: the entry (fn-ns-create-entry,
;;; fn-ns-rotate-entry), its octets (fn-ns-file-render) and its reading
;;; (fn-ns-file-parse).  The host supplies 32 octets from the OS CSPRNG and
;;; does the I/O.  The verbs are explicit and never replace a secret:
;;; `store ROOT node-secret create [IDENTITY]' (and `init') publishes epoch
;;; 1 once, refused by name when a secret exists; `store ROOT node-secret
;;; rotate [IDENTITY]' keeps the current file as node-secret-E.key and
;;; publishes epoch E+1.  A start never creates one
;;; (host/native/owner.lisp fnn-owner-load-node-secret).  Never printed, never
;;; exported (`store export' writes committed records only).
(defun fnn-node-secret-directory (store)
  (fnn-join (fnn-store-root store) "keys"))

(defun fnn-node-secret-path (store)
  (fnn-join (fnn-node-secret-directory store) "node-secret.key"))

(defun fnn-node-secret-epoch-path (store epoch)
  (fnn-join (fnn-node-secret-directory store) (format nil "node-secret-~d.key" epoch)))

;; The largest file fn-ns-file-parse can accept: magic 18, epoch 4, length
;; 2, identity below 2^16, root 32.
(defconstant +fnn-node-secret-file-bound+ (+ 18 4 2 65535 32))

(defun fnn-node-secret-ensure-directory (store)
  (let* ((dir (fnn-node-secret-directory store))
         (st (fnn-lstat dir)))
    (cond ((null st)
           (fnn-mkdir dir #o700)
           (fnn-fsync-dir (fnn-store-root store)))
          ((or (fnn-symlink-p st) (not (fnn-directory-p st)))
           (fnn-fault "refusing non-directory key path: ~a" dir)))
    dir))

(defun fnn-node-secret-identity (identity)
  "The octets of the operator's IDENTITY word, or NIL (ACL2 supplies the
default)."
  (if identity (fnn-octet-list (fnn-string-octets identity)) nil))

(defun fnn-node-secret-fresh-root ()
  (fnn-octet-list (fnn-csprng-octets (fnn-core 'fn-ns-secret-width) "node secret")))

(defun fnn-node-secret-render (entry)
  (unless (fnn-core 'fn-ns-entryp entry)
    (fnn-fault "ACL2 built an invalid node-secret entry"))
  (let ((octets (fnn-core 'fn-ns-file-render entry)))
    (unless (fnn-octet-list-p octets)
      (fnn-fault "ACL2 returned invalid node-secret file octets"))
    (fnn-octets octets)))

(defun fnn-node-secret-read-entry (path what)
  "The entry of the key file PATH, read by ACL2 (fn-ns-file-parse), or NIL
when PATH is absent.  Refused by name when it is not a regular file, is
readable or writable by group or others, or does not parse."
  (let ((st (fnn-lstat path)))
    (when st
      (unless (and (not (fnn-symlink-p st)) (fnn-regular-p st))
        (fnn-refuse "~a ~a is not a regular file" what path))
      (unless (zerop (logand (sb-posix:stat-mode st) #o077))
        (fnn-refuse "~a ~a is readable or writable by group or others (mode ~o)"
                    what path (logand (sb-posix:stat-mode st) #o777)))
      (let ((entry (fnn-core 'fn-ns-file-parse
                             (fnn-octet-list
                              (fnn-read-regular-bounded
                               path +fnn-node-secret-file-bound+)))))
        (unless entry
          (fnn-refuse "~a ~a is not a fn-node-secret v1 file" what path))
        entry))))

(defun fnn-node-secret-create (store &optional identity (existing :refuse))
  "Publish STORE's first node secret (epoch 1).  An existing secret is never
replaced: refused by name, or with EXISTING :keep (init's re-run) kept."
  (let* ((dir (fnn-node-secret-ensure-directory store))
         (path (fnn-node-secret-path store)))
    (flet ((exists ()
             (if (eq existing :keep)
                 (return-from fnn-node-secret-create :existing)
               (fnn-refuse "node secret ~a exists; refusing to replace it" path))))
      (when (fnn-lstat path) (exists))
      (let ((entry (fnn-core 'fn-ns-create-entry (fnn-node-secret-identity identity)
                             (fnn-node-secret-fresh-root))))
        (when (eq (fnn-publish-initial-file store path (fnn-node-secret-render entry))
                  :existing)
          (exists))
        (fnn-fsync-dir dir)
        :published))))

(defun fnn-node-secret-same-file-p (a b)
  (equalp (fnn-read-regular-bounded a +fnn-node-secret-file-bound+)
          (fnn-read-regular-bounded b +fnn-node-secret-file-bound+)))

(defun fnn-node-secret-rotate (store &optional identity)
  "Keep the current epoch E as node-secret-E.key, then publish epoch E+1 as
node-secret.key; the new epoch.  A rotation cut after the keep and before
the replace is resumed by running the verb again (the kept file equals the
current one)."
  (let* ((dir (fnn-node-secret-ensure-directory store))
         (path (fnn-node-secret-path store))
         (current (or (fnn-node-secret-read-entry path "node secret")
                      (fnn-refuse "node secret ~a is missing: run `store ~a node-secret create' once"
                                  path (fnn-store-root store))))
         (epoch (fnn-core 'fn-ns-entry-epoch current))
         (keep (fnn-node-secret-epoch-path store epoch)))
    (if (fnn-lstat keep)
        (unless (fnn-node-secret-same-file-p keep path)
          (fnn-refuse "retained node secret ~a exists and differs; refusing to rotate" keep))
      (progn (fnn-link path keep)
             (fnn-fsync-dir dir)))
    (let* ((next (fnn-core 'fn-ns-rotate-entry current (fnn-node-secret-identity identity)
                           (fnn-node-secret-fresh-root)))
           (octets (fnn-node-secret-render next))
           (stage (fnn-join dir (format nil ".node-secret-~d-~a.stage"
                                        (sb-posix:getpid) (fnn-random-hex 8))))
           (fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl)
                         #o600)))
      (unwind-protect (progn (fnn-write-all fd octets) (fnn-fsync-file fd))
        (fnn-close fd))
      (handler-case (fnn-replace stage path)
        (fnn-os-error (e)
          (ignore-errors (fnn-unlink stage))
          (fnn-indeterminate "node secret rotation outcome is indeterminate: ~a" e)))
      (fnn-fsync-dir dir)
      (fnn-core 'fn-ns-entry-epoch next))))

(defun fnn-command-node-secret (root words)
  "`store ROOT node-secret create [IDENTITY]' or `... rotate [IDENTITY]'."
  (let ((verb (first words)) (identity (second words)))
    (unless (and (member verb '("create" "rotate") :test #'equal) (null (cddr words)))
      (error 'fnn-usage-error
             :message "usage: store ROOT node-secret create|rotate [IDENTITY]"))
    (let ((store (make-fnn-store root :writable t)))
      (unwind-protect
           (progn (fnn-acquire store)
                  (if (string= verb "create")
                      (progn (fnn-node-secret-create store identity)
                             (fnn-out "node-secret created epoch 1"))
                    (fnn-out "node-secret rotated epoch ~d"
                             (fnn-node-secret-rotate store identity))))
        (fnn-store-close store))
      +fnn-exit-ok+)))

(defun fnn-command-init (root groups &optional (profile :development) policy)
  (let ((store (make-fnn-store root :writable t :fault (fnn-init-test-fault))))
    (unwind-protect
         (progn (fnn-initialize store (or groups +fnn-default-groups+) profile)
                (fnn-record-filesystem-at-init store profile policy)
                (fnn-acquire store)
                (fnn-node-secret-create store nil :keep)
                (fnn-out "initialized ~a" (fnn-store-root store)))
      (fnn-store-close store))
    +fnn-exit-ok+))

(defun fnn-command-init-published (root groups profile &optional policy)
  "`operator CONFIG init' (PKT-647): build the empty store beside ROOT, in
ROOT.init-XXXX, and publish it without replacing anything
(books/store-init-publication.lisp fn-bs-init-pub-program, through
fnn-staged-publication).  Its plan is ACL2's three frames: the profile, the
allocation frontier 0 and the generation-1 configuration record.  Before
writing anything the host observes a leftover ROOT.init-* and ROOT, and
ACL2's admission (fn-bs-init-pub-admission over fn-bs-imp-classify) proceeds
or refuses by name, saying what to run."
  (let* ((root-path (string-right-trim "/" root))
         (leftover (fnn-import-leftover-stage root-path "init"))
         (verdict (and leftover (fnn-import-classify leftover root-path)))
         (admission (fnn-core 'fn-bs-init-pub-admission verdict
                              (and (fnn-lstat root-path) t))))
    (cond ((eq admission :proceed))
          ((equal admission '(:refused :interrupted-init))
           (fnn-refuse "init refused reason=interrupted-init stage=~a: no store was published at ~a; remove ~a and run init again"
                       leftover root-path leftover))
          ((equal admission '(:refused :publication-uncertain))
           (fnn-refuse "init refused reason=publication-uncertain stage=~a: an earlier init may have published ~a; run recover, then remove ~a"
                       leftover root-path leftover))
          ((equal admission '(:refused :store-path-exists))
           (fnn-refuse "init refused reason=store-path-exists: ~a exists; init creates the store directory and never fills an existing one"
                       root-path))
          (t (fnn-fault "ACL2 returned a malformed init admission")))
    (let* ((stage-root (format nil "~a.init-~a" root-path (fnn-random-hex 6)))
           (stage (make-fnn-store stage-root :writable t :fault (fnn-init-test-fault)))
           (logp (fnn-core 'fn-store-profile-logp
                           (fnn-metadata-config-decode (fnn-metadata-config-frame profile))))
           (record (fnn-bridge-config-initial (or groups +fnn-default-groups+))))
      (fnn-staged-publication
       "init" stage root-path
       (if logp
           ;; books/store-init-log-publication.lisp fn-bs-init-log-files, in
           ;; its order: the profile, the generation-1 configuration record,
           ;; the segment's ACL2 extent of zeros.  No allocator file and no
           ;; transactions/ (a format-9 store reads neither).
           (list (cons (fnn-config-path stage) (fnn-metadata-config-frame profile))
                 (cons (fnn-config-record-path stage 1) record)
                 (cons (fnn-segment-path stage)
                       (fnn-make-octets (fnn-nat (fnn-core 'fn-store-log-initial-extent)))))
           ;; fn-bs-init-pub-files, in its order.
           (list (cons (fnn-config-path stage) (fnn-metadata-config-frame profile))
                 (cons (fnn-frontier-path stage) (fnn-metadata-frontier-frame 0))
                 (cons (fnn-config-record-path stage 1) record)))
       0
       (lambda (stage) (fnn-record-filesystem-at-init stage profile policy))
       (if logp
           (fnn-core 'fn-bs-init-log-subdir-names)
           '("transactions" "staging" "config")))
      ;; SEC-006: the node's key files, as `fnn-command-init' writes them,
      ;; once the store is published (outside fn-bs-init-pub-program: a
      ;; death between the two leaves the complete store without
      ;; keys/node-secret.key, which `run' refuses by name until
      ;; `store ROOT node-secret create'; PKT-694).
      (let ((published (make-fnn-store root-path :writable t)))
        (unwind-protect
             (progn (fnn-acquire published)
                    (fnn-node-secret-create published nil :keep))
          (fnn-store-close published)))
      (fnn-out "initialized ~a" root-path)
      +fnn-exit-ok+)))

(defun fnn-command-developer-init (root words)
  "Developer `store ROOT init [PROFILE-FLAGS] [GROUP ...]': ACL2 reads the
words (books/native-operator.lisp fn-nop-developer-init) with the operator's
profile grammar over the development base; a flag-shaped word left among the
groups is refused, never created as a group."
  (let ((plan (fnn-core 'fn-nop-developer-init words)))
    (unless (and (consp plan) (member (first plan) '(:init :refused)))
      (fnn-fault "ACL2 returned a malformed developer init plan"))
    (if (eq (first plan) :refused)
        (error 'fnn-usage-error
               :message (format nil "init refused: ~(~a~)" (second plan)))
      (fnn-command-init root (second plan) (third plan)))))

(defconstant +fnn-log-history-prefix-chunk+ 1024
  "Covered-prefix records encoded per ACL2 call while a verb streams the
history (a work quantum per call, never a bound on the store).")

(defun fnn-log-history-each (store fn)
  "Call FN on each record of a format-9 STORE's history, in log order, as
octets, read as the open read it (fnn-recover-log, its plan in
fnn-store-log-history): when a checkpoint covers dropped segments, the
covered prefix encoded from the loaded checkpoint's rows a chunk at a time
(fn-store-sco-prefix-octets-range); then each closed segment the open scanned,
read again from disk with the chain carried from the scan's genesis
(fnn-log-read-closed-segment); then the active segment's committed records
(the log kernel: the open's, and every batch fenced since).  No list of the
history is built.  After a rotation in this process (a checkpoint's
P-ROTATE, and then its drop), or once the loaded checkpoint was released,
the plan no longer names the history: that read is a fault, never a shorter
history."
  (destructuring-bind (prefixp closed genesis active) (fnn-log-history-plan store)
    (declare (ignore active))
    (when prefixp
      (let ((s (second (fnn-store-open-mode store))))
        (loop for start from 0 below s by +fnn-log-history-prefix-chunk+ do
          (dolist (octets (fnn-core-arena-state 'fn-store-sco-prefix-octets-range start
                                                (min +fnn-log-history-prefix-chunk+ (- s start))))
            (funcall fn (fnn-as-octets octets))))))
    (let ((unit (fnn-store-log-unit)) (max (fnn-store-log-max store)))
      (dolist (k closed)
        (multiple-value-bind (records last)
            (fnn-log-read-closed-segment store k genesis unit max)
          (dolist (record records) (funcall fn (fnn-octets record)))
          (setq genesis last))))
    (dolist (record (fnn-core 'fn-lgk-committed (fnn-log-kernel (fnn-store-log store))))
      (funcall fn (fnn-octets record)))))

(defun fnn-log-history-records (store)
  "A format-9 STORE's history as a list, each record's exact octets in log
order (`fnn-log-history-each' collected), for the verbs that take the whole
list (checkpoint publish, export, the offline configure's fallback)."
  (let ((records nil))
    (fnn-log-history-each store (lambda (record) (push record records)))
    (nreverse records)))

(defun fnn-log-history-plan (store)
  "The open's plan (fnn-store-log-history), checked against the log: a fault
before the open or after a rotation in this process."
  (let ((log (fnn-store-log store)) (plan (fnn-store-log-history store)))
    (unless (and log plan)
      (fnn-fault "a format-9 store's history was read before its open"))
    (unless (eql (fnn-log-index log) (fourth plan))
      (fnn-fault "the log rotated since the open; its history is the new checkpoint's"))
    (when (eq (first plan) :released)
      (fnn-fault "the checkpoint holding the log's covered prefix was released after the open"))
    plan))

(defun fnn-log-history-release-prefix (store)
  "The loaded checkpoint was released (fn-store-sco-clear): a covered prefix
can no longer be read from its rows."
  (let ((plan (fnn-store-log-history store)))
    (when (and plan (first plan))
      (setf (first (fnn-store-log-history store)) :released))))

(defun fnn-log-closed-records (store)
  "The records of the closed segments the open scanned, read again (octet
vectors, in order)."
  (destructuring-bind (prefixp closed genesis active) (fnn-log-history-plan store)
    (declare (ignore prefixp active))
    (let ((unit (fnn-store-log-unit)) (max (fnn-store-log-max store)) (parts nil))
      (dolist (k closed)
        (multiple-value-bind (records last)
            (fnn-log-read-closed-segment store k genesis unit max)
          (push (mapcar #'fnn-octets records) parts)
          (setq genesis last)))
      (apply #'append (nreverse parts)))))

(defun fnn-history-records (store)
  "The history of the acquired and opened STORE as the open reads it, each
record's exact octets in sequence order.  Format 9 (the one store format,
D34): the record log as the open read it (`fnn-log-history-records').  The
per-file branch (the selected pack's records and then the suffix files,
`fnn-durable-records' and the pack callbacks, as `fnn-recover-full-replay')
is the per-file open's twin; the open refuses a format-8 profile by name
(books/store-profile-open.lisp :store-format), so it is
unreachable-in-composition with that open (PKT-COL-1's remainder).  The open no longer keeps them
(PKT-823): a verb that needs the records' octets after `fnn-open-live-store'
reads them here, under the lock the open took, which no writer shares, so
they are the records the open replayed.  No file length or directory listing
stands in for a record."
  (if (fnn-store-logp store)
      (fnn-log-history-records store)
      (multiple-value-bind (physical lower sequences)
          (fnn-durable-records store (funcall *fnn-pack-lower-bound-callback* store))
        (funcall *fnn-pack-recover-callback* store physical sequences lower))))

(defun fnn-history-last-record (store)
  "The history's newest record's octets, or NIL when there is none: the newest
transaction file past the selected pack (the history is the pack's records and
then those files, `fnn-history-records'), unframed as the open unframes it;
without such a file, the last of the pack's reconstruction.  Read after the
open, under its lock, so it is the record the open replayed last.  Format
9: the log kernel's last committed record, else the last closed segment's
the open scanned, else (a checkpoint open whose suffix is empty) the
covered prefix's last (fn-store-sco-last-record-octets)."
  (when (fnn-store-logp store)
    (return-from fnn-history-last-record
      (let ((last (car (last (fnn-core 'fn-lgk-committed
                                       (fnn-log-kernel (fnn-store-log store)))))))
        (cond (last (fnn-octets last))
              ((car (last (fnn-log-closed-records store))))
              ((first (fnn-log-history-plan store))
               (let ((octets (fnn-core-arena-state 'fn-store-sco-last-record-octets)))
                 (and octets (fnn-as-octets octets))))
              (t nil)))))
  (let ((files (fnn-transaction-files store (funcall *fnn-pack-lower-bound-callback* store))))
    (if files
        (let ((path (cdr (car (last files)))))
          (fnn-check-regular path)
          (fnn-unframe (fnn-read-regular-bounded
                        path (fnn-core 'fn-store-profile-read-bound (fnn-store-config store)))))
        (car (last (fnn-history-records store))))))

(defun fnn-committed-history (store)
  "`fnn-history-records' with the committed-history marker checked against
their count (`fnn-check-history-marker'), for a reader that has not opened
STORE through `fnn-recover'.  The caller holds STORE's writer lock for as
long as it uses the result.  A format-9 store has no marker object (M := D:
the log's last complete entry is the committed history, `fnn-mark-committed'),
so its history is the log's, unchecked here."
  (let ((records (fnn-history-records store)))
    (unless (fnn-store-logp store)
      (fnn-check-history-marker store (length records)))
    records))

;;; `store export DIR' and `store import DIR' (D34, books/store-export.lisp).

(defun fnn-archive-write-file (path octets)
  "Create PATH (it must not exist), write OCTETS, fence it."
  (let ((fd (fnn-open path (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                    +fnn-o-nofollow+)
                      #o600)))
    (unwind-protect (progn (fnn-write-all fd (fnn-octets octets)) (fnn-fsync-file fd))
      (fnn-close fd))))

(defun fnn-archive-name (octets)
  (let ((name (fnn-octets-string (fnn-octets octets))))
    (when (or (zerop (length name)) (search ".." name) (char= (char name 0) #\/))
      (fnn-fault "ACL2 returned an invalid archive entry name"))
    name))

(defun fnn-command-store-export (root dir)
  "Offline: write the archive of ROOT's committed history to DIR (it must not
exist).  The store is acquired under its writer lock (a running owner refuses
this), the history is the one the open reads, read after the open
(`fnn-committed-history': on format 9 the log as the open read it, the
checkpoint's covered prefix then the scanned segments,
`fnn-log-history-records'), and the entries and MANIFEST are ACL2's
(fn-sxp-entries, fn-sxp-manifest)."
  (when (fnn-lstat dir)
    (fnn-refuse "export refused reason=archive-exists"))
  (multiple-value-bind (store count) (fnn-open-live-store root nil)
    (declare (ignore count))
    (unwind-protect
         (let* ((profile (fnn-octet-list (fnn-read-regular-bounded (fnn-config-path store) 16384)))
                ;; Format 9 holds no frontier file: the archive carries the
                ;; frontier the log derived at this open (ACL2's frame of
                ;; fn-store-log-next-txid), so the entry means what a
                ;; format-8 archive's does.
                (frontier (fnn-octet-list
                           (if (fnn-store-logp store)
                               (fnn-metadata-frontier-frame (fnn-store-frontier store))
                             (fnn-read-regular-bounded (fnn-frontier-path store) 4096))))
                (configs (mapcar (lambda (pair) (cons (car pair) (fnn-octet-list (cdr pair))))
                                 (fnn-config-record-observation store)))
                ;; The history the open recovered, read after it: on format
                ;; 9 the checkpoint's records, then the log's scan from the
                ;; segment its F row names (T8: the whole chain).
                (records (mapcar (lambda (record)
                                   (cons (fnn-bridge-record-sequence record)
                                         (fnn-octet-list record)))
                                 (fnn-committed-history store)))
                (entries (fnn-core 'fn-sxp-entries profile frontier configs records))
                (manifest (fnn-core 'fn-sxp-manifest entries)))
           (unless (and (consp entries) (fnn-octet-list-p manifest))
             (fnn-fault "ACL2 returned a malformed archive"))
           (fnn-mkdir dir #o700)
           (fnn-mkdir (fnn-join dir "config") #o700)
           (fnn-mkdir (fnn-join dir "records") #o700)
           (dolist (entry entries)
             (fnn-archive-write-file (fnn-join dir (fnn-archive-name (car entry))) (cdr entry)))
           (fnn-archive-write-file (fnn-join dir "MANIFEST") manifest)
           (fnn-fsync-dir (fnn-join dir "records"))
           (fnn-fsync-dir (fnn-join dir "config"))
           (fnn-fsync-dir dir)
           (fnn-out "exported records=~d configuration=~d" (length records) (length configs))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-archive-read-dir (dir sub)
  (sort (copy-list (fnn-list-directory (fnn-join dir sub))) #'string<))

;; books/store-import-publication.lisp fn-bs-imp-program's cuts, in program
;; order.  The per-subdirectory and per-file cuts repeat; `fnn-at' fires at
;; every match, so the selected cut stops the import at its first occurrence.
(defparameter +fnn-import-model-cuts+
  '("import-stage-created" "import-subdir-created" "import-file-created"
    "import-file-written" "import-file-durable" "import-subdir-durable"
    "import-staged-durable" "import-validated" "import-published"
    "import-durable"))

(defun fnn-import-test-fault ()
  "Developer-only FN_NATIVE_IMPORT_FAULT=MODEL-CUT:eio|kill selector for
fn-bs-imp-program's cuts."
  (let ((raw (fnn-developer-selector "FN_NATIVE_IMPORT_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_IMPORT_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (member label +fnn-import-model-cuts+ :test #'string=)
            (fnn-fault "unknown FN_NATIVE_IMPORT_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_IMPORT_FAULT action: ~a" action)))
                "developer-only native import fault"))))))

(defun fnn-pub-at (store kind suffix)
  "The cut KIND-SUFFIX of fn-bs-imp-program (KIND \"import\") or of
fn-bs-init-pub-program (KIND \"init\": the same program, init's cut names)."
  (fnn-at store (intern (string-upcase (fnn-concat kind "-" suffix)) :keyword)))

(defun fnn-import-write-file (store path octets &optional (kind "import"))
  "fn-bs-imp-file-steps: create PATH (it must not exist), write OCTETS, fence
it, with the program's cut after each of the three syscalls."
  (let ((fd (fnn-open path (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                    +fnn-o-nofollow+)
                      #o600)))
    (unwind-protect
         (progn
           (fnn-pub-at store kind "file-created")
           (fnn-write-all fd (fnn-octets octets))
           (fnn-pub-at store kind "file-written")
           (fnn-fsync-file fd)
           (fnn-pub-at store kind "file-durable"))
      (fnn-close fd))))

#+linux
(sb-alien:define-alien-routine ("renameat2" fnn-%import-renameat2)
    sb-alien:int
  (old-directory sb-alien:int) (old-name sb-alien:c-string)
  (new-directory sb-alien:int) (new-name sb-alien:c-string)
  (flags sb-alien:unsigned-int))

(defun fnn-rename-no-replace (old new)
  "Rename OLD onto NEW without replacing an existing NEW (fn-bs-imp-program's
:rename-dir-noreplace).  NIL once renamed; :EXISTS when NEW exists and nothing
was renamed; :UNSUPPORTED when the filesystem refuses the no-replace flag and
nothing was renamed.  Any other failure is an fnn-os-error, whose outcome the
caller does not know."
  #+linux
  (let ((result (fnn-%import-renameat2 -100 old -100 new 1)))   ; AT_FDCWD, RENAME_NOREPLACE
    (if (>= result 0)
        nil
      (let ((errno (sb-alien:get-errno)))
        (cond ((= errno sb-posix:eexist) :exists)
              ((or (= errno sb-posix:einval) (= errno sb-posix:enosys)) :unsupported)
              (t (fnn-os-fail errno new))))))
  ;; No renameat2 here (OpenBSD).  The caller holds NEW.lock
  ;; (fnn-publication-lock) for the whole program; NEW is observed absent
  ;; under it immediately before rename(2), which itself refuses a
  ;; non-empty directory and a non-directory at NEW.  Residual: a process
  ;; that does not take the lock creates an EMPTY directory at NEW between
  ;; the lstat and the rename, and it is replaced (docs/operator.md: an
  ;; operator constraint).  The OpenBSD evidence is scoped separately.
  #-linux
  (if (fnn-lstat new)
      :exists
    (handler-case (progn (sb-posix:rename old new) nil)
      (sb-posix:syscall-error (e)
        (let ((errno (sb-posix:syscall-errno e)))
          (if (member errno (list sb-posix:eexist sb-posix:enotempty sb-posix:enotdir))
              :exists
            (fnn-os-fail errno new)))))))

(defun fnn-publication-lock (root-path)
  "Where rename(2) has no no-replace flag (OpenBSD), the publication program
(import, init) holds an exclusive advisory lock on the sibling ROOT.lock for
its whole run, and fnn-rename-no-replace re-checks ROOT's absence under it
immediately before rename(2).  The residual is a process that does not take
the lock and creates an EMPTY directory at ROOT in that window: rename(2)
replaces it.  That is an operator constraint (docs/operator.md): nothing but
fn creates ROOT.  A second fn publication is refused, never waited on.  NIL
on Linux, where renameat2(RENAME_NOREPLACE) refuses any existing ROOT."
  #+linux (declare (ignore root-path))
  #+linux nil
  #-linux
  (let ((fd (fnn-open (fnn-concat root-path ".lock")
                      (logior sb-posix:o-rdwr sb-posix:o-creat +fnn-o-nofollow+) #o600)))
    (handler-case (progn (unless (fnn-regular-p (fnn-fstat fd))
                           (fnn-fault "refusing non-regular publication lock ~a.lock" root-path))
                         (fnn-flock fd (logior +fnn-lock-ex+ +fnn-lock-nb+))
                         fd)
      (fnn-os-error ()
        (fnn-close fd)
        (fnn-refuse "publication refused reason=publication-locked: another fn process holds ~a.lock"
                    root-path))
      (error (e) (fnn-close fd) (error e)))))

(defun fnn-publication-unlock (fd)
  (when fd
    (ignore-errors (fnn-flock fd +fnn-lock-un+))
    (fnn-close fd)))

(defun fnn-import-leftover-stage (root-path &optional (kind "import"))
  "The path of the first entry of ROOT-PATH's parent named BASENAME.KIND-*
(BASENAME being ROOT-PATH's last component), or NIL.  The directory is
streamed and one name retained."
  (let* ((parent (fnn-parent root-path))
         (slash (position #\/ root-path :from-end t))
         (prefix (fnn-concat (if slash (subseq root-path (1+ slash)) root-path)
                             "." kind "-"))
         (found nil))
    (when (fnn-lstat parent)
      (let ((dir (fnn-posix (parent) (sb-posix:opendir parent))))
        (unwind-protect
             (loop
               (let ((entry (fnn-posix (parent) (sb-posix:readdir dir))))
                 (when (sb-alien:null-alien entry) (return))
                 (let ((name (sb-posix:dirent-name entry)))
                   (when (and (> (length name) (length prefix))
                              (string= prefix name :end2 (length prefix)))
                     (setq found name)
                     (return)))))
          (fnn-posix (parent) (sb-posix:closedir dir)))))
    (and found (fnn-join parent found))))

(defun fnn-import-classify (stage-root root-path)
  "ACL2's reading (fn-bs-imp-classify) of whether STAGE-ROOT and ROOT-PATH
are present."
  (let ((verdict (fnn-core 'fn-bs-imp-classify
                           (and (fnn-lstat stage-root) t)
                           (and (fnn-lstat root-path) t))))
    (unless (member verdict '(:no-store :not-published :publication-uncertain :store-present))
      (fnn-fault "ACL2 returned a malformed import classification"))
    verdict))

(defun fnn-command-store-import (root dir request &optional policy)
  "Offline: make a new store at ROOT (it must not exist) from the archive at
DIR.  ACL2's plan (fn-sxp-import-plan) checks the MANIFEST, the order and the
profile (REQUEST's field overrides over the archive's) and refuses by name;
the host writes the plan's files into ROOT.import-XXXX as init writes its
files, opens that store the ordinary way (full replay, marker catch-up), and
publishes it by a no-replace rename onto ROOT only when the open admitted
it, then fences ROOT's parent: books/store-import-publication.lisp
fn-bs-imp-program, step for step, with its cuts (+fnn-import-model-cuts+).
A staged directory left beside ROOT by an earlier import is classified by
fn-bs-imp-classify and refused by name before anything is written.  An OS
error before the rename is a known failure (exit 1, the staged directory
named); at or after it the outcome is uncertain (exit 3) and the observed
presence of the two names is classified by fn-bs-imp-classify."
  (let* ((root-path (string-right-trim "/" root))
         (leftover (fnn-import-leftover-stage root-path)))
    (when leftover
      (case (fnn-import-classify leftover root-path)
        (:not-published
         (fnn-refuse "import refused reason=interrupted-import stage=~a: no store was published; remove ~a and import again"
                     leftover leftover))
        (:publication-uncertain
         (fnn-refuse "import refused reason=publication-uncertain stage=~a: run recover on ~a, then remove ~a"
                     leftover root-path leftover))
        (t (fnn-fault "ACL2 classified a present staged directory as absent")))))
  (when (fnn-lstat root)
    (fnn-refuse "import refused reason=store-exists"))
  (let* ((profile (fnn-octet-list (fnn-read-regular-bounded (fnn-join dir "profile") 16384)))
         (frontier (fnn-octet-list (fnn-read-regular-bounded (fnn-join dir "frontier") 4096)))
         (config-names (fnn-archive-read-dir dir "config"))
         (record-names (fnn-archive-read-dir dir "records"))
         ;; Work bounds, not data bounds: one record file is read within the
         ;; archive profile's record bound (the bound it was committed under),
         ;; and the MANIFEST within one line per entry.
         (record-bound (fnn-core 'fn-store-profile-read-bound
                                 (fnn-core 'fn-bs-config-decode profile)))
         (manifest (fnn-octet-list
                    (fnn-read-regular-bounded
                     (fnn-join dir "MANIFEST")
                     (* 512 (+ 2 (length config-names) (length record-names))))))
         (configs (mapcar (lambda (name)
                            (cons name (fnn-octet-list
                                        (fnn-read-regular-bounded
                                         (fnn-join (fnn-join dir "config") name)
                                         +fnn-config-record-bytes+))))
                          config-names))
         (records (mapcar (lambda (name)
                            (let ((octets (fnn-read-regular-bounded
                                           (fnn-join (fnn-join dir "records") name)
                                           record-bound)))
                              (cons (fnn-bridge-record-sequence octets)
                                    (fnn-octet-list octets))))
                          record-names))
         (plan (fnn-core 'fn-sxp-import-plan manifest profile frontier configs records
                         (or request '(:current nil)))))
    (unless (and (consp plan) (member (first plan) '(:import :refused)))
      (fnn-fault "ACL2 returned a malformed import plan"))
    (when (eq (first plan) :refused)
      (fnn-refuse "import refused reason=~(~a~)~@[ ~a~]" (second plan)
                  (let ((detail (third plan)))
                    (cond ((null detail) nil)
                          ((fnn-octet-list-p detail) (fnn-octets-string (fnn-octets detail)))
                          ((keywordp detail) (string-downcase (symbol-name detail)))
                          (t detail)))))
    (destructuring-bind (values frontier configs records) (rest plan)
      (let* ((root-path (string-right-trim "/" root))
             (stage-root (format nil "~a.import-~a" root-path (fnn-random-hex 6)))
             (stage (make-fnn-store stage-root :writable t :fault (fnn-import-test-fault)))
             (logp (fnn-core 'fn-store-profile-logp values)))
        (fnn-staged-publication
         "import" stage root-path
         ;; fn-sxp-import-plan's files, in its order.  The plan's profile is
         ;; format 9 (fn-sxp-log-profile): the records go into the log
         ;; below, not into transaction files.
         (append (list (cons (fnn-config-path stage) (fnn-core 'fn-bs-config-encode values))
                       (cons (fnn-frontier-path stage) frontier))
                 (mapcar (lambda (config)
                           (cons (fnn-join (fnn-config-dir stage) (car config)) (cdr config)))
                         configs)
                 (unless logp
                   (mapcar (lambda (record)
                             (cons (fnn-join (fnn-transactions stage)
                                             (fnn-transaction-name (car record)))
                                   (fnn-frame (fnn-octets (cdr record)))))
                           records)))
         (length records)
         ;; The imported store is a new store on the filesystem ROOT is on
         ;; (its stage is ROOT's sibling): its record, under the import's
         ;; policy (fn-smid-init-policy: 1), before the ordinary open.  On
         ;; format 9 the stage's segment is then written from the genesis
         ;; (fnn-log-write-history) before that open admits it.
         (lambda (stage)
           (fnn-record-filesystem-at-init stage request policy)
           (when logp
             (fnn-log-init-segment stage)
             (fnn-log-write-history stage values records)))
         ;; The staged tree's subdirectories: a format-9 store's are init's
         ;; (journal/ among them: fnn-log-init-segment's caller makes it
         ;; since log-2's initializer program).
         (if logp
             (fnn-core 'fn-bs-init-log-subdir-names)
             '("transactions" "staging" "config")))
        (fnn-out "imported records=~d configuration=~d" (length records) (length configs))
        +fnn-exit-ok+))))

(defun fnn-staged-publication (kind stage root-path files record-count
                               &optional record-filesystem
                                 (subdirs '("transactions" "staging" "config")))
  "Build the store STAGE (at ROOT-PATH.KIND-XXXX) from FILES, a list of
(PATH . OCTETS) in plan order, admit it through the ordinary open (it must
replay RECORD-COUNT records), and publish it at ROOT-PATH by a no-replace
rename, then fence ROOT-PATH's parent: books/store-import-publication.lisp
fn-bs-imp-program step for step, with its cuts (KIND \"import\") or
books/store-init-publication.lisp fn-bs-init-pub-program's (KIND \"init\":
the same steps, init's cut names).  An OS error before the rename is a known
failure (exit 1, the staged directory named); at or after it the outcome is
uncertain (exit 3) and the observed presence of the two names is classified
by fn-bs-imp-classify.  SUBDIRS are the staged tree's subdirectories in
the plan's order (a format-9 init's are ACL2's fn-bs-init-log-subdir-names:
books/store-init-log-publication.lisp)."
  (let* ((stage-root (fnn-store-root stage))
         (parent (fnn-parent root-path))
         (lock nil)
         (created nil)
         (attempted nil))
    (handler-case
        (unwind-protect
             (progn
               ;; OpenBSD has no renameat2: the whole program holds an
               ;; exclusive advisory lock on ROOT.lock and re-checks ROOT's
               ;; absence under it immediately before rename(2).
               (setq lock (fnn-publication-lock root-path))
               ;; fn-bs-imp-stage-steps
               (fnn-mkdir stage-root #o700)
               (setq created t)
               (fnn-pub-at stage kind "stage-created")
               ;; fn-bs-imp-subdir-steps
               (dolist (sub subdirs)
                 (fnn-mkdir (fnn-join stage-root sub) #o700)
                 (fnn-pub-at stage kind "subdir-created"))
               ;; fn-bs-imp-files-steps
               (dolist (file files)
                 (fnn-import-write-file stage (car file) (cdr file) kind))
               ;; fn-bs-imp-fence-steps
               (dolist (sub subdirs)
                 (fnn-fsync-dir (fnn-join stage-root sub))
                 (fnn-pub-at stage kind "subdir-durable"))
               ;; fn-bs-imp-seal-steps
               (fnn-fsync-dir stage-root)
               (fnn-pub-at stage kind "staged-durable")
               ;; The filesystem record (STO-031) the ordinary open checks,
               ;; written into the sealed stage by RECORD-FILESYSTEM (the
               ;; stage is ROOT's sibling, on ROOT's filesystem).
               (when record-filesystem (funcall record-filesystem stage))
               ;; fn-bs-imp-publication-program.  The ordinary open admits
               ;; the staged store or refuses it.
               (multiple-value-bind (opened replayed) (fnn-open-live-store stage-root t)
                 (unwind-protect
                      (unless (= replayed record-count)
                        (fnn-fault "the staged store replayed ~d of ~d records"
                                   replayed record-count))
                   (fnn-store-close opened)))
               (fnn-pub-at stage kind "validated")
               (setq attempted t)
               (case (fnn-rename-no-replace stage-root root-path)
                 ((nil))
                 (:exists
                  (fnn-refuse "~a refused reason=store-exists stage=~a: remove ~a"
                              kind stage-root stage-root))
                 (:unsupported
                  (fnn-refuse-io "~a failed before publication: the filesystem refuses a no-replace rename; remove ~a"
                                 kind stage-root))
                 (t (fnn-fault "invalid no-replace rename outcome")))
               (fnn-pub-at stage kind "published")
               (fnn-fsync-dir parent)
               (fnn-pub-at stage kind "durable"))
          (fnn-publication-unlock lock))
      (fnn-os-error (e)
        (cond ((not attempted)
               (fnn-refuse-io "~a failed before publication: ~a; ~:[no staged directory was left~;remove ~a~]"
                              kind e created stage-root))
              (t
               (let ((verdict (handler-case (fnn-import-classify stage-root root-path)
                                (fnn-os-error () nil))))
                 (fnn-indeterminate "~a publication uncertain state=~(~a~) stage=~a root=~a: ~a"
                                    kind (or verdict "unobserved") stage-root root-path e))))))))

(defparameter +fnn-cli-faults+
  (list (cons "prepublish" (list :record-staged-durable 'fnn-store-error
                                 "injected known abort before publication"))
        ;; On the record log (format 9) the same outcomes arm the log's
        ;; cuts: after the batch's barrier (the record durable) and at the
        ;; batch's write before its barrier.
        (cons "postpublish" (list '(:record-attempted :log-fenced) 'fnn-store-indeterminate
                                  "indeterminate injected failure after final publication"))
        (cons "frontierbarrier" (list :frontier-barrier 'fnn-os-error
                                      "injected allocator directory barrier failure"))
        (cons "recordbarrier" (list '(:record-barrier :log-written) 'fnn-os-error
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

;; The log route's commit cuts (format 9; tests/campaign/native_cuts.py
;; POST_LOG_CUTS), in a served batch's order: each member's finish (its
;; in-memory completion, fnn-finish's two cuts), then P-BATCH's append and
;; barrier (fnn-log-commit-open-batch).  A batch of one runs the append and
;; the barrier before its finish.
(defparameter +fnn-post-log-model-cuts+
  '(:finish-consumed :finish-durable :log-written :log-fenced))

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
                      (member point +fnn-post-log-model-cuts+)
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
             ;; ACL2's article verdict: the count gate and the history gate
             ;; at this article's own figure (fn-sbud-article-verdict-at).
             (unless (eq (fnn-core-state 'fn-store-sn-article-verdict
                                         (fnn-store-config store) (length payload)
                                         (length codes))
                         :admissible)
               (fnn-refuse "store budget refuses the article (transaction count or history bound)"))
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
  (multiple-value-bind (store count) (fnn-open-live-store root t (fnn-recovery-test-fault))
    (unwind-protect
         (multiple-value-bind (report code) (fnn-anchor-report store)
           (fnn-out "recovered transactions=~d articles=~d ~a ~a ~a"
                    count (fnn-bridge-article-count)
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
                               (or (stringp (cdr entry))
                                   (and (integerp (cdr entry)) (>= (cdr entry) 0)))))
                        report))
      (fnn-fault "ACL2 returned a malformed profile report"))
    (fnn-out "profile~{ ~a=~a~}"
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
               used budget bytes-used history reserved capacity)
      ;; PKT-707: the capacity in plain words, rendered by ACL2.
      (fnn-out "~a" (fnn-octets-string
                     (fnn-octets (fnn-core 'fn-nls-capacity-line headroom)))))))

(defun fnn-store-observation (store)
  "What this process observed at its own open, which the status report names:
the staging orphans, whether their listing stopped at its bound, and how
the Store was opened (checkpoint or full replay, and why), and one clock
observation, from which ACL2 derives the instant the retention rule is
measured at (books/native-live-status.lisp `fn-nls-reclaim-words')."
  (list (fnn-store-orphans store) (fnn-store-orphans-more store)
        (fnn-store-open-mode store)
        (fnn-store-prepare-observation)
        (fnn-state-checkpoint-file-observation store)))

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
           ;; The selected pack chain (books/checkpoint-pack-chain via
           ;; host/native/checkpoint.lisp): ACL2 computes the links and the
           ;; boundary; the offline report does not carry them yet.
           (when (and (eq kind :status) *fnn-pack-status-callback*)
             (fnn-out "~a" (funcall *fnn-pack-status-callback* store)))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-status (root)
  (fnn-filesystem-durability-warn root)
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

(defun fnn-probe-article (sequence size)
  "A well-formed article of exactly SIZE octets for probe record SEQUENCE: a
head naming its Message-ID, groups and Subject, a blank line, and a body of
CRLF lines of x padding the rest.  Developer fixture bytes, not a decision:
the Store and the served projection judge them like any posted article."
  (let* ((head (format nil "Message-ID: <capacity-~d@example.invalid>~c~cNewsgroups: fn.letters,fn.test~c~cSubject: capacity ~d~c~cFrom: probe@example.invalid~c~c~c~c"
                       sequence #\Return #\Newline #\Return #\Newline sequence
                       #\Return #\Newline #\Return #\Newline #\Return #\Newline))
         (octets (make-array size :element-type '(unsigned-byte 8)
                                  :initial-element (char-code #\x)))
         (at (length head)))
    (when (> (+ at 2) size) (fnn-fault "probe article head exceeds the payload"))
    (loop for i from 0 below at do (setf (aref octets i) (char-code (char head i))))
    ;; Lines of at most 76 x and CRLF; never leave one octet over.
    (loop while (< at size)
          do (let ((take (min 78 (- size at))))
               (when (= (- size at take) 1) (decf take))
               (setf (aref octets (+ at take -2)) 13
                     (aref octets (+ at take -1)) 10)
               (incf at take)))
    octets))

(defun fnn-command-probe (root count &optional articlep)
  "tests/store_capacity_probe.py's sequence in-process: commit COUNT maximum
payloads, close, reopen, and report both timings as JSON on stdout.  With
ARTICLEP (`probe N article') each payload is a well-formed article of the
same size (fnn-probe-article), so the served reader can frame it."
  (let* ((started (get-internal-real-time))
         (store (make-fnn-store root :writable t))
         (payload nil))
    (fnn-initialize store)
    (fnn-record-filesystem-at-init store :development)
    (fnn-acquire store)
    (fnn-bridge-reset)
    (fnn-recover store)
    (setq payload (make-array (fnn-config-max-payload store)
                              :element-type '(unsigned-byte 8)
                              :initial-element (char-code #\x)))
    (let ((codes (fnn-group-codes-for store +fnn-default-groups+)))
      (dotimes (sequence count)
        (let ((msgid (fnn-octets (fnn-ascii-octet-list
                                  (format nil "<capacity-~d@example.invalid>" sequence))))
              (payload (if articlep
                           (fnn-probe-article sequence (length payload))
                         payload)))
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
        (multiple-value-bind (reopened replayed) (fnn-open-live-store root nil)
          (let ((reopen-seconds (/ (- (get-internal-real-time) before)
                                   (float internal-time-units-per-second 1d0))))
            (unwind-protect
                 (progn
                   (unless (and (= replayed count) (= (fnn-bridge-article-count) count)
                                (= (fnn-bridge-pin-count) count)
                                (= (fnn-bridge-group-next 0) (1+ count))
                                (= (fnn-bridge-group-next 1) (1+ count))
                                (equalp (fnn-bridge-lookup
                                         (fnn-octets (fnn-ascii-octet-list "<capacity-0@example.invalid>")))
                                        (if articlep
                                            (fnn-probe-article 0 (length payload))
                                          payload))
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

;;; PKT-613 (PRF-231): a peer's host, dialled the way ACL2 decides.
;;; `fn-peer-dial-target' (books/peer-host.lisp) answers (:address OCTETS)
;;; for an IPv4 literal, which is dialled without a resolver; (:resolve NAME)
;;; for an RFC 1123 host name, resolved by one getaddrinfo on this attempt
;;; (nothing is cached here; the OS's resolver may cache); or (:refused
;;; :host-syntax).  A resolution that fails, or answers no IPv4 address, is
;;; FNN-PEER-DIAL-ERROR with its outcome: a named, retried condition for the
;;; feed and pull workers, never a fault.
(define-condition fnn-peer-dial-error (error)
  ((outcome :initarg :outcome :reader fnn-peer-dial-error-outcome)
   (detail :initarg :detail :initform nil :reader fnn-peer-dial-error-detail))
  (:report (lambda (c s)
             (format s "peer dial ~(~a~)~@[: ~a~]" (fnn-peer-dial-error-outcome c)
                     (fnn-peer-dial-error-detail c)))))

(defvar *fnn-peer-resolver*
  (lambda (name)
    (sb-bsd-sockets:host-ent-addresses (sb-bsd-sockets:get-host-by-name name)))
  "Resolver seam: NAME -> the IPv4 addresses getaddrinfo answers now.")

(defun fnn-peer-resolve-ipv4 (name)
  "The first IPv4 address one resolution of NAME answers."
  (let ((addresses (handler-case (funcall *fnn-peer-resolver* name)
                     (sb-bsd-sockets:name-service-error (condition)
                       (error 'fnn-peer-dial-error :outcome :unresolved
                                                   :detail (princ-to-string condition))))))
    (or (find-if (lambda (a) (= (length a) 4)) addresses)
        (error 'fnn-peer-dial-error :outcome :no-address
                                    :detail "no IPv4 address"))))

(defun fnn-peer-connect (host port &key (timeout 10))
  "Dial a configured peer HOST (an ACL2 string or octet list) on PORT."
  (let* ((octets (if (stringp host) (map 'list #'char-code host) (fnn-octet-list host)))
         (target (fnn-core 'fn-peer-dial-target octets)))
    (case (and (consp target) (first target))
      (:address
       (fnn-connect (coerce (second target) '(simple-array (unsigned-byte 8) (*)))
                    port :timeout timeout))
      (:resolve
       (fnn-connect (fnn-peer-resolve-ipv4 (map 'string #'code-char (second target)))
                    port :timeout timeout))
      (:refused (error 'fnn-peer-dial-error :outcome :host-syntax))
      (otherwise (fnn-fault "ACL2 returned a malformed peer dial target")))))

(defun fnn-peer-dial-outcome (condition)
  "The host's classification of a failed peer dial: an observation for ACL2's line."
  (typecase condition
    (fnn-peer-dial-error (fnn-peer-dial-error-outcome condition))
    (t (if (and (find-class 'fnn-tls-verify-error nil)
                (typep condition 'fnn-tls-verify-error))
           (slot-value condition 'outcome)
         (if (and (find-class 'fnn-tls-error nil) (typep condition 'fnn-tls-error))
             :tls
           :connect)))))

(defun fnn-peer-dial-report (via peer host condition)
  "Write ACL2's service-log line for one failed dial of PEER (octets) at HOST."
  (fnn-log-line (fnn-core 'fn-peer-dial-log-line via
                          (fnn-octet-list peer)
                          (if (stringp host) (map 'list #'char-code host)
                            (fnn-octet-list host))
                          (fnn-peer-dial-outcome condition))))

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

;;; Several listeners, one serialized loop (specs/bp-node-machine.md 9.1).
;;; poll(2) says which listeners have a connection waiting; the first ready
;;; one in LISTENERS order is accepted and its HANDLER runs to completion
;;; before the next poll.  No threads.  struct pollfd is {int fd; short
;;; events; short revents} (POSIX; 8 octets), written little-endian: the
;;; supported hosts (x86-64 and arm64) are little-endian, and the build
;;; refuses otherwise.
(defconstant +fnn-pollin+ 1)
(defconstant +fnn-poll-ready+ (logior 1 8 16)) ; POLLIN | POLLERR | POLLHUP

(defun fnn-poll-readable (fds timeout-ms)
  "The index in FDS of the first descriptor poll(2) reports ready, or nil
after TIMEOUT-MS milliseconds or an interrupted wait."
  (unless (member :little-endian *features*)
    (fnn-fault "fnn-poll-readable: struct pollfd is written little-endian"))
  (let* ((n (length fds))
         (buf (make-array (* 8 n) :element-type '(unsigned-byte 8)
                                  :initial-element 0)))
    (loop for fd in fds for i from 0
          do (loop for k from 0 below 4
                   do (setf (aref buf (+ (* 8 i) k)) (ldb (byte 8 (* 8 k)) fd)))
             (setf (aref buf (+ (* 8 i) 4)) +fnn-pollin+))
    (let ((ready
            (sb-sys:with-pinned-objects (buf)
              (sb-alien:alien-funcall
               (sb-alien:extern-alien
                "poll" (function sb-alien:int sb-sys:system-area-pointer
                                 sb-alien:unsigned-long sb-alien:int))
               (sb-sys:vector-sap buf) n timeout-ms))))
      (when (and (integerp ready) (> ready 0))
        (loop for i from 0 below n
              when (logtest +fnn-poll-ready+
                            (logior (aref buf (+ (* 8 i) 6))
                                    (ash (aref buf (+ (* 8 i) 7)) 8)))
                return i)))))

(defun fnn-accept-any-loop (listeners handler &optional once)
  "Run HANDLER on each connection accepted from any of LISTENERS, one at a
time; HANDLER owns and closes its socket.  With ONCE, return after one."
  (let ((fds (mapcar #'fnn-socket-fd listeners)))
    (loop
      (let ((index (fnn-poll-readable fds 1000)))
        (when index
          (funcall handler (sb-bsd-sockets:socket-accept (nth index listeners)))
          (when once (return)))))))

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

;;; The release version (VERSION at the tree root: 6.7.N, one line).  Read
;;; once while constructing the saved image, as the profile above is, and
;;; serialized into it; the packaging reads the same file for the tarball's
;;; name (packaging/release-tarball.sh).  `fn --version' prints it with the
;;; source revision recorded beside the core.
(defvar *fnn-release-version* nil)

(defun fnn-release-version-word-p (text)
  "TEXT is 6.7.N with N a decimal numeral without a leading zero."
  (and (stringp text)
       (> (length text) 4)
       (string= "6.7." text :end2 4)
       (let ((n (subseq text 4)))
         (and (every (lambda (c) (find c "0123456789")) n)
              (or (string= n "0") (char/= (char n 0) #\0))))))

(defun fnn-select-release-version (&optional (path "VERSION"))
  "Build-time: take the release version from PATH (the build runs at the
tree root), or stop the build."
  (let ((line (with-open-file (in path :direction :input :if-does-not-exist nil
                                       :external-format :latin-1)
                (and in (read-line in nil nil)))))
    (unless (fnn-release-version-word-p line)
      (error "~a does not hold a release version 6.7.N (read ~s)" path line))
    (setq *fnn-release-version* line)))

(defun fnn-release-version ()
  (or *fnn-release-version*
      (fnn-refuse "this image records no release version (built without VERSION)")))

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
    "FN_NATIVE_STATE_CHECKPOINT_FAULT" "FN_NATIVE_IMPORT_FAULT"
    "FN_NATIVE_CHECKPOINT_BUDGET_TEST"
    "FN_NATIVE_DISK_FREE"
    "FN_NATIVE_EXTENT_CACHE_TEST_OFF"
    "FN_NATIVE_CONTROL_FAULT" "FN_NATIVE_CONTROL_TEST_STOP"
    "FN_NATIVE_AUTH_ADMIN_FAULT" "FN_NATIVE_KEY_STATEMENT_FAULT"
    "FN_NATIVE_OWNER_TEST_SIGTERM" "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP"
    "FN_NATIVE_OWNER_TEST_PAUSE_BEFORE_LISTEN" "FN_NATIVE_OWNER_TEST_BARRIER_MS" "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE"
    "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT"
    "FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER" "FN_BP_TEST_DELIVER_FAULT"
    "FN_BP_TEST_PROFILE"
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
    "FN_APP_JOURNAL_TEST_FAIL" "FN_IMMUTABLE_PUBLISH_TEST_FAIL"
    "FN_PEER_TEST_STOP_AFTER_CONSUME" "FN_PEER_TEST_STOP_AFTER_CONFIGURE"
    "FN_PULL_TEST_KILL"
    "FN_NATIVE_RECLAIM_FAULT" "FN_NATIVE_CHECKPOINT_BATCH_FAULT"
    "FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH"
    "FN_NATIVE_LOG_FAULT"))

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


;;; The record log (books/store-log-programs.lisp; planning/design-2026-09-27-
;;; storage-log.md; lane w6-log-core).  One preallocated segment file.  ACL2
;;; decides every value the host writes or tests: the extent
;;; (fn-lg-extent-okp), the kernel at open from the segment's bytes
;;; (fn-lg-open-kernel over fn-lg-decode), recovery's zeroing range
;;; (fn-lg-recover-tail), each record's admission (fn-lgt-prepare: only at
;;; the kernel's next txid), the append's admission and octets
;;; (fn-lg-append-admitsp, fn-lgk-frontier, fn-lgk-append-octets) and the
;;; kernel after each step (fn-lgk-append, fn-lgk-fence, fn-lgk-fence-failed,
;;; fn-lgk-finish-one).  The host reads, writes and fences, in the order of
;;; fn-lg-recover-program, fn-lg-append-program and fn-lg-fence-program
;;; (tests/campaign/native_cuts.py LOG_CUTS, verify_log_cut_map).  No owner
;;; path calls these yet: lane w6-log-owner moves the commit onto them.

(defparameter +fnn-log-model-cuts+
  '("log-written" "log-fenced" "log-truncated" "log-recovered"
    ;; books/store-log-extend.lisp fn-lg-extend-program (fnn-log-ensure-extent).
    "log-extended" "log-extent-fenced"))

(defstruct (fnn-log (:constructor %make-fnn-log))
  path fd kernel unit max extent
  ;; The open batch's members and entry octets (fn-olr-take's COUNT and
  ;; OCTETS), the operator's bounds (fn-owb-bmax / fn-owb-omax of the live
  ;; configuration; set by the owner), and the fenced members not yet
  ;; acknowledged.
  (count 0) (octets 0) (bmax 64) (omax 67108864) (pending 0)
  ;; The txid the owner reserved for the record being published (ACL2's,
  ;; handed to fnn-log-reserve), which fn-olr-take admits at the log's next.
  (reserved nil)
  ;; The segment's index (books/store-log-segments.lisp): the active one of
  ;; the store; fnn-log-rotate moves to the next.
  (index 1)
  ;; The pipelined commit (lane log-2; books/owner-commit-pipeline.lisp):
  ;; the kernel value changes only under LOCK, because the syncer thread's
  ;; fence (fnn-log-sync-sealed-batch) runs while the owner prepares the
  ;; next batch behind it.  SEALED the members of the batch in flight;
  ;; SYNC-STATE :idle, :syncing (a sealed batch awaits its barrier),
  ;; :fenced or :failed (the syncer's word, until the COMPLETE consumes it);
  ;; SYNC-CV signalled when the syncer returns.
  (lock (sb-thread:make-mutex :name "fn log kernel"))
  (sealed 0) (sync-state :idle)
  (sync-cv (sb-thread:make-waitqueue :name "fn log sync")))

(defmacro fnn-log-with-kernel ((log) &body body)
  "BODY under the log's kernel lock (recursive: a kernel step may call another)."
  `(sb-thread:with-recursive-lock ((fnn-log-lock ,log)) ,@body))

(defun fnn-log-at (point)
  "A developer-image cut: FN_NATIVE_LOG_FAULT=NAME (a +fnn-log-model-cuts+
name) kills the process at NAME with SIGKILL, so no cleanup runs."
  (let ((armed (fnn-developer-selector "FN_NATIVE_LOG_FAULT")))
    (when (and armed (string= armed (string-downcase (symbol-name point))))
      (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
      (fnn-fault "test SIGKILL did not terminate the process"))))

(defun fnn-log-pwrite (fd offset octets)
  "The one positioned write of OCTETS at OFFSET: lseek, then write(2) to
completion (fnn-write-range)."
  (let ((data (fnn-octets octets)))
    (fnn-posix () (sb-posix:lseek fd offset sb-posix:seek-set))
    (fnn-write-range fd data 0 (length data))))

(defun fnn-log-fdatasync (fd)
  "The log's barrier.  fdatasync(2) on Linux: an append inside the
preallocated extent changes no size and no allocation, so it fences exactly
what the byte model's fn-bs-fsync-file fences (an A-HOST condition of the
qualification profile).  Elsewhere the platform's durable barrier."
  #+linux
  (when (minusp (sb-alien:alien-funcall
                 (sb-alien:extern-alien "fdatasync" (function sb-alien:int sb-alien:int))
                 fd))
    (fnn-os-fail (sb-alien:get-errno)))
  #-linux
  (fnn-durable-barrier fd)
  nil)

(defun fnn-log-preallocate (fd extent &optional (from 0))
  "Zero octets allocated over [FROM, EXTENT) of the segment: posix_fallocate
on Linux (its allocated range reads zeros: A-HOST), zeros written elsewhere
(OpenBSD has no fallocate).  FROM is the old extent when an existing segment
grows (fnn-log-ensure-extent): the octets before it are the log and are never
written here."
  #+linux
  (let ((r (sb-alien:alien-funcall
            (sb-alien:extern-alien "posix_fallocate"
                                   (function sb-alien:int sb-alien:int
                                             sb-alien:long sb-alien:long))
            fd from (- extent from))))
    (unless (zerop r) (fnn-os-fail r)))
  #-linux
  (let ((zeros (fnn-make-octets (min (- extent from) 65536))) (at from))
    (fnn-posix () (sb-posix:lseek fd from sb-posix:seek-set))
    (loop while (< at extent) do
      (let ((n (min (length zeros) (- extent at))))
        (fnn-write-range fd zeros 0 n)
        (incf at n)))))

(defun fnn-log-parent (path)
  (let ((slash (position #\/ path :from-end t)))
    (cond ((null slash) ".") ((zerop slash) "/") (t (subseq path 0 slash)))))

(defun fnn-log-open-segment (path extent unit &optional read-only)
  "The segment's descriptor.  Absent and not READ-ONLY: created, preallocated
to EXTENT, fenced with its directory.  Present: a regular file of exactly
EXTENT octets, or refused."
  (unless (fnn-core 'fn-lg-extent-okp extent unit)
    (error 'fnn-usage-error
           :message (format nil "log extent ~a is not a positive number of ~a-octet units"
                            extent unit)))
  (let ((st (fnn-check-regular path)))
    (cond (st
           (let ((fd (fnn-open path (logior (if read-only sb-posix:o-rdonly sb-posix:o-rdwr)
                                            +fnn-o-nofollow+))))
             (unless (= (sb-posix:stat-size (fnn-fstat fd)) extent)
               (fnn-close fd)
               (fnn-refuse "log segment ~a is not ~a octets long" path extent))
             fd))
          (read-only (fnn-refuse "no log segment at ~a" path))
          (t
           (let ((fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                            sb-posix:o-excl +fnn-o-nofollow+))))
             (fnn-log-preallocate fd extent)
             (fnn-fsync-file fd)
             (fnn-fsync-dir (fnn-log-parent path))
             fd)))))

(defun fnn-log-read-string (fd extent)
  "The segment's EXTENT octets as a string, one character per octet: the
concrete input of fn-lg-decode (its model is fn-lgd-octets)."
  (fnn-posix () (sb-posix:lseek fd 0 sb-posix:seek-set))
  (let ((data (fnn-read-exact-fd fd extent)))
    (unless data (fnn-fault "log segment shorter than its extent"))
    (map 'string #'code-char data)))

(defun fnn-log-open-kernel (fd extent unit max &optional (genesis *fn-lg-genesis*))
  "The segment's kernel scanned from GENESIS (fn-lg-open-kernel).  A scan
that stops at an entry validating under another predecessor is a splice or
a stale segment, refused by name (fn-lgs-chain-broken-string-p), never read
as a torn tail."
  (let ((text (fnn-log-read-string fd extent)))
    (when (fnn-core 'fn-lgs-chain-broken-string-p text genesis unit max)
      (error 'fnn-store-open-refusal
             :message "open refused reason=log-chain-broken: a log segment holds an entry chained from another history"))
    (fnn-core 'fn-lg-open-kernel text genesis unit max 1)))

(defun fnn-log-recover (path extent unit max &optional (genesis *fn-lg-genesis*))
  "P-LOG-RECOVER (fn-lg-recover-program): the kernel of the segment's decode
from GENESIS, then the tail [F, EXTENT) zeroed by one write and fenced.  The
kernel is R-related to the segment at log-recovered
(fn-lg-recover-program-establishes-the-relation)."
  (let* ((fd (fnn-log-open-segment path extent unit))
         (ks (handler-case (fnn-log-open-kernel fd extent unit max genesis)
               (error (e) (fnn-close fd) (error e)))))
    (destructuring-bind (offset count) (fnn-call 'fn-lg-recover-tail ks extent)
      (fnn-log-pwrite fd offset (fnn-make-octets count))
      (fnn-log-at :log-truncated)
      (fnn-log-fdatasync fd)
      (fnn-log-at :log-recovered))
    (%make-fnn-log :path path :fd fd :kernel ks :unit unit :max max :extent extent)))

(defun fnn-log-prepare (log record)
  "The checked prepare: RECORD joins the open batch only at the kernel's
next txid (fn-lgt-prepare)."
  (fnn-log-with-kernel (log)
    (setf (fnn-log-kernel log) (fnn-core 'fn-lgt-prepare (fnn-log-kernel log) record))))

(defun fnn-log-append (log)
  "P-BATCH's append (fn-lg-append-program): the kernel admits the open batch
and its chained entries are written at the frontier in one positioned write."
  (fnn-log-with-kernel (log)
    (let ((ks (fnn-log-kernel log)) (unit (fnn-log-unit log)) (extent (fnn-log-extent log)))
      (unless (fnn-core 'fn-lg-append-admitsp ks unit extent)
        (fnn-refuse "the log kernel refuses the append (a batch in flight, fenced, or past the extent)"))
      (fnn-log-pwrite (fnn-log-fd log) (fnn-core 'fn-lgk-frontier ks)
                      (fnn-core 'fn-lgk-append-octets ks unit))
      (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-append ks unit extent))))
  (fnn-log-at :log-written))

(defun fnn-log-fence (log)
  "P-BATCH's fence (fn-lg-fence-program): the barrier, then the kernel's
fence.  A failed barrier fences the kernel (fn-lgk-fence-failed): every
member of the batch is uncertain until recovery decides.  The barrier runs
outside the kernel lock (the owner may be preparing the next batch behind
it: fn-lgk-prepare changes only the open batch and the txid, fn-lgk-fence
only moves the batch in flight to the committed records, so the two
commute); the kernel's fence reads the kernel as it is when the barrier
returned."
  (handler-case (fnn-log-fdatasync (fnn-log-fd log))
    (fnn-os-error (e)
      (fnn-log-with-kernel (log)
        (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-fence-failed (fnn-log-kernel log))))
      (fnn-indeterminate "log barrier failed: ~a" e)))
  (fnn-log-with-kernel (log)
    (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-fence (fnn-log-kernel log) (fnn-log-unit log))))
  (fnn-log-at :log-fenced))

(defun fnn-log-finish (log count)
  "Acknowledge COUNT members in order (fn-lgk-finish-one; the kernel never
acknowledges past the committed records)."
  (fnn-log-with-kernel (log)
    (dotimes (i count)
      (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-finish-one (fnn-log-kernel log))))))

(defun fnn-log-rig-line (what log size)
  ;; Not `fnn-log-line': that is the service log's one-argument writer
  ;; (above), which this rig's definition used to replace in the image, so
  ;; every owner start faulted in fn-lgk-acked (friend-blockers-2, 09:10Z).
  (let ((ks (fnn-log-kernel log)))
    (fnn-out "~a records=~d frontier=~d next=~d last=~a workload=~(~a~)"
             what (fnn-core 'fn-lgk-acked ks) (fnn-core 'fn-lgk-frontier ks)
             (fnn-core 'fn-lgk-next-txid ks) (fnn-hex (fnn-core 'fn-lgk-last ks))
             (if (fnn-core 'fn-lg-workload-prefixp (fnn-core 'fn-lgk-committed ks) 1 size)
                 "t" "nil"))))

(defun fnn-log-nat-arg (text what)
  (let ((n (and text (every #'digit-char-p text) (plusp (length text))
                (<= (length text) 12) (parse-integer text))))
    (unless n (error 'fnn-usage-error :message (format nil "log: ~a is not a natural" what)))
    n))

;;; ---------------------------------------------------------------------------
;;; The store's commit through the record log (format 9; lane commit-onto-log,
;;; planning/design-2026-09-27-storage-log.md sections 3.3 and 4).
;;;
;;; The member step keeps its calls (fnn-advance-frontier, the prepare,
;;; fnn-publish, fnn-mark-committed, fnn-finish); on a format-9 store:
;;;   fnn-log-reserve   the owner's :log-reserve (books/owner-log-route.lisp
;;;                     fn-olr-ocfg-reserve): the allocation is derived, no
;;;                     frontier file exists.  The log kernel first consumes the
;;;                     txids the owner consumed by refusals (fn-olr-consume-to).
;;;   fnn-log-publish   the record joins the log kernel's open batch
;;;                     (fn-olr-take: T5's allocation rule), then -- in a batch of
;;;                     one -- P-BATCH's append (cut log-written) and barrier
;;;                     (cut log-fenced), and only then the owner's :log-order
;;;                     (fn-olr-ocfg-order).  Inside the owner's batch quantum
;;;                     (*fnn-log-batch*) the append and the barrier run once, at
;;;                     the batch's end (fnn-log-commit-open-batch), before any
;;;                     member's reply leaves the owner.
;;;   fnn-mark-committed nothing: M := D.
;;;   fnn-finish        the kernel acknowledges the member (fn-lgk-finish-one)
;;;                     after its barrier.
;;; ACL2 decides every value: the segment name, the unit, the extent and its
;;; growth, the take and its bounds, the append's octets and offset.

(defun fnn-store-log-unit () (fnn-nat (fnn-core 'fn-store-log-unit)))

(defun fnn-store-log-max (store)
  (fnn-nat (fnn-core 'fn-store-profile-max-record-octets (fnn-store-config store))))

(defun fnn-log-observed-extent (path)
  "The segment's size (the extent the recovery zeroes to).  Not a positive
number of units is a fault: init and every extension leave whole units."
  (let ((st (fnn-check-regular path)))
    (unless st (fnn-refuse "no log segment at ~a" path))
    (sb-posix:stat-size st)))

(defun fnn-log-init-segment (store)
  "books/byte-store-log-initializer.lisp fn-bsi-log-segment-steps: create the
store's segment (O_EXCL), its ACL2 initial extent of zeros
(fnn-log-preallocate), fence it and journal/, a cut after each.  The caller
made journal/.  An existing segment of any positive extent is kept (a re-run
init completes, never truncates): the retry branch, not the program."
  (let ((path (fnn-segment-path store)) (unit (fnn-store-log-unit)))
    (unless (fnn-check-regular path)
      (let ((extent (fnn-nat (fnn-core 'fn-store-log-initial-extent))))
        (unless (fnn-core 'fn-lg-extent-okp extent unit)
          (fnn-fault "ACL2 returned an invalid initial log extent"))
        (let ((fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat sb-posix:o-excl
                                         +fnn-o-nofollow+)
                            #o600)))
          (unwind-protect
               (progn
                 (fnn-init-cut store "init-segment-created")
                 (fnn-log-preallocate fd extent)
                 (fnn-init-cut store "init-segment-written")
                 (fnn-fsync-file fd)
                 (fnn-init-cut store "init-segment-file-fenced"))
            (fnn-close fd)))))
    (fnn-fsync-dir (fnn-journal-dir store))
    (fnn-init-cut store "init-journal-segment-fenced")))

(defun fnn-log-open-read-only (path unit max &optional (genesis *fn-lg-genesis*))
  (let* ((extent (fnn-log-observed-extent path))
         (fd (fnn-log-open-segment path extent unit t)))
    (handler-case
        (%make-fnn-log :path path :fd fd :unit unit :max max :extent extent
                       :kernel (fnn-log-open-kernel fd extent unit max genesis))
      (error (e) (fnn-close fd) (error e)))))

(defun fnn-log-batch-reset (log)
  (setf (fnn-log-count log) 0 (fnn-log-octets log) 0))

(defun fnn-recover-log-replay (store records config-records &optional positions)
  "The replay the per-file open runs (fnn-recover-full-replay), over the
log's records (the kernel's committed octet lists), in the chunks ACL2 closes
(`fnn-recover-record-chunks', as the pack path: PRF-261's
fn-srs-steps-are-one-step-of-the-concatenation, any chunking opens the same
Store); the history's COUNT (the open keeps no records, PKT-823).  POSITIONS
(the scan's entry positions) seal extents (fnn-bridge-recover)."
  (let ((action (fnn-bridge-recover (fnn-recover-record-chunks records positions)
                                    (fnn-store-frontier store) config-records)))
    (when (eq action :refused)
      (let ((text (fnn-core-state 'fn-store-open-refusal-text)))
        (unless (stringp text)
          (fnn-fault "ACL2 refused the open without naming a reason"))
        (error 'fnn-store-open-refusal :message text)))
    (unless (eq action :recovering)
      (fnn-fault "ACL2 replay rejected committed transaction history or configuration history")))
  (length records))

(defun fnn-recover-log-from-state-checkpoint (store config-records records)
  "fnn-recover-from-state-checkpoint over the log's records: the suffix is
the records at or after the checkpoint's S (the log holds every record).
Answers the history's COUNT, S plus the suffix's (PKT-823): the covered
prefix is not re-encoded (fn-store-sco-prefix-octets), since the log holds
it (`fnn-log-history-records'); NIL when the open falls back to the full
replay."
  (multiple-value-bind (status sequence) (fnn-state-checkpoint-load store)
    (let* ((count (if (eq status :ok)
                      (fnn-core 'fn-store-sco-observed-count
                                (loop for i below (length records) collect i) 0)
                    0))
           (choice (fnn-core 'fn-store-sco-select status sequence count
                             (fnn-store-config store))))
      (unless (and (consp choice) (member (first choice) '(:checkpoint :full-replay)))
        (fnn-fault "ACL2 returned a malformed checkpoint selection"))
      (when (eq (first choice) :full-replay)
        (setf (fnn-store-open-mode store) (list :full-replay (second choice)))
        (return-from fnn-recover-log-from-state-checkpoint nil))
      (let* ((s (second choice))
             (suffix (nthcdr s records)))
        (unless (eq (fnn-recover-suffix-rows store suffix config-records) :recovering)
          (fnn-core-state 'fn-store-sco-clear)
          (fnn-bridge-reset)
          (setf (fnn-store-open-mode store) (list :full-replay :checkpoint-open-refused))
          (return-from fnn-recover-log-from-state-checkpoint nil))
        (setf (fnn-store-open-mode store) (list :checkpoint s (length suffix)))
        (+ s (length suffix))))))

(defun fnn-store-recovery-barriers (store)
  "The five recovery barriers' thunks, in the model's order: the config file,
the history's authority (the segment on format 9, the frontier file on
format 8), its directory (journal/ or transactions/), the root and the root's
parent."
  (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
        (if (fnn-store-logp store)
            (lambda () (fnn-log-fdatasync (fnn-log-fd (fnn-store-log store))))
          (lambda () (fnn-fsync-regular (fnn-frontier-path store))))
        (if (fnn-store-logp store)
            (lambda () (fnn-fsync-dir (fnn-journal-dir store)))
          (lambda () (fnn-fsync-dir (fnn-transactions store))))
        (lambda () (fnn-fsync-dir (fnn-store-root store)))
        (lambda () (fnn-fsync-dir (fnn-parent (fnn-store-root store))))))

(defun fnn-log-segment-names (store)
  "journal/'s entries (bounded by the segment index's width)."
  (fnn-list-directory-bounded (fnn-journal-dir store)
                              (fnn-nat (fnn-core 'fn-lgs-listing-bound))
                              "log segment"))

(defun fnn-log-complete-rotation (store path)
  "The active segment as an interrupted rotation left it (created, not yet
preallocated to whole units): a writable open completes the rotation's
steps -- preallocate to ACL2's initial extent, fence the file, fence
journal/ -- before it scans; a reader refuses it.  A segment the rotation
created holds no entry (every append follows its rotate-durable)."
  (let ((size (sb-posix:stat-size (fnn-check-regular path)))
        (unit (fnn-store-log-unit)))
    (unless (fnn-core 'fn-lg-extent-okp size unit)
      (unless (fnn-store-writable store)
        (fnn-refuse "log segment ~a is an interrupted rotation: open it writable (recover)" path))
      (let ((fd (fnn-open path (logior sb-posix:o-rdwr +fnn-o-nofollow+))))
        (unwind-protect
             (progn (fnn-log-preallocate fd (fnn-nat (fnn-core 'fn-store-log-initial-extent)))
                    (fnn-fsync-file fd))
          (fnn-close fd)))
      (fnn-fsync-dir (fnn-journal-dir store)))))

(defun fnn-log-drop (store indices)
  "P-DROP (design 2026-09-27 storage-log section 6): unlink each covered
segment of INDICES (a checkpoint names a later first suffix segment and is
installed), cut drop-unlinked after each, then fence journal/, cut
drop-durable.  A death between unlinks leaves covered segments the next
open's plan names again (fn-lgs-open-plan's DROP), never a segment it scans."
  (when indices
    (dolist (k indices)
      (let ((path (fnn-segment-path-at store k)))
        (when (fnn-lstat path) (fnn-unlink path))
        (fnn-log-at :drop-unlinked)))
    (fnn-fsync-dir (fnn-journal-dir store))
    (fnn-log-at :drop-durable))
  (length indices))

(defun fnn-log-rotate (store)
  "P-ROTATE (design 2026-09-27 storage-log sections 4 and 6), at a
checkpoint's capture, with no batch open, none in flight and every member
acknowledged (fn-lgs-rotate-admitsp): the next segment (fn-lgs-next-segment)
is created and preallocated to ACL2's initial extent (cut rotate-created),
fenced (cut rotate-fenced) and journal/ fenced (cut rotate-durable) before
anything names it; then it is the active segment, its kernel fn-lgs-rotate
of the closed one's (the kernel recovery derives from its zeros:
fn-lgs-rotate-is-the-recovered-kernel).  Returns the log position the
checkpoint's F row carries: (K GENESIS), the new segment and the closed
one's last trailer.  An OS error before the switch leaves the closed segment
active and removes what it created (a leftover is an interrupted rotation
the next open completes); it is a known failure of the checkpoint."
  (let* ((log (fnn-store-log store))
         (ks (fnn-log-kernel log))
         (next (fnn-core 'fn-lgs-next-segment (fnn-log-index log))))
    (unless (fnn-core 'fn-lgs-rotate-admitsp ks)
      ;; A batch open, in flight or unacknowledged: no rotation now (the
      ;; checkpoint is not published; the owner retries at its next due).
      (fnn-refuse "rotation refused reason=batch-in-flight"))
    ;; An empty active segment is already where the suffix starts.
    (unless (fnn-core 'fn-lgs-rotate-needed-p ks)
      (return-from fnn-log-rotate
        (list (fnn-log-index log) (fnn-core 'fn-lgk-last ks))))
    (unless next
      (fnn-refuse "rotation refused reason=segment-index-exhausted"))
    (let* ((path (fnn-segment-path-at store next))
           (extent (fnn-nat (fnn-core 'fn-store-log-initial-extent)))
           (fd nil))
      (handler-case
          (progn
            (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                            sb-posix:o-excl +fnn-o-nofollow+)))
            (fnn-log-preallocate fd extent)
            (fnn-log-at :rotate-created)
            (fnn-fsync-file fd)
            (fnn-log-at :rotate-fenced)
            (fnn-fsync-dir (fnn-journal-dir store))
            (fnn-log-at :rotate-durable))
        (fnn-os-error (e)
          (when fd (ignore-errors (fnn-close fd)))
          (ignore-errors (when (fnn-lstat path) (fnn-unlink path)))
          (fnn-refuse-io "log rotation failed: ~a" e)))
      (fnn-close (fnn-log-fd log))
      (setf (fnn-log-path log) path
            (fnn-log-fd log) fd
            (fnn-log-kernel log) (fnn-core 'fn-lgs-rotate ks)
            (fnn-log-index log) next
            (fnn-log-extent log) extent
            (fnn-log-pending log) 0)
      (fnn-log-batch-reset log)
      (list next (fnn-core 'fn-lgk-last ks)))))

(defun fnn-log-covered-indices (store first)
  "The segments present below FIRST (a checkpoint's first suffix segment)."
  (let ((plan (fnn-core 'fn-lgs-open-plan (fnn-log-segment-names store) first)))
    (if (eq (first plan) :scan) (third plan) nil)))

(defun fnn-log-scan-segments (store scan genesis)
  "Scan the segments SCAN (indices, the last the active one) from GENESIS,
the chain carried from each segment's kernel to the next (fn-lgk-last).
The closed segments are read only; the active one is recovered (a writable
open: P-LOG-RECOVER) or read.  Returns (values RECORDS LOG POSITIONS): every
scanned record in order, the active segment's log, and per record its
entry's (FILE START N 0): FILE the extent realizer's id of the segment
(host/native/extent.lisp: a read-only descriptor held for the process's
life), the rest ACL2's (fn-arx-positions over the records' lengths)."
  (let ((unit (fnn-store-log-unit))
        (max (fnn-store-log-max store))
        (records nil)
        (positions nil))
    (loop for (k . more) on scan do
      (let ((path (fnn-segment-path-at store k)))
        (if more
            (multiple-value-bind (closed last)
                (fnn-log-read-closed-segment store k genesis unit max)
              (push closed records)
              (push (fnn-extent-positions path (mapcar #'length closed) unit) positions)
              (setq genesis last))
          (progn
            (fnn-log-complete-rotation store path)
            (let ((log (if (fnn-store-writable store)
                           (fnn-log-recover path (fnn-log-observed-extent path) unit max genesis)
                         (fnn-log-open-read-only path unit max genesis))))
              (setf (fnn-log-index log) k)
              ;; The kernel's committed records as the kernel holds them
              ;; (octet lists), not copied: the replay's chunks read them in
              ;; place (PKT-823).
              (let ((these (fnn-core 'fn-lgk-committed (fnn-log-kernel log))))
                (push these records)
                (push (fnn-extent-positions path (mapcar #'length these) unit) positions))
              (return-from fnn-log-scan-segments
                (values (apply #'append (nreverse records)) log
                        (apply #'append (nreverse positions)))))))))
    (fnn-fault "the log's open plan named no segment")))

(defun fnn-log-read-closed-segment (store k genesis unit max)
  "A closed segment K read only: the fold's step (books/store-log-segments.lisp
fn-lgs-open-chain-records and fn-lgs-open-chain-last over the one segment,
T8's subject) after the splice check.  (values RECORDS LAST): its records
(octet lists, ACL2's) and the chain's last trailer, the next segment's
genesis."
  (let* ((path (fnn-segment-path-at store k))
         (extent (fnn-log-observed-extent path))
         (fd (fnn-log-open-segment path extent unit t)))
    (unwind-protect
         (let ((text (fnn-log-read-string fd extent)))
           (when (fnn-core 'fn-lgs-chain-broken-string-p text genesis unit max)
             (error 'fnn-store-open-refusal
                    :message "open refused reason=log-chain-broken: a log segment holds an entry chained from another history"))
           (values (fnn-core 'fn-lgs-open-chain-records (list text) genesis unit max)
                   (fnn-core 'fn-lgs-open-chain-last (list text) genesis unit max)))
      (fnn-close fd))))

(defun fnn-recover-log-from-log-checkpoint (store config-records suffix s)
  "The open from a checkpoint whose F row names the log's first suffix
segment: SUFFIX is the scan from there (T8: with the checkpoint's records it
is the whole history), replayed over the checkpoint
(fn-store-sn-recover-from-checkpoint).  The covered segments may be gone, so
there is no full replay to fall back to: a checkpoint the open cannot use is
refused by name."
  (progn
    ;; S: the loaded checkpoint's (fnn-recover-log loaded it once, first).
    (unless (eq (fnn-recover-suffix-rows store suffix config-records) :recovering)
      (fnn-core-state 'fn-store-sco-clear)
      (fnn-bridge-reset)
      (error 'fnn-store-open-refusal
             :message "open refused reason=checkpoint-damaged: the checkpoint that covers the dropped log segments does not open"))
    (setf (fnn-store-open-mode store) (list :checkpoint s (length suffix)))
    ;; The history's count (PKT-823); the prefix stays in the arena and the
    ;; checkpoint's rows, encoded only for a verb that reads the history
    ;; (fnn-log-history-records).
    (+ s (length suffix))))

(defun fnn-recover-log (store)
  "The open of a format-9 store.  The checkpoint first: its F row names where
the log's suffix starts (books/store-log-segments.lisp: the first suffix
segment and its genesis) and the txid frontier at S.  ACL2's plan over
journal/ (fn-lgs-open-plan) names the segments to scan and the covered ones
to drop, or refuses by name (history-short-of-checkpoint,
checkpoint-damaged).  The segments are scanned with the chain carried across
them (fnn-log-scan-segments: P-LOG-RECOVER on the active one, cuts
log-truncated and log-recovered), the frontier derived (fn-store-log-next-txid
over the scanned records, floored at the checkpoint's), then the replay: over
the checkpoint when its F row names a position, else the per-file open's
choice (fnn-recover-log-from-state-checkpoint or the full replay); then the
five recovery barriers the per-file open runs, and a writable open finishes
an interrupted drop.  Answers the history's record COUNT, as `fnn-recover'
does, and records how the log holds the history (fnn-store-log-history) for
`fnn-log-history-records'."
  (let ((count nil) (drop nil))
    (handler-case
        (multiple-value-bind (status sequence) (fnn-state-checkpoint-load store)
          (let* ((position (and (eq status :ok) (fnn-core-state 'fn-store-sco-log-position)))
                 (log-position (first position))
                 (floor (if log-position (fnn-nat (second position)) 0))
                 (plan (fnn-core 'fn-lgs-open-plan (fnn-log-segment-names store)
                                 (first log-position))))
            (unless (and (consp plan) (member (first plan) '(:scan :refused)))
              (fnn-fault "ACL2 returned a malformed log open plan"))
            (when (eq (first plan) :refused)
              (error 'fnn-store-open-refusal
                     :message (format nil "open refused reason=~(~a~): the log's segments do not hold the history~@[ from segment ~d~]"
                                      (second plan) (first log-position))))
            (setq drop (third plan))
            (multiple-value-bind (scanned log positions)
                (fnn-log-scan-segments store (second plan)
                                       (if log-position (second log-position) *fn-lg-genesis*))
              (fnn-log-batch-reset log)
              ;; The frontier: one past the largest txid of every record the
              ;; scan holds, of every event kind (ACL2's fn-store-log-next-
              ;; txid), at least the checkpoint's frontier at S (the dropped
              ;; segments' txids), and the log kernel caught up to it.
              (let ((next (fnn-nat (fnn-core 'fn-store-log-next-txid
                                             scanned
                                             (max floor (fnn-core 'fn-lgk-next-txid
                                                                  (fnn-log-kernel log)))))))
                (setf (fnn-log-kernel log) (fnn-core 'fn-olr-consume-to (fnn-log-kernel log) next)
                      (fnn-store-log store) log
                      (fnn-store-frontier store) next))
              (setf (fnn-store-log-history store)
                    (let ((scan (second plan)))
                      (list (and log-position t) (butlast scan)
                            (if log-position (second log-position) *fn-lg-genesis*)
                            (car (last scan)))))
              (let ((config-records (fnn-config-records store)))
                (setq count
                      (if log-position
                          (fnn-recover-log-from-log-checkpoint store config-records scanned
                                                               sequence)
                        (or (fnn-recover-log-from-state-checkpoint store config-records scanned)
                            (fnn-recover-log-replay store scanned config-records positions)))))))
          (setf (fnn-store-config-generation store) (fnn-bridge-config-generation)
                (fnn-store-config-served store) (fnn-bridge-config-names 'fn-store-cfg-served)
                (fnn-store-config-domain store) (fnn-bridge-config-names 'fn-store-cfg-domain)))
      ((or fnn-store-fault fnn-store-indeterminate fnn-store-open-refusal) (e)
        (setf (fnn-store-fenced store) t)
        (error e))
      (fnn-store-error (e)
        (setf (fnn-store-fenced store) t)
        (fnn-fault "cannot reconstruct committed history: ~a" e)))
    (fnn-at store :recover-replayed)
    (handler-case
        (let ((phase nil))
          (loop for barrier in (fnn-store-recovery-barriers store)
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
        (fnn-indeterminate "cannot establish recovered log frontier")))
    (handler-case
        (if (fnn-store-writable store)
            (fnn-sweep-staging store)
            (setf (fnn-store-orphans store) (fnn-staging-orphans store)))
      ((or fnn-store-fault fnn-store-indeterminate) (e)
        (setf (fnn-store-fenced store) t)
        (error e)))
    ;; An interrupted drop: the covered segments the plan named go now.
    (when (and drop (fnn-store-writable store))
      (handler-case (fnn-log-drop store drop)
        (fnn-os-error (e)
          (setf (fnn-store-fenced store) t)
          (fnn-indeterminate "the drop of covered log segments is uncertain: ~a" e))))
    (setf (fnn-store-checkpoint-outcome store)
          (funcall *fnn-checkpoint-recover-callback* store count))
    (setf (fnn-store-fenced store) nil)
    count))

(defun fnn-log-reserve (store current-txid)
  "The member's reservation on the log route (fn-olr-ocfg-reserve through
the observe callback): the frontier is the log's derived one."
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  (unless (eql current-txid (fnn-store-frontier store))
    (setf (fnn-store-fenced store) t)
    (fnn-fault "ACL2 allocator and the log's frontier disagree"))
  (let ((next (fnn-metadata-frontier-next current-txid))
        (log (fnn-store-log store)))
    (when (null next)
      (fnn-refuse "finite transaction-ID domain exhausted"))
    (fnn-log-with-kernel (log)
      (setf (fnn-log-kernel log)
            (fnn-core 'fn-olr-consume-to (fnn-log-kernel log) current-txid)
            (fnn-log-reserved log) current-txid))
    (unless (eq (fnn-observe store :log-reserve) :reserved)
      (setf (fnn-store-fenced store) t)
      (fnn-fault "ACL2 rejected the log route's reservation"))
    (setf (fnn-store-frontier store) next)
    (fnn-at store :frontier-reserved)
    next))

(defun fnn-log-take (store record)
  "RECORD into the open batch (fn-olr-take).  :full commits the open batch
first (inside a batch quantum the batch closes at the operator's bounds)."
  (let* ((log (fnn-store-log store))
         (octets (fnn-octet-list record)))
    (loop repeat 2 do
      (when (eq (fnn-log-with-kernel (log) (fnn-core 'fn-lgk-phase (fnn-log-kernel log))) :fault)
        ;; The barrier of the batch in flight failed (the syncer fenced the
        ;; kernel) while this member was prepared behind it.
        (fnn-indeterminate "the log's barrier failed; the store needs recovery"))
      (destructuring-bind (verdict ks entry)
          (fnn-log-with-kernel (log)
            (let ((answer (fnn-core 'fn-olr-take (fnn-log-kernel log) octets (fnn-log-reserved log)
                                    (fnn-log-count log) (fnn-log-octets log)
                                    (fnn-log-bmax log) (fnn-log-omax log) (fnn-log-unit log))))
              (when (eq (first answer) :taken)
                (setf (fnn-log-kernel log) (second answer)))
              answer))
        (declare (ignore ks))
        (case verdict
          (:taken (incf (fnn-log-count log))
                  (incf (fnn-log-octets log) entry)
                  (return-from fnn-log-take :taken))
          (:full
           ;; The open batch is at the operator's bound.  Behind a batch in
           ;; flight (a pipelined START-NEXT) its append must wait for that
           ;; batch's barrier: the kernel admits one batch in flight.
           (unless (eq (fnn-log-await-sync log) :fenced)
             (fnn-indeterminate "the log's barrier failed; the store needs recovery"))
           (fnn-log-commit-open-batch store))
          (t (fnn-fault "the log kernel refused the record (the owner's txid is not the log's next)")))))
    (fnn-fault "the log kernel refused an empty batch's take")))

(defun fnn-log-ensure-extent (log)
  "books/store-log-extend.lisp fn-lg-extend-program: when the open batch and
one spare unit do not fit the segment (fn-olr-extension-needed-p), grow it to
ACL2's target (fn-olr-extension-target: whole units, past the old extent),
then one barrier.  Runs at rest (no batch in flight); the octets before the
old extent are never written, the new ones read zeros, and the kernel is
unchanged (fn-lg-extend-program-keeps-the-relation).  A death at
log-extended recovers exactly the committed records
(fn-lg-extension-written-crash-reads-the-committed-records)."
  (let* ((ks (fnn-log-kernel log)) (unit (fnn-log-unit log)) (extent (fnn-log-extent log))
         ;; The open batch's log length, digest-free (PKT-749: one packed
         ;; entry padded once; books/store-log.lisp fn-lg-log-len, which
         ;; fn-olr-log-need-is-the-append-end ties to the append's end).
         (octets (fnn-nat (fnn-core 'fn-lg-log-len (fnn-core 'fn-lgk-batch ks) unit))))
    (when (fnn-core 'fn-olr-extension-needed-p (fnn-core 'fn-lgk-frontier ks)
                    octets extent unit)
      (let ((next (fnn-nat (fnn-core 'fn-olr-extension-target
                                     (fnn-core 'fn-lgk-frontier ks) octets
                                     extent unit))))
        (unless (and (fnn-core 'fn-lg-extent-okp next unit) (> next extent))
          (fnn-fault "ACL2 returned an invalid log extent"))
        (fnn-log-preallocate (fnn-log-fd log) next extent)
        (fnn-log-at :log-extended)
        (fnn-log-fdatasync (fnn-log-fd log))
        (fnn-log-at :log-extent-fenced)
        (setf (fnn-log-extent log) next)))))

(defun fnn-log-commit-open-batch (store)
  "P-BATCH's append and barrier for the open batch (its members' records
are in the kernel's batch), cuts log-written and log-fenced.  Any OS error
from the append to the barrier is uncertain for every member: the kernel is
fenced (fn-lgk-fence-failed) and the store with it."
  (let ((log (fnn-store-log store))
        (fenced (fnn-store-fenced store)))
    (when (plusp (fnn-log-count log))
      ;; Never behind a batch in flight: its barrier first (the kernel
      ;; admits one batch in flight; lane log-2's pipelined commit).
      (unless (eq (fnn-log-await-sync log) :fenced)
        (fnn-indeterminate "the log's barrier failed; the store needs recovery"))
      (setf (fnn-store-fenced store) t)
      (handler-case
          (progn
            (fnn-log-ensure-extent log)
            (fnn-log-append log)
            (fnn-at store :log-written)
            (fnn-log-fence log)
            (fnn-at store :log-fenced))
        ((or fnn-store-indeterminate fnn-store-fault) (e) (error e))
        (fnn-os-error (e)
          (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-fence-failed (fnn-log-kernel log)))
          (fnn-indeterminate "log batch outcome is indeterminate: ~a" e))
        (fnn-store-error (e)
          ;; fnn-log-append's refusal: the kernel does not admit the batch
          ;; (in flight, fenced, or past the extent after the extension).
          (fnn-fault "the log kernel refused the batch's append: ~a" e)))
      (fnn-log-with-kernel (log)
        (setf (fnn-log-pending log) (+ (fnn-log-pending log) (fnn-log-count log))))
      (fnn-log-batch-reset log)
      ;; The barrier returned: the writer is as it was before the batch (a
      ;; commit quantum's members are finished; a batch of one's finish is
      ;; still to come and finds the store fenced, as fnn-finish requires).
      (setf (fnn-store-fenced store) fenced))
    t))

(defun fnn-log-write-history (store values records)
  "`store import' onto the record log (design 2026-09-27 storage-log section
5.3): the fresh segment of the staged STORE (profile VALUES) receives
RECORDS, a list of (SEQUENCE . OCTETS) in increasing sequence, from the
genesis, through the kernel the open recovered from it and the commit
route's own steps: per record the kernel catches up to its txid
(fn-store-log-record-txid; fn-olr-consume-to: the archive's burned
reservations stay burned) and takes it (fn-olr-take, at the bounds of a configuration naming none: fn-olr-bmax,
fn-olr-omax); a full batch, and the last, is P-BATCH's append and barrier
(fnn-log-commit-open-batch, cuts log-written and log-fenced) and is
acknowledged.  The stage is unpublished throughout: a death here leaves
ROOT.import-XXXX, never a store at ROOT (fn-bs-imp-classify)."
  (let* ((path (fnn-segment-path store))
         (log (fnn-log-recover path (fnn-log-observed-extent path) (fnn-store-log-unit)
                               (fnn-nat (fnn-core 'fn-store-profile-max-record-octets values)))))
    (setf (fnn-store-log store) log
          (fnn-log-bmax log) (fnn-nat (fnn-core 'fn-olr-bmax nil))
          (fnn-log-omax log) (fnn-nat (fnn-core 'fn-olr-omax nil)))
    (fnn-log-batch-reset log)
    (unwind-protect
         (let ((*fnn-log-batch* t))
           (dolist (record records)
             ;; The record's own txid (every event kind: ACL2's decode), as
             ;; the owner reserved it when it committed.
             (let ((txid (fnn-core 'fn-store-log-record-txid (cdr record))))
               (unless (and (integerp txid) (>= txid 0))
                 (fnn-fault "ACL2 found no txid in an archived record"))
               (setf (fnn-log-kernel log)
                     (fnn-core 'fn-olr-consume-to (fnn-log-kernel log) txid)
                     (fnn-log-reserved log) txid)
               (fnn-log-take store (cdr record))
               (fnn-log-batch-finish store)))
           (fnn-log-commit-open-batch store)
           (fnn-log-batch-finish store))
      (fnn-close (fnn-log-fd log))
      (setf (fnn-store-log store) nil))))

(defun fnn-log-publish (store sequence record)
  "fnn-publish on the log route."
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  (unless (eq (fnn-core 'fn-store-publication-admissibility
                        (fnn-store-config store) sequence (length record))
              :admissible)
    (fnn-refuse "prepared Store transaction exceeds persisted profile"))
  (setf (fnn-store-fenced store) t)
  (fnn-log-take store record)
  (unless *fnn-log-batch*
    (fnn-log-commit-open-batch store))
  (unless (eq (fnn-observe store :log-order) :completing)
    (fnn-indeterminate "ACL2 rejected the record's place in the log"))
  (setf (fnn-store-completion-pending store) t)
  (fnn-at store :record-completing)
  :durable)

(defun fnn-log-ack (log count)
  "The log kernel acknowledges COUNT fenced members in order
(fn-lgk-finish-one)."
  (fnn-log-with-kernel (log)
    (fnn-log-finish log count)
    (setf (fnn-log-pending log) (max 0 (- (fnn-log-pending log) count)))))

(defun fnn-log-batch-finish (store)
  "After the batch's barrier: every fenced member of the batch acknowledged."
  (let ((log (fnn-store-log store)))
    (fnn-log-with-kernel (log)
      (fnn-log-ack log (fnn-log-pending log)))))

;;; The pipelined commit (lane log-2; books/owner-commit-pipeline.lisp).
;;; SEAL under the owner (the START's end, or the COMPLETE's for the next
;;; batch): the open batch's append, cut log-written; the batch is in flight.
;;; SYNC in the syncer thread, the owner released: the barrier and the
;;; kernel's fence (fnn-log-fence: cut log-fenced), and nothing else -- no
;;; owner global, no store field but the log struct under its lock.
;;; COMPLETE under the owner: the acknowledgements (fnn-log-batch-finish).
;;; A batch of one and the inline quantum keep fnn-log-commit-open-batch.

(defun fnn-log-await-sync (log)
  "The syncer's word for the batch in flight: :fenced or :failed, waiting
while it runs; :fenced at once when no batch was sealed."
  (sb-thread:with-mutex ((fnn-log-lock log))
    (loop while (eq (fnn-log-sync-state log) :syncing)
          do (sb-thread:condition-wait (fnn-log-sync-cv log) (fnn-log-lock log)))
    (if (eq (fnn-log-sync-state log) :failed) :failed :fenced)))

(defun fnn-log-seal-open-batch (store)
  "SEAL: the open batch's append at the frontier (P-BATCH's append, cut
log-written); the batch is in flight and its barrier is the syncer's
(fnn-log-sync-sealed-batch).  Returns the number of members sealed (0: the
sync returns at once)."
  (let* ((log (fnn-store-log store))
         (count (fnn-log-count log)))
    (unless (eq (fnn-log-await-sync log) :fenced)
      (fnn-indeterminate "the log's barrier failed; the store needs recovery"))
    (when (plusp count)
      (handler-case
          (progn
            (fnn-log-ensure-extent log)
            (fnn-log-append log)
            (fnn-at store :log-written))
        ((or fnn-store-indeterminate fnn-store-fault) (e) (error e))
        (fnn-os-error (e)
          (fnn-log-with-kernel (log)
            (setf (fnn-log-kernel log) (fnn-core 'fn-lgk-fence-failed (fnn-log-kernel log))))
          (fnn-indeterminate "log batch outcome is indeterminate: ~a" e))
        (fnn-store-error (e)
          (fnn-fault "the log kernel refused the batch's append: ~a" e))))
    (fnn-log-with-kernel (log)
      (setf (fnn-log-sealed log) count
            (fnn-log-sync-state log) :syncing))
    (fnn-log-batch-reset log)
    count))

(defun fnn-log-sync-sealed-batch (store)
  "SYNC (the syncer thread, the owner released): the sealed batch's barrier
and the kernel's fence (fnn-log-fence, cut log-fenced); its members become
the fenced ones the COMPLETE acknowledges.  Returns (values WORD CONDITION):
:fenced, or :failed with the condition when it was not an indeterminate
observation (the COMPLETE re-signals it under the owner)."
  (let ((log (fnn-store-log store)) (word :fenced) (condition nil))
    (handler-case
        (when (plusp (fnn-log-sealed log))
          (fnn-log-fence log)
          (fnn-at store :log-fenced))
      (fnn-store-indeterminate (e)
        (fnn-err "Store outcome uncertain; the store needs recovery: ~a" e)
        (setq word :failed))
      (serious-condition (e)
        (setq word :failed condition e)))
    (sb-thread:with-mutex ((fnn-log-lock log))
      (when (eq word :fenced)
        (setf (fnn-log-pending log) (+ (fnn-log-pending log) (fnn-log-sealed log))))
      (setf (fnn-log-sealed log) 0
            (fnn-log-sync-state log) word)
      (sb-thread:condition-broadcast (fnn-log-sync-cv log)))
    (values word condition)))

(defun fnn-log-sync-collected (log)
  "The COMPLETE consumed the syncer's word: no batch is in flight."
  (sb-thread:with-mutex ((fnn-log-lock log))
    (unless (eq (fnn-log-sync-state log) :failed)
      (setf (fnn-log-sync-state log) :idle))))

;; `fn log scan SEGMENT EXTENT UNIT MAX SIZE' (both images: reads only) and,
;; on a developer image, `fn log recover ...' and `fn log append SEGMENT
;; EXTENT UNIT MAX SIZE BATCHES PER' (the power-loss rig's workload: recover,
;; then BATCHES batches of PER workload records, one `ACK' line after each
;; fence and its acknowledgements, flushed).
(defun fnn-command-log (command argv)
  (unless (member command '("scan" "recover" "append") :test #'equal)
    (error 'fnn-usage-error :message "log scan|recover|append SEGMENT EXTENT UNIT MAX SIZE [BATCHES PER]"))
  (when (and (not (string= command "scan")) (not (fnn-developer-image-p)))
    (error 'fnn-usage-error :message (format nil "log ~a is a developer-image verb" command)))
  (when (< (length argv) (if (string= command "append") 7 5))
    (error 'fnn-usage-error :message "log: missing arguments"))
  (let ((path (first argv))
        (extent (fnn-log-nat-arg (second argv) "EXTENT"))
        (unit (fnn-log-nat-arg (third argv) "UNIT"))
        (max (fnn-log-nat-arg (fourth argv) "MAX"))
        (size (fnn-log-nat-arg (fifth argv) "SIZE")))
    (cond
      ((string= command "scan")
       (let ((fd (fnn-log-open-segment path extent unit t)))
         (unwind-protect
              (fnn-log-rig-line "SCAN" (%make-fnn-log :path path :fd fd :unit unit :max max
                                                  :extent extent
                                                  :kernel (fnn-log-open-kernel fd extent unit max))
                            size)
           (fnn-close fd))))
      (t
       (let ((log (fnn-log-recover path extent unit max)))
         (unwind-protect
              (progn
                (fnn-log-rig-line "RECOVERED" log size)
                (when (string= command "append")
                  (let ((batches (fnn-log-nat-arg (sixth argv) "BATCHES"))
                        (per (fnn-log-nat-arg (seventh argv) "PER")))
                    (dotimes (b batches)
                      (dotimes (i per)
                        (fnn-log-prepare
                         log (fnn-core 'fn-lg-workload-record
                                       (fnn-core 'fn-lgk-next-txid (fnn-log-kernel log)) size)))
                      (fnn-log-append log)
                      (fnn-log-fence log)
                      (fnn-log-finish log per)
                      (fnn-log-rig-line (format nil "ACK batch=~d" (1+ b)) log size)))))
           (fnn-close (fnn-log-fd log)))))))
  +fnn-exit-ok+)

(fnn-register-verb "log" #'fnn-command-log)


;;; PKT-403: `fn --version' prints the release version and the source
;;; revision this image was built from, as the installer recorded it beside
;;; the core (packaging/install-native.sh writes libexec/fn/source-revision; the
;;; frozen image directory carries the same file, tools/runbooks/
;;; hbox-image-build.sh).  The word is printed only when it is a 40-digit
;;; lowercase hex commit; anything else is an image without provenance.
(defun fnn-source-revision ()
  (let* ((core (and sb-ext:*core-pathname* (namestring sb-ext:*core-pathname*)))
         (slash (and core (position #\/ core :from-end t)))
         (path (and slash (concatenate 'string (subseq core 0 (1+ slash))
                                       "source-revision"))))
    (unless (and path (fnn-lstat path))
      (fnn-refuse "this image records no source revision (no ~a)" (or path "core path")))
    (let* ((text (string-right-trim '(#\Newline #\Return)
                                    (fnn-octets-string
                                     (fnn-read-regular-bounded path 128)))))
      (unless (and (= (length text) 40)
                   (every (lambda (c) (find c "0123456789abcdef")) text))
        (fnn-refuse "~a is not a source revision" path))
      text)))

(defun fnn-dispatch (args)
  (flet ((need (n) (when (< (length args) n) (error 'fnn-usage-error :message "missing arguments"))))
    ;; PKT-403: bare `fn' is `fn operator - help': ACL2's operator usage
    ;; (books/native-operator.lisp fn-nop-help-text), never "missing arguments".
    (when (null args)
      (return-from fnn-dispatch (fnn-dispatch (list "operator" "-" "help"))))
    (when (and (null (rest args))
               (member (first args) '("--version" "version") :test #'string=))
      ;; `fn 6.7.N (REV12)': the release version built into the image and
      ;; the first twelve digits of the recorded source revision.
      (let ((revision (fnn-source-revision)))
        (fnn-out "fn ~a (~a)" (fnn-release-version) (subseq revision 0 12)))
      (return-from fnn-dispatch +fnn-exit-ok+))
    (need 1)
    (let ((verb (first args)))
      (cond
        ((string= verb "store")
         (need 3)
         (let ((root (second args)) (command (third args)) (rest (cdddr args)))
           (cond ((string= command "init") (fnn-command-developer-init root rest))
                 ((string= command "recover") (fnn-command-recover root))
                 ((string= command "node-secret") (need 4) (fnn-command-node-secret root rest))
                 ((string= command "status") (fnn-command-status root))
                 ((string= command "checkpoint") (fnn-command-state-checkpoint root))
                 ((string= command "export") (need 4) (fnn-command-store-export root (first rest)))
                 ((string= command "import") (need 4) (fnn-command-store-import root (first rest) nil))
                 ((string= command "retention") (fnn-command-retention root))
                 ;; PKT-579: record the filesystem the store is on now.
                 ((string= command "rebind-filesystem")
                  (fnn-command-rebind-filesystem
                   root
                   (cond ((null rest) nil)
                         ((and (null (cdr rest)) (string= (first rest) "on")) 1)
                         ((and (null (cdr rest)) (string= (first rest) "off")) 0)
                         (t (error 'fnn-usage-error
                                   :message "rebind-filesystem takes on, off or nothing")))))
                 ;; PKT-444: the repair of a pre-C1 control record.  Its
                 ;; semantics wait on ember; until then it refuses by name
                 ;; and touches nothing.
                 ((string= command "repair-control")
                  (fnn-refuse "~a" (fnn-core 'fn-store-repair-control-text)))
                 ((string= command "config") (fnn-command-config root))
                 ((string= command "inspect") (need 4) (fnn-command-inspect root (first rest)))
                 ((string= command "probe")
                  (need 4)
                  (fnn-command-probe root (parse-integer (first rest))
                                     (cond ((null (second rest)) nil)
                                           ((string= (second rest) "article") t)
                                           (t (error 'fnn-usage-error
                                                     :message "probe form must be article")))))
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
        ;; HST-025: a guard violation at the host boundary, on purpose.  The
        ;; saved world is the execution world (host/native/strip-world.lisp);
        ;; this is the native witness that a guard failure inside fnn-call is
        ;; still the same fault line and exit code
        ;; (tests/test_native_image_floor.py).  Developer image only.
        ((string= verb "guard-probe")
         (unless (fnn-developer-image-p)
           (error 'fnn-usage-error
                  :message "guard-probe is available only in the developer image"))
         (fnn-core 'fn-sha256-of-string 42)
         +fnn-exit-ok+)
        ((string= verb "redeem")
         (fnn-command-redeem (cdr args)))
        ((string= verb "model")
         (need 3)
         (fnn-command-model (second args) (fnn-dash-nil (third args))))
        ;; A registered verb: the TCPCLv4 convergence layer
        ;; (host/native/tcpcl.lisp) is the one today.  Its own positional
        ;; protocol, because its arguments are a peer and a session and not
        ;; a store, so a handler takes a command and the rest.
        ((fnn-verb-handler verb)
         ;; PKT-709: a registered verb with no command word is asked for
         ;; `help' (its own usage), never `missing arguments'.
         (if (null (cdr args))
             (funcall (fnn-verb-handler verb) "help" nil)
           (funcall (fnn-verb-handler verb) (second args) (cddr args))))
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

;;; The collection trigger for every entry of the image, the operator verbs
;;; included: the owner once set it in fnn-owner-run alone, so `store checkpoint', `recover' and the
;;; other offline verbs replayed a history under SBCL's default of 5% of the
;;; dynamic space (1.6 GB at the launcher's 32 GB) and let that much garbage
;;; pile up between collections (rep-wave-d baseline, section 1.2).  It bounds
;;; dead memory, never data, and decides nothing ACL2 decides.
(defparameter +fnn-gc-nursery-octets+ (* 64 1024 1024))

;;; HST-025: the trigger is also bounded by the dynamic space this process
;;; reserved.  SBCL's own default is a fixed fraction of it (5%); a copying
;;; collection of the nursery needs up to the nursery again in free space, so
;;; at a small reservation a 64 MiB trigger is 128 MiB of headroom the live
;;; heap cannot use.  A sixteenth of the reservation, at most
;;; +fnn-gc-nursery-octets+ (every reservation of 1 GiB or more, and the
;;; figure heap-from-profile's derivation assumes) and at least 8 MiB.
;;; ACL2 decides it (books/heap-store-figure.lisp fn-heap-nursery-trigger, 8 MiB
;;; least): the launcher's figure holds twice the trigger set here in the
;;; dynamic space it reserved (fn-heap-with-nursery-holds-the-trigger).
(defun fnn-gc-nursery-octets ()
  (fnn-core 'fn-heap-nursery-trigger (sb-ext:dynamic-space-size) +fnn-gc-nursery-octets+))

;;; `fn redeem HOST[:PORT] CODE LOGIN [--tls] [--cafile PEM]': a friend
;;; redeems an invitation code (the stranger rehearsal's stop 10).  The host
;;; dials and runs TLS; ACL2 decides each next step from the reply code
;;; (books/peer-host.lisp fn-redeem-step), which name and trust the TLS
;;; check uses (fn-peer-tls-verification: the typed HOST, SNI for a DNS name
;;; only, the PEM file given or the system roots), and every line printed
;;; (fn-redeem-text).  The password is read from the terminal without echo,
;;; else from standard input; it never enters argv.
(defun fnn-redeem-read-line (read-chunk pending)
  "One reply line (without CRLF) and the octets after it, reading chunks with
READ-CHUNK until an LF; at most 4096 octets (RFC 3977 s3.1: 512 is the
largest reply line)."
  (let ((buffer pending))
    (loop
      (let ((lf (position 10 buffer)))
        (when lf
          (return (values (coerce (subseq buffer 0 (if (and (> lf 0) (= (aref buffer (1- lf)) 13))
                                                       (1- lf) lf))
                                  'list)
                          (subseq buffer (1+ lf))))))
      (when (> (length buffer) 4096)
        (fnn-refuse "refused redeem reply: the server's line exceeds 4096 octets"))
      (let ((chunk (funcall read-chunk)))
        (when (or (eq chunk :timeout) (zerop (length chunk)))
          (fnn-refuse "refused redeem connection: the server closed or did not answer"))
        (setq buffer (concatenate 'fnn-octets buffer chunk))))))

(defun fnn-redeem-read-password ()
  "The new account's password: from the terminal without echo, else one line
of standard input; at most 512 octets (the XREDEEM PASS line's bound)."
  (let* ((tty (handler-case
                  (open "/dev/tty" :direction :io :element-type 'character
                                   :external-format :latin-1)
                (error () nil)))
         (stream (or tty *standard-input*))
         (attributes nil) (old-flags nil))
    (unwind-protect
         (progn
           (format *error-output* "Password for the new account: ")
           (finish-output *error-output*)
           (when tty
             (let ((fd (sb-sys:fd-stream-fd tty)))
               (setq attributes (sb-posix:tcgetattr fd)
                     old-flags (sb-posix:termios-lflag attributes))
               (setf (sb-posix:termios-lflag attributes) (logandc2 old-flags sb-posix:echo))
               (sb-posix:tcsetattr fd sb-posix:tcsanow attributes)))
           (let ((line (read-line stream nil nil)))
             (when (null line)
               (fnn-refuse "refused redeem password: no password was given"))
             (let ((text (string-right-trim '(#\Return) line)))
               (when (or (zerop (length text)) (> (length text) 512))
                 (fnn-refuse "refused redeem password: it must be 1 to 512 characters"))
               (map 'list #'char-code text))))
      (when tty
        (when attributes
          (setf (sb-posix:termios-lflag attributes) old-flags)
          (sb-posix:tcsetattr (sb-sys:fd-stream-fd tty) sb-posix:tcsanow attributes)
          (format *error-output* "~%")
          (finish-output *error-output*))
        (close tty)))))

(defun fnn-command-redeem (args)
  (let ((tls nil) (cafile nil) (words nil))
    (loop while args
          do (let ((word (pop args)))
               (cond ((string= word "--tls") (setq tls t))
                     ((string= word "--cafile")
                      (unless args (error 'fnn-usage-error :message "--cafile takes a PEM file"))
                      (setq cafile (pop args)))
                     (t (push word words)))))
    (setq words (nreverse words))
    (unless (= (length words) 3)
      (error 'fnn-usage-error
             :message "usage: fn redeem HOST[:PORT] CODE LOGIN [--tls] [--cafile PEM] (the password is asked for, or read from standard input)"))
    (destructuring-bind (target code login) words
      (let* ((colon (position #\: target :from-end t))
             (host (if colon (subseq target 0 colon) target))
             (port (if colon
                       (or (ignore-errors (parse-integer target :start (1+ colon)))
                           (error 'fnn-usage-error :message "the port after HOST: is a number"))
                     (if tls 563 119)))
             (verification (fnn-core 'fn-peer-tls-verification host
                                     (or cafile :system-roots)))
             (password (fnn-redeem-read-password))
             (socket nil) (context nil) (channel nil) (pending (fnn-make-octets 0))
             (last nil))
        (unless (eq (first verification) :verify)
          (fnn-refuse "refused redeem ~a: ~a"
                      (if (eq (second verification) :trust) "trust" "host")
                      (if (eq (second verification) :trust)
                          "the --cafile path is not usable"
                        "HOST is not a host name or an IPv4 address")))
        (flet ((send (text)
                 (let ((octets (fnn-string-octets (fnn-concat text (coerce '(#\Return #\Newline) 'string)))))
                   (if channel
                       (fnn-tls-send-all channel octets 30)
                     (fnn-send-all (fnn-socket-fd socket) octets 30))))
               (reply ()
                 (multiple-value-bind (line rest)
                     (fnn-redeem-read-line
                      (lambda () (if channel
                                     (fnn-tls-read channel 30)
                                   (fnn-recv (fnn-socket-fd socket) 30)))
                      pending)
                   (setq pending rest last line)
                   line))
               (finish (outcome)
                 (let ((text (fnn-octets-string
                              (fnn-octets (fnn-core 'fn-redeem-text outcome login last)))))
                   (if (equal outcome '(:done))
                       (progn (fnn-out "~a" text) +fnn-exit-ok+)
                     (progn (fnn-err "~a" text) +fnn-exit-refused+)))))
          (unwind-protect
               (handler-case
               (progn
                 (setq socket (fnn-connect host port :timeout 30))
                 (let ((stage (if tls :greeting-tls :greeting-starttls)))
                   (when tls
                     (setq context (fnn-tls-open-client-context (fourth verification))
                           channel (fnn-tls-connect context (fnn-socket-fd socket)
                                                    (second verification) 30
                                                    :sni (third verification))))
                   (loop
                     (let ((step (fnn-core 'fn-redeem-step stage (reply))))
                       (case (first step)
                         (:starttls (send "STARTTLS") (setq stage :starttls))
                         (:handshake
                          (setq context (fnn-tls-open-client-context (fourth verification))
                                channel (fnn-tls-connect context (fnn-socket-fd socket)
                                                         (second verification) 30
                                                         :sni (third verification))
                                pending (fnn-make-octets 0))
                          (send (format nil "XREDEEM ~a ~a" code login))
                          (setq stage :code))
                         (:send-code
                          (send (format nil "XREDEEM ~a ~a" code login))
                          (setq stage :code))
                         (:send-password
                          (send (format nil "XREDEEM PASS ~a"
                                        (map 'string #'code-char password)))
                          (setq stage :password))
                         (t (ignore-errors (send "QUIT"))
                            (return (finish step))))))))
                 ;; A certificate the given trust does not verify, a name
                 ;; that does not match, or a failed handshake: refused by
                 ;; name, never an unchecked session.
                 (fnn-tls-verify-error (e)
                   (fnn-err "refused redeem tls: ~a; give the node's certificate file with --cafile" e)
                   +fnn-exit-refused+)
                 (fnn-tls-handshake-error (e)
                   (fnn-err "refused redeem tls: ~a" e)
                   +fnn-exit-refused+))
            (when channel (ignore-errors (fnn-tls-close-channel channel)))
            (when context (ignore-errors (fnn-tls-close-context context)))
            (when socket (ignore-errors (sb-bsd-sockets:socket-close socket)))))))))

(defun fnn-main ()
  ;; Invariant-risk mode T (ACL2 :doc set-check-invariant-risk): the same
  ;; protection as the default :WARNING -- a :program-mode host wrapper that
  ;; updates the catalog or arena stobjs (host/owner-host.lisp: the recovery
  ;; load, fn-owner-prepare-buffer, fn-owner-finish-submission) still runs
  ;; with the guard checks that keep every stobj update well-guarded -- but no
  ;; warning text on standard output, which carries the LISTENING line and
  ;; the `model' verb's reply octets and nothing else.  Never NIL (unsafe).
  (f-put-global 'check-invariant-risk t *the-live-state*)
  (setf (sb-ext:bytes-consed-between-gcs) (fnn-gc-nursery-octets))
  (fnn-open-streams)
  ;; A peer that closed first must surface as EPIPE, never as a signal that
  ;; ends the listener; Python ignores SIGPIPE at interpreter start.
  (sb-sys:enable-interrupt sb-unix:sigpipe :ignore)
  ;; PKT-101: SIGHUP only counts.  The owner asks ACL2 at its next accept
  ;; poll whether a reopen of `[log] path' is due (fn-owner-log-reopen).
  (sb-sys:enable-interrupt sb-unix:sighup
                           (lambda (signal info context)
                             (declare (ignore signal info context))
                             (setq *fnn-sighup-count* (1+ *fnn-sighup-count*))))
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
