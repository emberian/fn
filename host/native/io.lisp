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
;;; counterpart (ACL2_*1*_ACL2) of the selected wrapper or logical function,
;;; or -- for an entry declared `:raw-with' (D40, RAW DISPATCH below) -- its
;;; guard-verified definition, the guard's carried conjuncts held by the
;;; named preservation theorems instead of evaluated per call.
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
;; host-entry-guard: the host handed an ACL2 entry an argument its guard
;; refuses, or the wrong number of arguments (fnn-entry-guard).  A fault
;; (exit 4) named by the entry, the argument position and the expected kind,
;; raised before the entry runs: never a silent refusal further down.
(define-condition fnn-entry-guard-fault (fnn-store-fault) ())
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

;; The record log's damage verdicts (books/store-log-damage.lisp; used by
;; fnn-log-stream-segment and `store recover').
(defvar *fnn-log-repair* nil
  "The operator's confirmed repair of a damaged record log: the SEGMENT:OFFSET
string `store recover --repair truncate SEGMENT:OFFSET' names, which ACL2
admits only for the damage it finds at exactly that place in the active
segment of a writable open (books/store-log-damage.lisp
fn-lgdm-repair-admitsp).  NIL: no repair.")

(defvar *fnn-log-open-reports* nil
  "The lines the open's log verdicts produced (ACL2's fn-lgdm-report-text and
fn-lgdm-repair-text: a torn tail dropped, a confirmed repair), newest first;
`store recover' prints them.")


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
;;; The digest has one owner, and it is ACL2.  books/crypto-attach.lisp
;;; attaches BLAKE3 (`fn-blake3-stobj', books/blake3-stobj.lisp) to the
;;; digest seams, and the diagnostic `blake3' verb
;;; hands ACL2 the file in the octet buffer (`fn-blake3-of-prefixed-buffer').
;;; In the saved images host/native/digest.lisp swaps the vendored C BLAKE3
;;; in for those functions after a start-up check against them
;;; (A-CRYPTO-NATIVE).  tools/fn_native.py `blake3-selftest' checks the verb
;;; against an independent BLAKE3.

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

;;; The CONTROL buffer: `fn-octets-ctl' (books/native-control-buffer.lisp), a
;;; third abstract stobj congruent to `fn-octets' with its own live object.
;;; A local-control client's worker thread (host/native/control.lisp
;;; fnn-control-handle-client) decodes its frame from it BEFORE it takes the
;;; owner mutex, so the owner's buffer, which served attempts fill under that
;;; mutex, is never shared with it; the workers share this one under the
;;; control buffer lock (control.lisp fnn-with-control-buffer).  One buffer,
;;; one lock.

(defvar *fnn-octets-ctl* nil)

(defun fnn-live-octets-ctl ()
  (or *fnn-octets-ctl*
      (setq *fnn-octets-ctl*
            (or (cdr (assoc 'fn-octets-ctl (user-stobj-alist *the-live-state*)))
                (fnn-fault "the control buffer stobj is not in this image")))))

(defun fnn-octets-ctl-fill (vector)
  "Make VECTOR's bytes the control buffer's contents; return the live stobj."
  (let* ((st (fnn-live-octets-ctl)) (n (length vector)))
    (fn-octets$c-reserve n st)
    (replace (the fnn-octets (svref st 0)) vector)
    (setf (svref st 1) n)
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
(defvar *fnn-hist* nil)

(defun fnn-live-arena ()
  (or *fnn-arena*
      (setq *fnn-arena*
            (or (cdr (assoc 'fn-arena (user-stobj-alist *the-live-state*)))
                (fnn-fault "the payload arena stobj is not in this image")))))

;;; The trailing stobjs of a state-returning entry: the live payload arena,
;;; catalog and history columns (books/payload-arena.lisp fn-arena,
;;; books/catalog.lisp fn-cat, books/history-columns.lisp fn-hist), in the
;;; order the entry's STOBJS-IN names them just before state: the served
;;; readers read an article's bytes through the arena (books/nntp-session.lisp
;;; fn-nntp-article-bytes; lane served-readers), the catalog's served chain
;;; and maintenance take both, and the owner's install and carried budget
;;; readers take fn-hist (host/owner-host.lisp; lane history-columns-2).  Read
;;; off the entry's own STOBJS-IN (a property the image keeps: host/native/
;;; strip-world.lisp), once per name, so a wrapper never carries a list that
;;; could go stale.
;; Filled lazily from every thread that calls an entry (served, owner,
;; control), like *fnn-entry-guard-specs* below: synchronized.
(defvar *fnn-trailing-stobjs* (make-hash-table :test 'eq :synchronized t))

(defun fnn-live-cat ()
  (or *fnn-cat*
      (setq *fnn-cat*
            (or (cdr (assoc 'fn-cat (user-stobj-alist *the-live-state*)))
                (fnn-fault "the catalog stobj is not in this image")))))

(defun fnn-live-hist ()
  (or *fnn-hist*
      (setq *fnn-hist*
            (or (cdr (assoc 'fn-hist (user-stobj-alist *the-live-state*)))
                (fnn-fault "the history stobj is not in this image")))))

(defun fnn-trailing-kind (name)
  "The names of NAME's live stobjs just before its trailing state, in order:
the longest run of fn-arena, fn-cat and fn-hist there (NIL for none)."
  (multiple-value-bind (known found) (gethash name *fnn-trailing-stobjs*)
    (if found
        known
      (setf (gethash name *fnn-trailing-stobjs*)
            (let ((ins (reverse (stobjs-in name (w *the-live-state*))))
                  (run nil))
              (when (eq (car ins) 'state)
                (loop for sym in (cdr ins)
                      while (member sym '(fn-arena fn-cat fn-hist))
                      do (push sym run)))
              run)))))

(defun fnn-live-stobj (sym)
  (ecase sym
    (fn-arena (fnn-live-arena))
    (fn-cat (fnn-live-cat))
    (fn-hist (fnn-live-hist))))

(defun fnn-arena-then-state (name)
  "The trailing stobj arguments of the state-returning entry NAME."
  (append (mapcar #'fnn-live-stobj (fnn-trailing-kind name))
          (list *the-live-state*)))

(defun fnn-core-arena-state (name &rest args)
  "A wrapper over the arena and state, the live arena passed before state:
its value.  An entry that seals returns (mv erp val fn-arena state) and a
reader (mv erp val state); the arena is updated in place either way."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (fnn-arena-then-state name)))
    (declare (ignore ignored))
    (when erp (fnn-fault "ACL2 error in ~(~a~)" name))
    val))

(defun fnn-core-buffer-arena-state (name &rest args)
  "A wrapper over the octet buffer, the arena and state (in that order, after
ARGS): its value.  The owner's POST entries read the payload from the buffer
and seal it into the arena (host/owner-host.lisp fn-owner-prepare-buffer)."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (cons (fnn-live-octets)
                                                (fnn-arena-then-state name))))
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

(defvar *fnn-test-entropy-draws* 0)

(defun fnn-test-entropy (width)
  "Developer-only FN_NATIVE_TEST_ENTROPY=N (0 to 255): the Kth draw of this
process (from 0) is octet I = (N + 7K + I) mod 256, recorded instead of read
(the extraction gate's stateful differential).  NIL when unset."
  (let ((raw (fnn-developer-selector "FN_NATIVE_TEST_ENTROPY")))
    (when raw
      (unless (and (plusp (length raw)) (<= (length raw) 3) (every #'digit-char-p raw)
                   (< (parse-integer raw) 256))
        (fnn-fault "invalid FN_NATIVE_TEST_ENTROPY (expected 0 to 255)"))
      (let ((n (parse-integer raw)) (k *fnn-test-entropy-draws*))
        (incf *fnn-test-entropy-draws*)
        (loop for i below width collect (mod (+ n (* 7 k) i) 256))))))

(defun fnn-csprng-octets (width what)
  "Exactly WIDTH octets from the OS CSPRNG as an octet list; short or failed
entropy is a host fault.  WIDTH is ACL2's."
  (unless (and (integerp width) (< 0 width))
    (fnn-fault "ACL2 returned an invalid ~a width" what))
  (let ((recorded (fnn-test-entropy width)))
    (when recorded (return-from fnn-csprng-octets recorded)))
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
;; PKT-872: the sink dropped a journal entry and no journal entry has been
;; queued since.  Read and written under the queue mutex only.
(defvar *fnn-journal-dropped* nil)

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
        (if (eq (first answer) :queue)
            ;; PKT-872: the first journal entry queued after a dropped one
            ;; tells the writer, which records the loss by name (ACL2's
            ;; fn-otm-jw-drop, then the mark line before it).
            (fnn-log-queue-push
             (cons (if (and (eq destination :journal) *fnn-journal-dropped*)
                       (progn (setq *fnn-journal-dropped* nil) :journal-gap)
                     destination)
                   octets))
          (when (eq destination :journal)
            (setq *fnn-journal-dropped* t)))
        t))))

(defun fnn-log-sink-snapshot ()
  "The sink ACL2 last returned, for `health' (fn-nh-log-sink-line); NIL when
no writer runs."
  (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    *fnn-log-sink*))

(defvar *fnn-journal-fd* nil
  "The decision journal's descriptor (STORE/decisions/decisions.fnj, lane
time-model-2), written only by the log writer thread while it runs.")

(defvar *fnn-journal-w* nil
  "ACL2's journal writer state (books/owner-time-journal-writer.lisp: OFFSET
OWE CLOSED), set by fnn-owner-journal-open before its first entry is offered
and then read and written only by the log writer thread.")

(defun fnn-journal-test-fail-p ()
  "A developer image's injected ENOSPC: while FN_NATIVE_TEST_JOURNAL_FAIL_FILE
names a file that exists, every journal append writes half its octets and
fails (the fitness f2-full shape, without filling a filesystem)."
  (let ((path (fnn-developer-selector "FN_NATIVE_TEST_JOURNAL_FAIL_FILE")))
    (and path (probe-file path) t)))

(defun fnn-journal-write (octets after-drop)
  "PKT-872 (PRF-360): append one journal entry by ACL2's writer rule
(books/owner-time-journal-writer.lisp).  The octets are ACL2's plan (the
mark line first when an entry was lost since the last whole one; nil when
the journal is closed); a failed append is truncated back to the last whole
entry, and a truncation that fails closes the journal for the run, so no
line is ever appended after a torn one.  :written or :failed (the sink
counts it dropped)."
  (let* ((w (if after-drop (fnn-core 'fn-otm-jw-drop *fnn-journal-w*) *fnn-journal-w*))
         (planned (fnn-core 'fn-otm-jw-plan w (fnn-octet-list octets))))
    (unless (listp planned)
      (fnn-fault "ACL2 returned a malformed journal plan"))
    (if (null planned)
        (progn (setq *fnn-journal-w* w) :failed)
      (let* ((data (fnn-octets planned))
             (outcome (handler-case
                          (progn
                            (if (fnn-journal-test-fail-p)
                                (progn (fnn-write-all *fnn-journal-fd*
                                                      (subseq data 0 (floor (length data) 2)))
                                       (error "injected journal append failure"))
                              (fnn-write-all *fnn-journal-fd* data))
                            :written)
                        (error () :failed))))
        (destructuring-bind (w2 action)
            (fnn-core 'fn-otm-jw-after w (length data) outcome)
          (when (consp action)
            (unless (and (eq (first action) :truncate) (integerp (second action))
                         (<= 0 (second action)))
              (fnn-fault "ACL2 returned a malformed journal action ~a" action))
            (let ((ok (handler-case
                          (progn (fnn-posix () (sb-posix:ftruncate *fnn-journal-fd* (second action)))
                                 t)
                        (error () nil))))
              (setq w2 (fnn-core 'fn-otm-jw-truncated w2 ok))
              (unless ok
                (fnn-log-line (fnn-core 'fn-otm-jw-closed-line (second action))))))
          (setq *fnn-journal-w* w2)
          outcome)))))

(defun fnn-log-write-item (destination octets)
  "Write one whole line: :written, or :failed (ACL2 counts it dropped)."
  (handler-case
      (cond ((member destination '(:journal :journal-gap))
             (if (and *fnn-journal-fd* *fnn-journal-w*)
                 (fnn-journal-write octets (eq destination :journal-gap))
               :failed))
            ((and (eq destination :log) *fnn-owner-log-fd*)
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

(defun fnn-journal-line (line)
  "Offer one ACL2-rendered decision-journal entry LINE (its LF included,
books/owner-time-journal.lisp fn-otm-jline) to the writer thread: never
written on the caller's thread, never waited on.  ACL2's sink bounds the
queue (books/log-sink.lisp); an entry it drops is counted there and shows
in the journal as a gap in the sequence numbers, which replay names
(fn-otm-replay's (:gap SEQ)).  With no writer running (no owner run) there
is no journal and the entry is dropped."
  (unless (fnn-octet-list-p line)
    (fnn-fault "ACL2 returned a malformed journal entry"))
  (when *fnn-journal-fd*
    (fnn-log-offer :journal (fnn-octets line))))

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
;;; wrapper, exactly as the interpreted bridge evaluates it -- or, for an
;;; entry declared `:raw-with' (D40), the guard-verified definition itself.

(defun fnn-counterpart (name)
  (let ((symbol (find-symbol (symbol-name name) "ACL2_*1*_ACL2")))
    (unless (and symbol (fboundp symbol))
      (fnn-fault "ACL2 executable counterpart missing: ~a" name))
    symbol))

;;; RAW DISPATCH (D40, lane depth-debt-9).  The executable counterpart
;;; (*1*) of a guard-verified entry evaluates the entry's whole guard and
;;; then runs the raw definition; for the owner's served entries that guard
;;; is fn-sn-statep of the live Store -- the whole-node revalidation
;;; AGENTS.md forbids on a served path -- and it cannot be a stobj invariant
;;; (fn-sn-statep depends on fn-digest, which has an attachment;
;;; stobj-attachment-restrictions).  Guard verification is the condition
;;; for faithful raw execution: where the guard holds, the raw definition IS
;;; the logical function.  So an entry whose guard is an invariant the host
;;; establishes at the open and every transition preserves -- named, per
;;; entry, by the theorems of its `:raw-with' declaration
;;; (host/interfaces.lisp; books/definterface.lisp refuses the annotation at
;;; image build unless the theorems exist in the loaded world and conclude
;;; the guard's carried conjuncts) -- is dispatched to its raw definition.
;;; The entry guard (arity and kind checks, below) runs before either
;;; dispatch, exactly as before; what raw dispatch skips is the carried
;;; conjuncts alone.
;;;
;;; The table is derived from the loaded world at image build
;;; (fnn-install-raw-dispatch, called by host/native/build.lisp after this
;;; file loads): each `:raw-with' entry of the `fn-interfaces' table, refused
;;; unless its raw symbol is bound and its symbol-class is
;;; :common-lisp-compliant, so an unknown dispatch target stops the build.
;;; The developer selector FN_NATIVE_DISPATCH_COUNTERPART=1 keeps the
;;; counterpart path for every entry (tests.test_native_owner runs the served
;;; POST both ways and requires identical replies); a production image has no
;;; selector and always dispatches raw.  planning/interfaces.json lists the
;;; raw-dispatched entries (tools/interface_emit.py).

(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq)
  "entry name -> its raw (guard-verified, compiled) function symbol")

(defvar *fnn-dispatch-counterpart* nil
  "T when the developer selector keeps the executable-counterpart path.")

(defun fnn-install-raw-dispatch ()
  "Fill *fnn-raw-dispatch* from the fn-interfaces table of the loaded world:
the :raw-with entries, each checked against the world; the count."
  (let ((wrld (w *the-live-state*)))
    (clrhash *fnn-raw-dispatch*)
    (dolist (entry (table-alist 'fn-interfaces wrld))
      (let ((name (car entry))
            (theorems (cadr (assoc-keyword :raw-with (cdr entry)))))
        (when theorems
          ;; Recheck the loaded table at the dispatch installation boundary,
          ;; rather than assuming every table entry came from definterface.
          (let ((problem (fn-di-raw-with-problem name (cdr entry) wrld)))
            (when problem
              (error "fnn-install-raw-dispatch: ~a has a refused declaration: ~s"
                     name problem)))
          (let ((raw (find-symbol (symbol-name name) "ACL2")))
            (unless (and raw (fboundp raw))
              (error "fnn-install-raw-dispatch: ~a is declared :raw-with but has no raw definition" name))
            (unless (eq (symbol-class name wrld) :common-lisp-compliant)
              (error "fnn-install-raw-dispatch: ~a is declared :raw-with but is ~a, not guard-verified"
                     name (symbol-class name wrld)))
            (setf (gethash name *fnn-raw-dispatch*) raw)
            (format t "~&FN_RAW_DISPATCH ~(~a~) ~(~a~) invariant-risk=~a with=~(~a~)~%"
                    name (symbol-class name wrld)
                    (if (getpropc name 'invariant-risk nil wrld) "t" "nil")
                    theorems)))))
    (hash-table-count *fnn-raw-dispatch*)))

(defun fnn-dispatch-function (name)
  "The function fnn-call applies for NAME: its raw definition when NAME is
raw-dispatched and the counterpart selector is off, else its executable
counterpart."
  (or (and (not *fnn-dispatch-counterpart*)
           (gethash name *fnn-raw-dispatch*))
      (fnn-counterpart name)))

;;; The entry guard (lane entry-guards, 2026-09-27).  Every call into the
;;; core passes through fnn-call; before the counterpart runs, the host checks
;;; the entry's ARITY and the CHEAP conjuncts of the entry's own ACL2 guard on
;;; the actual arguments: a conjunct (R v) with v a non-stobj formal and R one
;;; of the kind recognizers books/payload-kinds.lisp lists in
;;; *fn-entry-guard-kinds* (each guard-t and at most linear in the argument it
;;; reads, which the entry consumes anyway).  The spec is read once per name
;;; off the image's world (formals, stobjs-in, guard: kept by
;;; host/native/strip-world.lisp) and cached.  A guard conjunct that is not a
;;; kind recognizer (a whole-state invariant, a relation between arguments) is
;;; never evaluated here: no whole-state revalidation on the served path.
;;; Failure is a fault named host-entry-guard with the entry, the position,
;;; the formal and the kind: the six handle-for-octets defects of 2026-09-27
;;; surfaced as silent refusals downstream instead.  The kind decision is
;;; ACL2's (the guard and the recognizer); the host only evaluates it.
;; Filled lazily by whichever thread first calls an entry: the served
;; threads, the owner and the control workers all do, so the table is
;; synchronized.  Unsynchronized, two first calls at once stopped the owner:
;; "Unsafe concurrent operations on #<HASH-TABLE :TEST EQ :COUNT 161>"
;; (owner core/store fault, exit 4; hbox native-r2, test_native_log_compaction,
;; 2 of 8 rounds under load).
(defvar *fnn-entry-guard-specs* (make-hash-table :test 'eq :synchronized t))

(defun fnn-guard-conjuncts (term)
  "The conjuncts of a translated guard TERM ((if a b 'nil) is a conjunction)."
  (if (and (consp term) (eq (car term) 'if) (equal (fourth term) *nil*))
      (append (fnn-guard-conjuncts (second term)) (fnn-guard-conjuncts (third term)))
    (list term)))

(defun fnn-entry-guard-spec (name)
  "(arity . checks) for the entry NAME, each check (position formal recognizer
kind); :unknown when the world has no formals for NAME (a raw primitive)."
  (multiple-value-bind (spec found) (gethash name *fnn-entry-guard-specs*)
    (if found
        spec
      (setf (gethash name *fnn-entry-guard-specs*)
            (let* ((wrld (w *the-live-state*))
                   (formals (getpropc name 'formals :none wrld))
                   (stobjs (getpropc name 'stobjs-in nil wrld))
                   (checks nil))
              (if (eq formals :none)
                  :unknown
                (progn
                  (dolist (c (fnn-guard-conjuncts (getpropc name 'guard *t* wrld)))
                    (when (and (consp c) (symbolp (car c)) (consp (cdr c)) (null (cddr c))
                               (symbolp (second c)) (member (second c) formals)
                               (null (nth (position (second c) formals) stobjs)))
                      (let ((kind (assoc (car c) *fn-entry-guard-kinds*)))
                        (when kind
                          (push (list (position (second c) formals) (second c) (car c) (cdr kind))
                                checks)))))
                  (cons (length formals) (sort checks #'< :key #'first)))))))))

(defun fnn-entry-guard-describe (value)
  "A bounded description of VALUE's kind (never its contents)."
  (cond ((and (integerp value) (>= value 0)) (format nil "the natural ~d" value))
        ((integerp value) (format nil "the integer ~d" value))
        ((null value) "NIL")
        ((stringp value) (format nil "a string of ~d characters" (length value)))
        ((symbolp value) (format nil "the symbol ~s" value))
        ((consp value) (let ((n (loop for tail = value then (cdr tail)
                                      for i from 0
                                      while (and (consp tail) (< i 1000000))
                                      finally (return i))))
                         (format nil "a list of ~d element~:p (first ~a)" n
                                 (let ((head (car value)))
                                   (cond ((integerp head) head)
                                         ((consp head) "a list")
                                         (t (type-of head)))))))
        ((vectorp value) (format nil "a vector of ~d element~:p" (length value)))
        (t (format nil "a ~(~a~)" (type-of value)))))

(defun fnn-entry-guard (name args)
  "Refuse, by name, a call the entry NAME's arity or kind guards refuse."
  (let ((spec (fnn-entry-guard-spec name)))
    (unless (eq spec :unknown)
      (let ((given (length args)))
        (unless (= given (car spec))
          (error 'fnn-entry-guard-fault
                 :message (format nil "host-entry-guard: ~(~a~) takes ~d argument~:p (stobjs and state included); the host passed ~d"
                                  name (car spec) given))))
      (dolist (check (cdr spec))
        (destructuring-bind (position formal recognizer kind) check
          (let ((value (nth position args)))
            (unless (funcall recognizer value)
              (error 'fnn-entry-guard-fault
                     :message (format nil "host-entry-guard: ~(~a~) argument ~d (~(~a~)) must be ~a (~(~a~)); the host passed ~a"
                                      name (1+ position) formal kind recognizer
                                      (fnn-entry-guard-describe value))))))))))

(defun fnn-call (name &rest args)
  "Apply NAME's executable counterpart to ARGS, after the entry guard.

An explicit core result such as :REFUSED remains a semantic result for its
wrapper to handle.  A thrown condition or escaped raw evaluation is an
execution-boundary fault, never a claim that the core refused an input."
  (fnn-entry-guard name args)
  (let ((outcome :thrown) (values nil))
    (setq values
          (catch 'raw-ev-fncall
            (handler-case
                (prog1 (multiple-value-list (apply (fnn-dispatch-function name) args))
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

(defparameter +fnn-actions+
  '(:ready :prepared :durable :aborted :indeterminate :duplicate :conflict :absent :invalid
    :refused :article-numbers-exhausted :fault :recovering :frontier-staged :frontier-data-durable :frontier-attempted
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
  "ACL2's decoded store profile (the one format, D34).  The host keeps the
value opaque and reads every field through an ACL2 accessor.  The verdict is
ACL2's open (books/store-profile-open.lisp fn-spo-config-open): a profile
frame of another format word is refused by name, exit 1, with ACL2's line
(\"not an fn store of this release: redeploy fresh\"); a frame that is no
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

;; test-only (tools/host_callers.py): tests/test_spec_cite_check.py
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

(defun fnn-bridge-reset () (fnn-action (fnn-core-state 'fn-store-sn-reset)))
(defun fnn-bridge-record-sequence (record)
  (fnn-nat (fnn-core 'fn-store-record-sequence (fnn-octet-list record))))
(defun fnn-bridge-recover (next-chunk frontier config-records)
  "Replay the configuration history and then the article history.

The core replays `config-records' with the article records through
`fn-cpr-replay', takes the allocation domain and the capacity from the
configured node, and opens the observed store through `fn-cpo-open-observed'
(host/store-node-host.lisp `fn-store-sn-recover-rows'); a store with no
configuration record never reaches here.

The history goes over in chunks. The file reader uses fn-srs-checked-decode;
the pack path uses fn-store-decode-records. The guard-verified sequential
worker fn-ssr-intern-step carries the active statement keyring, generation
and identity cursor between records. fn-ssr-resident-step-of-append equates
arbitrary resident chunking, including the resulting arena. Its physical
modes refine that resident worker under fn-arena-p and faithful placement:
fn-ssr-extent-step-refines-resident and fn-ssr-lz-step-refines-resident.
The host passes ACL2's values back unchanged. Full replay clears the arena
and any previous selected checkpoint before initializing the epoch."
  (let ((replay (fnn-bridge-recover-begin)))
    (loop
      (let ((decoded (funcall next-chunk)))
        (when (eq decoded :end) (return))
        (when (eq decoded :sequence)
          (fnn-fault "record sequence does not match immutable filename"))
        (unless (fnn-bridge-recover-step replay decoded)
          (return-from fnn-bridge-recover :fault))))
    (fnn-bridge-recover-end replay frontier config-records)))

;; fnn-bridge-recover's three parts, in its order, for a history that arrives
;; a record at a time (the open, fnn-recover-log-stream-replay): the
;; arena cleared, each decoded chunk interned by the guard-verified
;; fn-ssr-intern-step (rows and the statement epoch in one cell), then the open
;; over the rows.
(defun fnn-bridge-recover-begin ()
  (fnn-core-state 'fn-store-sco-clear)
  (fnn-call 'fn-arena-clear (fnn-live-arena))
  (list (fnn-core 'fn-ssr-seed (fnn-core 'fn-stxk-initial-context 0))))

(defun fnn-bridge-recover-step (replay decoded)
  "Intern one decoded chunk; NIL when ACL2 answered :bad (a fault)."
  (let ((acc (first (fnn-call 'fn-ssr-intern-step (car replay) decoded nil nil :resident nil (fnn-live-arena)))))
    (setf (car replay) acc)
    (not (eq acc :bad))))


(defun fnn-bridge-recover-step-extents (replay decoded chunk places)
  "fnn-bridge-recover-step with the chunk's octets and places: the guard-
verified fn-ssr-intern-step :extent preserves the sequential identity epoch
and seals a faithful payload placement; NIL on :bad."
  (let ((acc (first (fnn-call 'fn-ssr-intern-step (car replay) decoded chunk places :extent nil
                              (fnn-live-arena)))))
    (unless (eq acc :bad)
      (setf (car replay) acc)
      t)))

(defun fnn-bridge-recover-step-lz (replay decoded stored places)
  "fnn-bridge-recover-step-extents for a chunk holding compressed records:
the guard-verified fn-ssr-intern-step :lz over
the decoded expansions, the octets the log holds (STORED) and their places,
with the store's dictionaries; NIL on :bad."
  (let ((acc (first (fnn-call 'fn-ssr-intern-step (car replay) decoded stored places :lz
                              (fnn-lz-dicts) (fnn-live-arena)))))
    (unless (eq acc :bad)
      (setf (car replay) acc)
      t)))

(defun fnn-bridge-recover-end (replay frontier config-records)
  (fnn-action (fnn-core-state 'fn-store-sn-recover-rows
                              (fnn-core 'fn-ssr-rows (car replay)) frontier
                              (mapcar #'fnn-octet-list config-records))))

(defun fnn-recover-record-chunks (records)
  "A chunk source over RECORDS (octet vectors, or octet lists: the log
kernel's committed records, taken as they are; checked already): each call
converts the next chunk to octet lists and answers ACL2's decode of it; a
chunk closes where ACL2 says (`fn-srs-chunk-fullp', a work quantum: one
record is always taken first, so no record is refused or split for its size)."
  (lambda ()
    (if (null records)
        :end
        (let ((chunk nil) (octets 0))
          (loop while (and records (not (fnn-core 'fn-srs-chunk-fullp octets))) do
            (let ((record (pop records)))
              (incf octets (length record))
              (push (fnn-octet-list record) chunk)))
          (fnn-core 'fn-store-decode-records (nreverse chunk))))))

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

(defun fnn-monotonic-ms ()
  "One monotonic reading, in milliseconds: SBCL's tick counter and its rate,
converted by ACL2 (books/clock-wall-reading.lisp fn-otm-monotonic-ms; PRF-305,
books/clock-reading.lisp fn-clkr-monotonic-readings-are-the-ns-decision)."
  (fnn-core 'fn-otm-monotonic-ms (get-internal-real-time)
            internal-time-units-per-second))

(defun fnn-owner-wall-milliseconds ()
  "One gettimeofday reading since 2000-01-01; the second value says if usable.
Lane time-model-2 (N3 of lane proto-determinism): ACL2 decides both from the
raw reading (books/clock-wall-reading.lisp fn-otm-wall-reading, whose DTN
epoch is ACL2's constant: PRF-305); the host computes and compares nothing."
  (handler-case
      (multiple-value-bind (seconds microseconds) (sb-ext:get-time-of-day)
        (destructuring-bind (wall has-wall)
            (fnn-core 'fn-otm-wall-reading seconds microseconds)
          (unless (and (integerp wall) (<= 0 wall) (member has-wall '(t nil)))
            (fnn-fault "ACL2 returned a malformed wall reading"))
          (values wall has-wall)))
    (fnn-store-fault (condition) (error condition))
    (error () (values 0 nil))))

(defun fnn-test-clock-readings ()
  "Developer-only FN_NATIVE_TEST_CLOCK=MONO-MS:SECONDS:MICROSECONDS: the
readings a prepare's observation is taken from, recorded instead of read (the
extraction gate's stateful differential gives the image and the extracted
program the same environment).  NIL when unset."
  (let ((raw (fnn-developer-selector "FN_NATIVE_TEST_CLOCK")))
    (when raw
      (let* ((a (position #\: raw)) (b (and a (position #\: raw :start (1+ a))))
             (words (and b (list (subseq raw 0 a) (subseq raw (1+ a) b) (subseq raw (1+ b))))))
        (unless (and words (every (lambda (w) (and (plusp (length w)) (<= (length w) 18)
                                                   (every #'digit-char-p w)))
                                  words))
          (fnn-fault "invalid FN_NATIVE_TEST_CLOCK (expected MONO-MS:SECONDS:MICROSECONDS)"))
        (mapcar #'parse-integer words)))))

(defun fnn-store-prepare-observation ()
  (let ((recorded (fnn-test-clock-readings)))
    (if recorded
        (destructuring-bind (wall has-wall)
            (fnn-core 'fn-otm-wall-reading (second recorded) (third recorded))
          (unless (and (integerp wall) (<= 0 wall) (member has-wall '(t nil)))
            (fnn-fault "ACL2 returned a malformed wall reading"))
          (fnn-core 'fn-clock-observation (first recorded) wall +fnn-owner-wall-error-ms+ has-wall))
      (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
        (fnn-core 'fn-clock-observation (fnn-monotonic-ms)
                  wall +fnn-owner-wall-error-ms+ has-wall)))))

(defun fnn-seal-octets (octets)
  "The arena update a prepare names: seal OCTETS (the octet list the core
answered with) through the guard-verified `fn-arena-seal-list'
(books/payload-arena.lisp).  The core entries only READ the arena: an entry
that also sealed would carry ACL2's invariant-risk and run through its *1*
body, checking every callee's guard (the whole history, per POST)."
  (fnn-call 'fn-arena-seal-list octets (fnn-live-arena))
  t)

(defvar *fnn-staged-handle* nil
  "The handle the owner's last buffer prepare sealed (staged: books/payload-
arena-extent.lisp), for the next record the log takes (fnn-log-take); ACL2
checks the pairing before any reseat (fn-arx-commit-extent).")

(defun fnn-seal-live-buffer ()
  "The arena update the owner's buffer prepare names (:seal-buffer): seal the
octet buffer's payload through the guard-verified `fn-arena-seal-buffer'
(books/payload-arena.lisp); see FNN-SEAL-OCTETS.  The node's arena stages
the copy (a page of its own) until the commit reseats it as its log extent."
  (let ((arena (fnn-live-arena)))
    (setq *fnn-staged-handle* (first (fnn-call 'fn-arena-count arena)))
    (fnn-call 'fn-arena-seal-buffer (fnn-live-octets) arena))
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

(defun fnn-bridge-identity-reservation (operation)
  (when operation
    (fnn-fault "standalone writer has no retention identity grant"))
  (fnn-core-state 'fn-store-sn-identity-reservation))

(defvar *fnn-identity-reservation-callback* #'fnn-bridge-identity-reservation)
(defvar *fnn-finish-callback* #'fnn-bridge-finish)
; Developer fault cut, dynamically scoped to one canonical Store publication.
; NIL in normal operation.  The cut runs after the final link and before its
; directory barrier, so an injected EIO is an uncertain publication.
(defvar *fnn-record-barrier-fault-observer* nil)
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
  ;; PKT-665: the record carries this host's clock (milliseconds, the
  ;; record stamp's unit, PRF-378), the creation time of every initial
  ;; group; ACL2 keeps the wall claim or its absence (PRF-379).
  (let ((value (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
                 (fnn-core 'fn-cfg-host-initial-octets-at
                           (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) names)
                           (fnn-monotonic-ms)
                           wall has-wall))))
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
realised by BLAKE3 (`fn-blake3-stobj') through `books/crypto-attach.lisp'.
This host once ran a SHA-256 of its own here, which made three separate
digests the owners of one decision -- the other two being
`tools/frame_bridge.py' and `tools/run_owner.py' -- and that is what
AGENTS.md's one-owner rule forbids.  The diagnostic `blake3' verb asks ACL2
too; this host has no digest of its own (host/native/digest.lisp's C
BLAKE3 replaces ACL2's executable only after checking it against it)."
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

(defun fnn-subject-id (payload)
  "Content identity v1 (books/identity), derived end to end in ACL2.
`books/crypto-attach.lisp' attaches BLAKE3 to `fn-frame-digest', so the
preimage AND the digest are ACL2's; this host no longer hashes for identity,
because a second digest here would be a second owner of the derivation.
Hashing the bare payload is the v0 profile and derives a different identity,
which `fn-store-sn-prepare' then refuses."
  (fnn-as-octets (fnn-core 'fn-store-subject-id-of-payload
                           (fnn-octet-list payload))))

(defun fnn-subject-id-buffer ()
  "FNN-SUBJECT-ID of the payload in the octet buffer, digested in place.
books/subject-id-buffer.lisp `fn-sidb-subject-id-bounded', guard-verified with
guard T, so the call runs the compiled stobj code and ACL2 raises no
invariant-risk warning on standard output (qual-e747dbcc A4): the subject
preimage's fixed head is a short list and the payload is read from the
buffer by index, so no octet list of the payload is built for the digest
(D27 wave C; the served POST, host/native/owner.lisp fnn-owner-attempt)."
  (fnn-as-octets (fnn-core 'fn-sidb-subject-id-bounded (fnn-live-octets))))

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
  root writable lock-fd config frontier fenced
  ;; The profile config.json seals (the genesis digest's subject); CONFIG is
  ;; the served one, SEALED under the configuration history's limit rows
  ;; (fnn-load-config, books/limits-live.lisp).
  (sealed-config nil) (orphans nil) (orphans-more nil)
  ;; Row S1: how long this open took, in milliseconds (an observation; the
  ;; next start's open takes about as long): the limit verb's words read it.
  (open-ms 0)
  (completion-pending nil)
  ;; P3: how the last open reached the Store state: (:checkpoint S K) or
  ;; (:full-replay REASON).  `operator status' prints it.
  (open-mode '(:full-replay :absent))
  ;; The replayed configuration the core hands back at recover.  The host
  ;; stores it and passes it back; it derives no name, code or generation.
  (config-generation nil) (config-served nil) (config-domain nil)
  ;; The one scripted fault point, or NIL: tools/run_store.py's ScriptedFaults.
  (fault-point nil) (fault-class nil) (fault-message nil)
  ;; The open answers the history's record COUNT and keeps no records
  ;; (PKT-823); a verb that needs them reads them after the open
  ;; (fnn-history-records).  The open records here how the log
  ;; holds the history (fnn-recover-log): (PREFIXP CLOSED GENESIS ACTIVE):
  ;; whether a checkpoint covers dropped segments (the prefix is then its
  ;; rows'), the closed segments scanned and the genesis the scan started
  ;; from, and the active segment's index (fnn-log-history-records).
  (log-history nil)
  ;; The newest record the open's scan handed to its sink (ACL2's octet
  ;; list) and the active segment's committed count when the open ended:
  ;; (COUNT RECORD), or NIL.  fnn-history-last-record answers it while the
  ;; kernel's count is still COUNT (nothing committed since the open)
  ;; instead of reading the log again (lane snapshot-open: that re-read was
  ;; 1.3 s of a 40k open and 33 s of a 10k x 32 KiB one).
  (log-last nil)
  ;; Lane commit-onto-log: the commit route ACL2 names from the profile
  ;; (fn-store-profile-logp) and, on that route, the open record
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
          ;; A test-only setup action.  fnn-config-record-names invokes this
          ;; immediately before its real fnn-list-directory call, so that call
          ;; itself returns EACCES.  A handler that turned its error into NIL
          ;; would make the regression test below falsely succeed.
          ((eq (fnn-store-fault-class store) :fnn-test-config-no-read)
           (fnn-chmod (fnn-config-dir store) #o000))
          (t
           (error (fnn-store-fault-class store) :message (fnn-store-fault-message store))))))

(defun fnn-config-path (s) (fnn-join (fnn-store-root s) "config.json"))
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
;; The record log's directory and its one segment.  The name is
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

(defun fnn-refuse-another-format (store)
  "A store whose config.json ACL2's open names as another format
(`:store-format') is refused by ACL2's line before any other check reads the
store; anything else is left to the ordinary open."
  (let ((path (fnn-config-path store)))
    (when (ignore-errors (fnn-check-regular path))
      (let* ((raw (ignore-errors (fnn-read-regular-bounded path 16384)))
             (verdict (and raw (> (length raw) 0)
                           (fnn-core 'fn-store-metadata-config-open (fnn-octet-list raw)))))
        (when (and (consp verdict) (eq (first verdict) :refused)
                   (eq (second verdict) :store-format))
          (error 'fnn-store-profile-refusal
                 :message (fnn-core 'fn-store-metadata-config-refusal-text verdict)))))))

(defun fnn-load-config (store)
  (fnn-check-regular (fnn-config-path store))
  (let ((raw (handler-case
                 (fnn-read-regular-bounded (fnn-config-path store) 16384)
               (fnn-os-error (e) (fnn-fault "invalid durable config: ~a" e)))))
    (let ((sealed (fnn-metadata-config-decode raw)))
      (setf (fnn-store-sealed-config store) sealed
            (fnn-store-config store) sealed)
      ;; The live limits (row S1): the configuration history's :set-limit
      ;; rows over the sealed profile, read before any bound of the log
      ;; applies (the history's own readdir bound is a sealed field).
      (when (let ((st (fnn-lstat (fnn-config-dir store))))
              (and st (fnn-directory-p st) (not (fnn-symlink-p st))))
        (let ((observation (fnn-config-record-observation store)))
          (when observation
            (setf (fnn-store-config store)
                  (fnn-core 'fn-store-lim-effective sealed
                            (mapcar #'fnn-octet-list (mapcar #'cdr observation))))))))))

(defun fnn-initialize (store &optional (groups +fnn-default-groups+) (profile :development))
  ;; One durable configuration record at generation 1, built and admitted by
  ;; the core from the operator's group names.  The program is ACL2's:
  ;; books/byte-store-log-initializer.lisp fn-bsi-log-init-program (journal/
  ;; and the segment; every profile is on the record log, fn-store-profile-logp).
  (let ((logp (fnn-core 'fn-store-profile-logp
                        (fnn-metadata-config-decode (fnn-metadata-config-frame profile)))))
    (unless logp
      (fnn-fault "the init profile is not a record-log profile"))
    (fnn-safe-directory (fnn-store-root store) t store
                        "init-root-mkdir" "init-root-parent-fenced")
    (fnn-require-clone-activated store)
    (let ((lock-fd (fnn-open-lock store t t)))
      (unwind-protect
           (progn
             (fnn-init-cut store "init-lock-created")
             (fnn-safe-directory (fnn-staging store) t store
                                 "init-staging-mkdir" "init-staging-parent-fenced")
             (fnn-safe-directory (fnn-config-dir store) t store
                                 "init-config-dir-mkdir" "init-config-dir-parent-fenced")
             (fnn-safe-directory (fnn-journal-dir store) t store
                                 "init-journal-mkdir" "init-journal-parent-fenced")
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
             ;; Format 10: the genesis at position 0 (books/store-genesis.lisp),
             ;; then fn-bsi-log-segment-steps.
             (fnn-log-init-genesis store)
             (fnn-log-init-segment store)
             (fnn-fsync-regular (fnn-config-path store))
             (fnn-init-cut store "init-final-config-file-fenced")
             (dolist (name (fnn-config-record-names store :init-config-records-final-enumerate))
               (fnn-fsync-regular (fnn-join (fnn-config-dir store) name))
               ;; The fresh branch has generation 1 only.  Existing history is
               ;; intentionally outside this packet.
               (fnn-init-cut store "init-final-config-record-file-fenced"))
             (fnn-fsync-dir (fnn-store-root store))
             (fnn-init-cut store "init-root-fenced")
             (fnn-fsync-dir (fnn-parent (fnn-store-root store)))
             (fnn-init-cut store "init-parent-fenced"))
        (ignore-errors (fnn-flock lock-fd +fnn-lock-un+))
        (fnn-close lock-fd)))))

(defun fnn-acquire (store)
  (fnn-safe-directory (fnn-store-root store))
  (fnn-require-clone-activated store)
  ;; Format 10 (lane format-bump-10): a store of another format is named
  ;; first.  Its filesystem record is a frame of its own release's digest, so
  ;; the record check below would call a store's record undecodable
  ;; and point at `rebind-filesystem'; the profile's open (ACL2's
  ;; fn-spo-config-open) names the format and the way out instead.
  (fnn-refuse-another-format store)
  ;; PKT-579: the store root is on the filesystem its record names, or the
  ;; open is refused by name before anything else is read.
  (fnn-check-filesystem-identity store)
  (fnn-safe-directory (fnn-staging store))
  (handler-case
      (progn
        (setf (fnn-store-lock-fd store)
              (fnn-open-lock store (fnn-store-writable store) (fnn-store-writable store)))
        (fnn-load-config store)
        ;; The commit route is ACL2's reading of the profile (the
        ;; record log); the host keeps the answer and decides nothing.
        (setf (fnn-store-logp store)
              (and (fnn-core 'fn-store-profile-logp (fnn-store-config store)) t))
        ;; Format 8 is refused by name at the profile's open
        ;; (books/store-profile-open.lisp); a profile ACL2 does not read as the
        ;; record log is a fault.  The frontier is derived from the log at
        ;; recovery (fnn-recover-log).
        (unless (fnn-store-logp store)
          (fnn-fault "a store that is not on the record log opened"))
        (fnn-safe-directory (fnn-journal-dir store)))
    (error (e) (fnn-store-close store) (error e))))

(defun fnn-store-close (store)
  (setf (fnn-store-completion-pending store) nil)
  (let ((log (fnn-store-log store)))
    (when log
      (setf (fnn-store-log store) nil)
      (ignore-errors (fnn-log-discard-spare log))
      (ignore-errors (fnn-close (fnn-log-fd log)))))
  (let ((fd (fnn-store-lock-fd store)))
    (when fd
      (setf (fnn-store-lock-fd store) nil)
      (unwind-protect (fnn-flock fd +fnn-lock-un+)
        (fnn-close fd)))))

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

;; thread-confined: the open (the state checkpoint's plan and load)
(defvar *fnn-checkpoint-image* nil
  "(PATH NP BASE) of the history image region the last plan found at the
checkpoint file's start, or NIL.")

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
    (setq *fnn-checkpoint-image* nil)
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
                  (let ((np (and (= at 0) (null frames)
                                 (fnn-core 'fn-his-image-header-np
                                           (fnn-octet-list
                                            (concatenate '(vector (unsigned-byte 8)) first rest))))))
                   ;; The history image region (books/history-image-snapshot.lisp):
                   ;; ACL2 recognized its header at the file's start; the framed
                   ;; segments begin after it.  Its pages are not read here: the
                   ;; open adopts the image and reads a page at first touch.
                   (if (integerp np)
                       (progn
                         (sb-posix:lseek fd (+ header-octets (fnn-core 'fn-his-skip-octets np))
                                         sb-posix:seek-set)
                         (setq *fnn-checkpoint-image* (list path np (fnn-core 'fn-his-base-octets))))
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
                             (incf total extent)))))))))))
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
               (multiple-value-bind (st s)
                   (fnn-state-checkpoint-load-arena (second answer) (third answer)
                                                    (fourth answer))
                 (if (and (eq st :ok) *fnn-checkpoint-image*)
                     (fnn-state-checkpoint-adopt-image store s)
                     (values st s)))
               ;; A file without the arena run (tables-only, written before
               ;; the flip) is refused by name: reason=checkpoint-arena.
               (values (if (equal answer '(:refused :arena)) :arena :refused) 0)))))))

(defun fnn-state-checkpoint-adopt-image (store s)
  "The checkpoint's history image adopted (host/store-node-host.lisp
fn-store-sco-image-open over the live fn-hrecs$c: the binding checked against
this store's genesis, the log position and the codec; page 0 read and
checked; the last row compared with the checkpoint's last record): (values
:ok S), or the checkpoint is unusable, refused BY NAME on stderr, (values
:refused 0), and the open goes on as for a corrupt checkpoint."
  (destructuring-bind (path np base) *fnn-checkpoint-image*
    (declare (ignore np))
    (fnn-genesis-open store)
    (let* ((file (fnn-extent-register-at path base))
           (answer (fnn-call 'fn-store-sco-image-open file (fnn-live-hrecs) *the-live-state*))
           (verdict (second answer)))
      (unless (and (consp answer) (null (first answer)))
        (fnn-fault "ACL2 error in fn-store-sco-image-open"))
      ;; checked; the adopted words are not kept (nothing reads them yet)
      (fnn-call 'fn-his-release (fnn-live-hrecs))
      (if (null verdict)
          (values :ok s)
          (progn
            ;; ~s: the verdict's keywords keep their colons, so
            ;; (:refused :store-identity) is told apart from a symbol list.
            (fnn-err "checkpoint image refused reason=~(~s~)" verdict)
            (fnn-core-state 'fn-store-sco-clear)
            (values :refused 0))))))

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
      ;; PKT-854: the arena is exactly the checkpoint's payloads here; a
      ;; requested checkpoint digest takes its pool now (a no-op otherwise).
      (when (and (consp answer) (eq (first answer) :ok))
        (fnn-core-state 'fn-store-sco-note-checkpoint-digest))
      (if (and (consp answer) (eq (first answer) :ok)
               (integerp (second answer)) (>= (second answer) 0))
          (values :ok (second answer))
          (values :refused 0)))))

(defun fnn-recover-suffix-intern (suffix configs acc)
  "Intern decoded suffix chunks over the arena left by the selected checkpoint.
fn-store-statement-replay-seed reads the selected fn-store-sco-current
checkpoint's captured identity epoch; it never uses the current live keyring.
fn-ssr-intern-step :resident carries that keyring, generation and cursor
between every record and chunk. fn-ssr-resident-step-of-append proves the
chunk composition, including arena effects, under true-listp of the first
chunk. The result is (values ROWS ACC2), rows oldest first (fn-ssr-rows),
or :bad on invalid configuration, decode or identity replay. ACC2 is
fn-ofw-wire-next over decoded events, starting at ACC. The suffix is decoded
one work quantum at a time using fn-srs-chunk-fullp."
  (if (eq (fnn-core 'fn-store-sn-recover-records nil configs) :bad)
      (values :bad acc)
      (let ((next (fnn-recover-record-chunks suffix)) (rows (fnn-core-state 'fn-store-statement-replay-seed)) (fold acc))
        (loop
          (let ((decoded (funcall next)))
            (when (eq decoded :end) (return))
            (when (eq decoded :bad) (return-from fnn-recover-suffix-intern (values :bad acc)))
            (setq fold (fnn-core 'fn-ofw-wire-next decoded fold)
                  rows (first (fnn-call 'fn-ssr-intern-step rows decoded nil nil :resident nil (fnn-live-arena))))
            (when (eq rows :bad) (return-from fnn-recover-suffix-intern (values :bad acc)))))
        (values (fnn-core 'fn-ssr-rows rows) fold))))

(defun fnn-recover-suffix-rows (store suffix config-records &optional (interned nil internedp))
  "The open from the loaded checkpoint: the suffix decoded and interned ON
TOP of the arena the load left, a chunk at a time (fnn-recover-suffix-intern;
INTERNED, its rows, when the caller interned SUFFIX with it already; the
canonical handles continue from the checkpoint's payload count), then the
open over the rows (fn-store-sn-recover-from-checkpoint).  The calls are
fn-scka-recover-rows over the host's extension (books/store-checkpoint-
arena.lisp, KEYSTONE fn-scka-recover-from-checkpoint-is-full-recover), its
intern chunked (fnn-recover-suffix-intern's keystones)."
  (let* ((configs (mapcar #'fnn-octet-list config-records))
         (rows (if internedp interned (values (fnn-recover-suffix-intern suffix configs 0)))))
    (if (eq rows :bad)
        :fault
        (fnn-action (fnn-core-state 'fn-store-sn-recover-from-checkpoint
                                    rows (fnn-store-frontier store) configs)))))


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
  (fnn-state-checkpoint-install store (fnn-state-checkpoint-stage store octets)))

(defun fnn-state-checkpoint-stage (store octets)
  "fnn-state-checkpoint-write's first half: the staged file written and fenced
(cuts created, written, staged-durable).  A failure is known: the old
checkpoint stays.  Answers the staged path, for fnn-state-checkpoint-install
(Q16's reclaim pass stages off the owner mutex and installs under it)."
  (let ((stage (fnn-join (fnn-staging store)
                         (format nil ".stage-checkpoint-~d-~a" (sb-posix:getpid) (fnn-random-hex 12)))))
    (handler-case
        (progn
          (fnn-write-staged-at store stage octets
                               :state-checkpoint-created :state-checkpoint-written)
          (fnn-at store :state-checkpoint-staged-durable)
          stage)
      (fnn-os-error (e)
        (fnn-refuse-io "known failure before the state checkpoint replacement: ~a" e)))))

(defun fnn-state-checkpoint-install (store stage)
  "fnn-state-checkpoint-write's second half: the staged file STAGE renamed
onto the checkpoint name and the root fenced (cuts replaced, durable).  From
the rename on the outcome is uncertain (the old or the new file, never a torn
one: fn-bs-scp-program-crash-is-old-or-new)."
  (handler-case
      (progn
        (fnn-replace stage (fnn-state-checkpoint-path store))
        (fnn-at store :state-checkpoint-replaced)
        (fnn-fsync-dir (fnn-store-root store))
        (fnn-at store :state-checkpoint-durable))
    (fnn-os-error (e)
      (fnn-indeterminate "state checkpoint replacement is indeterminate: ~a" e))))

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

;; PKT-169: a state checkpoint's temporary space is checked against the
;; disk.  The host observes the free octets of the store's filesystem
;; (statvfs: f_bavail blocks of f_frsize octets, what an unprivileged writer
;; may use) and ACL2 decides (host/store-node-host.lisp
;; `fn-store-sco-publish-setup' for `store compact' and `store reclaim',
;; host/owner-host.lisp `fn-owner-sco-due' for the owner's checkpoint).
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

(defun fnn-disk-free-cap-text (cap)
  "The developer cap's text: CAP itself, or with a leading @ the first line
of the file it names, read at every observation (lane health-truth, PRF-359:
the native case fills and frees the disk while the owner runs; a missing
file is no cap)."
  (if (and (plusp (length cap)) (char= (char cap 0) #\@))
      (ignore-errors
       (with-open-file (in (subseq cap 1) :direction :input :if-does-not-exist nil)
         (and in (string-trim '(#\Space #\Newline #\Return #\Tab) (or (read-line in nil) "")))))
    cap))

(defun fnn-disk-free-octets (store)
  (let* ((free (fnn-statvfs-free-octets (fnn-store-root store)))
         (raw (fnn-developer-selector "FN_NATIVE_DISK_FREE"))
         (cap (and raw (fnn-disk-free-cap-text raw))))
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
load, but the identity is not checked: that is what this replaces.  The
store (ACL2's fn-store-profile-logp) has no frontier file: its
frontier is derived from the log at recovery, as fnn-acquire reads it.
REQUESTED is 1, 0 or NIL (keep the store's policy)."
  (let ((store (make-fnn-store root :writable t)))
    (fnn-safe-directory (fnn-store-root store))
    (fnn-safe-directory (fnn-staging store))
    (setf (fnn-store-lock-fd store) (fnn-open-lock store t nil))
    (unwind-protect
         (progn
           (fnn-load-config store)
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

;;; Lane scale-reads: a stop ends a checkpoint publication at its next batch.
;;; The owner's publication thread binds this to a test of the service's stop
;;; fence (host/native/owner.lisp fnn-owner-publish-captured); each batch loop
;;; below asks it first and, when it answers true, ends the publication as a
;;; known failure before the rename (fnn-refuse-io): the staged file is
;;; dropped and the old checkpoint, or none, stays -- the state a process
;;; death between two batches leaves (fn-bs-scp-program-crash-is-old-or-new),
;;; and the record log stays authoritative.  Before this the stop joined the
;;; publication, which walks the whole history: at syn100k-2k the owner took
;;; 102 s to stop.  Unbound (the offline verbs), nothing is asked.
(defvar *fnn-checkpoint-stop-test* nil)

(defun fnn-checkpoint-yield (where count)
  "Refuse the publication at a batch boundary when the owner is stopping."
  (let ((test *fnn-checkpoint-stop-test*))
    (when (and test (funcall test))
      (fnn-refuse-io "the owner is stopping: the checkpoint publication ends before ~a batch ~d; the old checkpoint stays"
                     where count))))

(defun fnn-checkpoint-walk (records)
  "The walk of the owner's captured RECORDS: each canonical payload's length
and source (books/store-checkpoint-arena-writer.lisp fn-scka-srcs-n), a
bounded number of rows per call (+fnn-checkpoint-batch-rows+; the calls are
one walk: fn-scka-srcs-n-compose).  READS the arena.  The last state,
(ROWS' LACC SACC), ROWS' empty."
  (let ((walk (list records nil nil)) (arena (fnn-live-arena)))
    (loop
      (when (atom (first walk)) (return walk))
      (fnn-checkpoint-yield "walk" (length (second walk)))
      (setq walk (fnn-core 'fn-scka-srcs-n (first walk) +fnn-checkpoint-batch-rows+
                           (second walk) (third walk) arena))
      (unless (and (consp walk) (= (length walk) 3))
        (fnn-fault "ACL2 returned a malformed checkpoint walk")))))

(defvar *fnn-checkpoint-frames* :off
  "The owner's publication binds this to a list: the arena run's payload
frames written, newest first, each (EOFF ELEN HANDLES) -- the entry's file
offset (the frame start less 32), its protected prefix's length, and the
step's handles (fn-xrt-step-handles).  :off for the offline verbs.")

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
        (fnn-checkpoint-yield "arena" steps)
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
            ;; The owner's publication keeps, per payload frame, where it
            ;; lies and the handles it holds, for the reseat after the
            ;; install (books/extent-retire.lisp fn-xrt-step-handles; the
            ;; frame's entry opens 32 octets before it, at the previous
            ;; frame's trailer).
            (when (listp *fnn-checkpoint-frames*)
              (let ((handles (fnn-core 'fn-xrt-step-handles state)))
                (when (and (consp handles) (= (length frames) 1))
                  (let ((at (sb-posix:lseek fd 0 sb-posix:seek-cur))
                        (frame (first frames)))
                    (when (>= at 32)
                      (push (list (- at 32)
                                  (+ 32 (length (first frame)) (- (third frame) (second frame)))
                                  handles)
                            *fnn-checkpoint-frames*))))))
            (fnn-plan-write-all fd frames st)
            (setq state next)
            (incf steps)
            (when (and fault (= steps (1+ fault)))
              (sb-posix:kill (sb-posix:getpid) sb-posix:sigkill))))))))

;;; The history image region of the state checkpoint's file (lane
;;; composed-owner; books/history-image-snapshot.lisp).  The file opens with
;;; the image of the checkpoint's records on a page store: ACL2 builds and
;;; commits it (fn-his-snapshot over the live fn-hrecs$c) and answers the
;;; pages to write (ADDR SEL A); the host writes the region's header
;;; (fn-his-image-header), zeros to the region's base, then page ADDR's 2048
;;; words (fn-his-words) little-endian at base + 16 KiB * ADDR, zeros where
;;; no page is named.  The binding (fn-his-binding) goes into the F row's log
;;; position, so the image and the fold state are one file, one rename.  The
;;; host computes no address, digest or length: every one is ACL2's.

(defvar *fnn-live-hrecs* nil)

(defun fnn-live-hrecs ()
  (or *fnn-live-hrecs*
      (setq *fnn-live-hrecs*
            (or (cdr (assoc 'fn-hrecs$c (user-stobj-alist *the-live-state*)))
                (fnn-fault "the history image stobj is not in this image")))))

(defun fnn-history-image-build (records node salt position)
  "The image of RECORDS for a publication whose log POSITION is (K TRAIL):
(values POSITION' IMAGE), POSITION' = (K TRAIL BINDING) and IMAGE = (NP
WRITES); with no position, (values POSITION NIL): no binding, no image."
  (if (null position)
      (values position nil)
      (let ((answer (fnn-call 'fn-his-snapshot records salt (fnn-live-hrecs))))
        (unless (and (consp answer) (>= (length answer) 3))
          (fnn-fault "ACL2 returned a malformed history image"))
        (destructuring-bind (verdict rec writes &rest ignored) answer
          (declare (ignore ignored))
          (unless (eq verdict :ok)
            (fnn-refuse-io "history image refused by name: ~a" verdict))
          (let ((binding (fnn-core 'fn-his-binding node salt (length records) (second position) rec))
                (np (fnn-core 'fn-his-np writes 0)))
            (unless (and (integerp np) (> np 0))
              (fnn-fault "ACL2 returned a malformed history image page count"))
            (values (list (first position) (second position) binding) (list np writes)))))))

(defun fnn-history-image-np (image)
  "IMAGE's page count, or NIL for a publication without an image: what
ACL2's fn-his-stream-free and fn-his-file-octets (host/store-node-host.lisp)
take for the image region."
  (and image (first image)))

(defun fnn-history-image-write (fd image)
  "Write IMAGE's region at FD's current position (the file's start)."
  (when image
    (destructuring-bind (np writes) image
      (let ((header (fnn-octets (fnn-core 'fn-his-image-header np)))
            (skip (fnn-core 'fn-his-skip-octets np))
            (by-addr (make-hash-table))
            (zeros (make-array 16384 :element-type '(unsigned-byte 8) :initial-element 0))
            (page (make-array 16384 :element-type '(unsigned-byte 8))))
        (dolist (w writes) (setf (gethash (first w) by-addr) (rest w)))
        (fnn-write-range fd header 0 (length header))
        ;; zeros to the base: SKIP less the pages
        (let ((pad (- skip (* 16384 np))))
          (loop while (> pad 0) do
            (let ((k (min pad 16384))) (fnn-write-range fd zeros 0 k) (decf pad k))))
        (dotimes (addr np)
          (let ((w (gethash addr by-addr)))
            (if (null w)
                (fnn-write-range fd zeros 0 16384)
                (let ((words (fnn-core 'fn-his-words (first w) (second w) (fnn-live-hrecs))))
                  (unless (and (listp words) (= (length words) 2048))
                    (fnn-fault "ACL2 returned a malformed history image page"))
                  (let ((i 0))
                    (dolist (x words)
                      (dotimes (b 8)
                        (setf (aref page (+ i b)) (ldb (byte 8 (* 8 b)) x)))
                      (incf i 8)))
                  (fnn-write-range fd page 0 16384)))))
        ;; the image's words are not kept past the write
        (fnn-call 'fn-his-release (fnn-live-hrecs))))))

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
      (fnn-checkpoint-yield "table" steps)
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
publication buffer, one step's rows at a time.  On a store the log
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
         (position (fnn-log-rotate-now store))
         ;; one walk of the live rows, a bounded number per call: each
         ;; canonical payload's length and source (fn-store-sco-pass-step)
         (walked (progn
                   (fnn-core-state 'fn-store-sco-pass-begin)
                   (loop until (fnn-core-arena-state 'fn-store-sco-pass-step
                                                     +fnn-checkpoint-batch-rows+))
                   t))
         ;; the setup's first half (NEXT), then the history image of NEXT's
         ;; records (its binding into the F row's position), then the
         ;; second half over the position and the space left after the image
         (prepared (fnn-core-arena-state 'fn-store-sco-publish-next))
         (ident (fnn-core-state 'fn-store-genesis-ident))
         (image nil)
         (answer (multiple-value-bind (position2 image2)
                     (if prepared
                         (fnn-history-image-build (fnn-core 'fn-sco-records (first prepared))
                                                  (first ident) (second ident) position)
                         (values position nil))
                   (setq image image2)
                   (fnn-core-state 'fn-store-sco-publish-setup-of prepared segment budget
                                   (fnn-core 'fn-his-stream-free (fnn-disk-free-octets store)
                                             (fnn-history-image-np image))
                                   (fnn-checkpoint-revision) position2))))
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
                   (fnn-history-image-write fd image)
                   (setq steps (fnn-checkpoint-write-steps fd setup segment sequence
                                                           profile st arun))))
             (fnn-octets-pub-release))
           (when position
             (handler-case
                 (setq dropped (fnn-log-drop store (fnn-log-covered-indices store (first position))))
               (fnn-os-error (e)
                 (fnn-indeterminate "the drop of covered log segments is uncertain: ~a" e))))
           (format nil "checkpoint sequence=~d octets=~d steps=~d~@[ segment=~d~]~:[~; dropped=~d~] ~a"
                   sequence (fnn-core 'fn-his-file-octets (fnn-history-image-np image)
                                      (second verdict))
                   steps (first position) position dropped
                   (fnn-open-report store))))
        (t (fnn-fault "ACL2 returned a malformed checkpoint verdict"))))))

(defun fnn-command-store-digest (root)
  "`store ROOT digest': open the store read-only as `status' does (the shared
lock, so a running owner refuses this) and print ACL2's digest of the state
the open folded (host/store-node-host.lisp fn-store-sn-replay-digest-report,
books/state-digest.lisp), then the open line.  Two opens of the same history
print the same digests; tests/test_native_replay_determinism.py compares
them across processes, copies, checkpoint and full replay, and boxes."
  ;; PKT-854: the open's checkpoint load keeps its verifiable digest
  ;; (host/store-node-host.lisp fn-store-sco-note-checkpoint-digest).
  (fnn-core-state 'fn-store-sco-want-checkpoint-digest t)
  (multiple-value-bind (store count) (fnn-open-live-store root nil)
    (declare (ignore count))
    (unwind-protect
         (progn (fnn-write-report (fnn-core-state 'fn-store-sn-replay-digest-report))
                (fnn-out "~a" (fnn-open-report store))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-store-journal (root)
  "`store ROOT journal' (lane time-model-2, HST-028): read the decision
journal STORE/decisions/decisions.fnj back and print ACL2's one-line replay
(books/owner-time-journal.lisp fn-otm-journal-report: entries, segments,
whole/torn/malformed, and agrees or the first gap, divergence or malformed
entry).  It opens no store (a running owner keeps its journal open for
append; a torn last line is one the writer had not finished).  Exit 0 when
the replay agrees, 1 otherwise."
  (let ((path (fnn-join (fnn-join root "decisions") "decisions.fnj")))
    (unless (probe-file path)
      (fnn-refuse "no decision journal at ~a" path))
    (let* ((octets (with-open-file (in path :element-type '(unsigned-byte 8))
                     (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
                       (read-sequence v in)
                       (coerce v 'list))))
           (report (fnn-core 'fn-otm-journal-report octets)))
      (fnn-write-report report)
      (let ((exit (fnn-core 'fn-otm-journal-exit octets)))
        (unless (member exit '(0 1))
          (fnn-fault "ACL2 returned a malformed journal verdict"))
        exit))))

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
  "The open's recovery.  Every store an image opens is on the record
log; a format-8 profile is refused by name at the open,
books/store-profile-open.lisp fn-spo-open-of-a-format-8-profile-refuses-by-name):
fnn-recover-log.  Answers the history's record COUNT; the records themselves
are not kept (PKT-823): a caller that needs their octets reads them after the
open, a record at a time (`fnn-log-history-each')."
  (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil
        (fnn-store-open-mode store) '(:full-replay :absent))
  ;; the collector's trigger for the open (no effect on the store; before the
  ;; record-log guard, whose arm is the one call native_program_check reads)
  (fnn-open-nursery store)
  (unless (fnn-store-logp store)
    (fnn-fault "a store that is not on the record log opened"))
  (fnn-recover-log store))

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

(defun fnn-advance-frontier (store current-txid &optional operation)
  "The allocator's reservation: the record log's (fnn-log-reserve; the
frontier is derived from the log, design 2026-09-27 section 3.3)."
  (unless (fnn-store-logp store)
    (fnn-fault "a store that is not on the record log opened"))
  (fnn-log-reserve store current-txid operation))

(defun fnn-publish (store sequence record)
  "The record's publication: the record log's P-BATCH (fnn-log-publish)."
  ;; Developer injection only, no process-death cut (FN_NATIVE_POST_FAULT=
  ;; record-prepublish:refuse, fnn-post-test-fault): a known refusal before
  ;; anything of the record is written, which the owner resolves by ACL2's
  ;; known abort (host/native/owner.lisp fnn-owner-publish-prepared;
  ;; tests/test_native_known_abort.py).
  (fnn-at store :record-prepublish)
  (unless (fnn-store-logp store)
    (fnn-fault "a store that is not on the record log opened"))
  (fnn-log-publish store sequence record))

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
    ;; now (fn-lgc-finish-one).  Inside a batch the committer acknowledges
    ;; each member after the batch's barrier (fnn-log-batch-finish).
    (when (and (fnn-store-logp store) (not *fnn-log-batch*))
      (fnn-log-ack (fnn-store-log store) 1)
      ;; and its staged payload reseated as its log extent (PRF-309)
      (fnn-log-reseat-fenced (fnn-store-log store)))
    (handler-case (fnn-at store :finish-durable)
      (fnn-os-error (e)
        (setf (fnn-store-fenced store) t)
        (fnn-indeterminate "writer reopening interrupted after the consumed completion: ~a" e)))
    completion))

(defun fnn-identity-text (identity)
  "The one rendering of a canonical identity where a string is forced: a
store record metadata field, a journal record and an NNTP header all carry
text, and ACL2 decides what that text is.  A record field holds this, never
the canonical octets, which are not `fn-pfld-textp' (books/post-fields.lisp)."
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
        (let ((before (get-internal-real-time)))
          (fnn-bridge-reset)
          (let ((count (fnn-recover store)))
            (setf (fnn-store-open-ms store)
                  (floor (* 1000 (- (get-internal-real-time) before))
                         internal-time-units-per-second))
            (values store count)))
      (error (e) (fnn-store-close store) (error e)))))

(defun fnn-orphan-report (store)
  (if (null (fnn-store-orphans store))
      "staging-orphans=0"
      (format nil "staging-orphans=~d~:[~;+~] [~{~a~^ ~}]" (length (fnn-store-orphans store))
              (fnn-store-orphans-more store) (fnn-store-orphans store))))

;;; Commands.

(defparameter +fnn-init-model-cuts+
  '("init-root-mkdir" "init-root-parent-fenced" "init-lock-created"
    "init-staging-mkdir" "init-staging-parent-fenced"
    "init-config-dir-mkdir" "init-config-dir-parent-fenced"
    "init-config-created" "init-config-written" "init-config-file-fenced"
    "init-config-linked" "init-config-link-eexist" "init-config-root-fenced" "init-config-stage-unlinked"
    "init-history-created" "init-history-written" "init-history-file-fenced"
    "init-history-linked" "init-history-link-eexist" "init-history-root-fenced" "init-history-stage-unlinked"
    "init-config-history-fenced"
    "init-final-config-file-fenced" "init-final-config-record-file-fenced"
    "init-root-fenced" "init-parent-fenced"
    ;; books/byte-store-log-initializer.lisp fn-bsi-log-init-program (format 10:
    ;; the genesis, books/store-genesis.lisp, then segment 1).
    "init-journal-mkdir" "init-journal-parent-fenced"
    "init-genesis-created" "init-genesis-written" "init-genesis-file-fenced"
    "init-genesis-linked" "init-genesis-link-eexist" "init-genesis-root-fenced"
    "init-genesis-stage-unlinked" "init-genesis-journal-fenced"
    "init-segment-created" "init-segment-written" "init-segment-file-fenced"
    "init-journal-segment-fenced"))

;; These controls are intentionally outside fn-bsi-log-init-program: they
;; fail *before* a directory enumeration to verify the host does not confuse
;; an OS error with an empty configuration history.
(defparameter +fnn-init-test-controls+
  '("init-config-records-first-enumerate" "init-config-records-final-enumerate"))

;; The init publication's cuts (books/store-init-publication.lisp
;; *fn-bs-init-pub-cut-names*, which books/store-init-log-publication.lisp
;; fn-bs-init-log-program applies): the import's program with init's names,
;; in program order.
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
;; `recover-barrier' are fn-lg-open-program's own cuts
;; (books/store-log-route-programs.lisp); `recover-barrier-N' selects each of
;; the three model cuts.  `recovery-stage-unlinked' is
;; fn-bs-recover-stage-cleanup-program's cut, and that program runs once per
;; removed orphan AFTER fn-lg-open-program has completed: fnn-recover
;; sweeps only once the last barrier observation has reached :ready.
(defparameter +fnn-recovery-model-cuts+
  '("recover-replayed" "recover-barrier-1" "recover-barrier-2"
    "recover-barrier-3" "recovery-stage-unlinked"))

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
(books/store-init-log-publication.lisp fn-bs-init-log-program: the import's
steps with init's cut names, through fnn-staged-publication).  Its plan is
ACL2's: the profile, the generation-1 configuration record and the log's
first segment (fn-bs-init-log-files).  Before
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
      (unless logp
        (fnn-fault "the init profile is not a record-log profile"))
      (fnn-staged-publication
       "init" stage root-path
       ;; books/store-init-log-publication.lisp fn-bs-init-log-files, in
       ;; its order: the profile, the generation-1 configuration record,
       ;; the genesis (format 10, books/store-genesis.lisp), the segment's
       ;; ACL2 extent of zeros.  No allocator file and no transactions/.
       (list (cons (fnn-config-path stage) (fnn-metadata-config-frame profile))
             (cons (fnn-config-record-path stage 1) record)
             (cons (fnn-genesis-path stage)
                   (fnn-genesis-octets
                    (fnn-metadata-config-decode (fnn-metadata-config-frame profile))))
             (cons (fnn-segment-path stage)
                   (fnn-make-octets (fnn-nat (fnn-core 'fn-store-log-initial-extent)))))
       0
       (lambda (stage) (fnn-record-filesystem-at-init stage profile policy))
       (fnn-core 'fn-bs-init-log-subdir-names))
      ;; SEC-006: the node's key files, as `fnn-command-init' writes them,
      ;; once the store is published (outside fn-bs-init-log-program: a
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
  "Call FN on each record of a STORE's history, in log order, as
octets, read as the open read it (fnn-recover-log, its plan in
fnn-store-log-history): when a checkpoint covers dropped segments, the
covered prefix encoded from the loaded checkpoint's rows a chunk at a time
(fn-store-sco-prefix-octets-range); then each closed segment the open scanned,
read again from disk with the chain carried from the scan's genesis
(fnn-log-read-closed-segment); then the active segment's committed records
(fnn-log-read-active-segment: the open's, and every batch fenced since, to
the kernel's frontier).  No list of the
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
        (setq genesis (fnn-log-read-closed-segment store k genesis unit max
                                                   (lambda (r) (funcall fn (fnn-octets r))))))
      (fnn-log-check-history-chain store genesis))
    (fnn-log-read-active-segment store (lambda (r) (funcall fn (fnn-octets r))))))

(defun fnn-log-check-history-chain (store last)
  "LAST, the last trailer of the closed segments read again, must be the active
segment's genesis (books/store-log-damage.lisp fn-lgdm-chain-continues-p):
else a closed segment changed since the open, refused by name."
  (unless (fnn-core 'fn-lgdm-chain-continues-p last (fnn-log-genesis (fnn-store-log store)))
    (error 'fnn-store-open-refusal :message (fnn-core 'fn-lgdm-history-break-text))))

(defun fnn-log-history-records (store)
  "A STORE's history as a list, each record's exact octets in log
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
      (fnn-fault "a store's history was read before its open"))
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
        (setq genesis (fnn-log-read-closed-segment store k genesis unit max
                                                   (lambda (r) (push (fnn-octets r) parts)))))
      (fnn-log-check-history-chain store genesis)
      (nreverse parts))))

(defun fnn-history-records (store)
  "The history of the acquired and opened STORE as the open reads it, each
record's exact octets in sequence order (the one store format, D34): the
record log as the open read it (`fnn-log-history-records'); the
per-file branch went with the per-file layout (PKT-838).  The open no longer keeps them
(PKT-823): a verb that needs the records' octets after `fnn-open-live-store'
reads them here, under the lock the open took, which no writer shares, so
they are the records the open replayed.  No file length or directory listing
stands in for a record."
  (unless (fnn-store-logp store)
    (fnn-fault "a store that is not on the record log opened"))
  (fnn-log-history-records store))

(defun fnn-history-last-record (store)
  "The history's newest record's octets, or NIL when there is none.  Read
after the open, under its lock, so it is the record the open replayed last:
the open's own newest record while nothing was committed since
(snapshot-open), else the active segment's last committed record
(fnn-log-read-active-segment), else the last closed segment's the open
scanned, else (a checkpoint open whose suffix is empty) the covered prefix's
last (fn-store-sco-last-record-octets)."
  (unless (fnn-store-logp store)
    (fnn-fault "a store that is not on the record log opened"))
  (let ((last nil)
        (noted (fnn-store-log-last store)))
    (fnn-log-history-plan store)
    ;; The open's own newest record, while no record was committed since
    ;; (the rotation check is fnn-log-history-plan's).
    (when (and noted
               (eql (first noted) (fnn-log-committed-count store)))
      (return-from fnn-history-last-record (fnn-octets (second noted))))
    (fnn-log-read-active-segment store (lambda (r) (setq last (fnn-octets r))))
    (cond (last last)
          ((car (last (fnn-log-closed-records store))))
          ((first (fnn-log-history-plan store))
           (let ((octets (fnn-core-arena-state 'fn-store-sco-last-record-octets)))
             (and octets (fnn-as-octets octets))))
          (t nil))))

;;; `store export DIR' and `store import DIR' (D34, books/store-export.lisp).

(defun fnn-archive-write-file (path octets)
  "Create PATH (it must not exist) and write OCTETS, no fence: the export's
data share one sync at the end (books/store-export-durability.lisp, the
step pair :create/:write-all of fn-sxd-entry-steps)."
  (let ((fd (fnn-open path (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                    +fnn-o-nofollow+)
                      #o600)))
    (unwind-protect (fnn-write-all fd (fnn-octets octets))
      (fnn-close fd))))

(defun fnn-archive-name (octets)
  (let ((name (fnn-octets-string (fnn-octets octets))))
    (when (or (zerop (length name)) (search ".." name) (char= (char name 0) #\/))
      (fnn-fault "ACL2 returned an invalid archive entry name"))
    name))

(defconstant +fnn-export-chunk+ 1024
  "History records per ACL2 export step (fn-sxp-export-chunk): a work and
allocation quantum per call, never a bound on the store; every record is in
exactly one step.")

;; books/store-export-durability.lisp fn-sxd-program's cuts, in program order.
;; export-entry-written repeats (per entry); the selected cut stops the export
;; at its first occurrence.
(defparameter +fnn-export-model-cuts+
  '("export-entry-written" "export-data-written" "export-data-durable"
    "export-manifest-staged" "export-manifest-renamed" "export-durable"))

(defun fnn-export-test-fault ()
  "Developer-only FN_NATIVE_EXPORT_FAULT=MODEL-CUT:eio|kill selector for
fn-sxd-program's cuts: (CUT-KEYWORD ACTION), or NIL."
  (let ((raw (fnn-developer-selector "FN_NATIVE_EXPORT_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_EXPORT_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (member label +fnn-export-model-cuts+ :test #'string=)
            (fnn-fault "unknown FN_NATIVE_EXPORT_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_EXPORT_FAULT action: ~a" action)))))))))

(defun fnn-export-at (fault cut)
  "The cut CUT of fn-sxd-program: a developer image's armed fault fires here
(SIGKILL: the next command observes a new process; eio: an OS error)."
  (when (and fault (eq (first fault) (intern (string-upcase cut) :keyword)))
    (if (eq (second fault) :fnn-test-kill)
        (progn (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
               (fnn-fault "test SIGKILL did not terminate the process"))
        (fnn-os-fail sb-posix:eio))))

#+linux
(sb-alien:define-alien-routine ("syncfs" fnn-%syncfs) sb-alien:int (fd sb-alien:int))

(defun fnn-export-sync-tree (dir)
  "Where syncfs(2) is not available: fence every regular file and directory
under DIR, a directory entry at a time (the archive's names are not held)."
  (let ((handle (fnn-posix (dir) (sb-posix:opendir dir))))
    (unwind-protect
         (loop
           (let ((entry (fnn-posix (dir) (sb-posix:readdir handle))))
             (when (sb-alien:null-alien entry) (return))
             (let ((name (sb-posix:dirent-name entry)))
               (unless (or (string= name ".") (string= name ".."))
                 (let* ((path (fnn-join dir name)) (st (fnn-lstat path)))
                   (cond ((null st))
                         ((fnn-regular-p st) (fnn-fsync-regular path))
                         ((fnn-directory-p st) (fnn-export-sync-tree path))))))))
      (fnn-posix (dir) (sb-posix:closedir handle))))
  (fnn-fsync-dir dir))

(defun fnn-export-sync-data (dir)
  "fn-sxd-program's :sync-all: ONE sync of the filesystem DIR is on (Linux
syncfs(2)); every entry written before it is durable after it.  Elsewhere
every file and directory under DIR is fenced (fnn-export-sync-tree): the
same postcondition, one barrier per file."
  #+linux
  (let ((fd (fnn-open dir (logior sb-posix:o-rdonly +fnn-o-directory+))))
    (unwind-protect
         (when (< (fnn-%syncfs fd) 0)
           (fnn-os-fail (sb-alien:get-errno) dir))
      (fnn-close fd)))
  #-linux
  (fnn-export-sync-tree dir))

(defun fnn-export-entries (dir entries fault)
  "Write each (NAME . OCTETS) of ENTRIES, an ACL2 export step's, under DIR:
fn-sxd-entry-steps, the cut after each entry."
  (unless (listp entries)
    (fnn-fault "ACL2 returned malformed archive entries"))
  (dolist (entry entries)
    (fnn-archive-write-file (fnn-join dir (fnn-archive-name (car entry))) (cdr entry))
    (fnn-export-at fault "export-entry-written")))

(defun fnn-export-step (dir manifest-fd step fault)
  "An export step's value (ENTRIES . LINES): write the entries, then append
the MANIFEST lines to the staged MANIFEST."
  (unless (and (consp step) (fnn-octet-list-p (cdr step)))
    (fnn-fault "ACL2 returned a malformed archive step"))
  (fnn-export-entries dir (car step) fault)
  (fnn-write-all manifest-fd (fnn-octets (cdr step))))

(defun fnn-command-store-export (root dir)
  "Offline: write the archive of ROOT's committed history to DIR (it must not
exist).  The store is acquired under its writer lock (a running owner refuses
this), and the history is the one the open read, read after the open a chunk
of +fnn-export-chunk+ records at a time (`fnn-log-history-each': the
checkpoint's covered prefix, then the scanned segments); no list of the
history is built.  ACL2 decides every entry and MANIFEST line: the head
(fn-sxp-export-head: profile, frontier, configuration records), then per
chunk fn-sxp-export-chunk; books/store-export-stream.lisp
fn-sxp-stream-is-the-export proves that, for every chunking, the entries
written in this order are fn-sxp-entries of the whole history and the
MANIFEST's octets are fn-sxp-manifest of them.

Durability is books/store-export-durability.lisp fn-sxd-program, step for
step, with its cuts (+fnn-export-model-cuts+): the entries are written with
no per-file fence and the MANIFEST's lines go to DIR/MANIFEST.partial; then
ONE sync of the data (fnn-export-sync-data); then MANIFEST.partial, records/
and config/ are fenced, MANIFEST.partial is renamed onto DIR/MANIFEST, and
DIR is fenced.  KEYSTONE fn-sxd-crash-is-incomplete-or-complete: a crash
anywhere leaves no MANIFEST, which the import refuses by name
(archive-incomplete entry=MANIFEST, fn-sxd-archive-verdict), or the
MANIFEST over every entry with its octets."
  (when (fnn-lstat dir)
    (fnn-refuse "export refused reason=archive-exists"))
  (multiple-value-bind (store count) (fnn-open-live-store root nil)
    (declare (ignore count))
    (unwind-protect
         (let* ((fault (fnn-export-test-fault))
                (profile (fnn-octet-list (fnn-read-regular-bounded (fnn-config-path store) 16384)))
                ;; The store holds no frontier file: the archive carries the
                ;; frontier the log derived at this open (ACL2's frame of
                ;; fn-store-log-next-txid), so the entry means what a
                ;; format-8 archive's does.
                (frontier (fnn-octet-list
                           (fnn-metadata-frontier-frame (fnn-store-frontier store))))
                (configs (mapcar (lambda (pair) (cons (car pair) (fnn-octet-list (cdr pair))))
                                 (fnn-config-record-observation store)))
                (head (fnn-core 'fn-sxp-export-head profile frontier configs))
                (staged (fnn-join dir "MANIFEST.partial"))
                (records 0))
           (unless (and (consp head) (consp (car head)))
             (fnn-fault "ACL2 returned a malformed archive"))
           (fnn-mkdir dir #o700)
           ;; fn-sxd-head-steps
           (fnn-mkdir (fnn-join dir "config") #o700)
           (fnn-mkdir (fnn-join dir "records") #o700)
           (let ((fd (fnn-open staged (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                              +fnn-o-nofollow+)
                               #o600))
                 (chunk nil) (n 0))
             (unwind-protect
                  (flet ((flush ()
                           (when chunk
                             (fnn-export-step dir fd
                                              (fnn-core 'fn-sxp-export-chunk (nreverse chunk))
                                              fault)
                             (setq chunk nil n 0))))
                    ;; fn-sxd-entry-steps, then the MANIFEST's lines
                    ;; (fn-sxd-tail-steps).
                    (fnn-export-step dir fd head fault)
                    (fnn-log-history-each
                     store
                     (lambda (record)
                       ;; The record's sequence as ACL2's decoder reads it.
                       (push (cons (fnn-bridge-record-sequence record) (fnn-octet-list record))
                             chunk)
                       (incf n)
                       (incf records)
                       (when (>= n +fnn-export-chunk+) (flush))))
                    (flush)
                    (fnn-export-at fault "export-data-written")
                    ;; :sync-all
                    (fnn-export-sync-data dir)
                    (fnn-export-at fault "export-data-durable")
                    ;; fn-sxd-publish-program
                    (fnn-fsync-file fd))
               (fnn-close fd)))
           (fnn-fsync-dir (fnn-join dir "records"))
           (fnn-fsync-dir (fnn-join dir "config"))
           (fnn-export-at fault "export-manifest-staged")
           (fnn-replace staged (fnn-join dir "MANIFEST"))
           (fnn-export-at fault "export-manifest-renamed")
           (fnn-fsync-dir dir)
           (fnn-export-at fault "export-durable")
           (fnn-out "exported records=~d configuration=~d" records (length configs))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-archive-read-dir (dir sub)
  (sort (copy-list (fnn-list-directory (fnn-join dir sub))) #'string<))

;;; One entry of an archive `store import' reads.  The archive is external
;;; input: an entry that is absent or larger than its work bound is a
;;; refusal of that archive by the entry's name (exit 1), never a fault of
;;; the host (lane fuzz-nntp found `[Errno 2]' and `store file exceeds bound'
;;; faults, exit 4, from a dropped MANIFEST and an enlarged frontier).
(defun fnn-archive-entry (dir name maximum)
  (let ((path (fnn-join dir name)))
    (unless (fnn-check-regular path)
      (fnn-refuse "import refused reason=archive-incomplete entry=~a" name))
    (handler-case (fnn-read-regular-bounded path maximum)
      (fnn-input-overbound ()
        (fnn-refuse "import refused reason=entry-over-bound entry=~a bound=~d" name maximum)))))

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
fn-bs-init-log-program (KIND \"init\": the same program over the log's plan,
init's cut names)."
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
DIR, a chunk of +fnn-export-chunk+ records at a time (PRF-369,
books/store-import-stream.lisp).  Pass one (`fnn-import-pass', no sink)
reads the archive and asks ACL2 per step: fn-sxi-head and fn-sxi-start over
the profile, frontier and configuration records, then per chunk fn-sxi-want
(the MANIFEST octets the chunk's entries must be) and fn-sxi-step over the
octets read at that place, then fn-sxi-final; KEYSTONE
fn-sxi-stream-plan-is-the-import-plan: for every chunking and every MANIFEST
this decides what fn-sxp-import-plan decides over the whole archive, so a
refused archive is refused by the same name with nothing written.  No list
of the archive's records, and never the MANIFEST as one list, is built: the
work and allocation per step are one chunk's.  An accepted plan is written
into ROOT.import-XXXX as init writes its files, and pass two runs the same
steps inside the staged publication, appending each chunk's records (the
step's own) to the stage's log; a pass
two that does not decide what pass one decided (fn-sxi-same-verdict: the
archive changed under the import) is refused by name before the open.  The
ordinary open (full replay, marker catch-up) admits the stage and it is
published by a no-replace rename onto ROOT, then ROOT's parent fenced:
books/store-import-publication.lisp fn-bs-imp-program, step for step, with
its cuts (+fnn-import-model-cuts+).  A staged directory left beside ROOT by
an earlier import is classified by fn-bs-imp-classify and refused by name
before anything is written.  An OS error before the rename is a known
failure (exit 1, the staged directory named); at or after it the outcome is
uncertain (exit 3) and the observed presence of the two names is classified
by fn-bs-imp-classify."
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
  (when (fnn-lstat root)
    (fnn-refuse "import refused reason=store-exists"))
  (multiple-value-bind (plan count) (fnn-import-pass dir request nil)
    (unless (and (consp plan) (member (first plan) '(:import :refused)))
      (fnn-fault "ACL2 returned a malformed import plan"))
    (when (eq (first plan) :refused)
      (fnn-refuse "import refused reason=~(~a~)~@[ ~a~]" (second plan)
                  (let ((detail (third plan)))
                    (cond ((null detail) nil)
                          ((fnn-octet-list-p detail) (fnn-octets-string (fnn-octets detail)))
                          ((keywordp detail) (string-downcase (symbol-name detail)))
                          (t detail)))))
    (destructuring-bind (values frontier configs) (rest plan)
      (declare (ignore frontier))
      (let* ((root-path (string-right-trim "/" root))
             (stage-root (format nil "~a.import-~a" root-path (fnn-random-hex 6)))
             (stage (make-fnn-store stage-root :writable t :fault (fnn-import-test-fault)))
             (logp (fnn-core 'fn-store-profile-logp values)))
        (unless logp
          (fnn-fault "ACL2's import plan is not a record-log profile"))
        (fnn-staged-publication
         "import" stage root-path
         ;; fn-sxp-import-plan's files, in its order, as init stages its
         ;; files (books/store-init-log-publication.lisp fn-bs-init-log-files:
         ;; the profile, the configuration records, the segment's ACL2 extent
         ;; of zeros; no allocator file, no transactions/), and the records go
         ;; into the log below, not into transaction files.
         (append (list (cons (fnn-config-path stage) (fnn-core 'fn-bs-config-encode values)))
                 (mapcar (lambda (config)
                           (cons (fnn-join (fnn-config-dir stage) (car config)) (cdr config)))
                         configs)
                 ;; The imported store's own genesis (a new node:
                 ;; its identity, salt and clock reading drawn here and
                 ;; recorded; the archive carries none), before the segment.
                 (list (cons (fnn-genesis-path stage) (fnn-genesis-octets values)))
                 (list (cons (fnn-segment-path stage)
                             (fnn-make-octets
                              (fnn-nat (fnn-core 'fn-store-log-initial-extent))))))
         count
         ;; The imported store is a new store on the filesystem ROOT is on
         ;; (its stage is ROOT's sibling): its record, under the import's
         ;; policy (fn-smid-init-policy: 1), before the ordinary open.  The
         ;; stage's segment (staged above) then receives the
         ;; history from the genesis (fnn-log-write-history), pass two's
         ;; records a chunk at a time, before that open admits it.
         (lambda (stage)
           (fnn-record-filesystem-at-init stage request policy)
           (fnn-log-init-segment stage)
           (fnn-log-write-history
            stage values
            (lambda (sink)
              (multiple-value-bind (again again-count) (fnn-import-pass dir request sink)
                (unless (fnn-core 'fn-sxi-same-verdict (cons again-count again)
                                  (cons count plan))
                  (fnn-refuse "import refused reason=archive-changed stage=~a: the archive changed while it was imported; no store was published; remove ~a and import again"
                              stage-root stage-root))))))
         ;; The staged tree's subdirectories: init's
         ;; (journal/ among them: fnn-log-init-segment's caller makes it
         ;; since log-2's initializer program).
         (fnn-core 'fn-bs-init-log-subdir-names))
        (fnn-out "imported records=~d configuration=~d" count (length configs))
        +fnn-exit-ok+))))

(defun fnn-command-store-bless-snapshot (dir)
  "S7a: read-only validation of an existing copy, not a snapshot producer.

ACL2 decides which observation is needed, its first refusal, the report and
exit.  A regular SNAPSHOT is a producer completion observation, not evidence
that this host produced an atomic copy.  The read-only open checks the copy's
own lineage; no observation of the currently configured store is used."
  (let* ((markerp (and (fnn-check-regular (fnn-join dir "SNAPSHOT")) t))
         (opened :never-observed) (count 0) (keysp nil))
    (when (fnn-core 'fn-osn-bless-open-needed markerp)
      (handler-case
          (multiple-value-bind (store records) (fnn-open-live-store dir nil)
            (unwind-protect
                 (setf opened :ok count records
                       keysp (and (fnn-node-secret-read-entry
                                   (fnn-node-secret-path store) "node secret") t))
              (fnn-store-close store)))
        (fnn-store-open-refusal (condition)
          (setf opened (fnn-message condition)))))
    (let ((word (fnn-core 'fn-osn-bless-word markerp opened keysp)))
      (fnn-out "~a" (fnn-core 'fn-osn-bless-line word dir opened count))
      (fnn-core 'fn-outcome-code (fnn-core 'fn-osn-bless-status word)))))

(defun fnn-read-up-to (fd n)
  "At most N octets from FD's position, fewer only at end of file."
  (let ((data (fnn-make-octets n)) (at 0))
    (loop while (< at n) do
      (let* ((buffer (fnn-make-octets (- n at)))
             (count (fnn-read-fd fd buffer)))
        (when (zerop count) (return))
        (replace data buffer :start1 at :end2 count)
        (incf at count)))
    (if (= at n) data (subseq data 0 at))))

(defun fnn-import-pass (dir request sink)
  "One pass over the archive at DIR: (values PLAN COUNT), PLAN fn-sxi-final's
verdict and COUNT the records read.  SINK, when given, receives every record
the steps return, (SEQUENCE . OCTETS), in order (pass two).  The archive is
external input: an entry that is absent or past its work bound is refused by
its name (fnn-archive-entry), never a host fault."
  ;; The MANIFEST first: an archive counts as complete only once its MANIFEST
  ;; is durable (the export renames it into place last), so an archive
  ;; without one is refused by that name before any entry is read
  ;; (books/store-export-durability.lisp fn-sxd-archive-verdict, KEYSTONE
  ;; fn-sxd-import-verdict-is-incomplete-or-complete).
  (case (fnn-core 'fn-sxd-archive-verdict
                  (and (fnn-check-regular (fnn-join dir "MANIFEST")) t))
    (:archive-incomplete
     (fnn-refuse "import refused reason=archive-incomplete entry=MANIFEST"))
    (:read)
    (t (fnn-fault "ACL2 returned a malformed archive verdict")))
  (let* ((profile (fnn-octet-list (fnn-archive-entry dir "profile" 16384)))
         (frontier (fnn-octet-list (fnn-archive-entry dir "frontier" 4096)))
         (config-names (fnn-archive-read-dir dir "config"))
         (record-names (fnn-archive-read-dir dir "records"))
         ;; Work bounds, not data bounds: one record file is read within the
         ;; archive profile's record bound (the bound it was committed under).
         ;; A profile the codec does not decode gives no bound: no record is
         ;; read, and fn-sxi-final refuses the archive by name (its MANIFEST
         ;; check comes first and names the profile when its octets changed;
         ;; lane fuzz-nntp, planning/evidence/fuzz-nntp-2026-09-27.md).
         (decoded (fnn-core 'fn-store-metadata-config-decode profile))
         (record-bound (and decoded (fnn-core 'fn-store-profile-read-bound decoded)))
         (configs (mapcar (lambda (name)
                            (cons name (fnn-octet-list
                                        (fnn-archive-entry
                                         dir (fnn-join "config" name)
                                         +fnn-config-record-bytes+))))
                          config-names))
         (manifest-path (fnn-join dir "MANIFEST")))
    (let ((fd (fnn-open manifest-path (logior sb-posix:o-rdonly +fnn-o-nofollow+)))
          (count 0))
      (unwind-protect
           (let* ((head (fnn-core 'fn-sxi-head profile frontier configs))
                  (lines (cdr head))
                  (st (fnn-core 'fn-sxi-start (car head) lines
                                (fnn-octet-list (fnn-read-up-to fd (length lines)))))
                  (chunk nil) (n 0) (stop nil))
             (flet ((flush ()
                      (when chunk
                        (let* ((records (nreverse chunk))
                               (want (fnn-core 'fn-sxi-want records))
                               (r (fnn-core 'fn-sxi-step st records want
                                            (fnn-octet-list (fnn-read-up-to fd (length want))))))
                          (unless (consp r)
                            (fnn-fault "ACL2 returned a malformed import step"))
                          (setq st (car r) chunk nil n 0)
                          ;; A MANIFEST mismatch is the verdict: stop reading.
                          (setq stop (fnn-core 'fn-sxi-st-mm st))
                          (when sink
                            (dolist (record (cdr r)) (funcall sink record)))))))
               (when record-bound
                 (dolist (name record-names)
                   (when stop (return))
                   ;; The sequence is ACL2's decode of the record, whatever it
                   ;; is: a record that does not decode is not a natural, and
                   ;; fn-sxp-out-of-sequence refuses it by name (after the
                   ;; MANIFEST check), instead of the host faulting on it.
                   (let ((octets (fnn-octet-list
                                  (fnn-archive-entry dir (fnn-join "records" name)
                                                     record-bound))))
                     (push (cons (fnn-core 'fn-store-record-sequence octets) octets)
                           chunk)
                     (incf n)
                     (incf count)
                     (when (>= n +fnn-export-chunk+) (flush))))
                 (flush)))
             (values (fnn-core 'fn-sxi-final st
                               ;; What follows the last chunk's lines: at
                               ;; most one octet (the MANIFEST must end).
                               (fnn-octet-list (fnn-read-up-to fd 1))
                               profile frontier configs (or request '(:current nil)))
                     count))
        (fnn-close fd)))))

(defun fnn-staged-publication (kind stage root-path files record-count
                               record-filesystem subdirs)
  "Build the store STAGE (at ROOT-PATH.KIND-XXXX) from FILES, a list of
(PATH . OCTETS) in plan order, admit it through the ordinary open (it must
replay RECORD-COUNT records), and publish it at ROOT-PATH by a no-replace
rename, then fence ROOT-PATH's parent: books/store-import-publication.lisp
fn-bs-imp-program step for step, with its cuts (KIND \"import\") or
books/store-init-log-publication.lisp fn-bs-init-log-program's (KIND \"init\":
the same steps, init's cut names).  An OS error before the rename is a known
failure (exit 1, the staged directory named); at or after it the outcome is
uncertain (exit 3) and the observed presence of the two names is classified
by fn-bs-imp-classify.  SUBDIRS are the staged tree's subdirectories in
the plan's order (init's are ACL2's fn-bs-init-log-subdir-names:
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
  ;; The record log's cuts: after the batch's barrier (the record durable)
  ;; and at the batch's write before its barrier.
  (list (cons "postpublish" (list :log-fenced 'fnn-store-indeterminate
                                  "indeterminate injected failure after final publication"))
        (cons "recordbarrier" (list :log-written 'fnn-os-error
                                    "injected transaction directory barrier failure"))))

(defparameter +fnn-post-model-cuts+
  '(:frontier-reserved :record-completing :finish-consumed :finish-durable))

;; The log route's commit cuts (tests/campaign/native_cuts.py
;; POST_LOG_CUTS), in a served batch's order: each member's place
;; (fnn-log-publish's record-completing) and finish (its in-memory
;; completion, fnn-finish's two cuts), then P-BATCH's append and barrier
;; (fnn-log-commit-open-batch).  Inside a batch the first three precede the
;; append: the record is absent at them (lane ack-before-barrier: the table
;; named record-completing only as a batch of one's, present).  A batch of
;; one runs the append and the barrier before its place and finish.
(defparameter +fnn-post-log-model-cuts+
  '(:record-completing :finish-consumed :finish-durable :log-written :log-fenced))

(defun fnn-post-test-fault ()
  "Developer-only FN_NATIVE_POST_FAULT=MODEL-CUT:eio|kill selector, or
record-prepublish:refuse (a known refusal before the record's first write).

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
          ;; The one injection-only point: a known refusal before the
          ;; record's first write (fnn-publish), never a kill.
          (when (eq point :record-prepublish)
            (unless (string= action "refuse")
              (fnn-fault "FN_NATIVE_POST_FAULT record-prepublish takes only :refuse"))
            (return-from fnn-post-test-fault
              (list point 'fnn-store-error
                    "developer-only known refusal before publication")))
          (unless (or (member point +fnn-post-model-cuts+)
                      (member point +fnn-post-log-model-cuts+))
            (fnn-fault "unknown FN_NATIVE_POST_FAULT cut: ~a" label))
          (list point
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
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
             ;; ACL2's article verdict: the count gate, the history gate and
             ;; the vector at this article's own figure, and its word
             ;; (fn-cvec-article-verdict-word): :memberships when the
             ;; membership charge alone refused it, named as the served
             ;; POST names it (books/nntp-post.lisp).
             (case (fnn-core-state 'fn-store-sn-article-verdict-word
                                   (fnn-store-config store) (length payload)
                                   (length codes))
               (:admissible nil)
               (:memberships
                (fnn-refuse "store budget refuses the article's groups (memberships): each group it is posted to is charged to the history budget, and the article alone would fit; post it to fewer groups"))
               (:unaffordable
                (fnn-refuse "store budget refuses the article (transaction count or history bound)"))
               (otherwise
                (fnn-fault "ACL2 returned an invalid article verdict word")))
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

(defun fnn-recover-repair-option (rest)
  "`store ROOT recover' takes nothing, or `--repair truncate SEGMENT:OFFSET':
the operator's confirmation of the one repair a log-damaged refusal names
(books/store-log-damage.lisp; ACL2 admits it only for that damage)."
  (cond ((null rest) nil)
        ((and (= (length rest) 3) (string= (first rest) "--repair")
              (string= (second rest) "truncate"))
         (third rest))
        (t (error 'fnn-usage-error
                  :message "recover takes nothing, or --repair truncate SEGMENT:OFFSET (the at= of a log-damaged refusal)"))))

(defun fnn-command-recover (root &optional rest)
  (multiple-value-bind (store count)
      (let ((*fnn-log-repair* (fnn-recover-repair-option rest)))
        (fnn-open-live-store root t (fnn-recovery-test-fault)))
    (unwind-protect
         (multiple-value-bind (report code) (fnn-anchor-report store)
           (fnn-out "recovered transactions=~d articles=~d ~a ~a"
                    count (fnn-bridge-article-count)
                    (fnn-orphan-report store) report)
           (fnn-out "~a" (fnn-open-report store))
           (dolist (line (reverse *fnn-log-open-reports*)) (fnn-out "~a" line))
           code)
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

(defun fnn-write-report-pages (pages)
  "Write the pages of one paged report, in order; render nothing."
  (dolist (page pages)
    (unless (typep page 'fnn-octets)
      (fnn-fault "ACL2 returned a malformed report page"))
    (write-sequence page *fnn-stdout*))
  (finish-output *fnn-stdout*))

(defun fnn-command-live-pages (store)
  "Write the paged report of the Store this process replayed, a page at a
time (books/native-live-pages.lisp `fn-nlp-offline-step'; KEYSTONE
fn-nlp-offline-pages-join-to-the-report): the report is never held whole."
  (declare (ignore store))
  (let ((cursor (fnn-core 'fn-native-live-pages-host-offline-start *the-live-state*)))
    (loop
      (let ((step (fnn-core 'fn-native-live-pages-host-offline-step cursor)))
        (unless (and (consp step) (fnn-octet-list-p (first step)))
          (fnn-fault "ACL2 returned a malformed report page"))
        (write-sequence (fnn-octets (first step)) *fnn-stdout*)
        (when (third step) (return))
        (setq cursor (second step)))))
  (finish-output *fnn-stdout*))

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
           (if (fnn-core 'fn-native-live-pages-host-pagedp kind)
               (fnn-command-live-pages store)
             (fnn-write-report
              (fnn-core 'fn-native-live-status-host-offline kind
                        (fnn-store-config store) (fnn-store-observation store)
                        (fnn-live-arena) *the-live-state*)))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-inspect-group-offline (root kind)
  "Row S3d: `store inspect --group GROUP' with no owner running: ACL2's report
of KIND, (:inspect-group . GROUP), over the archive this process replayed from
the checkpoint and its suffix (books/control-evidence.lisp
fn-cev-offline-report -> books/owner-inspect-group.lisp fn-oig-report),
through the offline renderer every status kind takes; the exit is ACL2's
reading of the octets printed (fn-oig-report-exit)."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (let ((octets (fnn-core 'fn-native-live-status-host-offline kind
                                 (fnn-store-config store) (fnn-store-observation store)
                                 (fnn-live-arena) *the-live-state*)))
           (unless (fnn-octet-list-p octets)
             (fnn-fault "ACL2 returned a malformed inspect group report"))
           (fnn-write-report octets)
           (fnn-core 'fn-native-live-status-host-inspect-group-exit octets))
      (fnn-store-close store))))

(defun fnn-read-regular-prefix (path maximum &optional (offset 0))
  "The MAXIMUM octets at OFFSET of one regular, non-symlink file (fewer when
it is shorter), or NIL when there is none."
  (let ((st (fnn-check-regular path)))
    (and st
         (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
           (unwind-protect
                ;; One read of MAXIMUM octets: never the whole file
                ;; (fnn-read-bounded-fd refuses a longer file by design).
                (let ((buffer (fnn-make-octets maximum)))
                  (unless (zerop offset) (sb-posix:lseek fd offset sb-posix:seek-set))
                  (let ((count (fnn-read-fd fd buffer)))
                    (if (= count (length buffer)) buffer (subseq buffer 0 count))))
             (fnn-close fd))))))

(defun fnn-stopped-checkpoint-header (path)
  "The newest checkpoint's first segment header, as the open finds it
(fnn-state-checkpoint-plan): the file's first fn-omr-header-octets, or,
when ACL2 recognizes those as a history image region's header
(fn-his-image-header-np, books/history-image-snapshot.lisp), as many past
the region (fn-his-skip-octets).  NIL when there is no file."
  (let* ((octets (fnn-nat (fnn-core 'fn-omr-header-octets)))
         (prefix (fnn-read-regular-prefix path octets))
         (np (and prefix (= (length prefix) octets)
                  (fnn-core 'fn-his-image-header-np (fnn-octet-list prefix)))))
    (if (integerp np)
        (fnn-read-regular-prefix path octets
                                 (+ octets (fnn-nat (fnn-core 'fn-his-skip-octets np))))
      prefix)))

(defun fnn-stopped-observation (root)
  "Row S3: what a stopped store's status is rendered from, nothing replayed:
config.json's octets, the newest checkpoint's first segment header (ACL2's
fn-omr-header-octets of it, past a history image region:
fnn-stopped-checkpoint-header), the journal's octets (every
segment's lstat size) and the checkpoint file's lstat."
  (let* ((store (make-fnn-store root))
         (config (fnn-octet-list (fnn-read-regular-bounded (fnn-config-path store) 16384)))
         (prefix (fnn-stopped-checkpoint-header (fnn-state-checkpoint-path store)))
         (header (and prefix (fnn-octet-list prefix)))
         (dir (fnn-journal-dir store))
         (journal (loop for name in (fnn-log-segment-names store)
                        for st = (fnn-lstat (fnn-join dir name))
                        sum (if st (sb-posix:stat-size st) 0))))
    (list config header journal (fnn-state-checkpoint-file-observation store))))

(defun fnn-stopped-report (root kind &optional last)
  "Row S3: `status' or `health' on a stopped store, from its checkpoint header
and its journal's sizes (books/owner-maintenance-request.lisp
fn-omr-stopped-report, fn-omr-stopped-health-report): (EXIT OCTETS) for
:status, the health octets (their exit is the header's) for :health.  A
writer lock an owner holds refuses by name first (fn-omr-route :held): the
report is never rendered behind an owner."
  (let ((lock (fnn-store-owner-observation root)))
    (when (eq lock :unknown)
      (fnn-indeterminate "the store's writer lock could not be observed"))
    (when (eq (fnn-core 'fn-omr-route (if (eq lock :held) :held :offline)) :held)
      (fnn-refuse "~a" (fnn-core 'fn-omr-held-line
                                 (if (eq kind :health) "health" "status")))))
  (destructuring-bind (config header journal obs) (fnn-stopped-observation root)
    (if (eq kind :health)
        (fnn-core 'fn-omr-stopped-health-report last config header journal obs)
      (fnn-core 'fn-omr-stopped-report config header journal obs))))

(defun fnn-command-stopped-status (root)
  (let ((report (fnn-stopped-report root :status)))
    (unless (and (consp report) (member (first report) '(0 1))
                 (fnn-octet-list-p (second report)))
      (fnn-fault "ACL2 returned a malformed stopped report"))
    (fnn-write-report (second report))
    (if (eql (first report) 0) +fnn-exit-ok+ +fnn-exit-refused+)))

(defun fnn-command-status (root &optional replayp)
  "Row S3: a stopped store's status is its checkpoint header's (no replay);
`--replay' (REPLAYP) asks for the report over the replayed log."
  (fnn-filesystem-durability-warn root)
  (if replayp
      (fnn-command-live-report root :status)
    (fnn-command-stopped-status root)))

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

(defun fnn-command-compression (root)
  "`store ROOT compression': the profile's compression threshold and ACL2's
tally of the log the open replayed (fn-lzr-tally-text): records, compressed
records, the octets the log holds and their expansions, the dictionary ids
in use (lane compression-extents-2)."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (progn
           (fnn-out "~a" (fnn-core 'fn-lzr-tally-text
                                   (fnn-nat (fnn-core-state 'fn-store-compress-min-octets))
                                   (or *fnn-lz-tally* (fnn-core 'fn-lzr-tally-empty))))
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

(defun fnn-command-provenance (root message-id)
  "`store ROOT provenance MSGID': the provenance the article's retention pin
records, as ACL2 describes it (host/store-node-host.lisp
fn-store-prov-for-msgid, books/provenance-inspect.lisp fn-provi-of-msgid),
then LF; refused when the store binds no such Message-ID or its pin was
released.  The host decodes nothing: it relays ACL2's octets."
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (progn
           (unless (every (lambda (c) (< (char-code c) 128)) message-id)
             (error 'fnn-usage-error :message "Message-ID is not ASCII"))
           (let ((value (fnn-core-state 'fn-store-prov-for-msgid
                                        (fnn-ascii-octet-list message-id))))
             (cond ((null value) +fnn-exit-refused+)
                   (t (write-sequence (fnn-as-octets value) *fnn-stdout*)
                      (write-byte 10 *fnn-stdout*)
                      (finish-output *fnn-stdout*)
                      +fnn-exit-ok+))))
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
                (fnn-fault "probe publish refused")))
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
;;;   store ROOT provenance MESSAGE-ID
;;;   store ROOT probe COUNT
;;;   reader PORT ONCE(0|1) STORE-ROOT|-
;;;   model CHUNK-FILE STORE-ROOT|-
;;;   tcpcl listen PORT [ONCE SPOOL NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU REPLY-FILE TRACE]
;;;   tcpcl send HOST PORT BUNDLE-FILE [SPOOL NODE-ID PEER KEEPALIVE
;;;                      SEGMENT-MRU TRANSFER-MRU EXPECT TRACE]
;;;   tcpcl replay TRACE-FILE [ROLE NODE-ID PEER KEEPALIVE SEGMENT-MRU
;;;                      TRANSFER-MRU]
;;;   blake3 PATH
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

;;; The release version (VERSION at the tree root, one line).  Read
;;; once while constructing the saved image, as the profile above is, and
;;; serialized into it; the packaging reads the same file for the tarball's
;;; name (packaging/release-tarball.sh).  `fn --version' prints it with the
;;; source revision recorded beside the core.  The build checks only its
;;; shape; which versions are releases, and their order, is D37's sequence
;;; (planning/release-sequence.json), decided by tools/release_sequence.py
;;; at the cut (tools/cut_release.sh gate 01) and by the packaging.
(defvar *fnn-release-version* nil)

;;; The clock at the image's entry (fnn-main).  The owner's OWNER-OPEN line
;;; records the milliseconds from here to its open (`ms=N'): the measured
;;; length of a start, which `install.sh --upgrade' quotes as the gap of
;;; the next one (docs/install.md, "Upgrading").  A measurement, no
;;; decision: the heap probe (packaging/fn, a first run of the image) and
;;; the stop are outside it.
(defvar *fnn-process-started* nil)

(defun fnn-ms-since-process-start ()
  "Milliseconds since fnn-main began; 0 when the owner runs without the
entry (a harness that calls it directly)."
  (if *fnn-process-started*
      (values (round (* 1000 (- (get-internal-real-time) *fnn-process-started*))
                     internal-time-units-per-second))
      0))

(defun fnn-release-version-word-p (text)
  "TEXT is dotted decimal numerals without leading zeros, any number of
components (6.6.0, 6.7.12, 6.6.6.6)."
  (and (stringp text)
       (plusp (length text))
       (let ((start 0))
         (loop
           (let* ((dot (position #\. text :start start))
                  (n (subseq text start (or dot (length text)))))
             (unless (and (plusp (length n))
                          (every (lambda (c) (find c "0123456789")) n)
                          (or (string= n "0") (char/= (char n 0) #\0)))
               (return nil))
             (if dot
                 (setq start (1+ dot))
                 (return t)))))))

(defun fnn-select-release-version (&optional (path "VERSION"))
  "Build-time: take the release version from PATH (the build runs at the
tree root), or stop the build."
  (let ((line (with-open-file (in path :direction :input :if-does-not-exist nil
                                       :external-format :latin-1)
                (and in (read-line in nil nil)))))
    (unless (fnn-release-version-word-p line)
      (error "~a does not hold a release version (dotted numerals, read ~s)" path line))
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
    ;; lane join-f2-13: the OVER/XOVER cursor quantum (numbers per hold of
    ;; the owner mutex) for the natives; ACL2's fn-splan-cursor-window
    ;; decides the value (books/served-plan-cursor.lisp).
    "FN_NATIVE_OVER_WINDOW"
    "FN_NATIVE_OVER_TEST_PAUSE_AFTER_QUANTUM"
    ;; the extraction gate's stateful differential (tools/extract/stateful.py):
    ;; a recorded clock observation and a recorded entropy stream, the
    ;; environment readings the image and the extracted program then share.
    "FN_NATIVE_TEST_CLOCK" "FN_NATIVE_TEST_ENTROPY"
    "FN_NATIVE_STATE_CHECKPOINT_FAULT" "FN_NATIVE_IMPORT_FAULT" "FN_NATIVE_EXPORT_FAULT"
    "FN_NATIVE_CHECKPOINT_BUDGET_TEST" "FN_NATIVE_RECLAIM_FAULT"
    "FN_NATIVE_TEST_RECLAIM_STALL_FILE" "FN_NATIVE_RECLAIM_HOLD"
    "FN_NATIVE_PAGE_READ_HOLD"
    "FN_NATIVE_PAGE_IO_HOLD" "FN_NATIVE_PAGE_IO_RESULT"
    "FN_NATIVE_DISK_FREE"
    "FN_NATIVE_EXTENT_CACHE_TEST_OFF"
    ;; host/native/digest.lisp: the matched measurement's reference arm.
    "FN_NATIVE_DIGEST_TEST_OFF"
    ;; D40: the executable-counterpart path for every :raw-with entry, so a
    ;; native compares the served path both ways (fnn-dispatch-function).
    "FN_NATIVE_DISPATCH_COUNTERPART"
    "FN_NATIVE_IMPORT_COMPRESS_MIN_TEST"
    "FN_NATIVE_CONTROL_FAULT" "FN_NATIVE_CONTROL_TEST_STOP"
    "FN_NATIVE_AUTH_ADMIN_FAULT" "FN_NATIVE_KEY_STATEMENT_FAULT"
    "FN_NATIVE_OWNER_TEST_SIGTERM" "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP"
    "FN_NATIVE_OWNER_TEST_PAUSE_BEFORE_LISTEN" "FN_NATIVE_OWNER_TEST_BARRIER_MS" "FN_NATIVE_TEST_DISK_STALL_FILE" "FN_NATIVE_TEST_READ_STALL_FILE" "FN_NATIVE_TEST_JOURNAL_FAIL_FILE" "FN_NATIVE_OWNER_TEST_PIPELINE_TRACE" "FN_NATIVE_FAULT_BACKTRACE"
    "FN_NATIVE_COUNT_LOOKUPS"
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
    "FN_BP_LISTENER_TEST_PAUSE_CUT"
    "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_ATTEMPT"
    "FN_BP_OBLIGATION_TEST_PAUSE_AFTER_SUBMIT"
    "FN_TCPCL_TEST_FAIL_STAGING_UNLINK" "FN_TCPCL_TEST_FAIL_STAGING_BARRIER"
    "FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA"
    "FN_CHECKPOINT_TEST_FAIL" "FN_CHECKPOINT_TEST_STOP_AFTER"
    "FN_CHECKPOINT_TEST_STOP" "FN_CHECKPOINT_TEST_MISMATCH"
    "FN_APP_JOURNAL_TEST_OBSERVER"
    "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE"
    "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE"
    ;; Cut receipt-observed (host/native/bp-app.lisp
    ;; fnn-bpapp-pause-after-decision): =decided holds the receipt path after
    ;; the recorded decision until the RELEASE file appears.
    "FN_APP_JOURNAL_TEST_HOLD_RECEIPT" "FN_APP_JOURNAL_TEST_HOLD_RECEIPT_RELEASE"
    "FN_APP_JOURNAL_TEST_FENCE_STORE" "FN_APP_JOURNAL_TEST_READ_ONLY_STORE"
    "FN_APP_JOURNAL_TEST_FAIL" "FN_IMMUTABLE_PUBLISH_TEST_FAIL"
    "FN_PEER_TEST_STOP_AFTER_CONSUME" "FN_PEER_TEST_STOP_AFTER_CONFIGURE"
    "FN_PULL_TEST_KILL"
    ;; PRF-325: the catch-up journal's append cuts (host/native/pull-service.lisp).
    "FN_CATCHUP_TEST_KILL"
    "FN_NATIVE_CHECKPOINT_BATCH_FAULT"
    "FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH"
    "FN_NATIVE_LOG_FAULT"
    ;; The power-loss rig's handshake for `fn log append': after each RECOVERED
    ;; and ACK line, wait for the client's line, so its device mark precedes
    ;; the next batch's writes; tools/power_loss.py log_run.
    "FN_NATIVE_LOG_RIG_HANDSHAKE"))

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

(defun fnn-stack-exhaustion-report (next)
  "FN_NATIVE_FAULT_BACKTRACE's report of a control-stack exhaustion, printed
on the exhausted stack before any handler unwinds it, then NEXT (SBCL's own
signal).  The frames as a run-length list of function names, innermost
first: a recursion that takes one frame per line or per octet is one row
with its depth, and the rows under it name the path that called it."
  (ignore-errors
   (let ((runs nil))
     (sb-debug::map-backtrace
      (lambda (frame)
        (let ((name (ignore-errors
                     (sb-di:debug-fun-name (sb-di:frame-debug-fun frame)))))
          (if (and runs (equal (car (car runs)) name))
              (incf (cdr (car runs)))
              (push (cons name 1) runs))))
      :count most-positive-fixnum)
     (let ((*print-length* 3) (*print-level* 3))
       (format *error-output* "~&fault backtrace (thread ~a): control stack exhausted~%"
               (sb-thread:thread-name sb-thread:*current-thread*))
       (dolist (run (reverse runs))
         (format *error-output* "frames ~a x~a~%" (car run) (cdr run))))
     (finish-output *error-output*)))
  (funcall next))

;;; FN_NATIVE_COUNT_LOOKUPS (release row F2's lookup count; lane sca-join-4):
;;; a diagnostic, not a fault.  Each function below is one catalog or index
;;; lookup, or the entry of a walk; each is wrapped with a counter
;;; (sb-int:encapsulate, as FN_NATIVE_FAULT_BACKTRACE wraps the stack signal),
;;; and every served read (fn-owner-chunk-span through fnn-core-buffer-state)
;;; first prints the counts since the previous one to stderr and clears them:
;;; `lookups window K: NAME=N ...' is the work of the read before it, its
;;; render included.  The wrappers return the wrapped function's values, so no
;;; outcome changes; a production image never reads the selector.  Only
;;; entries are counted (SBCL compiles a function's self-calls as local calls,
;;; which no wrapper sees): a self-recursive walk counts once per walk, so the
;;; bisection is counted at fn-scr-mid (one call per probe) and a walk over a
;;; list is given as (NAME . I), which also adds the length of its Ith
;;; argument to `NAME/len', the size of what it walks.  The exports of the
;;; fn-cat abstract stobj are counted at their :exec functions (fn-cat$c-*),
;;; the functions a served call reaches.
(defparameter +fnn-lookup-functions+
  '(;; the pinned view: fn-scr-view-of's bisection, one fn-scr-mid per probe
    fn-scr-view-of fn-scr-mid
    ;; the catalog's tables (books/catalog.lisp exports, :exec side)
    fn-cat$c-group-number fn-cat$c-msgid-seqs fn-cat$c-at fn-cat$c-visible-at
    fn-cat$c-group-next fn-cat$c-group-count
    ;; the maintained group summary and withdrawal horizon (one cell each)
    fn-cat$c-group-live-count fn-cat$c-group-live-low fn-cat$c-group-live-high
    fn-cat$c-horizon
    ;; the catalog finders over them
    fn-cnx-view-seq fn-cnx-view-range fn-scat-range-numbers
    (fn-cat-view-last-visible . 0) fn-cat-row-article
    ;; the Message-ID trie
    fn-midx-lookup
    ;; archive and catalog-list walks (their entries and the length walked;
    ;; none belongs on the served path)
    (fn-find-article . 1) (fn-nntp-find-group-number . 2)
    (fn-nntp-available-article . 2) (fn-nntp-group-range-numbers . 3)
    (fn-nntp-group-count . 1) (fn-nntp-group-low . 1) (fn-nntp-group-high . 1)
    fn-cat-view-below fn-cat-view-articles fn-cat-view-find
    fn-cat-view-number-find fn-cat-number-seq fn-cat-seqs-for fn-cnx-walk-range
    fn-nntp-archive-command fn-nntp-over-range fn-nntp-group-result))

(defvar *fnn-lookup-counts* nil)
(defvar *fnn-lookup-names* nil)
(defvar *fnn-lookup-window* 0)

(defun fnn-lookup-window-close ()
  "Print the counts since the previous served read, then clear them."
  (let ((counts *fnn-lookup-counts*))
    (format *error-output* "~&lookups window ~d:" *fnn-lookup-window*)
    (dotimes (i (length counts))
      (let ((n (aref counts i)))
        (when (> n 0)
          (format *error-output* " ~(~a~)=~d" (aref *fnn-lookup-names* i) n)
          (setf (aref counts i) 0))))
    (terpri *error-output*)
    (finish-output *error-output*)
    (incf *fnn-lookup-window*)))

(defun fnn-lookup-counter (i)
  (lambda (next &rest args)
    (sb-ext:atomic-incf (aref (the (simple-array sb-ext:word (*)) *fnn-lookup-counts*) i))
    (apply next args)))

(defun fnn-lookup-walk-counter (i len-i arg)
  (lambda (next &rest args)
    (let ((counts (the (simple-array sb-ext:word (*)) *fnn-lookup-counts*)))
      (sb-ext:atomic-incf (aref counts i))
      (let ((walked (nth arg args)))
        (when (listp walked)
          (sb-ext:atomic-incf (aref counts len-i) (length walked)))))
    (apply next args)))

(defun fnn-install-lookup-counters ()
  (unless *fnn-lookup-counts*
    (let* ((specs (remove-if-not (lambda (spec)
                                   (let ((s (if (consp spec) (car spec) spec)))
                                     (and (fboundp s) (not (macro-function s)))))
                                 +fnn-lookup-functions+))
           (missing (set-difference +fnn-lookup-functions+ specs :test #'equal))
           (names nil))
      ;; One column per function, one more (NAME/len) per walk.
      (dolist (spec specs)
        (if (consp spec)
            (progn (push (car spec) names)
                   (push (intern (format nil "~a/LEN" (car spec)) "ACL2") names))
            (push spec names)))
      (setq names (nreverse names)
            *fnn-lookup-names* (coerce names 'simple-vector)
            *fnn-lookup-counts* (make-array (length names) :element-type 'sb-ext:word
                                                           :initial-element 0))
      (dolist (spec specs)
        (if (consp spec)
            (let ((i (position (car spec) names)))
              (sb-int:encapsulate (car spec) 'fnn-lookup-count
                                  (fnn-lookup-walk-counter i (1+ i) (cdr spec))))
            (sb-int:encapsulate spec 'fnn-lookup-count
                                (fnn-lookup-counter (position spec names)))))
      (sb-int:encapsulate
       'fnn-core-buffer-state 'fnn-lookup-count
       (lambda (next name &rest args)
         (when (eq name 'fn-owner-chunk-span) (fnn-lookup-window-close))
         (apply next name args)))
      (format *error-output* "~&lookups counted:~{ ~(~a~)~}~%lookups not counted (unbound or a macro):~{ ~(~a~)~}~%"
              names missing)
      (finish-output *error-output*))))

(defun fnn-developer-selector-gate (argv)
  "Refuse, before any store is opened, a production start that names a cut."
  ;; A stack exhaustion is signalled inside fnn-core's handlers, which unwind
  ;; it before fnn-owner-shared-action-locked's handler-bind sees it: the
  ;; report is installed at SBCL's signal instead (developer image only).
  (when (fnn-developer-selector "FN_NATIVE_FAULT_BACKTRACE")
    (unless (sb-int:encapsulated-p 'sb-kernel::control-stack-exhausted-error
                                   'fnn-stack-exhaustion-report)
      (sb-int:encapsulate 'sb-kernel::control-stack-exhausted-error
                          'fnn-stack-exhaustion-report
                          #'fnn-stack-exhaustion-report)))
  (when (fnn-developer-selector "FN_NATIVE_COUNT_LOOKUPS")
    (fnn-install-lookup-counters))
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
;;; (fnn-log-stream-segment: one entry at a time, books/store-log-stream.lisp),
;;; recovery's zeroing range
;;; (fn-lg-recover-tail), each record's admission (fn-lgc-t-prepare, fn-lgc-take:
;;; only at the kernel's next txid), the extension (fn-lgc-extension-needed-p,
;;; fn-lgc-extension-target), the append's admission and octets
;;; (fn-lgc-append-admitsp, fn-lgc-frontier, fn-lgc-append-octets) and the
;;; kernel after each step (fn-lgc-append, fn-lgc-fence, fn-lgc-fence-failed,
;;; fn-lgc-finish-one).  The kernel the host holds is the CONCRETE one
;;; (books/store-log-kernel-concrete.lisp, lanes per-record-state and
;;; kernel-concrete-2, PRF-282): the committed records' COUNT in place of
;;; their list, the append's length by arithmetic and its octets by
;;; guard-verified framing (no per-octet recursion: a 10 MiB article), each
;;; transition fn-lgc-of the logical one (KEYSTONE fn-lgc-run-refines-the-
;;; kernel, over the pipelined commit's operations too); the open's records are
;;; streamed to the replay one entry at a time (fnn-log-stream-segment, KEYSTONE
;;; fn-lgw-run-is-the-open).  The host reads,
;;; writes and fences, in the order of
;;; fn-lg-recover-program, fn-lg-append-program and fn-lg-fence-program
;;; (tests/campaign/native_cuts.py LOG_CUTS, verify_log_cut_map).  No owner
;;; path calls these yet: lane w6-log-owner moves the commit onto them.

(defparameter +fnn-log-model-cuts+
  '("log-written" "log-fenced" "log-truncated" "log-recovered"
    ;; books/store-log-extend.lisp fn-lg-extend-program (fnn-log-ensure-extent).
    "log-extended" "log-extent-fenced"))

(defstruct (fnn-log (:constructor %make-fnn-log))
  path fd kernel unit max extent
  ;; The open batch's members and entry octets (fn-lgc-take's COUNT and
  ;; OCTETS), the operator's bounds (fn-owb-bmax / fn-owb-omax of the live
  ;; configuration; set by the owner), and the fenced members not yet
  ;; acknowledged.
  (count 0) (octets 0) (bmax 64) (omax 67108864) (pending 0)
  ;; The txid the owner reserved for the record being published (ACL2's,
  ;; handed to fnn-log-reserve), which fn-lgc-take admits at the log's next.
  (reserved nil)
  ;; The segment's index (books/store-log-segments.lisp): the active one of
  ;; the store; fnn-log-rotate moves to the next.
  (index 1)
  ;; The active segment's genesis: the predecessor its first entry chains
  ;; from (the open's scan, or the rotation's closed segment's last trailer);
  ;; a history read streams the active segment again from it.
  (genesis nil)
  ;; The pipelined commit (lane log-2; books/owner-commit-pipeline.lisp):
  ;; the kernel value changes only under LOCK, because the syncer thread's
  ;; fence (fnn-log-sync-sealed-batch) runs while the owner prepares the
  ;; next batch behind it.  SEALED the members of the batch in flight;
  ;; SYNC-STATE :idle, :syncing (a sealed batch awaits its barrier),
  ;; :fenced or :failed (the syncer's word, until the COMPLETE consumes it);
  ;; SYNC-CV signalled when the syncer returns.
  (lock (sb-thread:make-mutex :name "fn log kernel"))
  (sealed 0) (sync-state :idle)
  (sync-cv (sb-thread:make-waitqueue :name "fn log sync"))
  ;; The commit's extent reseat (lane arena-offheap-3, PRF-309): per record
  ;; of the open batch, newest first, (HANDLE . OCTETS), HANDLE the arena
  ;; handle the owner's buffer prepare staged for it or NIL; at the append,
  ;; the staged ones with their places move to INFLIGHT, (H FILE PLACE
  ;; OCTETS); the fence moves them to FENCED (under LOCK: the syncer's
  ;; fence); the COMPLETE reseats FENCED (fnn-log-reseat-fenced).
  ;; EXTENT-FILE the realizer's id of the active segment (EXTENT-PATH).
  (members nil) (inflight nil) (fenced nil) (extent-file nil) (extent-path nil)
  ;; Compressed records (lane compression-extents-2).  LZ-MIN the
  ;; compression threshold (the `compress-min-octets' configuration row; 0
  ;; off, the default): the owner's live one, set with the batch bounds, or
  ;; (NIL until read) the store's replayed configuration's; LZ set once this log has taken a compressed record: the
  ;; COMPLETE then reseats through ACL2's compressed reseat
  ;; (fn-lzr-commit-reseats), which a framed member needs; NIL keeps
  ;; fn-arx-commit-reseats, as before.
  (lz-min nil) (lz nil)
  ;; The rotation's spare (lane operations, P-ROTATE split): (INDEX PATH FD)
  ;; of the next segment, created in staging/ under a `.stage-' name,
  ;; preallocated and fenced OFF the owner mutex (fnn-log-prepare-spare); the
  ;; rotation under the mutex only renames it into journal/.  SPARE-LOCK
  ;; serializes preparers; it is never taken under the owner mutex.
  (spare nil) (spare-lock (sb-thread:make-mutex :name "fn log spare"))
  ;; journal/'s path while the rotated-to segment's name is not yet durable:
  ;; the first fence of the new segment (fnn-log-fence) and the checkpoint
  ;; that names it (fnn-owner-publish-captured) fence journal/ first
  ;; (fnn-log-make-durable, cut rotate-durable).  NIL when durable.
  (dir-pending nil))

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

(defun fnn-log-pread (fd offset count)
  "COUNT octets of the segment at OFFSET (lseek, then read to completion); a
segment shorter than the extent ACL2 asked within is a fault."
  (fnn-posix () (sb-posix:lseek fd offset sb-posix:seek-set))
  (or (fnn-read-exact-fd fd count)
      (fnn-fault "log segment shorter than its extent")))

(defvar *fnn-extent-file* nil
  "The extent realizer's id of the segment being streamed, bound by the full
replay (fnn-recover-log) when its records' places are wanted; NIL otherwise.")

(defvar *fnn-log-record-place* nil
  "While the stream hands a record to its sink under *fnn-extent-file*: the
record's (FILE . PLACE), PLACE ACL2's (START N ROFF RLEN); else NIL.")

;;; ---------------------------------------------------------------------------
;;; Compressed records (lane compression-extents-2; books/payload-lz-append.lisp
;;; PRF-341 over books/payload-lz-record.lisp PRF-326).
;;;
;;; The APPEND (fnn-log-compress, from fnn-log-publish): with the owner's
;;; live threshold set (`policy set compress-min-octets N', a configuration
;;; row; no row is off), ACL2 plans the payload span of the record
;;; (fn-lzr-append-plan), the host asks the untrusted zlib encoder for a
;;; candidate DEFLATE stream over the current shipped dictionary within
;;; ACL2's cap (host/native/deflate.lisp fnn-deflate-candidate), and ACL2
;;; decides (fn-lzr-append-decide: the proved decoder runs over the
;;; candidate): the
;;; frame is taken, or the record is kept by the named policy :lz-no-gain, or
;;; the candidate is refused and the append stops with a named store fault
;;; before anything is taken.  The digests stay over the original octets
;;; (fn-lzr-append-replay-reads-the-record).
;;;
;;; The READ (fnn-log-read-record): every record a log stream hands out is
;;; ACL2's read step over the octets the log holds (fn-lzr-read-step: the
;;; expansion, KEYSTONE fn-lzr-expand-of-seal), so every consumer -- the
;;; replay, the txid fold, export, checkpoint capture -- sees the record R.
;;; The replay alone also needs the stored octets (*fnn-log-record-stored*)
;;; for the compressed extents.
;;;
;;; Dictionaries: the release's shipped table (books/payload-lz-dicts.lisp,
;;; ACL2's fn-lzr-dicts-initial), each under the first four octets of its
;;; BLAKE3 digest; ID 0 is the empty dictionary.  New payloads are made under
;;; the current one (fn-lzd-current-id); nothing is transcoded at rest.

(defvar *fnn-log-record-stored* nil
  "While a log stream hands a record to its sink: the octets the log holds
for it (a compressed record's frame, or the record itself).")

(defvar *fnn-lz-tally* nil
  "ACL2's tally of the records the last full replay read (fn-lzr-read-step):
what `store ROOT compression' reports.")

(defvar *fnn-lz-dicts* nil)
(defvar *fnn-lz-current* nil)

(defun fnn-lz-current-dict ()
  "The dictionary new payloads are made under (books/payload-lz-dicts.lisp
fn-lzd-current-id): (ID OCTET-LIST . OCTET-VECTOR)."
  (or *fnn-lz-current*
      (setq *fnn-lz-current*
            (let* ((id (fnn-core 'fn-lzd-current-id))
                   (octets (fnn-core 'fn-lzd-lookup id)))
              (list* id octets (coerce octets '(simple-array (unsigned-byte 8) (*))))))))

(defun fnn-lz-dicts ()
  "The store's dictionary table (ACL2's): ID 0 only."
  (or *fnn-lz-dicts* (setq *fnn-lz-dicts* (fnn-core 'fn-lzr-dicts-initial))))

(defun fnn-log-read-record (z)
  "The record the log holds as Z (ACL2's octet list), through ACL2's read
step: Z itself (the same list) when it is no frame, the expansion of a
frame.  An expansion ACL2 refuses stops the read by name: a dictionary this
store does not hold is a refusal; a malformed or undecodable frame, whose
entry passed its trailer, is a store fault."
  (destructuring-bind (x tally)
      (fnn-call 'fn-lzr-read-step (or *fnn-lz-tally* (fnn-core 'fn-lzr-tally-empty))
                (fnn-lz-dicts) z)
    (setq *fnn-lz-tally* tally)
    (if (and (consp x) (eq (first x) :ok))
        (second x)
      (let ((line (or (fnn-core 'fn-lzr-read-refusal-text x)
                      "log-frame: ACL2 refused a compressed record without a line")))
        (if (equal x '(:refused :lz-dictionary))
            (error 'fnn-store-open-refusal :message line)
          (fnn-fault "~a" line))))))

(defun fnn-store-compress-min (store)
  "The compression threshold (the `compress-min-octets' configuration row;
0 off): the log's LZ-MIN, which the owner sets from its live configuration
(fn-owner-compress-min-octets); without an owner (the developer image's
offline `store ROOT post'), the store's replayed configuration's
(fn-store-compress-min-octets)."
  (let ((log (fnn-store-log store)))
    (cond ((null log) 0)
          ((fnn-log-lz-min log) (fnn-nat (fnn-log-lz-min log)))
          (t (setf (fnn-log-lz-min log)
                   (fnn-nat (fnn-core-state 'fn-store-compress-min-octets)))))))

(defun fnn-log-compress (store record)
  "RECORD (octets) as the log takes it: ACL2's frame of it, or RECORD."
  (let ((min (fnn-store-compress-min store)))
    (if (zerop min)
        record
      (let* ((r (fnn-octet-list record))
             (plan (fnn-core 'fn-lzr-append-plan min r)))
        (if (null plan)
            record
          (let* ((k (car plan)) (n (cdr plan))
                 (dict (fnn-lz-current-dict))
                 (candidate (funcall 'fnn-deflate-candidate (cddr dict) (fnn-octets record) k n
                                     (fnn-core 'fn-lzr-candidate-cap n)))
                 (decision (fnn-core 'fn-lzr-append-decide (second dict) (first dict) min r k n
                                     (if (eq candidate :none) :none
                                       (fnn-octet-list candidate)))))
            (case (and (consp decision) (first decision))
              (:framed (setf (fnn-log-lz (fnn-store-log store)) t)
                       (second decision))
              (:kept record)
              (t (fnn-fault "~a" (or (fnn-core 'fn-lzr-append-refusal-text decision)
                                     "lz-candidate: ACL2 refused the encoder's block"))))))))))

(defun fnn-log-probe-tail (fd extent unit max st)
  "After the stream's stop ST: ACL2's probe of the rest of the segment
(books/store-log-damage.lisp).  At each offset ACL2 names (fn-lgdm-q), the
header window it names (fn-lgdm-header-len), the entry length it answers from
that window (fn-lgdm-entry-len; NIL: none starts there) and that entry's
octets, then ACL2's step (fn-lgdm-step).  One unit's header, or one entry, per
step.  Returns the probe's final state."
  (let ((ps (fnn-core 'fn-lgdm-start st)))
    (loop until (fnn-core 'fn-lgdm-done-p ps extent) do
      (let* ((q (fnn-nat (fnn-core 'fn-lgdm-q ps)))
             (h (fnn-octet-list (fnn-log-pread fd q (fnn-nat (fnn-core 'fn-lgdm-header-len ps extent)))))
             (n (fnn-core 'fn-lgdm-entry-len h ps extent))
             (e (and n (fnn-octet-list (fnn-log-pread fd q (fnn-nat n))))))
        (setq ps (fnn-core 'fn-lgdm-step h e ps unit max))))
    ps))

(defvar *fnn-octets-lg* nil)

(defun fnn-live-octets-lg ()
  "The log walk's own octet buffer (books/store-log-buffer.lisp fn-octets-lg,
congruent to fn-octets): the served attempt's buffer and the realizer's are
never touched by an open."
  (or *fnn-octets-lg*
      (setq *fnn-octets-lg*
            (or (cdr (assoc 'fn-octets-lg (user-stobj-alist *the-live-state*)))
                (fnn-fault "the log walk's buffer stobj is not in this image")))))

(defvar *fnn-log-stream-finish* nil
  "While the full replay scans the log (fnn-recover-log): a function the
stream calls at each segment's end for the fold of that segment's records'
txids over 1, which the replay took from its one decode of each record
(fn-lgb-decode-next); the stream then steps without the fold
(fn-lgw-step-buf-nf) and sets its NEXT to that fold (fn-lgw-set-next):
books/store-log-walk-once.lisp KEYSTONE fn-lgw-run-nf-then-fold-is-run.
NIL otherwise: the step folds (fn-lgw-step-buf).")

(defun fnn-log-stream-segment (fd extent unit max genesis sink &optional label writable)
  "The segment's decode from GENESIS as a stream of entries
(books/store-log-stream.lisp): at the state's offset the header octets ACL2
names (fn-lgw-header-len), the entry's length from them (fn-lgw-entry-len),
that entry's octets read into the walk's octet buffer (none: an empty
buffer), and ACL2's step over the buffer (fn-lgw-step-buf,
books/store-log-buffer.lisp: KEYSTONE fn-lgw-step-buf-is-step, the list step
on the buffer's octets); each record the step takes (one, or a batch entry's
several) goes to SINK as ACL2's octet list and is not kept here.  One entry's
octets at a time, never the segment (KEYSTONE fn-lgw-run-is-the-open: the
records are the recovered kernel's committed records and the kernel is its
fn-lgc-of).  At the stop, ACL2's probe of the rest of the segment
(fnn-log-probe-tail) and its verdict (fn-lgdm-verdict; KEYSTONES
fn-lgdm-open-verdict-is-the-classification, fn-lgdm-no-silent-prefix): an
entry at the stop validating under another predecessor (a splice or a stale
segment: fn-lgw-broken, which is fn-lgs-chain-broken-p by
fn-lgw-run-is-the-open) or a valid entry anywhere after the stop (DAMAGE, not a torn tail)
is refused by name (fn-lgdm-refusal-text: log-chain-broken, log-damaged),
never read as a torn tail -- unless the operator's repair *fnn-log-repair*
names exactly this damage and ACL2 admits it (fn-lgdm-effective: LABEL the
segment's file name, WRITABLE the active segment of a writable open).
The walk reads each entry through the log walk's own octet buffer
(fn-lgw-step-buf, lane snapshot-open-3; with *fnn-log-stream-finish* the
no-fold step and the replay's fold, fn-lgw-run-nf-then-fold-is-run), and the
verdict is taken on the state it ends in.  Returns (values KERNEL VERDICT): the kernel (fn-lgw-kernel) and the verdict
the open proceeds on (:complete, :torn or :repaired)."
  (let ((st (fnn-core 'fn-lgw-start genesis 1))
        (buf (fnn-live-octets-lg))
        (finish *fnn-log-stream-finish*))
    (unwind-protect
         (loop until (fnn-core 'fn-lgw-stop st) do
           (let* ((pos (fnn-nat (fnn-core 'fn-lgw-pos st)))
                  (h (fnn-log-pread fd pos (fnn-nat (fnn-core 'fn-lgw-header-len st extent))))
                  (n (fnn-core 'fn-lgw-entry-len (fnn-octet-list h) st extent))
                  (e (if n (fnn-log-pread fd pos (fnn-nat n)) (fnn-make-octets 0))))
             ;; The buffer holds exactly the entry's octets (its array E, its
             ;; fill (length E)), as fnn-extent-entry-ok fills the realizer's.
             (setf (svref buf 0) e
                   (svref buf 1) (length e))
             (destructuring-bind (took records next)
                 (fnn-call (if finish 'fn-lgw-step-buf-nf 'fn-lgw-step-buf) st unit max extent buf)
               (when took
                 (if *fnn-extent-file*
                     ;; The full replay's extent seals (PRF-294): each record's
                     ;; PLACE in this entry, ACL2's (fn-lgb-entry-places over
                     ;; the buffer: fn-arx-list-places of its octets), bound for
                     ;; the sink as *fnn-log-record-place* (FILE . PLACE), or NIL.
                     ;; Each place with the entry's COMMITMENT (its trailer, read
                     ;; from the buffer by ACL2: fn-arx-attach-trailers-buffer,
                     ;; books/payload-extent-read.lisp; lane extent-identity,
                     ;; PRF-994): the descriptor the seal makes carries it.
                     (let ((places (fnn-core 'fn-arx-attach-trailers-buffer
                                             (fnn-core 'fn-lgb-entry-places pos (length records) unit buf)
                                             pos buf)))
                       (dolist (record records)
                         (let ((*fnn-log-record-place*
                                 (and (consp places) (cons *fnn-extent-file* (pop places))))
                               (*fnn-log-record-stored* record))
                           (funcall sink (fnn-log-read-record record)))))
                   (dolist (record records)
                     (let ((*fnn-log-record-stored* record))
                       (funcall sink (fnn-log-read-record record))))))
               (setq st next))))
      (setf (svref buf 1) 0
            (svref buf 0) (fnn-make-octets 0)))
    ;; The fold the replay took from its decode of this segment's records.
    (when finish
      (setq st (fnn-core 'fn-lgw-set-next st (fnn-nat (funcall finish)))))
    (let* ((label (or label "segment"))
           (verdict (fnn-core 'fn-lgdm-effective
                              (fnn-core 'fn-lgdm-verdict st (fnn-log-probe-tail fd extent unit max st)
                                        extent)
                              label *fnn-log-repair* (and writable t))))
      (when (fnn-core 'fn-lgdm-refused-p verdict)
        (error 'fnn-store-open-refusal
               :message (or (fnn-core 'fn-lgdm-refusal-text verdict label)
                            (fnn-fault "ACL2 refused a log segment without a line"))))
      (let ((line (or (fnn-core 'fn-lgdm-report-text verdict label)
                      (fnn-core 'fn-lgdm-repair-text verdict label))))
        (when (stringp line) (push line *fnn-log-open-reports*)))
      (values (fnn-core 'fn-lgw-kernel st) verdict))))

(defun fnn-log-quarantine (path fd extent name)
  "Keep the segment's octets [0, EXTENT) as quarantine/NAME beside journal/
(created O_EXCL, fenced with its directory) before a confirmed repair
truncates the segment: the dropped entries stay available to the operator."
  (let* ((journal (fnn-log-parent path))
         (dir (fnn-join (fnn-log-parent journal) "quarantine"))
         (target (fnn-join dir name)))
    (unless (fnn-lstat dir)
      (fnn-posix () (sb-posix:mkdir dir #o700))
      (fnn-fsync-dir (fnn-log-parent journal)))
    (let ((out (fnn-open target (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl
                                        +fnn-o-nofollow+))))
      (unwind-protect
           (let ((at 0))
             (loop while (< at extent) do
               (let ((chunk (fnn-log-pread fd at (min 1048576 (- extent at)))))
                 (fnn-write-range out chunk 0 (length chunk))
                 (incf at (length chunk))))
             (fnn-fsync-file out))
        (fnn-close out)))
    (fnn-fsync-dir dir)
    target))

(defun fnn-log-open-kernel (fd extent unit max &optional (genesis *fn-lg-genesis*))
  "(values RECORDS KERNEL) of the segment (fnn-log-stream-segment collecting
the records, ACL2's octet lists): for the log rig's oracle, never the open."
  (let* ((records nil)
         (ks (fnn-log-stream-segment fd extent unit max genesis
                                     (lambda (r) (push r records)))))
    (values (nreverse records) ks)))

(defun fnn-log-recover (path extent unit max &optional (genesis *fn-lg-genesis*) (sink #'identity))
  "P-LOG-RECOVER (fn-lg-recover-program): the kernel of the segment's decode
from GENESIS, each record handed to SINK as it is read (fnn-log-stream-
segment), then the tail [F, EXTENT) zeroed by one write and fenced.  The
kernel is R-related to the segment at log-recovered
(fn-lg-recover-program-establishes-the-relation)."
  (let* ((fd (fnn-log-open-segment path extent unit))
         (ks (handler-case
                 (multiple-value-bind (ks verdict)
                     (fnn-log-stream-segment fd extent unit max genesis sink
                                             (file-namestring path) t)
                   ;; A confirmed repair (fn-lgdm-effective :repaired): the
                   ;; segment's octets are kept before the tail is zeroed.
                   (let ((name (fnn-core 'fn-lgdm-quarantine-name verdict (file-namestring path))))
                     (when (stringp name) (fnn-log-quarantine path fd extent name)))
                   ks)
               (error (e) (fnn-close fd) (error e)))))
    ;; fn-lg-recover-tail-of-abstraction: the range read from the
    ;; concrete kernel is the logical kernel's.
    (destructuring-bind (offset count) (fnn-call 'fn-lg-recover-tail ks extent)
      (fnn-log-pwrite fd offset (fnn-make-octets count))
      (fnn-log-at :log-truncated)
      (fnn-log-fdatasync fd)
      (fnn-log-at :log-recovered))
    (%make-fnn-log :path path :fd fd :kernel ks :unit unit :max max :extent extent)))

(defun fnn-log-prepare (log record)
  "The checked prepare: RECORD joins the open batch only at the kernel's
next txid (fn-lgc-t-prepare)."
  (fnn-log-with-kernel (log)
    (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-t-prepare (fnn-log-kernel log) record))))

(defun fnn-log-append (log)
  "P-BATCH's append (fn-lg-append-program): the kernel admits the open batch
and its chained entries are written at the frontier in one positioned write.
The batch's staged members go in flight with their places (ACL2's
fn-arx-list-places over the octets written)."
  (fnn-log-with-kernel (log)
    (let* ((ks (fnn-log-kernel log)) (unit (fnn-log-unit log)) (extent (fnn-log-extent log))
           (frontier (fnn-core 'fn-lgc-frontier ks)))
      (unless (fnn-core 'fn-lgc-append-admitsp ks unit extent)
        (fnn-refuse "the log kernel refuses the append (a batch in flight, fenced, or past the extent)"))
      (let ((octets (fnn-core 'fn-lgc-append-octets ks unit)))
        (fnn-log-pwrite (fnn-log-fd log) frontier octets)
        (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-append ks unit extent))
        (fnn-log-members-in-flight log octets frontier unit))))
  (fnn-log-at :log-written))

(defun fnn-log-members-in-flight (log octets frontier unit)
  "The open batch's staged members, with their places, go in flight (under
the kernel lock): ACL2 reads the places from OCTETS, the entries the append
wrote at FRONTIER (fn-arx-list-places: a batch's records share chunk
entries).  Nothing is placed when ACL2 answers none."
  (let ((members (reverse (fnn-log-members log))))
    (setf (fnn-log-members log) nil)
    (when (some #'car members)
      ;; Each place with its entry's COMMITMENT (the trailer the log wrote,
      ;; fn-arx-attach-trailers; lane extent-identity, PRF-994).
      (let ((places (fnn-core 'fn-arx-attach-trailers
                              (fnn-core 'fn-arx-list-places octets frontier (length members) unit
                                        0 0 nil 0 0 nil)
                              frontier octets)))
        (when (and (consp places) (= (length places) (length members)))
          (unless (equal (fnn-log-extent-path log) (fnn-log-path log))
            (setf (fnn-log-extent-file log) (fnn-extent-register (fnn-log-path log))
                  (fnn-log-extent-path log) (fnn-log-path log)))
          (loop for m in members for place in places
                when (car m)
                  do (push (list (car m) (fnn-log-extent-file log) place (cdr m))
                           (fnn-log-inflight log))))))))

(defvar *fnn-arena-pins-lock* (sb-thread:make-mutex :name "fn arena pins")
  "Serializes every event of *fnn-arena-pins* (its own lock: a reader ends,
and unpins, outside the owner's mutex).")

(defvar *fnn-arena-pins* nil
  "ACL2's arena-reader generation state (books/arena-reader-pins.lisp,
PRF-941: (CUR PINS PEND)), NIL before its first event.  A thread that reads
the live arena outside the owner's mutex (a checkpoint publication,
host/native/owner.lisp fnn-owner-publish-captured; the installing reclaim
pass) PINS the current generation under the mutex before it starts and
UNPINS it when it ends; what is taken away from the arena (a COMPLETE's
reseated staged pages, fnn-log-reseat-fenced) is RETIRED at a stamp and
RELEASED once no live pin is at or below the stamp (KEYSTONE
fn-arpn-release-postdates-every-live-pin): an old retirement goes as soon as
the readers older than it end, whatever newer readers run.")

(defun fnn-arena-pins-step (event)
  "One EVENT of ACL2's fn-arpn-step over *fnn-arena-pins*, under its lock;
answers the step's answer."
  (sb-thread:with-mutex (*fnn-arena-pins-lock*)
    (destructuring-bind (st answer)
        (fnn-call 'fn-arpn-step (or *fnn-arena-pins* (fnn-core 'fn-arpn-initial)) event)
      (setq *fnn-arena-pins* st)
      answer)))

(defun fnn-arena-pin ()
  "Pin the current generation for a reader of the live arena outside the
owner's mutex (taken under the mutex, before the reader runs).  Answers G,
which the reader passes to fnn-arena-unpin when it ends."
  (let ((g (fnn-arena-pins-step '(:pin))))
    (unless (integerp g) (fnn-fault "ACL2 returned a malformed arena pin"))
    g))

(defun fnn-arena-unpin (g)
  "The reader pinned at G ended."
  (unless (eq (fnn-arena-pins-step (list :unpin g)) :ok)
    (fnn-fault "ACL2 refused an arena unpin at generation ~a" g)))

(defun fnn-arena-retire (items)
  "ITEMS (a list) taken away from the arena now: pending at the stamp ACL2
answers, released by fnn-arena-release-due."
  (let ((s (fnn-arena-pins-step (list :retire items))))
    (unless (integerp s) (fnn-fault "ACL2 returned a malformed arena stamp"))
    s))

(defun fnn-arena-stamp ()
  "A stamp for a retirement the caller keeps itself (the generation
advances): release it once (fnn-arena-clear-p S)."
  (let ((s (fnn-arena-pins-step '(:stamp))))
    (unless (integerp s) (fnn-fault "ACL2 returned a malformed arena stamp"))
    s))

(defun fnn-arena-clear-p (s &optional own)
  "Whether no reader is pinned at or below the stamp S; OWN, when given, the
asking reader's own pin, not counted."
  (let ((answer (fnn-arena-pins-step (if own (list :clear-except s own) (list :clear s)))))
    (when (eq answer :refused) (fnn-fault "ACL2 refused an arena clear test"))
    answer))

(defun fnn-arena-reader-count ()
  "The live off-mutex arena readers."
  (fnn-arena-pins-step '(:count)))

(defun fnn-arena-release-due ()
  "The pending retirements ACL2 releases now, ((S . ITEMS) ...)."
  (let ((due (fnn-arena-pins-step '(:release))))
    (unless (listp due) (fnn-fault "ACL2 returned a malformed arena release"))
    due))

(defun fnn-log-reseat-fenced (log)
  "The COMPLETE's reseat (PRF-309): each fenced staged member's handle is
re-pointed at the log extent that now durably holds its payload, as ACL2
decides it (fn-arx-commit-reseats: KEYSTONE fn-arx-commit-reseats-keep-the-
arena); the staged pages are then retired, and released (fn-arena-release)
once no reader outside the owner's mutex (a checkpoint publication) that
pinned before them runs (books/arena-reader-pins.lisp); until then they wait
for a later COMPLETE."
  (let ((fenced (fnn-log-with-kernel (log)
                  (prog1 (reverse (fnn-log-fenced log)) (setf (fnn-log-fenced log) nil)))))
    (when fenced
      (let ((arena (fnn-live-arena)))
        (if (fnn-log-lz log)
            ;; KEYSTONE fn-lzr-commit-reseats-keep-the-arena (PRF-326): a
            ;; framed member is re-pointed at its block when the block
            ;; decodes to the handle's payload; any other member takes the
            ;; plain reseat.
            (fnn-call 'fn-lzr-commit-reseats fenced (fnn-lz-dicts) arena)
          (fnn-call 'fn-arx-commit-reseats fenced arena))
        (fnn-arena-retire (mapcar #'first fenced))))
    (let ((due (fnn-arena-release-due)))
      (when due
        (let ((arena (fnn-live-arena)))
          (dolist (entry due)
            (dolist (h (cdr entry)) (fnn-call 'fn-arena-release h arena))))))))


(defun fnn-log-member-files (log)
  "The realizer file ids the log's members in flight or fenced name (their
COMPLETE reseats them there): fn-xrt-scan-may-start's and fn-xrt-close-set's
NAMED."
  (if log
      (fnn-log-with-kernel (log)
        (remove-duplicates
         (loop for m in (append (fnn-log-inflight log) (fnn-log-fenced log))
               when (and (consp m) (integerp (second m))) collect (second m))))
    nil))

(defun fnn-log-fence (log)
  "P-BATCH's fence (fn-lg-fence-program): the barrier, then the kernel's
fence.  A failed barrier fences the kernel (fn-lgc-fence-failed): every
member of the batch is uncertain until recovery decides.  The barrier runs
outside the kernel lock (the owner may be preparing the next batch behind
it: fn-lgc-take changes only the open batch and the txid, fn-lgc-fence
only moves the batch in flight to the committed count); the kernel's fence
reads the kernel as it is when the barrier returned, one step of the
serialized run fn-lgc-run-refines-the-kernel speaks of."
  (handler-case (progn
                  ;; A developer image's test observer of the record barrier
                  ;; (host/native/bp-obligation.lisp's release cut): an EIO
                  ;; here is the barrier's failure.
                  (when *fnn-record-barrier-fault-observer*
                    (funcall *fnn-record-barrier-fault-observer* (fnn-log-path log)))
                  ;; A segment rotated to off-mutex-fenced names: its name is
                  ;; made durable before any member in it is acknowledged.
                  (fnn-log-make-durable log)
                  (fnn-log-fdatasync (fnn-log-fd log)))
    (fnn-os-error (e)
      (fnn-log-with-kernel (log)
        (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence-failed (fnn-log-kernel log))
              (fnn-log-inflight log) nil))
      (fnn-indeterminate "log barrier failed: ~a" e)))
  (fnn-log-with-kernel (log)
    (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence (fnn-log-kernel log) (fnn-log-unit log))
          (fnn-log-fenced log) (append (fnn-log-inflight log) (fnn-log-fenced log))
          (fnn-log-inflight log) nil))
  (fnn-log-at :log-fenced))

(defun fnn-log-finish (log count)
  "Acknowledge COUNT members in order (fn-lgc-finish-one; the kernel never
acknowledges past the committed records' count)."
  (fnn-log-with-kernel (log)
    (dotimes (i count)
      (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-finish-one (fnn-log-kernel log))))))

(defun fnn-log-rig-line (what log size &optional (base 0))
  ;; Not `fnn-log-line': that is the service log's one-argument writer
  ;; (above), which this rig's definition used to replace in the image, so
  ;; every owner start faulted in fn-lgk-acked (friend-blockers-2, 09:10Z).
  ;; The oracle's records are the segment's own, decoded again from its
  ;; bytes (the concrete kernel keeps only their count).  BASE: the records
  ;; before this segment (`log scan-store': the checkpoint's S and the
  ;; closed segments scanned), so records= is the history's count.
  (let ((ks (fnn-log-kernel log))
        ;; From the segment's own genesis (a store's segment 1 chains from
        ;; its genesis record, a suffix segment from the checkpoint's F row:
        ;; `log scan-store'), the log's constant one for a bare rig segment.
        (records (fnn-log-open-kernel (fnn-log-fd log) (fnn-log-extent log)
                                      (fnn-log-unit log) (fnn-log-max log)
                                      (or (fnn-log-genesis log) *fn-lg-genesis*))))
    (fnn-out "~a records=~d frontier=~d next=~d last=~a workload=~(~a~)"
             what (+ base (fnn-nat (fnn-core 'fn-lgc-acked ks))) (fnn-core 'fn-lgc-frontier ks)
             (fnn-core 'fn-lgc-next-txid ks) (fnn-hex (fnn-core 'fn-lgc-last ks))
             (if (fnn-core 'fn-lg-workload-prefixp records 1 size)
                 "t" "nil"))))

(defun fnn-log-rig-handshake ()
  "With FN_NATIVE_LOG_RIG_HANDSHAKE (developer image), the line just printed
is flushed and the verb waits for one line from the client before it writes
again: the power-loss rig marks the device between the two, so its windows
are exact (a client reading behind the process let two batches land inside
one ack window, kernel-concrete-2's first rig run)."
  (when (fnn-developer-selector "FN_NATIVE_LOG_RIG_HANDSHAKE")
    (finish-output *standard-output*)
    (read-line *standard-input* nil nil)))

(defun fnn-log-nat-arg (text what)
  (let ((n (and text (every #'digit-char-p text) (plusp (length text))
                (<= (length text) 12) (parse-integer text))))
    (unless n (error 'fnn-usage-error :message (format nil "log: ~a is not a natural" what)))
    n))

;;; ---------------------------------------------------------------------------
;;; The store's commit through the record log (lane commit-onto-log,
;;; planning/design-2026-09-27-storage-log.md sections 3.3 and 4).
;;;
;;; The member step keeps its calls (fnn-advance-frontier, the prepare,
;;; fnn-publish, fnn-mark-committed, fnn-finish); on a store:
;;;   fnn-log-reserve   the owner's :log-reserve (books/owner-log-route.lisp
;;;                     fn-olr-ocfg-reserve): the allocation is derived, no
;;;                     frontier file exists.  The log kernel first consumes the
;;;                     txids the owner consumed by refusals (fn-olr-consume-to).
;;;   fnn-log-publish   the record joins the log kernel's open batch
;;;                     (fn-lgc-take: T5's allocation rule), then -- in a batch of
;;;                     one -- P-BATCH's append (cut log-written) and barrier
;;;                     (cut log-fenced), and only then the owner's :log-order
;;;                     (fn-olr-ocfg-order).  Inside the owner's batch quantum
;;;                     (*fnn-log-batch*) the append and the barrier run once, at
;;;                     the batch's end (fnn-log-commit-open-batch), before any
;;;                     member's reply leaves the owner.
;;;   fnn-mark-committed nothing: M := D.
;;;   fnn-finish        the kernel acknowledges the member (fn-lgc-finish-one)
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

;;; The genesis at position 0 of the log (format 10, lane format-bump-10;
;;; books/store-genesis.lisp).  The host draws the recorded readings -- the
;;; node identity (32 CSPRNG octets), the history salt (4 CSPRNG octets), the
;;; wall-clock reading and the image's source revision -- and ACL2 builds the
;;; file from them (fn-gen-octets-for); the host neither frames nor checks.
(defun fnn-genesis-path (store)
  (fnn-join (fnn-journal-dir store) (fnn-core 'fn-store-genesis-file-name)))

(defun fnn-genesis-created-seconds ()
  "The genesis's creation time: ACL2 decides the whole seconds past the DTN
epoch (0 without a usable wall) from gettimeofday's raw reading
(books/clock-wall-reading.lisp fn-otm-wall-seconds, KEYSTONE
fn-clkr-wall-seconds-is-the-ns-decision); the host divides nothing."
  (multiple-value-bind (seconds microseconds) (sb-ext:get-time-of-day)
    (let ((created (fnn-core 'fn-otm-wall-seconds seconds microseconds)))
      (unless (and (integerp created) (<= 0 created))
        (fnn-fault "ACL2 returned a malformed genesis time"))
      created)))

(defun fnn-genesis-octets (profile)
  (let ((octets (fnn-core 'fn-store-genesis-octets
                          (fnn-csprng-octets 32 "genesis node identity")
                          (fnn-csprng-octets 4 "genesis history salt")
                          (fnn-genesis-created-seconds)
                          (fnn-octet-list (fnn-string-octets
                                           (or (ignore-errors (fnn-source-revision))
                                               "unknown")))
                          profile)))
    (unless (and octets (fnn-octet-list-p octets))
      (fnn-fault "ACL2 built no genesis for these readings"))
    (fnn-octets octets)))

(defun fnn-log-init-genesis (store)
  "books/byte-store-log-initializer.lisp: the genesis published into journal/
as config.json is (fnn-publish-initial-file, cuts init-genesis-*), then
journal/ fenced (init-genesis-journal-fenced).  An existing genesis is kept (a
re-run init completes, never redraws: EEXIST at the link)."
  (fnn-publish-initial-file store (fnn-genesis-path store)
                            (fnn-genesis-octets (fnn-store-config store))
                            "init-genesis-")
  (fnn-fsync-dir (fnn-journal-dir store))
  (fnn-init-cut store "init-genesis-journal-fenced"))

(defun fnn-genesis-open (store &optional (profile (or (fnn-store-sealed-config store)
                                                      (fnn-store-config store))))
  "Every open of a format-10 store: ACL2's open of journal/000000.log under
the profile the store opened (fn-gen-open, books/store-genesis.lisp),
refused by name (genesis-damaged, genesis-format, schema-digest,
profile-digest) or kept for this process (fn-store-genesis-install: the
owner's history salt, `store digest').  Answers the chain value segment 1
starts from.  No file at all: an init that did not finish."
  (let ((path (fnn-genesis-path store)))
    (unless (fnn-check-regular path)
      (fnn-fault "missing store genesis: ~a (an init that did not finish: run init again)" path))
    (let ((verdict (fnn-core 'fn-store-genesis-open
                             (fnn-octet-list (fnn-read-regular-bounded path 1024))
                             profile)))
      (unless (and (consp verdict) (member (first verdict) '(:genesis :refused)))
        (fnn-fault "ACL2 returned a malformed genesis verdict"))
      (when (eq (first verdict) :refused)
        (let ((text (fnn-core 'fn-store-genesis-refusal-text verdict)))
          (unless (stringp text)
            (fnn-fault "ACL2 refused the genesis without naming a reason"))
          (error 'fnn-store-open-refusal :message text)))
      (fnn-core-state 'fn-store-genesis-install verdict)
      (fnn-core 'fn-store-genesis-chain verdict))))

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

(defun fnn-log-open-read-only (path unit max &optional (genesis *fn-lg-genesis*) (sink #'identity))
  (let* ((extent (fnn-log-observed-extent path))
         (fd (fnn-log-open-segment path extent unit t))
         (ks (handler-case (fnn-log-stream-segment fd extent unit max genesis sink
                                                   (file-namestring path))
               (error (e) (fnn-close fd) (error e)))))
    (%make-fnn-log :path path :fd fd :unit unit :max max :extent extent :kernel ks)))

(defun fnn-log-batch-reset (log)
  (setf (fnn-log-count log) 0 (fnn-log-octets log) 0))

(defun fnn-recover-log-stream-begin ()
  "The full replay of a history that arrives a record at a time: the replay
begun (fnn-bridge-recover-begin), an empty chunk, its octet count, the
next txid folded over the decoded chunks (fn-ofw-wire-next),
the chunk's places, and (SIXTH) the log stream's txid fold over the current
segment's records from 1, taken from the same decode (fn-lgb-decode-next) and
handed to the stream at the segment's end (*fnn-log-stream-finish*).  The
chunks close where ACL2 says (fn-srs-chunk-fullp before a record is added, one
record always taken first), as fnn-recover-record-chunks closes them; any
chunking gives the same statement-context replay and arena
(fn-ssr-resident-step-of-append; physical modes refine the resident worker)."
  (setq *fnn-lz-tally* nil)
  (list (fnn-bridge-recover-begin) nil 0 0 nil 1 nil))

(defun fnn-recover-log-stream-flush (replay)
  "Decode and intern the open chunk with its sequential statement epoch.
Physical placement modes of fn-ssr-intern-step refine its resident mode
under fn-arena-p and fn-arx-faithful-p, including rows and arena effects
(fn-ssr-extent-step-refines-resident, fn-ssr-lz-step-refines-resident)."
  (when (second replay)
    (let* ((chunk (nreverse (second replay)))
           (places (nreverse (fifth replay)))
           (stored (nreverse (seventh replay)))
           ;; The chunk's events and the fold of its records' txids over the
           ;; segment's fold so far, from one decode of each record
           ;; (books/store-log-walk-once.lisp fn-lgb-decode-next: EQUAL to
           ;; fn-srs-decode and fn-lgw-next-fold).
           (answer (fnn-call 'fn-lgb-decode-next chunk (sixth replay)))
           (decoded (first answer)))
      (setf (sixth replay) (second answer))
      (when (consp decoded)
        (setf (fourth replay)
              (fnn-core 'fn-ofw-wire-next decoded (fourth replay))))
      (unless (cond ((not (some #'identity places))
                     (fnn-bridge-recover-step (first replay) decoded))
                    ;; A chunk holding a compressed record (its stored octets
                    ;; are not the record: a frame): ACL2's compressed intern
                    ;; (books/payload-lz-replay.lisp fn-lzr-intern-step,
                    ;; KEYSTONE fn-lzr-intern-step-refines) over the octets
                    ;; the log holds.
                    ((notevery #'eq chunk stored)
                     (fnn-bridge-recover-step-lz (first replay) decoded stored places))
                    (t (fnn-bridge-recover-step-extents (first replay) decoded chunk places)))
        (fnn-fault "ACL2 replay rejected committed transaction history")))
    (setf (second replay) nil (third replay) 0 (fifth replay) nil (seventh replay) nil)))

(defun fnn-replay-fault ()
  "The replay's fault (a history ACL2 cannot apply: damage, exit 4), with
where the replay stopped when ACL2 recorded it (fn-store-open-stop-text,
books/store-open-replay-refusal.lisp fn-sorr-stop-text)."
  (let ((stop (fnn-core-state 'fn-store-open-stop-text)))
    (if (stringp stop)
        (fnn-fault "ACL2 replay rejected committed transaction history or configuration history: ~a"
                   stop)
      (fnn-fault "ACL2 replay rejected committed transaction history or configuration history"))))

(defun fnn-recover-log-stream-take (replay record)
  "RECORD (ACL2's octet list) into the open chunk; a full chunk is decoded
and interned first."
  (when (and (second replay) (fnn-core 'fn-srs-chunk-fullp (third replay)))
    (fnn-recover-log-stream-flush replay))
  (push record (second replay))
  (push *fnn-log-record-place* (fifth replay))
  ;; The octets the log holds for it (SEVENTH): the frame of a compressed
  ;; record, else the record itself (EQ: fnn-log-read-record answers the
  ;; stored list when it is no frame).
  (push *fnn-log-record-stored* (seventh replay))
  (incf (third replay) (length record)))

(defun fnn-recover-log-stream-end (store replay config-records)
  "The last chunk, then the open over the rows at the derived frontier, as
fnn-recover-log-replay ends."
  (fnn-recover-log-stream-flush replay)
  (let ((action (fnn-bridge-recover-end (first replay) (fnn-store-frontier store)
                                        config-records)))
    (when (eq action :refused)
      (let ((text (fnn-core-state 'fn-store-open-refusal-text)))
        (unless (stringp text)
          (fnn-fault "ACL2 refused the open without naming a reason"))
        (error 'fnn-store-open-refusal :message text)))
    (unless (eq action :recovering)
      (fnn-replay-fault))))

(defun fnn-recover-log-replay (store records config-records)
  "The replay the per-file open runs (fnn-recover-full-replay), over the
log's records (the kernel's committed octet lists), in the chunks ACL2 closes
(`fnn-recover-record-chunks', as the pack path: PRF-261's
fn-srs-steps-are-one-step-of-the-concatenation, any chunking opens the same
Store); the history's COUNT (the open keeps no records, PKT-823)."
  (let ((action (fnn-bridge-recover (fnn-recover-record-chunks records)
                                    (fnn-store-frontier store) config-records)))
    (when (eq action :refused)
      (let ((text (fnn-core-state 'fn-store-open-refusal-text)))
        (unless (stringp text)
          (fnn-fault "ACL2 refused the open without naming a reason"))
        (error 'fnn-store-open-refusal :message text)))
    (unless (eq action :recovering)
      (fnn-replay-fault)))
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
  "The open's recovery barriers' thunks after P-LOG-RECOVER's segment fence,
in the model's order (books/store-log-route-programs.lisp fn-lg-open-program;
*fn-sf-recovery-barrier-count* 3): journal/ (a create or unlink a death in
P-ROTATE, P-DROP or init left pending), the root (a checkpoint renamed before
its root fence, ahead of the open's drop) and the root's parent (an import
at import-published).  The config file's and the segment's second fence are
gone: both are the identity at the open (books/store-log-open-barriers.lisp
fn-lgob-three-barrier-open-after-recovery-is-the-five); none of the three can
go (the same book's fn-lgob-two-barriers-without-* counterexamples)."
  (list (lambda () (fnn-fsync-dir (fnn-journal-dir store)))
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

(defun fnn-log-spare-path (store k)
  "staging/.stage-segment-K: the spare of segment K.  A `.stage-' name, so a
writable open's staging sweep (books/store-sweep.lisp fn-sn-staging-namep)
removes one a death left, and the open's segment listing never sees it
(fn-lgs-indices keeps only NNNNNN.log names)."
  (fnn-join (fnn-staging store) (format nil ".stage-segment-~6,'0d" k)))

(defun fnn-log-discard-spare (log)
  "Close and unlink a spare that will not be renamed (another index, or the
store closing).  Removing a staged name is never uncertain for the history:
the open ignores and sweeps it."
  (let ((spare (fnn-log-spare log)))
    (when spare
      (setf (fnn-log-spare log) nil)
      (destructuring-bind (index path fd) spare
        (declare (ignore index))
        (ignore-errors (fnn-close fd))
        (ignore-errors (when (fnn-lstat path) (fnn-unlink path)))))))

(defun fnn-log-prepare-spare (store)
  "P-ROTATE's first half, fn-lgs-spare-program (books/store-log-segments.lisp),
OFF the owner mutex: the next segment (fn-lgs-next-segment of the active
index) created in staging/, preallocated to ACL2's initial extent (cut
rotate-created) and fenced (cut rotate-fenced).  Nothing names it in
journal/, so a death here leaves the history as it was and the next open
sweeps the staged file.  Idempotent: a spare of the next index already
prepared is kept.  An OS error removes what it made and is a known failure
of the checkpoint that wanted the rotation (serving continues)."
  (let ((log (fnn-store-log store)))
    (sb-thread:with-mutex ((fnn-log-spare-lock log))
      (let ((next (fnn-core 'fn-lgs-next-segment (fnn-log-index log)))
            (spare (fnn-log-spare log)))
        (unless (and spare (eql (first spare) next))
          (fnn-log-discard-spare log)
          (unless next
            (fnn-refuse "rotation refused reason=segment-index-exhausted"))
          (let ((path (fnn-log-spare-path store next))
                (extent (fnn-nat (fnn-core 'fn-store-log-initial-extent)))
                (fd nil))
            (handler-case
                (progn
                  ;; A staged spare an earlier failed prepare of this run left.
                  (when (fnn-lstat path) (fnn-unlink path))
                  (setq fd (fnn-open path (logior sb-posix:o-rdwr sb-posix:o-creat
                                                  sb-posix:o-excl +fnn-o-nofollow+)))
                  (fnn-log-preallocate fd extent)
                  (fnn-log-at :rotate-created)
                  (fnn-fsync-file fd)
                  (fnn-log-at :rotate-fenced))
              (fnn-os-error (e)
                (when fd (ignore-errors (fnn-close fd)))
                (ignore-errors (when (fnn-lstat path) (fnn-unlink path)))
                (fnn-refuse-io "log rotation's spare failed: ~a" e)))
            (setf (fnn-log-spare log) (list next path fd))))))))

(defun fnn-log-rotate (store)
  "P-ROTATE's switch, fn-lgs-rotate-program (design 2026-09-27 storage-log
sections 4 and 6; lane operations), at a checkpoint's capture, with no batch
open, none in flight and every member acknowledged (fn-lgc-rotate-admitsp):
the prepared spare of the next segment (fn-lgs-next-segment;
fnn-log-prepare-spare made it off the mutex) is renamed into journal/ under
its segment name (cut rotate-renamed) and becomes the active segment, its
kernel fn-lgc-rotate of the closed one's (fn-lgc-rotate-refines:
fn-lgs-rotate's abstraction, the kernel recovery derives from its zeros:
fn-lgs-rotate-is-the-recovered-kernel).  The rename is the only I/O here:
journal/'s fence (cut rotate-durable) is fnn-log-make-durable's, taken by
the new segment's first fence and by the checkpoint that names it, both off
the owner mutex; until then no member in the new segment is acknowledged
and no checkpoint names it.  The new segment opens with its ROTATION ENTRY
(lane store-lineage, PRF-979: fn-lgc-rotation-octets, written here at
offset 0, cut rotate-headed; the kernel starts past it).  Returns the log
position the checkpoint's F row carries: (K GENESIS), the new segment and
its head's trailer, which the open checks the head against
(fnn-log-lineage-genesis).  No spare of the next index: refused (spare-unprepared), the
closed segment stays active; the caller prepares one and asks again.  A
rename whose outcome is unknown is a recovery event (the name may or may not
be in journal/ while the closed segment would take more records)."
  (let* ((log (fnn-store-log store))
         (ks (fnn-log-kernel log))
         (next (fnn-core 'fn-lgs-next-segment (fnn-log-index log))))
    (unless (fnn-core 'fn-lgc-rotate-admitsp ks)
      ;; A batch open, in flight or unacknowledged: no rotation now (the
      ;; checkpoint is not published; the owner retries at its next due).
      (fnn-refuse "rotation refused reason=batch-in-flight"))
    ;; An empty active segment is already where the suffix starts.
    (unless (fnn-core 'fn-lgc-rotate-needed-p ks)
      (return-from fnn-log-rotate
        (list (fnn-log-index log) (fnn-core 'fn-lgc-last ks))))
    (unless next
      (fnn-refuse "rotation refused reason=segment-index-exhausted"))
    (let ((spare (fnn-log-spare log)))
      (unless (and spare (eql (first spare) next))
        (fnn-refuse "rotation refused reason=spare-unprepared"))
      (setf (fnn-log-spare log) nil)
      (destructuring-bind (index staged fd) spare
        (declare (ignore index))
        (let* ((path (fnn-segment-path-at store next))
               (renamed (handler-case (fnn-rename-no-replace staged path)
                          (fnn-os-error (e)
                            (ignore-errors (fnn-close fd))
                            (fnn-indeterminate "log rotation's rename is uncertain: ~a" e)))))
          (when renamed
            ;; :exists (a segment of that index is already there) or
            ;; :unsupported: nothing was renamed.
            (ignore-errors (fnn-close fd))
            (ignore-errors (when (fnn-lstat staged) (fnn-unlink staged)))
            (fnn-refuse "rotation refused reason=spare-rename-~(~a~)" renamed))
          (fnn-log-at :rotate-renamed)
          ;; The head (lane store-lineage; books/store-log-lineage.lisp): the
          ;; rotation entry chained from the closed segment's last trailer,
          ;; at offset 0 of the new segment (cut rotate-headed).  No fence
          ;; here: fnn-log-make-durable fences the file before journal/, so
          ;; an F row never names an unheaded segment.  A write whose
          ;; outcome is unknown is a recovery event, as the rename's is.
          (let ((unit (fnn-log-unit log)))
            (handler-case (fnn-log-pwrite fd 0 (fnn-core 'fn-lgc-rotation-octets ks next unit))
              (fnn-os-error (e)
                (fnn-indeterminate "log rotation's head write is uncertain: ~a" e)))
            (fnn-log-at :rotate-headed)
            (fnn-close (fnn-log-fd log))
            (setf (fnn-log-path log) path
                  (fnn-log-fd log) fd
                  (fnn-log-kernel log) (fnn-core 'fn-lgc-rotate ks next unit)
                  (fnn-log-index log) next
                  (fnn-log-genesis log) (fnn-core 'fn-lgc-last ks)
                  (fnn-log-extent log) (fnn-nat (fnn-core 'fn-store-log-initial-extent))
                  (fnn-log-pending log) 0
                  (fnn-log-dir-pending log) (fnn-journal-dir store))
            (fnn-log-batch-reset log)
            ;; The F row's position: the new segment and its head's trailer,
            ;; the chain value its records continue from.
            (list next (fnn-core 'fn-lgc-last (fnn-log-kernel log)))))))))

(defun fnn-log-make-durable (log)
  "fn-lgs-rotate-durable-program: the rotated-to segment's file fenced (its
head, the rotation entry of cut rotate-headed) and then journal/ (cut
rotate-durable) while the segment's name is pending.  Called off the owner
mutex by the new segment's first fence (fnn-log-fence: no member there is
acknowledged before its name is durable) and by the publication before its
checkpoint names the segment, so an F row never names an unheaded segment.
Two callers may both fence; that is harmless."
  (let ((dir (fnn-log-dir-pending log)))
    (when dir
      (fnn-fsync-file (fnn-log-fd log))
      (fnn-fsync-dir dir)
      (fnn-log-at :rotate-durable)
      (setf (fnn-log-dir-pending log) nil))))

(defun fnn-log-rotate-now (store)
  "The whole P-ROTATE in one thread, for a store no owner serves (`store
compact', `store reclaim'): the spare, the switch, journal/'s fence."
  (fnn-log-prepare-spare store)
  (prog1 (fnn-log-rotate store)
    (fnn-log-make-durable (fnn-store-log store))))

(defun fnn-log-covered-indices (store first)
  "The segments present below FIRST (a checkpoint's first suffix segment)."
  (let ((plan (fnn-core 'fn-lgs-open-plan (fnn-log-segment-names store) first)))
    (if (eq (first plan) :scan) (third plan) nil)))

(defun fnn-log-lineage-genesis (store k g t0)
  "The open's lineage decision (books/store-log-lineage.lisp fn-lgl-open,
PRF-979) over the checkpoint's F row (K G): segment K's head -- its first
fn-lgl-head-len octets, the rotation entry the rotation wrote (cut
rotate-headed) -- must be a readable rotation entry naming K whose trailer
is G; for K = 1 (no head) G must be the genesis record's trailer T0.
Refused by name (foreign-lineage: a restored backup's or another store's
checkpoint against this log, or this store's checkpoint against a restored
log that diverged; segment-head-damaged; segment-misnamed).  Answers the
chain value the scan of K starts from: the head's claimed predecessor
(fn-lgl-head-prev, the closed segment's last trailer; the head then
validates as K's first entry, with no record), or T0.  Nothing is written:
an ordinary restart opens under the same (K G); the chain through the heads
is the store's ancestry and changes only when the log does."
  (let* ((unit (fnn-store-log-unit))
         (max (fnn-store-log-max store))
         (head (and (>= k 2)
                    (let* ((path (fnn-segment-path-at store k))
                           (fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
                      (unwind-protect
                           (let ((octets (fnn-read-exact-fd
                                          fd (fnn-nat (fnn-core 'fn-lgl-head-len unit)))))
                             (and octets (fnn-octet-list octets)))
                        (fnn-close fd)))))
         (verdict (fnn-core 'fn-lgl-open k g head t0 max)))
    (when verdict
      (error 'fnn-store-open-refusal :message (fnn-core 'fn-lgl-refusal-text verdict)))
    (if (>= k 2) (fnn-core 'fn-lgl-head-prev head max) g)))

(defun fnn-log-head-segment (store log)
  "An active segment K >= 2 the scan read to nothing (frontier 0): a rotation
died between the rename and the head (cut rotate-renamed), or its torn head
was truncated by P-LOG-RECOVER (cut log-truncated).  The writable open
completes the rotation: the rotation entry from the chain the scan carried
(fn-lgc-rotation-octets of the recovered kernel, whose LAST is that chain
value) at offset 0, the file fenced, journal/ fenced, the kernel the
rotation's (fn-lgc-rotate; fn-lgs-rotate-is-the-recovered-kernel).  Its
byte states are those of the rotation's own cuts rotate-renamed and
rotate-headed (the same entry at the same offset), so a death here is a
death there.  A reader writes nothing and reads the segment as it is, empty
(frontier 0, no record): the history is the closed segments', the same one
the writable open reaches (specs/storage.md: a death at any rotation cut
reopens to the same history; `status' exits 0 after cut rotate-renamed).  A
headed segment reads past its head and is left alone."
  (when (and (>= (fnn-log-index log) 2)
             (fnn-store-writable store)
             (zerop (fnn-nat (fnn-core 'fn-lgc-frontier (fnn-log-kernel log)))))
    (let ((ks (fnn-log-kernel log)) (k (fnn-log-index log)) (unit (fnn-store-log-unit)))
      (fnn-log-pwrite (fnn-log-fd log) 0 (fnn-core 'fn-lgc-rotation-octets ks k unit))
      (fnn-fsync-file (fnn-log-fd log))
      (fnn-fsync-dir (fnn-journal-dir store))
      (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-rotate ks k unit)))))

(defun fnn-log-scan-segments (store scan genesis sink &optional places)
  "Scan the segments SCAN (indices, the last the active one) from GENESIS,
the chain carried from each segment's kernel to the next (fn-lgc-last), each
record handed to SINK in order as it is read (fnn-log-stream-segment: one
entry's octets at a time).  The closed segments are read only (the fold's step,
books/store-log-stream.lisp fn-lgw-open-chain-records / -last over one
segment, T8's subject, fn-lgw-segment-drop-preserves-the-open); the active one
is recovered (a
writable open: P-LOG-RECOVER) or read.  Returns the active segment's log.
With PLACES (the full replay), each segment gets an extent realizer id
(host/native/extent.lisp fnn-extent-register: a read-only descriptor held for
the process's life) and the stream binds each record's place for SINK
(*fnn-log-record-place*)."
  (let ((unit (fnn-store-log-unit))
        (max (fnn-store-log-max store)))
    (loop for (k . more) on scan do
      (let ((path (fnn-segment-path-at store k)))
        (if more
            (let* ((extent (fnn-log-observed-extent path))
                   (fd (fnn-log-open-segment path extent unit t))
                   (*fnn-extent-file* (and places (fnn-extent-register path))))
              (unwind-protect
                   (setq genesis (fnn-core 'fn-lgc-last
                                           (fnn-log-stream-segment fd extent unit max genesis sink
                                                                   (file-namestring path))))
                (fnn-close fd)))
          (progn
            (fnn-log-complete-rotation store path)
            (let* ((*fnn-extent-file* (and places (fnn-extent-register path)))
                   (log (if (fnn-store-writable store)
                            (fnn-log-recover path (fnn-log-observed-extent path) unit max genesis sink)
                          (fnn-log-open-read-only path unit max genesis sink))))
              (setf (fnn-log-index log) k
                    (fnn-log-genesis log) genesis)
              ;; An unheaded segment (a rotation that died before its head):
              ;; headed now by a writable open, read as empty by a reader.
              (fnn-log-head-segment store log)
              (return-from fnn-log-scan-segments log))))))
    (fnn-fault "the log's open plan named no segment")))

(defun fnn-log-read-closed-segment (store k genesis unit max sink)
  "A closed segment K read only, one entry at a time (fnn-log-stream-segment;
the fold's step of books/store-log-stream.lisp fn-lgw-open-chain-records /
-last over the one segment, T8's subject), each record to SINK as ACL2's octet
list, the
splice refused by name.  Answers the chain's last trailer, the next segment's
genesis."
  (let* ((path (fnn-segment-path-at store k))
         (extent (fnn-log-observed-extent path))
         (fd (fnn-log-open-segment path extent unit t)))
    (unwind-protect
         (fnn-core 'fn-lgc-last (fnn-log-stream-segment fd extent unit max genesis sink
                                                        (file-namestring path)))
      (fnn-close fd))))

(defun fnn-log-committed-count (store)
  "The active segment's committed record count (the log kernel's, read under
its lock): fnn-history-last-record's test that nothing was committed since
the open noted its newest record."
  (let ((log (fnn-store-log store)))
    (fnn-core 'fn-lgc-count (fnn-log-with-kernel (log) (fnn-log-kernel log)))))

(defun fnn-log-read-active-segment (store sink)
  "The active segment's COMMITTED records again, one entry at a time, each to
SINK as ACL2's octet list: a read-only descriptor streamed from the segment's
genesis over its first FRONTIER octets (the concrete kernel's frontier, read
under the kernel lock), which scan completely to the committed records (R's
first conjunct, books/store-log-kernel.lisp): an appended but unfenced batch
lies past the frontier and is never read as history.  The read-back's count
and last trailer must be the kernel's, or the read is a fault."
  (let* ((log (fnn-store-log store))
         (ks (fnn-log-with-kernel (log) (fnn-log-kernel log)))
         (frontier (fnn-nat (fnn-core 'fn-lgc-frontier ks)))
         (unit (fnn-log-unit log))
         (fd (fnn-log-open-segment (fnn-log-path log) (fnn-log-observed-extent (fnn-log-path log))
                                   unit t)))
    (unwind-protect
         (let ((read (fnn-log-stream-segment fd frontier unit (fnn-log-max log)
                                             (fnn-log-genesis log) sink)))
           (unless (and (eql (fnn-core 'fn-lgc-count read) (fnn-core 'fn-lgc-count ks))
                        (equal (fnn-core 'fn-lgc-last read) (fnn-core 'fn-lgc-last ks)))
             (fnn-fault "the active log segment does not read back its committed records")))
      (fnn-close fd))))

(defun fnn-recover-log-from-log-checkpoint (store config-records suffix s &optional (interned nil internedp))
  "The open from a checkpoint whose F row names the log's first suffix
segment: SUFFIX is the scan from there (T8: with the checkpoint's records it
is the whole history), replayed over the checkpoint
(fn-store-sn-recover-from-checkpoint).  The covered segments may be gone, so
there is no full replay to fall back to: a checkpoint the open cannot use is
refused by name."
  (progn
    ;; S: the loaded checkpoint's (fnn-recover-log loaded it once, first).
    (let ((action (if internedp
                      (fnn-recover-suffix-rows store suffix config-records interned)
                      (fnn-recover-suffix-rows store suffix config-records))))
      (unless (eq action :recovering)
        ;; A replay that stopped names itself (fn-store-open-refusal-text:
        ;; books/store-open-replay-refusal.lisp); else the checkpoint is damaged.
        (let ((text (and (eq action :refused) (fnn-core-state 'fn-store-open-refusal-text)))
              (stop (and (eq action :fault) (fnn-core-state 'fn-store-open-stop-text))))
          (fnn-core-state 'fn-store-sco-clear)
          (fnn-bridge-reset)
          (error 'fnn-store-open-refusal
                 :message (cond ((stringp text) text)
                                ((stringp stop)
                                 (format nil "open refused reason=checkpoint-damaged: the checkpoint that covers the dropped log segments does not open: ~a" stop))
                                (t "open refused reason=checkpoint-damaged: the checkpoint that covers the dropped log segments does not open"))))))
    (setf (fnn-store-open-mode store) (list :checkpoint s (length suffix)))
    ;; The history's count (PKT-823); the prefix stays in the arena and the
    ;; checkpoint's rows, encoded only for a verb that reads the history
    ;; (fnn-log-history-records).
    (+ s (length suffix))))

(defun fnn-recover-log (store)
  "The open of a store.  The checkpoint first: its F row names where
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
            ;; No segment and no checkpoint: an init that did not finish
            ;; (the segment is its last step); init again completes it.
            (when (equal plan '(:refused :no-segment))
              (fnn-fault "missing store directory: ~a has no log segment (an init that did not finish: run init again)"
                         (fnn-journal-dir store)))
            (when (eq (first plan) :refused)
              (error 'fnn-store-open-refusal
                     :message (format nil "open refused reason=~(~a~): the log's segments do not hold the history~@[ from segment ~d~]"
                                      (second plan) (first log-position))))
            (setq drop (third plan))
            ;; The records arrive one at a time (fnn-log-scan-segments), each
            ;; folded into the next txid (one past the largest txid of every
            ;; record the log holds, of every event kind: fn-store-log-next-
            ;; txid-step per record, or -of-events over the replay's decoded
            ;; chunks when the replay streams).  With no checkpoint to open from (no F row position, no
            ;; state checkpoint: ACL2's selection over a count of 0, the call
            ;; fnn-recover-log-from-state-checkpoint makes, answers the full
            ;; replay before any record is read), each record goes straight to
            ;; the replay's chunk (fnn-recover-log-stream-take) and none is
            ;; kept; otherwise each is kept as its octet vector for the
            ;; checkpoint's suffix.
            ;; Format 10: the genesis is read and checked at every open (its
            ;; schema and profile digests, refused by name); segment 1 chains
            ;; from its trailer, a checkpoint's first suffix segment from the
            ;; F row's genesis.
            (let* ((genesis (let ((chain (fnn-genesis-open store)))
                              ;; The lineage decision (lane store-lineage,
                              ;; PRF-979): the F row's (K G) against segment
                              ;; K's head; the scan of K starts from the
                              ;; head's predecessor.
                              (if log-position
                                  (fnn-log-lineage-genesis store (first log-position)
                                                           (second log-position) chain)
                                chain)))
                   (full (and (not log-position) (not (eq status :ok))
                              (let ((choice (fnn-core 'fn-store-sco-select status sequence 0
                                                      (fnn-store-config store))))
                                (unless (and (consp choice)
                                             (member (first choice) '(:checkpoint :full-replay)))
                                  (fnn-fault "ACL2 returned a malformed checkpoint selection"))
                                (and (eq (first choice) :full-replay) choice))))
                   (config-records (fnn-config-records store))
                   (acc 0) (kept nil) (decoded nil) (scanned 0) (newest nil)
                   (replay (and full (fnn-recover-log-stream-begin)))
                   (log (let ((*fnn-log-stream-finish*
                                ;; The full replay decodes every record once:
                                ;; at each segment's end its pending chunk is
                                ;; decoded, and the stream takes the fold
                                ;; of the segment's txids from that decode
                                ;; (books/store-log-walk-once.lisp).
                                (and replay
                                     (lambda ()
                                       (fnn-recover-log-stream-flush replay)
                                       (prog1 (sixth replay) (setf (sixth replay) 1))))))
                         (fnn-log-scan-segments
                         store (second plan) genesis
                         (lambda (record)
                           (incf scanned)
                           (setq newest record)
                           (cond (replay
                                  (fnn-recover-log-stream-take replay record))
                                 ;; Over a checkpoint whose F row names the
                                 ;; suffix, every scanned record is the
                                 ;; suffix, decoded once below: its txids
                                 ;; are folded from that decode.
                                 (log-position
                                  (push (fnn-octets record) kept))
                                 (t
                                  (setq acc (fnn-core 'fn-store-log-next-txid-step record acc))
                                  (push (fnn-octets record) kept))))
                         ;; the full replay seals extents: each record's place
                         replay))))
              ;; The streamed replay folded the txids from its decoded chunks
              ;; (the last chunk decoded here, before the frontier is derived).
              (when replay
                (fnn-recover-log-stream-flush replay)
                (setq acc (fourth replay)))
              ;; The suffix over a log checkpoint, decoded and interned once,
              ;; a chunk at a time (fnn-recover-suffix-intern): the txid fold
              ;; reads each chunk's decoded events (fn-store-log-next-txid-of-
              ;; events, as the streamed replay's does), and the replay over
              ;; the checkpoint opens over the rows (fnn-recover-suffix-rows).
              ;; A suffix that does not decode folds nothing here; its replay
              ;; refuses the open.
              (when (and log-position (not replay))
                (setq kept (nreverse kept))
                (multiple-value-setq (decoded acc)
                  (fnn-recover-suffix-intern kept (mapcar #'fnn-octet-list config-records) acc)))
              (fnn-log-batch-reset log)
              (setf (fnn-store-log-last store)
                    (and newest (list (fnn-core 'fn-lgc-count (fnn-log-kernel log)) newest)))
              ;; The frontier: the fold, at least the checkpoint's frontier at S
              ;; (the dropped segments' txids) and the log kernel's next, and
              ;; the log kernel caught up to it.
              ;; And past every configuration record's txid
              ;; (fn-store-cfg-next-txid): a record accepted while POSTs were
              ;; refused on a full budget stands above every event.
              (let ((next (fnn-nat (fnn-core 'fn-store-log-next-txid-join
                                             (fnn-core 'fn-store-log-next-txid-join
                                                       (fnn-core 'fn-store-log-next-txid-join acc floor)
                                                       (fnn-core 'fn-store-cfg-next-txid
                                                                 (mapcar #'fnn-octet-list config-records) 0))
                                             (fnn-core 'fn-lgc-next-txid (fnn-log-kernel log))))))
                (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-consume-to (fnn-log-kernel log) next)
                      (fnn-store-log store) log
                      (fnn-store-frontier store) next))
              (setf (fnn-store-log-history store)
                    (let ((scan (second plan)))
                      (list (and log-position t) (butlast scan) genesis (car (last scan)))))
              (setq count
                    (cond (full
                           (setf (fnn-store-open-mode store) (list :full-replay (second full)))
                           (fnn-recover-log-stream-end store replay config-records)
                           scanned)
                          (t
                           (let ((records (if log-position kept (nreverse kept))))
                             (setq kept nil)
                             (if log-position
                                 (fnn-recover-log-from-log-checkpoint store config-records records
                                                                      sequence decoded)
                               (or (fnn-recover-log-from-state-checkpoint store config-records records)
                                   (fnn-recover-log-replay store records config-records)))))))))
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
    (setf (fnn-store-fenced store) nil)
    count))

(defun fnn-log-reserve (store current-txid &optional operation)
  "The member's reservation on the log route (fn-olr-ocfg-reserve through
the observe callback): the frontier is the log's derived one."
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  (unless (eql current-txid (fnn-store-frontier store))
    (setf (fnn-store-fenced store) t)
    (fnn-fault "ACL2 allocator and the log's frontier disagree"))
  (let ((next (funcall *fnn-identity-reservation-callback* operation))
        (log (fnn-store-log store)))
    (case next
      (:identity-exhausted (fnn-refuse "finite transaction-ID domain exhausted"))
      (:identity-reserve (fnn-refuse "transaction identities reserved for promised releases"))
      (:operation-refused (fnn-refuse "retention operation has no current identity grant"))
      (:unaffordable (fnn-refuse "retention operation cannot fund its other resources")))
    (unless (and (integerp next) (<= 0 next))
      (fnn-fault "ACL2 returned malformed identity reservation"))
    (fnn-log-with-kernel (log)
      (setf (fnn-log-kernel log)
            (fnn-core 'fn-lgc-consume-to (fnn-log-kernel log) current-txid)
            (fnn-log-reserved log) current-txid))
    (unless (eq (fnn-observe store :log-reserve) :reserved)
      (setf (fnn-store-fenced store) t)
      (fnn-fault "ACL2 rejected the log route's reservation"))
    (setf (fnn-store-frontier store) next)
    (fnn-at store :frontier-reserved)
    next))

(defun fnn-log-take (store record)
  "RECORD into the open batch (fn-lgc-take; fn-lgc-take-refines: fn-olr-take's
verdict, kernel and entry length).  :full commits the open batch
first (inside a batch quantum the batch closes at the operator's bounds)."
  (let* ((log (fnn-store-log store))
         (octets (fnn-octet-list record)))
    (loop repeat 2 do
      (when (eq (fnn-log-with-kernel (log) (fnn-core 'fn-lgc-phase (fnn-log-kernel log))) :fault)
        ;; The barrier of the batch in flight failed (the syncer fenced the
        ;; kernel) while this member was prepared behind it.
        (fnn-indeterminate "the log's barrier failed; the store needs recovery"))
      (destructuring-bind (verdict ks entry)
          (fnn-log-with-kernel (log)
            (let ((answer (fnn-core 'fn-lgc-take (fnn-log-kernel log) octets (fnn-log-reserved log)
                                    (fnn-log-count log) (fnn-log-octets log)
                                    (fnn-log-bmax log) (fnn-log-omax log) (fnn-log-unit log))))
              (when (eq (first answer) :taken)
                (setf (fnn-log-kernel log) (second answer)))
              answer))
        (declare (ignore ks))
        (case verdict
          (:taken (incf (fnn-log-count log))
                  (incf (fnn-log-octets log) entry)
                  (push (cons *fnn-staged-handle* octets) (fnn-log-members log))
                  (setq *fnn-staged-handle* nil)
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
  "books/store-log-extend.lisp fn-lg-extend-program: when the open batch's
append and one spare unit do not fit the segment (fn-lgc-extension-needed-p),
grow it to ACL2's target (fn-lgc-extension-target: whole units, past the old
extent), then one barrier.  Runs at rest (no batch in flight); the octets
before the old extent are never written, the new ones read zeros, and the
kernel is unchanged (fn-lgc-extend-program-keeps-the-relation), and the
append then fits (fn-lgc-sealed-extent-fits-the-batch).  A death at
log-extended recovers exactly the committed records
(fn-lg-extension-written-crash-reads-the-committed-records).  The append's
length is ACL2's arithmetic over the records' lengths (fn-lgc-append-len):
no octet of the batch is built here."
  (let ((ks (fnn-log-kernel log)) (unit (fnn-log-unit log)) (extent (fnn-log-extent log)))
    (when (fnn-core 'fn-lgc-extension-needed-p ks extent unit)
      (let ((next (fnn-nat (fnn-core 'fn-lgc-extension-target ks extent unit))))
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
fenced (fn-lgc-fence-failed) and the store with it."
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
          (fnn-log-with-kernel (log)
            (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence-failed (fnn-log-kernel log))))
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

(defun fnn-log-write-history (store values feed)
  "`store import' onto the record log (design 2026-09-27 storage-log section
5.3): the fresh segment of the staged STORE (profile VALUES) receives the
records FEED hands it -- FEED is called once with a function of one record,
(SEQUENCE . OCTETS), and calls it for each in increasing sequence (the import's
pass two, a chunk at a time: no list of the history is built) -- from the
genesis, through the kernel the open recovered from it and the commit
route's own steps: per record the take (fn-lgc-take at the kernel's own next
txid: the import allocates nothing; the open derives the frontier from the
records, so the archive's burned reservations stay burned) (fn-olr-take, at the bounds of a configuration naming none: fn-olr-bmax,
fn-olr-omax); a full batch, and the last, is P-BATCH's append and barrier
(fnn-log-commit-open-batch, cuts log-written and log-fenced) and is
acknowledged.  The stage is unpublished throughout: a death here leaves
ROOT.import-XXXX, never a store at ROOT (fn-bs-imp-classify)."
  (let* ((path (fnn-segment-path store))
         (log (fnn-log-recover path (fnn-log-observed-extent path) (fnn-store-log-unit)
                               (fnn-nat (fnn-core 'fn-store-profile-max-record-octets values))
                               ;; format 10: segment 1 chains from the stage's genesis
                               (fnn-genesis-open store values))))
    (setf (fnn-store-log store) log
          (fnn-log-bmax log) (fnn-nat (fnn-core 'fn-olr-bmax nil))
          (fnn-log-omax log) (fnn-nat (fnn-core 'fn-olr-omax nil))
          ;; The import writes the archive's records as they are (the
          ;; archive holds each record R); a developer image given
          ;; FN_NATIVE_IMPORT_COMPRESS_MIN_TEST=N appends them through the
          ;; compressed append at threshold N instead (tools/fixtures.py's
          ;; compressed fixtures; lane compression-extents-2).
          (fnn-log-lz-min log) (let ((n (fnn-developer-selector
                                         "FN_NATIVE_IMPORT_COMPRESS_MIN_TEST")))
                                 (if (and n (plusp (length n)) (every #'digit-char-p n)
                                          (<= (length n) 9))
                                     (parse-integer n)
                                   0)))
    (fnn-log-batch-reset log)
    (unwind-protect
         (let ((*fnn-log-batch* t))
           (funcall
            feed
            (lambda (record)
             ;; The import appends the archive's records in their order and
             ;; allocates nothing: each is taken at the kernel's own next txid
             ;; (an archived history may hold several records of one
             ;; transaction, as the per-file layout's did); the ordinary open
             ;; that admits the stage derives the frontier from the records
             ;; (fn-store-log-next-txid).
             (setf (fnn-log-reserved log) (fnn-core 'fn-lgc-next-txid (fnn-log-kernel log)))
             (fnn-log-take store (fnn-log-compress store (cdr record)))
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
  ;; The record as the log holds it: its compressed frame when the profile
  ;; compresses and ACL2 frames it (fnn-log-compress), else itself.  Before
  ;; the fence: a refused candidate takes nothing.
  (setq record (fnn-log-compress store record))
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
(fn-lgc-finish-one)."
  (fnn-log-with-kernel (log)
    (fnn-log-finish log count)
    (setf (fnn-log-pending log) (max 0 (- (fnn-log-pending log) count)))))

(defun fnn-log-batch-finish (store)
  "After the batch's barrier: every fenced member of the batch acknowledged,
and the fenced staged payloads reseated as their log extents."
  (let ((log (fnn-store-log store)))
    (fnn-log-with-kernel (log)
      (fnn-log-ack log (fnn-log-pending log)))
    (fnn-log-reseat-fenced log)))

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
            (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence-failed (fnn-log-kernel log))))
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
      ;; An OS error at the barrier's cut, after fnn-log-fence returned (a
      ;; developer image's FN_NATIVE_POST_FAULT=log-fenced:eio): uncertain
      ;; for every member, as fnn-log-commit-open-batch classifies the same
      ;; error on the inline commit -- never the fault boundary's exit 4
      ;; (lane ack-before-barrier; the wire probe's log-fenced eio row).
      (fnn-os-error (e)
        (fnn-log-with-kernel (log)
          (setf (fnn-log-kernel log) (fnn-core 'fn-lgc-fence-failed (fnn-log-kernel log))))
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
(defun fnn-command-log-scan-store (root)
  "`log scan-store ROOT': the rig's SCAN line over a format-10 store's
history as the open reads it (fnn-recover-log), every parameter the store's
own and none typed: the profile from config.json (fnn-metadata-config-decode);
the checkpoint's F row (fnn-state-checkpoint-load, fn-store-sco-log-position:
the first suffix segment K and the chain recorded for it) or, when no
checkpoint names one, segment 1 chained from journal/000000.log
(fnn-genesis-open: ACL2's fn-store-genesis-open, refused by name); ACL2's
plan over journal/ (books/store-log-segments.lisp fn-lgs-open-plan: the
segments to scan in order, or refused by name -- history-short-of-
checkpoint, checkpoint-damaged -- with the open's own words); the unit
(fn-store-log-unit) and the record bound (fn-store-profile-max-record-octets;
the entry header's length field is read against it).  The closed segments
are streamed with the chain carried to the next (fnn-log-stream-segment,
T8's step); the line is the active segment's, its records= the history's
count as the open answers it: the checkpoint's S plus every record scanned.
Read only, no lock, nothing renamed (an interrupted rotation's spare is the
owner's to complete): the durable prefix a crash would keep, while an owner
may run (tests/native_log_observation.py).  Before lane operability-4 this
verb took segment 1 and the genesis chain unconditionally, so a store after
`store compact' (whose covered segments are dropped) answered a host `no log
segment' (tests/test_native_topic_local.py)."
  (let* ((store (make-fnn-store root))
         (raw (fnn-read-regular-bounded (fnn-config-path store) 16384))
         (profile (fnn-metadata-config-decode raw))
         (chain (progn (setf (fnn-store-config store) profile)
                       (fnn-genesis-open store profile)))
         (unit (fnn-store-log-unit))
         (max (fnn-store-log-max store)))
    (multiple-value-bind (status s) (fnn-state-checkpoint-load store)
      (let* ((position (and (eq status :ok) (fnn-core-state 'fn-store-sco-log-position)))
             (log-position (first position))
             (plan (fnn-core 'fn-lgs-open-plan (fnn-log-segment-names store)
                             (first log-position))))
        (unless (and (consp plan) (member (first plan) '(:scan :refused)))
          (fnn-fault "ACL2 returned a malformed log open plan"))
        (when (equal plan '(:refused :no-segment))
          (fnn-fault "missing store directory: ~a has no log segment (an init that did not finish: run init again)"
                     (fnn-journal-dir store)))
        (when (eq (first plan) :refused)
          (error 'fnn-store-open-refusal
                 :message (format nil "open refused reason=~(~a~): the log's segments do not hold the history~@[ from segment ~d~]"
                                  (second plan) (first log-position))))
        (let ((genesis (if log-position (second log-position) chain))
              (base (if (eq status :ok) (fnn-nat s) 0)))
          (loop for (k . more) on (second plan) do
            (let* ((path (fnn-segment-path-at store k))
                   (extent (fnn-log-observed-extent path))
                   (fd (fnn-log-open-segment path extent unit t)))
              (unwind-protect
                   (if more
                       (let ((read (fnn-log-stream-segment fd extent unit max genesis #'identity
                                                           (file-namestring path))))
                         (setq genesis (fnn-core 'fn-lgc-last read)
                               base (+ base (fnn-nat (fnn-core 'fn-lgc-count read)))))
                     (fnn-log-rig-line "SCAN"
                                       (%make-fnn-log :path path :fd fd :unit unit :max max
                                                      :extent extent :genesis genesis :index k
                                                      :kernel (nth-value 1 (fnn-log-open-kernel
                                                                            fd extent unit max genesis)))
                                       0 base))
                (fnn-close fd))))))))
  +fnn-exit-ok+)

(defun fnn-command-log (command argv)
  (when (string= command "scan-store")
    (unless (= (length argv) 1)
      (error 'fnn-usage-error :message "log scan-store ROOT"))
    (return-from fnn-command-log (fnn-command-log-scan-store (first argv))))
  (unless (member command '("scan" "recover" "append") :test #'equal)
    (error 'fnn-usage-error :message "log scan|recover|append SEGMENT EXTENT UNIT MAX SIZE [BATCHES PER] | log scan-store ROOT"))
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
                                                  :kernel (nth-value 1 (fnn-log-open-kernel
                                                                        fd extent unit max)))
                            size)
           (fnn-close fd))))
      (t
       (let ((log (fnn-log-recover path extent unit max)))
         (unwind-protect
              (progn
                (fnn-log-rig-line "RECOVERED" log size)
                (when (string= command "append")
                  (fnn-log-rig-handshake)
                  (let ((batches (fnn-log-nat-arg (sixth argv) "BATCHES"))
                        (per (fnn-log-nat-arg (seventh argv) "PER")))
                    (dotimes (b batches)
                      (dotimes (i per)
                        (fnn-log-prepare
                         log (fnn-core 'fn-lg-workload-record
                                       (fnn-core 'fn-lgc-next-txid (fnn-log-kernel log)) size)))
                      (fnn-log-append log)
                      (fnn-log-fence log)
                      (fnn-log-finish log per)
                      (fnn-log-rig-line (format nil "ACK batch=~d" (1+ b)) log size)
                      (fnn-log-rig-handshake)))))
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
      ;; `fn VERSION (REV12)': the release version built into the image and
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
                 ((string= command "recover") (fnn-command-recover root rest))
                 ((string= command "node-secret") (need 4) (fnn-command-node-secret root rest))
                 ((string= command "status")
                  ;; Row S3: the operator verb's decision, for the store verb
                  ;; (books/owner-maintenance-request.lisp
                  ;; fn-omr-store-status-word): the checkpoint header, or the
                  ;; report over the replayed log with `--replay'.
                  (case (fnn-core 'fn-omr-store-status-word rest)
                    (:replay (fnn-command-status root t))
                    (:header (fnn-command-status root))
                    (t (error 'fnn-usage-error :message "store ROOT status [--replay]"))))
                 ((string= command "checkpoint") (fnn-command-state-checkpoint root))
                 ((string= command "digest") (fnn-command-store-digest root))
                 ((string= command "journal") (fnn-command-store-journal root))
                 ((string= command "export") (need 4) (fnn-command-store-export root (first rest)))
                 ((string= command "bless-snapshot")
                  ;; The direct store entry reuses the operator's grammar.
                  ;; ROOT is the CLI context, never the copy that is opened.
                  (let ((plan (fnn-core 'fn-nop-parse-store (cons command rest) nil)))
                    (if (eq (fnn-core 'fn-native-operator-host-result-status plan) :accepted)
                        (fnn-command-store-bless-snapshot
                         (fnn-octets-string
                          (fnn-core 'fn-native-operator-host-result-archive-path-octets plan)))
                      (progn
                        (fnn-operator-emit-result plan)
                        (fnn-core 'fn-native-operator-host-result-exit-code plan)))))
                 ((string= command "import") (need 4) (fnn-command-store-import root (first rest) nil))
                 ((string= command "retention") (fnn-command-retention root))
                 ((string= command "compression") (fnn-command-compression root))
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
                 ((string= command "provenance") (need 4) (fnn-command-provenance root (first rest)))
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
         (fnn-core 'fn-b3-left-chunks 42 -1)
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
        ((string= verb "blake3")
         (need 2)
         ;; The file reaches ACL2 in the octet buffer, read in place by
         ;; `fn-blake3-of-prefixed-buffer-any' (books/frame-digest-buffer.lisp):
         ;; no octet list.
         (fnn-out "~a" (fnn-hex (fnn-as-octets
                                 (fnn-core 'fn-blake3-of-prefixed-buffer-any nil
                                           (fnn-octets-fill
                                            (fnn-read-regular-bounded (second args) (ash 1 26)))))))
         (fnn-octets-clear)
         +fnn-exit-ok+)
        (t (error 'fnn-usage-error :message (format nil "unknown verb ~a" verb)))))))

;;; The collection trigger for every entry of the image, the operator verbs
;;; included: the owner once set it in fnn-owner-run alone, so `store checkpoint', `recover' and the
;;; other offline verbs replayed a history under SBCL's default of 5% of the
;;; dynamic space (1.6 GB at the launcher's 32 GB) and let that much garbage
;;; pile up between collections (rep-wave-d baseline, section 1.2).  It bounds
;;; dead memory, never data, and decides nothing ACL2 decides.
(defparameter +fnn-gc-nursery-octets+ (* (fn-profile-limit :gc-nursery-mib) 1024 1024)) ; books/profile-limits.lisp

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

;;; The trigger while a store opens (lane f1-bisect, F1).  The open allocates
;;; in proportion to the history it reads, so at the figure's trigger its
;;; garbage piles up to the whole trigger (48.75 MiB at the small profile's
;;; 780 MB) before the first collection, whatever the store's size.  ACL2
;;; sizes it to the history on disk (books/heap-open-nursery.lisp
;;; fn-heap-open-nursery-trigger: at most 4 x the history, at least 8 MiB,
;;; never more than the figure's trigger; KEYSTONE
;;; fn-heap-open-nursery-trigger-bounds).  The history is the launcher's own
;;; observation (host/native/heap.lisp fnn-heap-history-octets: the log's
;;; segments, checkpoints/ and the state checkpoint), NIL when it cannot be
;;; read (the figure's trigger).  The owner sets the service trigger when the
;;; open is done (fnn-owner-service-nursery).
(defun fnn-open-nursery (store)
  (let ((profile (fnn-store-config store)))
    (setf (sb-ext:bytes-consed-between-gcs)
          (fnn-core 'fn-heap-open-nursery-trigger (sb-ext:dynamic-space-size)
                    +fnn-gc-nursery-octets+
                    (and profile
                         (fnn-heap-history-octets (fnn-store-root store) profile))))))

;;; `fn redeem HOST[:PORT] CODE LOGIN [--tls] [--cafile PEM]': a friend
;;; redeems an invitation code (the stranger rehearsal's stop 10).  The host
;;; dials and runs TLS; ACL2 decides each next step from the reply code
;;; (books/peer-host.lisp fn-redeem-step), which name and trust the TLS
;;; check uses (fn-peer-tls-verification: the typed HOST, SNI for a DNS name
;;; only, the PEM file given or the system roots), and every line printed
;;; (fn-redeem-text).  The password is read from the terminal without echo,
;;; else from standard input; it never enters argv.  A connection that ends
;;; or never opens is ACL2's fn-redeem-lost at the stage it ended in, and the
;;; exit code is fn-outcome-code of fn-redeem-outcome-class: uncertain, never
;;; refused (the OpenBSD rehearsal's finding 8: the web reader counted an
;;; unreachable node as a refused code).
(defun fnn-redeem-read-line (read-chunk pending)
  "One reply line (without CRLF) and the octets after it, reading chunks with
READ-CHUNK until an LF; at most 4096 octets (RFC 3977 s3.1: 512 is the
largest reply line).  :LOST when the server closed or did not answer."
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
          (return (values :lost buffer)))
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
           ;; The prompt only to a terminal: a caller feeding standard
           ;; input (the web reader) reads fn's last line as its answer.
           (when tty
             (format *error-output* "Password for the new account: ")
             (finish-output *error-output*))
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
             (last nil) (stage :connect))
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
                              (fnn-octets (fnn-core 'fn-redeem-text outcome login last))))
                       (class (fnn-core 'fn-redeem-outcome-class outcome)))
                   (if (eq class :accepted)
                       (fnn-out "~a" text)
                     (fnn-err "~a" text))
                   (fnn-core 'fn-outcome-code class))))
          (unwind-protect
               (handler-case
               (progn
                 (setq socket (fnn-connect host port :timeout 30))
                 (setq stage (if tls :greeting-tls :greeting-starttls))
                 (progn
                   (when tls
                     (setq context (fnn-tls-open-client-context (fourth verification))
                           channel (fnn-tls-connect context (fnn-socket-fd socket)
                                                    (second verification) 30
                                                    :sni (third verification))))
                   (loop
                     (let* ((line (reply))
                            (step (if (eq line :lost)
                                      (fnn-core 'fn-redeem-lost stage)
                                    (fnn-core 'fn-redeem-step stage line))))
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
                         ((:uncertain :unreachable) (return (finish step)))
                         (t (ignore-errors (send "QUIT"))
                            (return (finish step))))))))
                 ;; The node could not be reached, or the connection failed
                 ;; under the exchange: ACL2's lost outcome at this stage.
                 ((or fnn-os-error fnn-tls-io-error
                      sb-bsd-sockets:socket-error sb-bsd-sockets:name-service-error) ()
                   (finish (fnn-core 'fn-redeem-lost stage)))
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
  (setq *fnn-process-started* (get-internal-real-time))
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
                 ;; D40: a developer image may keep the counterpart path.
                 (setq *fnn-dispatch-counterpart*
                       (equal (fnn-developer-selector "FN_NATIVE_DISPATCH_COUNTERPART") "1"))
                 (when *fnn-dispatch-counterpart*
                   (fnn-err "fn-dispatch: counterpart for ~d raw-dispatched entries (FN_NATIVE_DISPATCH_COUNTERPART)"
                            (hash-table-count *fnn-raw-dispatch*)))
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
