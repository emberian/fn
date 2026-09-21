;;; host/native/io.lisp -- the fn native host's raw-Lisp I/O adapter.
;;;
;;; TRUST BOUNDARY.  Every form in this file is raw Common Lisp, loaded into
;;; the ACL2 world under the trust tag :fn-native-host by host/native/build.lisp
;;; (progn! (set-raw-mode t) (load "host/native/io.lisp")).  Nothing here is
;;; proved.  This file is the whole raw surface of the native host: SBCL's
;;; sb-posix, sb-unix, sb-alien and sb-bsd-sockets contribs, the diagnostic
;;; SHA-256 CLI below, and the socket loop.  specs/host.md lists the surface
;;; function by function.
;;;
;;; Calls into the certified core go through `fnn-call`, which applies the
;;; executable counterpart (the ACL2_*1*_ACL2 function) of the named host
;;; wrapper.  That is the raw-Lisp spelling of `ec-call`: the same evaluation
;;; the interpreted bridge performs when Python types the form at the ACL2
;;; prompt, under the same `guard-checking-on` policy.  No book function is
;;; called by its raw symbol, so no unverified guard is bypassed here; the
;;; wrappers it reaches are the `:program` functions in host/*-host.lisp that
;;; tools/run_store.py and tools/run_reader.py drive today.
;;;
;;; SOCKET SURFACE.  host/native/tcpcl.lisp (the DTN wave, planning/lanes/
;;; HANDOFF-w4-tcpcl.md "Proposed host surface") builds its convergence layer
;;; on exactly these entry points and opens no socket and makes no syscall of
;;; its own:
;;;
;;;   (fnn-listen port &key family backlog) -> (values socket bound-port)
;;;   (fnn-connect host port &key family)   -> socket, an active open
;;;   (fnn-accept-loop listener handler once) -> one handler call per client
;;;   (fnn-socket-fd socket)                -> the descriptor the three below take
;;;   (fnn-socket-shut socket)              -> close, errors swallowed
;;;   (fnn-recv fd seconds)                 -> octets, an empty vector at end
;;;                                            of input, or :timeout; at most
;;;                                            +fnn-max-read+ octets per call
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
(define-condition fnn-store-indeterminate (fnn-store-error) ())
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
;;; SHA-256 (FIPS 180-4).  A-CRYPTO: the host supplies digest octets and the
;;; constrained `fn-frame-digest` consumers in books/frame decide everything
;;; else.  tools/fn_native.py `sha256-selftest` checks this against hashlib.

(deftype fnn-u32 () '(unsigned-byte 32))

(declaim (type (simple-array fnn-u32 (64)) +fnn-sha256-k+))
(defparameter +fnn-sha256-k+
  (make-array
   64 :element-type 'fnn-u32 :initial-contents
   '(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5 #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
     #xd807aa98 #x12835b01 #x243185be #x550c7dc3 #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
     #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
     #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7 #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
     #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13 #x650a7354 #x766a0abb #x81c2c92e #x92722c85
     #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3 #xd192e819 #xd6990624 #xf40e3585 #x106aa070
     #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5 #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
     #x748f82ee #x78a5636f #x84c87814 #x8cc70208 #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2)))

(declaim (inline fnn-rotr))
(defun fnn-rotr (x n)
  (declare (type fnn-u32 x) (type (integer 1 31) n))
  (logior (ash x (- n)) (logand #xffffffff (ash x (- 32 n)))))
(defmacro fnn-add32 (&rest xs)
  `(logand #xffffffff (+ ,@xs)))

(defun fnn-sha256 (input)
  "SHA-256 of INPUT (any octet sequence) as a fresh 32-octet vector."
  (let* ((data (fnn-octets input))
         (len (length data))
         (rest (mod (+ len 1) 64))
         (pad (if (<= rest 56) (- 56 rest) (- 120 rest)))
         (total (+ len 1 pad 8))
         (msg (fnn-make-octets total))
         (h (make-array 8 :element-type 'fnn-u32
                          :initial-contents '(#x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a
                                              #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19)))
         (w (make-array 64 :element-type 'fnn-u32 :initial-element 0)))
    (declare (type fnn-octets data msg) (type (simple-array fnn-u32 (8)) h)
             (type (simple-array fnn-u32 (64)) w))
    (replace msg data)
    (setf (aref msg len) #x80)
    (let ((bits (* 8 len)))
      (dotimes (i 8)
        (setf (aref msg (- total 1 i)) (ldb (byte 8 (* 8 i)) bits))))
    (loop for chunk from 0 below total by 64 do
      (dotimes (i 16)
        (let ((p (+ chunk (* 4 i))))
          (setf (aref w i) (logior (ash (aref msg p) 24) (ash (aref msg (+ p 1)) 16)
                                   (ash (aref msg (+ p 2)) 8) (aref msg (+ p 3))))))
      (loop for i from 16 below 64 do
        (let* ((w15 (aref w (- i 15))) (w2 (aref w (- i 2)))
               (s0 (logxor (fnn-rotr w15 7) (fnn-rotr w15 18) (ash w15 -3)))
               (s1 (logxor (fnn-rotr w2 17) (fnn-rotr w2 19) (ash w2 -10))))
          (setf (aref w i) (fnn-add32 (aref w (- i 16)) s0 (aref w (- i 7)) s1))))
      (let ((a (aref h 0)) (b (aref h 1)) (c (aref h 2)) (d (aref h 3))
            (e (aref h 4)) (f (aref h 5)) (g (aref h 6)) (hh (aref h 7)))
        (declare (type fnn-u32 a b c d e f g hh))
        (dotimes (i 64)
          (let* ((s1 (logxor (fnn-rotr e 6) (fnn-rotr e 11) (fnn-rotr e 25)))
                 (ch (logxor (logand e f) (logand (logxor e #xffffffff) g)))
                 (t1 (fnn-add32 hh s1 ch (aref +fnn-sha256-k+ i) (aref w i)))
                 (s0 (logxor (fnn-rotr a 2) (fnn-rotr a 13) (fnn-rotr a 22)))
                 (maj (logxor (logand a b) (logand a c) (logand b c)))
                 (t2 (fnn-add32 s0 maj)))
            (setf hh g g f f e e (fnn-add32 d t1) d c c b b a a (fnn-add32 t1 t2))))
        (setf (aref h 0) (fnn-add32 (aref h 0) a) (aref h 1) (fnn-add32 (aref h 1) b)
              (aref h 2) (fnn-add32 (aref h 2) c) (aref h 3) (fnn-add32 (aref h 3) d)
              (aref h 4) (fnn-add32 (aref h 4) e) (aref h 5) (fnn-add32 (aref h 5) f)
              (aref h 6) (fnn-add32 (aref h 6) g) (aref h 7) (fnn-add32 (aref h 7) hh))))
    (let ((out (fnn-make-octets 32)))
      (dotimes (i 8)
        (dotimes (j 4)
          (setf (aref out (+ (* 4 i) j)) (ldb (byte 8 (* 8 (- 3 j))) (aref h i)))))
      out)))

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

(defun fnn-write-all (fd octets)
  (let ((data (fnn-octets octets)) (offset 0))
    (loop while (< offset (length data)) do
      (multiple-value-bind (count errno)
          (sb-unix:unix-write fd data offset (- (length data) offset))
        (when (null count) (fnn-os-fail errno))
        (when (<= count 0) (fnn-fault "short store write"))
        (incf offset count)))))

(defun fnn-read-fd (fd buffer)
  "Read into BUFFER; the octet count, 0 at end of file."
  (multiple-value-bind (count errno)
      (sb-sys:with-pinned-objects (buffer)
        (sb-unix:unix-read fd (sb-sys:vector-sap buffer) (length buffer)))
    (when (null count) (fnn-os-fail errno))
    count))

(defun fnn-read-regular-bounded (path maximum)
  "Read one regular, non-symlink file through a no-follow descriptor."
  (let ((fd (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))))
    (unwind-protect
         (let ((info (fnn-fstat fd)))
           (unless (fnn-regular-p info)
             (fnn-fault "refusing non-regular store file: ~a" path))
           (when (> (sb-posix:stat-size info) maximum)
             (fnn-fault "store file exceeds bound: ~a" path))
           (let ((chunks nil) (remaining (+ maximum 1)) (total 0))
             (loop while (> remaining 0) do
               (let* ((buffer (fnn-make-octets (min 65536 remaining)))
                      (count (fnn-read-fd fd buffer)))
                 (when (zerop count) (return))
                 (push (subseq buffer 0 count) chunks)
                 (incf total count)
                 (decf remaining count)))
             (when (> total maximum)
               (fnn-fault "store file exceeds bound: ~a" path))
             (let ((data (fnn-make-octets total)) (at 0))
               (dolist (chunk (nreverse chunks))
                 (replace data chunk :start1 at)
                 (incf at (length chunk)))
               data)))
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

(defun fnn-link (old new) (fnn-posix (new) (sb-posix:link old new)))
(defun fnn-replace (old new) (fnn-posix (new) (sb-posix:rename old new)))
(defun fnn-unlink (path) (fnn-posix (path) (sb-posix:unlink path)))
(defun fnn-mkdir (path mode) (fnn-posix (path) (sb-posix:mkdir path mode)))

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
  "Apply NAME's executable counterpart to ARGS; a refusal is fnn-store-error."
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
      (:thrown (fnn-refuse "ACL2 error in ~(~a~): ~a" name
                           (handler-case (princ-to-string values) (error () "guard violation"))))
      (t (fnn-refuse "ACL2 error in ~(~a~): ~a" name outcome)))))

(defun fnn-core (name &rest args)
  "A state-free wrapper's single value."
  (first (apply #'fnn-call name args)))

(defun fnn-core-state (name &rest args)
  "A `state`-returning wrapper's value; its error flag is a refusal."
  (destructuring-bind (erp val &rest ignored)
      (apply #'fnn-call name (append args (list *the-live-state*)))
    (declare (ignore ignored))
    (when erp (fnn-refuse "ACL2 error in ~(~a~)" name))
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
    (fnn-refuse "unexpected ACL2 action: ~s" value))
  value)

(defun fnn-nat (value)
  (unless (and (integerp value) (>= value 0))
    (fnn-refuse "ACL2 returned a non-natural"))
  value)

(defun fnn-as-octets (value)
  (unless (fnn-octet-list-p value)
    (fnn-refuse "ACL2 returned a non-octet list"))
  (fnn-octets value))

;;; Durable metadata is one certified interface.  These functions deliberately
;;; mirror tools/frame_bridge.py's wrappers: the raw host neither frames nor
;;; parses a field, and it does not restate the frontier domain or successor.

(defun fnn-metadata-config-frame (profile)
  (let ((value (fnn-core 'fn-store-metadata-config-frame profile)))
    (when (or (null value) (not (fnn-octet-list-p value)))
      (fnn-refuse "ACL2 refused metadata profile"))
    (fnn-octets value)))

(defun fnn-metadata-config-decode (octets)
  (let ((value (fnn-core 'fn-store-metadata-config-decode
                         (fnn-octet-list octets))))
    (unless (and (listp value) (= (length value) 6)
                 (fnn-octet-list-p (first value))
                 (every (lambda (n) (and (integerp n) (>= n 0)))
                        (subseq value 1 5))
                 (fnn-octet-list-p (nth 5 value)))
      (fnn-fault "ACL2 rejected durable configuration frame"))
    value))

(defun fnn-metadata-frontier-frame (frontier)
  (let ((value (fnn-core 'fn-store-metadata-frontier-frame frontier)))
    (when (or (null value) (not (fnn-octet-list-p value)))
      (fnn-fault "ACL2 refused allocation frontier"))
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

The core replays `config-records' first (`fn-cnode-config-replay'), takes the
allocation domain and the capacity from the configured node, and only then
opens the observed store; a store with no configuration record never reaches
here.  The host supplies octets and decides nothing about them."
  (fnn-action (fnn-core-state 'fn-store-sn-recover
                              (mapcar #'fnn-octet-list records) frontier
                              (mapcar #'fnn-octet-list config-records))))
(defun fnn-bridge-io (operation result)
  (fnn-action (fnn-core-state 'fn-store-sn-io operation result)))
(defun fnn-bridge-prepare (msgid payload codes obligation subject evidence charge)
  (fnn-action (fnn-core-state 'fn-store-sn-prepare (fnn-octet-list msgid) (fnn-octet-list payload)
                              codes (fnn-octet-list obligation) (fnn-octet-list subject)
                              (fnn-octet-list evidence) charge)))
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

(defun fnn-bridge-config-names (wrapper)
  "A replayed name table: the core joins the names with LF, which no group
name contains (`fn-store-cfg-join-names', host/store-node-host.lisp)."
  (let ((octets (fnn-core-state wrapper)))
    (unless (fnn-octet-list-p octets) (fnn-refuse "ACL2 returned a non-octet list"))
    (let ((names nil) (current nil))
      (dolist (octet octets)
        (if (= octet 10)
            (progn (push (fnn-octets-string (fnn-octets (nreverse current))) names)
                   (setq current nil))
            (push octet current)))
      (when current (push (fnn-octets-string (fnn-octets (nreverse current))) names))
      (nreverse names))))

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
          (t (fnn-refuse "ACL2 returned a non-boolean")))))

;;; The frame session: tools/frame_bridge.py, with SHA-256 from above.

(defvar *fnn-constants* nil)

(defun fnn-constants ()
  (or *fnn-constants*
      (let ((values (fnn-core 'fn-store-frame-constants))
            (names '(:header :trailer :overhead :max-store :max-workflow :max-receipt
                     :max-inbound :max-text :max-blob :max-identity)))
        (unless (and (listp values) (= (length values) (length names))
                     (every #'integerp values))
          (fnn-refuse "ACL2 returned an unexpected constant vector"))
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
`fnn-sha256' stays only for the diagnostic `sha256' CLI verb."
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

(defun fnn-post-boundary (msgid payload-length group-count charge)
  (let ((value (fnn-core 'fn-store-post-boundary (fnn-octet-list msgid) payload-length
                         group-count charge)))
    (unless (keywordp value) (fnn-refuse "ACL2 returned an unexpected boundary verdict"))
    value))

(defun fnn-charge (length)
  (let ((value (fnn-core 'fn-store-charge length)))
    (unless (and (integerp value) (> value 0)) (fnn-refuse "ACL2 returned a non-positive charge"))
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

(defconstant +fnn-max-staging-report+ 64)
(defconstant +fnn-config-record-bytes+ 65538)
;; tools/run_store.py's `init --group` default, an operator default and not a
;; group table: what a store serves is what the core admits and replays.
(defparameter +fnn-default-groups+ (list "fn.letters" "fn.test"))

(defun fnn-seq-name-p (name)
  (and (= (length name) 24)
       (every (lambda (c) (char<= #\0 c #\9)) (subseq name 0 20))
       (string= (subseq name 20) ".txn")))

(defstruct (fnn-store (:constructor %make-fnn-store))
  root writable lock-fd config frontier fenced (orphans nil) (completion-pending nil)
  ;; The replayed configuration the core hands back at recover.  The host
  ;; stores it and passes it back; it derives no name, code or generation.
  (config-generation nil) (config-served nil) (config-domain nil)
  ;; The one scripted fault point, or NIL: tools/run_store.py's ScriptedFaults.
  (fault-point nil) (fault-class nil) (fault-message nil))

(defun fnn-config-capacity (store) (second (fnn-store-config store)))
(defun fnn-config-max-payload (store) (third (fnn-store-config store)))
(defun fnn-config-max-recovery (store) (fourth (fnn-store-config store)))
(defun fnn-config-max-transactions (store) (nth 4 (fnn-store-config store)))

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
          ;; FN_NATIVE_INIT_FAULT is a developer-test seam.  SIGKILL is
          ;; deliberate: unlike an exception it cannot run unwind-protect
          ;; cleanup, so the next command tests an actual new process.
          ((eq (fnn-store-fault-class store) :fnn-test-kill)
           (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
           (fnn-fault "test SIGKILL did not terminate the process"))
          (t
           (error (fnn-store-fault-class store) :message (fnn-store-fault-message store))))))

(defun fnn-config-path (s) (fnn-join (fnn-store-root s) "config.json"))
(defun fnn-transactions (s) (fnn-join (fnn-store-root s) "transactions"))
(defun fnn-staging (s) (fnn-join (fnn-store-root s) "staging"))
(defun fnn-lock-path (s) (fnn-join (fnn-store-root s) "writer.lock"))
(defun fnn-frontier-path (s) (fnn-join (fnn-store-root s) "allocation-frontier.json"))
(defun fnn-config-dir (s) (fnn-join (fnn-store-root s) "config"))
(defun fnn-config-record-path (s generation)
  (fnn-join (fnn-config-dir s) (format nil "~8,'0d.cfg" generation)))

(defun fnn-config-record-names (store &optional test-fault-point)
  "The durable configuration records in generation order; NIL when absent.

Enumeration failure is not absence.  In particular, initialization must not
turn an unreadable config directory into a generation-one publication or skip
its final record-file barrier.  TEST-FAULT-POINT is the native fidelity test's
pre-enumeration control; normal callers pass NIL."
  (when test-fault-point (fnn-at store test-fault-point))
  (sort (remove-if-not (lambda (name)
                         (let ((n (length name)))
                           (and (> n 4) (string= ".cfg" (subseq name (- n 4))))))
                       (fnn-list-directory (fnn-config-dir store)))
        #'string<))

(defun fnn-config-records (store)
  "The durable configuration record history, oldest first.

A store with no configuration record is a refused store -- a distinct outcome
from an uncertain persistence observation, and never a compiled-in default.
The core decides whether the records replay."
  (let ((names (fnn-config-record-names store)))
    (when (null names)
      (fnn-fault "refusing store with no durable configuration record"))
    (mapcar (lambda (name)
              (let ((path (fnn-join (fnn-config-dir store) name)))
                (fnn-check-regular path)
                (fnn-read-regular-bounded path +fnn-config-record-bytes+)))
            names)))

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
  "Stage, barrier, link and barrier one initialization metadata file."
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
         (progn
           (handler-case (fnn-link stage final)
             (fnn-os-error (e)
               (if (= (fnn-os-errno e) sb-posix:eexist)
                   (return-from fnn-publish-initial-file nil)
                   (error e))))
           (when initializer-prefix (fnn-init-cut store (fnn-concat initializer-prefix "linked")))
           (fnn-fsync-dir (fnn-store-root store))
           (when initializer-prefix (fnn-init-cut store (fnn-concat initializer-prefix "root-fenced")))
           t)
      (ignore-errors (fnn-unlink stage))
      ;; Keep the real best-effort unlink policy above.  The test seam is
      ;; deliberately outside that handler so its selected outcome is visible.
      (when initializer-prefix (fnn-init-cut store (fnn-concat initializer-prefix "stage-unlinked"))))))

(defun fnn-transaction-files (store)
  "Sorted (sequence . path) pairs of the final namespace, gap-free or a fault."
  (let ((files nil)
        (names (handler-case (fnn-list-directory (fnn-transactions store))
                 (fnn-os-error () (fnn-fault "cannot enumerate transactions")))))
    (dolist (name names)
      (when (>= (length files) (fnn-config-max-transactions store))
        (fnn-fault "transaction count exceeds configured bound"))
      (unless (fnn-seq-name-p name)
        (fnn-fault "unexpected final-namespace entry: ~a" name))
      (let* ((path (fnn-join (fnn-transactions store) name))
             (st (fnn-lstat path)))
        (when (or (null st) (fnn-symlink-p st) (not (fnn-regular-p st)))
          (fnn-fault "refusing transaction symlink or non-file"))
        (push (cons (parse-integer name :end 20) path) files)))
    (setq files (sort files #'< :key #'car))
    (loop for (sequence . nil) in files for expected from 0 do
      (unless (= sequence expected) (fnn-fault "transaction sequence gap")))
    files))

(defun fnn-staging-orphans (store)
  (let ((names (handler-case (fnn-list-directory (fnn-staging store))
                 (fnn-os-error () (fnn-fault "cannot enumerate staging"))))
        (report nil))
    (dolist (name names)
      (when (>= (length report) +fnn-max-staging-report+)
        (push "..." report)
        (return))
      (push name report))
    (sort report #'string<)))

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

(defun fnn-initialize (store &optional (groups +fnn-default-groups+) (profile :development))
  ;; One durable configuration record at generation 1, built and admitted by
  ;; the core from the operator's group names.
  (fnn-safe-directory (fnn-store-root store) t store
                      "init-root-mkdir" "init-root-parent-fenced")
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
             (if (fnn-publish-initial-file store (fnn-config-path store) config "init-config-")
                 (setf (fnn-store-config store) (fnn-metadata-config-decode config))
                 (fnn-load-config store)))
           (when (null (fnn-config-record-names store :init-config-records-first-enumerate))
             (fnn-publish-initial-file store (fnn-config-record-path store 1)
                                       (fnn-bridge-config-initial groups) "init-history-")
             (fnn-fsync-dir (fnn-config-dir store))
             (fnn-init-cut store "init-config-history-fenced"))
           ;; A missing allocator alongside committed history would permit
           ;; reuse of an aborted ID.  It is a fault, never an implicit 0.
           (when (and (null (fnn-check-regular (fnn-frontier-path store)))
                      (fnn-transaction-files store))
             (fnn-fault "refusing missing allocator frontier with committed history"))
           (if (fnn-publish-initial-file store (fnn-frontier-path store)
                                         (fnn-metadata-frontier-frame 0) "init-frontier-")
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

(defun fnn-durable-records (store)
  (let ((records nil) (aggregate 0)
        (bound (+ (fnn-constant :overhead) (fnn-constant :max-store))))
    (loop for (sequence . path) in (fnn-transaction-files store) do
      (fnn-check-regular path)
      (let ((record (fnn-unframe (fnn-read-regular-bounded path bound))))
        (incf aggregate (length record))
        (when (> aggregate (fnn-config-max-recovery store))
          (fnn-fault "transaction recovery input exceeds configured bound"))
        (unless (= (fnn-bridge-record-sequence record) sequence)
          (fnn-fault "record sequence does not match immutable filename"))
        (push record records)))
    (nreverse records)))

(defun fnn-observe (store operation &optional (result :ok))
  "Submit one already-observed filesystem result and keep failure fenced."
  (handler-case (funcall *fnn-observe-callback* operation result)
    ((or fnn-store-error fnn-os-error) ()
      (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil)
      (fnn-indeterminate "ACL2 could not record ~(~a~) observation" operation))))

(defun fnn-recover (store)
  (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil)
  (let ((records nil))
    (handler-case
        (progn
          (fnn-load-frontier store)
          (let ((config-records (fnn-config-records store)))
            (setq records (fnn-durable-records store))
            (setf (fnn-store-orphans store) (fnn-staging-orphans store))
            (unless (eq (fnn-bridge-recover records (fnn-store-frontier store) config-records)
                        :recovering)
              (fnn-fault "ACL2 replay rejected committed transaction history or configuration history")))
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
          (dolist (barrier (list (lambda () (fnn-fsync-regular (fnn-config-path store)))
                                 (lambda () (fnn-fsync-regular (fnn-frontier-path store)))
                                 (lambda () (fnn-fsync-dir (fnn-transactions store)))
                                 (lambda () (fnn-fsync-dir (fnn-store-root store)))
                                 (lambda () (fnn-fsync-dir (fnn-parent (fnn-store-root store))))))
            (handler-case (funcall barrier)
              (fnn-os-error (e)
                (fnn-observe store :recovery-barrier :uncertain)
                (error e)))
            (setq phase (fnn-observe store :recovery-barrier :ok))
            (unless (member phase '(:recovering :ready))
              (fnn-fault "ACL2 rejected recovered barrier ordering"))
            (fnn-at store :recover-barrier))
          (unless (eq phase :ready)
            (fnn-fault "ACL2 did not complete all recovery barriers")))
      (fnn-os-error ()
        (setf (fnn-store-fenced store) t)
        (fnn-indeterminate "cannot establish recovered namespace frontier")))
    (setf (fnn-store-fenced store) nil)
    records))

(defun fnn-require-writer (store)
  (unless (and (fnn-store-writable store) (fnn-store-lock-fd store))
    (fnn-refuse "mutation requires a live exclusive store owner")))

(defun fnn-write-staged (stage contents)
  (let ((fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (unwind-protect (progn (fnn-write-all fd contents) (fnn-fsync-file fd))
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
          (fnn-write-staged stage contents)
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
        (fnn-refuse "known pre-publication allocator failure: ~a" e)))))

(defun fnn-publish (store sequence record)
  (fnn-require-writer store)
  (when (fnn-store-fenced store) (fnn-indeterminate "store is fenced pending recovery"))
  (let* ((final (fnn-join (fnn-transactions store) (fnn-transaction-name sequence)))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".stage-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (data (fnn-frame record))
         (attempted nil))
    (handler-case
        (progn
          (fnn-write-staged stage data)
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
                               (fnn-fsync-dir (fnn-transactions store)))
            (fnn-os-error (e) (fnn-observe store :record-directory :error) (error e)))
          (fnn-at store :record-durable)
          (unless (eq (fnn-observe store :record-directory :ok) :completing)
            (fnn-indeterminate "ACL2 rejected record directory barrier after publication"))
          (setf (fnn-store-completion-pending store) t)
          (fnn-at store :record-completing)
          (ignore-errors (fnn-unlink stage) (fnn-fsync-dir (fnn-staging store)))
          (fnn-at store :record-staging-cleaned)
          :durable)
      (fnn-os-error (e)
        (when attempted
          (setf (fnn-store-fenced store) t)
          (fnn-indeterminate "transaction publication outcome is indeterminate"))
        (fnn-refuse "known pre-publication store failure: ~a" e)))))

(defun fnn-finish (store)
  "Open the writer gate only after exact fn-sn durable completion."
  (fnn-require-writer store)
  (unless (and (fnn-store-fenced store) (fnn-store-completion-pending store))
    (fnn-indeterminate "durable completion was not pending"))
  (setf (fnn-store-completion-pending store) nil)
  (fnn-at store :finish-consumed)
  (let ((completion (handler-case (funcall *fnn-finish-callback*)
                      ((or fnn-store-error fnn-os-error) ()
                        (setf (fnn-store-fenced store) t)
                        (fnn-indeterminate "ACL2 completion failed after publication")))))
    (unless (eq completion :durable)
      (setf (fnn-store-fenced store) t)
      (fnn-indeterminate "ACL2 rejected durable completion after publication"))
    (setf (fnn-store-fenced store) nil)
    (fnn-at store :finish-durable)
    completion))

(defun fnn-identity-text (identity)
  "The one rendering of a canonical identity where a string is forced: a
store record metadata field, a journal record and an NNTP header all carry
text, and ACL2 decides what that text is.  A record field holds this, never
the canonical octets, which are not `fn-store-text-octetsp'."
  (fnn-as-octets (fnn-core 'fn-store-identity-text (fnn-octet-list identity))))

(defun fnn-metadata (msgid payload)
  "Content identity, derived in ACL2 by books/identity over host digests.
The obligation binds the CANONICAL subject identity octets; what comes back
is each identity's text.  The evidence label is a host constant naming a
provenance the model only compares."
  (let* ((subject (handler-case (fnn-subject-id payload)
                    (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity"))))
         (obligation (handler-case (fnn-obligation-id msgid subject)
                       (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity")))))
    (values (fnn-identity-text obligation) (fnn-identity-text subject)
            (fnn-string-octets "unsigned-legacy-v0"))))

(defun fnn-group-codes-for (store groups)
  (when (null groups) (fnn-refuse "provide one or more distinct configured groups"))
  (fnn-group-codes groups (fnn-store-config-domain store)))

(defun fnn-validate-post-boundary (store msgid payload groups charge)
  (when (> (fnn-config-max-payload store) (fnn-constant :max-store))
    (fnn-fault "configured payload bound disagrees with the model"))
  (let ((verdict (fnn-post-boundary msgid (length payload) (length groups) charge)))
    (case verdict
      (:ok nil)
      (:bad-message-id (fnn-refuse "Message-ID is not a valid RFC 5536 message identifier"))
      (:payload-bound (fnn-refuse "payload exceeds the modelled bound"))
      (:group-bound (fnn-refuse "group count exceeds codec bound"))
      (:charge-bound (fnn-refuse "charge must be a positive uint32"))
      (t (fnn-refuse "ACL2 refused the post boundary: ~(~a~)" verdict)))))

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
      (format nil "staging-orphans=~d [~{~a~^ ~}]" (length (fnn-store-orphans store))
              (fnn-store-orphans store))))

;;; Commands.

(defparameter +fnn-init-model-cuts+
  '("init-root-mkdir" "init-root-parent-fenced" "init-lock-created"
    "init-transactions-mkdir" "init-transactions-parent-fenced"
    "init-staging-mkdir" "init-staging-parent-fenced"
    "init-config-dir-mkdir" "init-config-dir-parent-fenced"
    "init-config-created" "init-config-written" "init-config-file-fenced"
    "init-config-linked" "init-config-root-fenced" "init-config-stage-unlinked"
    "init-history-created" "init-history-written" "init-history-file-fenced"
    "init-history-linked" "init-history-root-fenced" "init-history-stage-unlinked"
    "init-config-history-fenced"
    "init-frontier-created" "init-frontier-written" "init-frontier-file-fenced"
    "init-frontier-linked" "init-frontier-root-fenced" "init-frontier-stage-unlinked"
    "init-final-config-file-fenced" "init-final-config-record-file-fenced"
    "init-final-frontier-file-fenced" "init-transactions-fenced"
    "init-root-fenced" "init-parent-fenced"))

;; These controls are intentionally outside fn-bsi-current-init-program: they
;; fail *before* a directory enumeration to verify the host does not confuse
;; an OS error with an empty configuration history.
(defparameter +fnn-init-test-controls+
  '("init-config-records-first-enumerate" "init-config-records-final-enumerate"))

(defun fnn-init-test-fault ()
  "Developer-only FN_NATIVE_INIT_FAULT=MODEL-CUT:eio|kill selector.

This is intentionally not a command-line option or an operator configuration
field.  The external native fidelity test uses it to stop one child process at
a source-pinned post-syscall cut."
  (let ((raw (sb-ext:posix-getenv "FN_NATIVE_INIT_FAULT")))
    (when raw
      (let ((colon (position #\: raw :from-end t)))
        (unless colon
          (fnn-fault "invalid FN_NATIVE_INIT_FAULT (expected MODEL-CUT:eio|kill)"))
        (let ((label (subseq raw 0 colon)) (action (subseq raw (1+ colon))))
          (unless (or (member label +fnn-init-model-cuts+ :test #'string=)
                      (member label +fnn-init-test-controls+ :test #'string=))
            (fnn-fault "unknown FN_NATIVE_INIT_FAULT cut: ~a" label))
          (list (intern (string-upcase label) :keyword)
                (cond ((string= action "eio") 'fnn-os-error)
                      ((string= action "kill") :fnn-test-kill)
                      (t (fnn-fault "invalid FN_NATIVE_INIT_FAULT action: ~a" action)))
                "developer-only native initializer fault"))))))

(defun fnn-command-init (root groups)
  (let ((store (make-fnn-store root :writable t :fault (fnn-init-test-fault))))
    (unwind-protect
         (progn (fnn-initialize store (or groups +fnn-default-groups+))
                (fnn-acquire store)
                (fnn-out "initialized ~a" (fnn-store-root store)))
      (fnn-store-close store))
    +fnn-exit-ok+))

(defparameter +fnn-cli-faults+
  (list (cons "prepublish" (list :record-staged-durable 'fnn-store-error
                                 "injected known abort before publication"))
        (cons "postpublish" (list :record-attempted 'fnn-store-indeterminate
                                  "indeterminate injected failure after final publication"))
        (cons "frontierbarrier" (list :frontier-barrier 'fnn-os-error
                                      "injected allocator directory barrier failure"))
        (cons "recordbarrier" (list :record-barrier 'fnn-os-error
                                    "injected transaction directory barrier failure"))))

(defun fnn-command-post (root message-id payload-path charge-text inject groups)
  (let* ((msgid (fnn-octets (fnn-ascii-octet-list message-id)))
         (fault (and inject (cdr (assoc inject +fnn-cli-faults+ :test #'string=)))))
    (when (and inject (null fault)) (error 'fnn-usage-error :message "unknown fault point"))
    (multiple-value-bind (store records) (fnn-open-live-store root t fault)
      (unwind-protect
           (let* ((payload (fnn-read-regular-bounded payload-path
                                                     (fnn-config-max-payload store)))
                  (codes (fnn-group-codes-for store groups))
                  (charge (if charge-text (parse-integer charge-text) (fnn-charge (length payload)))))
             (fnn-validate-post-boundary store msgid payload codes charge)
             (let ((existing (fnn-bridge-existing-action msgid payload codes)))
               (when (eq existing :duplicate)
                 (fnn-out "duplicate")
                 (return-from fnn-command-post +fnn-exit-ok+))
               (when (eq existing :conflict)
                 (fnn-refuse "conflicting immutable Message-ID")))
             (when (>= (length records) (fnn-config-max-transactions store))
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
               (handler-case (fnn-publish store (length records) record)
                 (fnn-store-indeterminate (e) (error e))
                 (fnn-store-error (e)
                   (unless (fnn-store-fenced store)
                     (setf (fnn-store-fenced store) t)
                     (unless (eq (fnn-bridge-known-abort) :aborted)
                       (fnn-indeterminate "ACL2 rejected known pre-publication abort")))
                   (error e))))
             (setf (fnn-store-fenced store) t)
             (fnn-finish store)
             (fnn-out "committed sequence=~d charge=~d" (length records) charge)
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
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (unwind-protect
         (multiple-value-bind (report code) (fnn-anchor-report store)
           (fnn-out "recovered transactions=~d articles=~d ~a ~a"
                    (length records) (fnn-bridge-article-count)
                    (fnn-orphan-report store) report)
           code)
      (fnn-store-close store))))

(defun fnn-command-status (root)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (unwind-protect
         (progn (fnn-out "transactions=~d articles=~d ~a unsigned-legacy-experiment"
                         (length records) (fnn-bridge-article-count) (fnn-orphan-report store))
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
            (unless (eq (fnn-publish store sequence (fnn-bridge-pending-record)) :durable)
              (fnn-fault "probe publish refused"))
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
      (fnn-refuse "unexpected ACL2 archive-selection result"))
    (unless (eq selection :ready)
      (fnn-refuse "reader archive is not NNTP-projectable"))))

(defun fnn-reader-octets-of (value)
  (unless (fnn-octet-list-p value) (fnn-refuse "unexpected ACL2 octet-list result"))
  (fnn-octets value))

(defun fnn-reader-octets (global)
  (let ((value (fnn-global global)))
    (unless (fnn-octet-list-p value) (fnn-refuse "unexpected ACL2 octet-list result"))
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
          (unless (member closing '(t nil)) (fnn-refuse "unexpected ACL2 boolean result"))
          (values (fnn-octets (fnn-reader-octets 'fn-reader-output)) closing)))))

(defun fnn-reader-submission ()
  "The article a served step injected, or NIL.  ACL2 produced every octet."
  (let ((octets (fnn-global 'fn-reader-submit-octets)))
    (and octets
         (progn
           (unless (fnn-octet-list-p octets) (fnn-refuse "unexpected ACL2 octet-list result"))
           (list (fnn-octets (fnn-reader-octets 'fn-reader-submit-msgid))
                 (fnn-octets octets))))))

(defun fnn-reader-outcome (completion)
  "One durable outcome, served: ACL2 writes the 240 or the 441, never this file."
  (fnn-core-state 'fn-reader-outcome completion)
  (fnn-octets (fnn-reader-octets 'fn-reader-output)))

(defun fnn-recv (fd seconds)
  "Up to +fnn-max-read+ octets, an empty vector at end of input, :timeout."
  (if (not (sb-sys:wait-until-fd-usable fd :input seconds))
      :timeout
      (let* ((buffer (fnn-make-octets +fnn-max-read+))
             (count (fnn-read-fd fd buffer)))
        (subseq buffer 0 count))))

(defun fnn-send-all (fd octets seconds)
  (let ((offset 0))
    (loop while (< offset (length octets)) do
      (unless (sb-sys:wait-until-fd-usable fd :output seconds)
        (fnn-os-fail sb-posix:etimedout))
      (multiple-value-bind (count errno) (sb-unix:unix-write fd octets offset (- (length octets) offset))
        (when (null count) (fnn-os-fail errno))
        (incf offset count)))))

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

(defun fnn-socket-fd (socket) (sb-bsd-sockets:socket-file-descriptor socket))

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
by passing one, not this file's default."
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

(defun fnn-connect (host port &key (family :inet))
  "An active open.  HOST is an address vector, or a name resolved here."
  (let ((socket (make-instance (fnn-socket-class family) :type :stream :protocol :tcp)))
    (handler-case
        (progn
          (sb-bsd-sockets:socket-connect
           socket
           (if (stringp host)
               (sb-bsd-sockets:host-ent-address (sb-bsd-sockets:get-host-by-name host))
               host)
           port)
          socket)
      (error (e) (fnn-socket-shut socket) (error e)))))

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
                         (fnn-store-error ()
                           ;; An invalid bridge result is not a protocol
                           ;; reply; this connection's input is dropped.
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
           ;; An ACL2 refusal is an answer that leaves the core usable, as an
           ;; ACL2 Error reply leaves the pipe synchronized; only a Lisp
           ;; condition that is not a refusal is a bridge fault.
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
;;;   store ROOT init [GROUP...] | recover | status | config
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
;;; `FN_NATIVE_INIT_FAULT=MODEL-CUT:eio|kill` is a developer-only test seam;
;;; it is intentionally absent from this command protocol and normal CLI.

;;; Verbs a layer above this file owns.  host/native/tcpcl.lisp registers
;;; "tcpcl" when it loads; naming its dispatcher here instead made this file
;;; unloadable on its own and made the two files order-dependent in both
;;; directions.  An unregistered verb is an unknown verb, which is what a
;;; host built without that layer should say.

(defvar *fnn-verbs* nil)

(defun fnn-register-verb (verb handler)
  (push (cons verb handler) *fnn-verbs*)
  verb)

(defun fnn-verb-handler (verb)
  (cdr (assoc verb *fnn-verbs* :test #'string=)))

(defun fnn-dash-nil (text) (if (string= text "-") nil text))

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
                 ((string= command "config") (fnn-command-config root))
                 ((string= command "inspect") (need 4) (fnn-command-inspect root (first rest)))
                 ((string= command "probe") (need 4) (fnn-command-probe root (parse-integer (first rest))))
                 ((string= command "post")
                  (need 8)
                  (fnn-command-post root (first rest) (second rest) (fnn-dash-nil (third rest))
                                    (fnn-dash-nil (fourth rest)) (cddddr rest)))
                 (t (error 'fnn-usage-error :message (format nil "unknown store command ~a" command))))))
        ((string= verb "reader")
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
         (fnn-out "~a" (fnn-hex (fnn-sha256 (fnn-read-regular-bounded (second args) (ash 1 26)))))
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
                             (fnn-exit (+ 128 sb-unix:sigterm))))
  (let* ((argv (cdr (member "--fn" sb-ext:*posix-argv* :test #'string=)))
         (reader-p (and argv (string= (first argv) "reader")))
         (code
           (handler-case
               (progn
                 (unless (eq (fnn-global 'guard-checking-on) t)
                   (fnn-fault "guard-checking-on is not t in the saved image"))
                 (fnn-dispatch argv))
             (fnn-usage-error (e)
               (fnn-err "fn-host: error: ~a" e)
               +fnn-exit-usage+)
             ((or fnn-store-error fnn-os-error) (e)
              ;; The reader's Python has no outcome table before it listens:
              ;; an uncaught StoreError there exits 1 with a traceback.
              (fnn-err "~a: ~a" (if reader-p "reader" "store") e)
              (if reader-p +fnn-exit-refused+ (fnn-exit-code-for e)))
             (serious-condition (e)
               (fnn-err "~a: internal error: ~a" (if reader-p "reader" "store") e)
               (if reader-p +fnn-exit-refused+ +fnn-exit-fault+)))))
    (fnn-exit code)))

;; The ACL2-visible entry that host/native/build.lisp defines in :program
;; mode is redefined here in raw Lisp, so that save-exec's :return-from-lp
;; form (fn-native-entry state) reaches fnn-main.
(defun fn-native-entry (st)
  (declare (ignore st))
  (fnn-main)
  (values nil :exited *the-live-state*))
