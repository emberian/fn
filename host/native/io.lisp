;;; host/native/io.lisp -- the fn native host's raw-Lisp I/O adapter.
;;;
;;; TRUST BOUNDARY.  Every form in this file is raw Common Lisp, loaded into
;;; the ACL2 world under the trust tag :fn-native-host by host/native/build.lisp
;;; (progn! (set-raw-mode t) (load "host/native/io.lisp")).  Nothing here is
;;; proved.  This file is the whole raw surface of the native host: SBCL's
;;; sb-posix, sb-unix, sb-alien and sb-bsd-sockets contribs, the SHA-256 below
;;; (A-CRYPTO), the JSON of the two host-owned metadata files, and the socket
;;; loop.  specs/host.md lists the surface function by function.
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
;;; The host's decisions are the Python host's decisions, in the same order,
;;; with the same messages, so that the two can be compared byte for byte.
;;; Where Python holds a decision ACL2 does not (the config and frontier
;;; checksums, the bounded directory grammar, errno classes), this file holds
;;; the same one; it adds none.

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
;;; JSON, for config.json and allocation-frontier.json only.  Values: strings,
;;; integers, (:float . text), :true, :false, :null, (:array . items) and
;;; (:object . alist).  The canonical writer is Python's
;;; json.dumps(sort_keys=True, separators=(",", ":")).  Parsing never touches
;;; the Lisp reader; input is bounded by the caller's read bound.

(define-condition fnn-json-error (error)
  ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))

(defun fnn-json-fail (control &rest args)
  (error 'fnn-json-error :message (apply #'format nil control args)))

(defun fnn-json-object-p (v) (and (consp v) (eq (car v) :object)))

(defun fnn-json-get (object key)
  "The value under KEY, or :absent."
  (let ((cell (assoc key (cdr object) :test #'string=)))
    (if cell (cdr cell) :absent)))

(defun fnn-json-escape (string out)
  (write-char #\" out)
  (loop for ch across string do
    (let ((code (char-code ch)))
      (cond ((char= ch #\") (write-string "\\\"" out))
            ((char= ch #\\) (write-string "\\\\" out))
            ((char= ch #\Newline) (write-string "\\n" out))
            ((char= ch #\Return) (write-string "\\r" out))
            ((char= ch #\Tab) (write-string "\\t" out))
            ((= code 8) (write-string "\\b" out))
            ((= code 12) (write-string "\\f" out))
            ((or (< code 32) (> code 126))
             (if (> code #xffff)
                 (let ((v (- code #x10000)))
                   (format out "\\u~(~4,'0x~)\\u~(~4,'0x~)"
                           (+ #xd800 (ash v -10)) (+ #xdc00 (logand v #x3ff))))
                 (format out "\\u~(~4,'0x~)" code)))
            (t (write-char ch out)))))
  (write-char #\" out))

(defun fnn-json-write (value out)
  (cond ((stringp value) (fnn-json-escape value out))
        ((integerp value) (format out "~d" value))
        ((eq value :true) (write-string "true" out))
        ((eq value :false) (write-string "false" out))
        ((eq value :null) (write-string "null" out))
        ((and (consp value) (eq (car value) :float)) (write-string (cdr value) out))
        ((and (consp value) (eq (car value) :array))
         (write-char #\[ out)
         (loop for (item . more) on (cdr value) do
           (fnn-json-write item out)
           (when more (write-char #\, out)))
         (write-char #\] out))
        ((fnn-json-object-p value)
         (write-char #\{ out)
         (loop for ((key . item) . more) on (sort (copy-list (cdr value)) #'string< :key #'car) do
           (fnn-json-escape key out)
           (write-char #\: out)
           (fnn-json-write item out)
           (when more (write-char #\, out)))
         (write-char #\} out))
        (t (fnn-json-fail "unserializable value"))))

(defun fnn-json-canonical (value)
  (with-output-to-string (out) (fnn-json-write value out)))

(defun fnn-json-parse (octets)
  "Parse one JSON document from OCTETS (UTF-8), the way json.loads reads it."
  (let* ((text (handler-case (fnn-octets-string octets)
                 (error () (fnn-json-fail "invalid UTF-8"))))
         (pos 0) (len (length text)))
    (labels ((peek () (if (< pos len) (char text pos) nil))
             (next () (prog1 (peek) (incf pos)))
             (skip-space ()
               (loop while (and (< pos len) (member (char text pos) '(#\Space #\Tab #\Newline #\Return)))
                     do (incf pos)))
             (expect (ch)
               (unless (eql (next) ch) (fnn-json-fail "expected ~a at ~d" ch pos)))
             (parse-value (depth)
               (when (> depth 32) (fnn-json-fail "nesting too deep"))
               (skip-space)
               (let ((ch (peek)))
                 (cond ((null ch) (fnn-json-fail "unexpected end of document"))
                       ((char= ch #\{) (parse-object depth))
                       ((char= ch #\[) (parse-array depth))
                       ((char= ch #\") (parse-string))
                       ((or (digit-char-p ch) (char= ch #\-)) (parse-number))
                       ((literal "true") :true)
                       ((literal "false") :false)
                       ((literal "null") :null)
                       (t (fnn-json-fail "unexpected character at ~d" pos)))))
             (literal (word)
               (when (and (<= (+ pos (length word)) len)
                          (string= word text :start2 pos :end2 (+ pos (length word))))
                 (incf pos (length word))
                 t))
             (parse-object (depth)
               (expect #\{)
               (let ((pairs nil))
                 (skip-space)
                 (if (eql (peek) #\})
                     (next)
                     (loop
                       (skip-space)
                       (unless (eql (peek) #\") (fnn-json-fail "expected object key at ~d" pos))
                       (let ((key (parse-string)))
                         (skip-space)
                         (expect #\:)
                         (let ((value (parse-value (1+ depth))))
                           ;; json.loads keeps the last of duplicate keys.
                           (setf pairs (remove key pairs :key #'car :test #'string=))
                           (setf pairs (append pairs (list (cons key value))))))
                       (skip-space)
                       (case (next)
                         (#\, nil)
                         (#\} (return))
                         (t (fnn-json-fail "expected , or } at ~d" pos)))))
                 (cons :object pairs)))
             (parse-array (depth)
               (expect #\[)
               (let ((items nil))
                 (skip-space)
                 (if (eql (peek) #\])
                     (next)
                     (loop
                       (push (parse-value (1+ depth)) items)
                       (skip-space)
                       (case (next)
                         (#\, nil)
                         (#\] (return))
                         (t (fnn-json-fail "expected , or ] at ~d" pos)))))
                 (cons :array (nreverse items))))
             (parse-string ()
               (expect #\")
               (with-output-to-string (out)
                 (loop
                   (let ((ch (next)))
                     (cond ((null ch) (fnn-json-fail "unterminated string"))
                           ((char= ch #\") (return))
                           ((char= ch #\\)
                            (let ((esc (next)))
                              (case esc
                                (#\" (write-char #\" out)) (#\\ (write-char #\\ out))
                                (#\/ (write-char #\/ out)) (#\b (write-char (code-char 8) out))
                                (#\f (write-char (code-char 12) out)) (#\n (write-char #\Newline out))
                                (#\r (write-char #\Return out)) (#\t (write-char #\Tab out))
                                (#\u (write-char (code-char (parse-hex4)) out))
                                (t (fnn-json-fail "bad escape")))))
                           ((< (char-code ch) 32) (fnn-json-fail "control character in string"))
                           (t (write-char ch out)))))))
             (parse-hex4 ()
               (when (> (+ pos 4) len) (fnn-json-fail "bad unicode escape"))
               (multiple-value-bind (value end)
                   (parse-integer text :start pos :end (+ pos 4) :radix 16 :junk-allowed t)
                 (unless (and value (= end (+ pos 4))) (fnn-json-fail "bad unicode escape"))
                 (incf pos 4)
                 value))
             (parse-number ()
               (let ((start pos) (float nil))
                 (when (eql (peek) #\-) (next))
                 (unless (and (peek) (digit-char-p (peek))) (fnn-json-fail "bad number"))
                 (loop while (and (peek) (digit-char-p (peek))) do (next))
                 (when (eql (peek) #\.)
                   (setq float t) (next)
                   (unless (and (peek) (digit-char-p (peek))) (fnn-json-fail "bad number"))
                   (loop while (and (peek) (digit-char-p (peek))) do (next)))
                 (when (member (peek) '(#\e #\E))
                   (setq float t) (next)
                   (when (member (peek) '(#\+ #\-)) (next))
                   (unless (and (peek) (digit-char-p (peek))) (fnn-json-fail "bad number"))
                   (loop while (and (peek) (digit-char-p (peek))) do (next)))
                 (let ((token (subseq text start pos)))
                   (if float (cons :float token) (parse-integer token))))))
      (let ((value (parse-value 0)))
        (skip-space)
        (when (< pos len) (fnn-json-fail "trailing data at ~d" pos))
        value))))

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

;;; ---------------------------------------------------------------------------
;;; The store bridge: fixed calls into host/store-node-host.lisp.

(defun fnn-bridge-reset () (fnn-action (fnn-core-state 'fn-store-sn-reset)))
(defun fnn-bridge-record-sequence (record)
  (fnn-nat (fnn-core 'fn-store-record-sequence (fnn-octet-list record))))
(defun fnn-bridge-record-txid (record)
  (fnn-nat (fnn-core 'fn-store-record-txid (fnn-octet-list record))))
(defun fnn-bridge-recover (records frontier)
  (fnn-action (fnn-core-state 'fn-store-sn-recover (mapcar #'fnn-octet-list records) frontier)))
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
(defun fnn-bridge-article-count () (fnn-nat (fnn-core-state 'fn-store-sn-article-count)))
(defun fnn-bridge-next-txid () (fnn-nat (fnn-core-state 'fn-store-sn-next-txid)))
(defun fnn-bridge-group-next (code) (fnn-nat (fnn-core-state 'fn-store-sn-group-next code)))
(defun fnn-bridge-pin-count () (fnn-nat (fnn-core-state 'fn-store-sn-pin-count)))
(defun fnn-bridge-reserved () (fnn-nat (fnn-core-state 'fn-store-sn-reserved)))
(defun fnn-bridge-lookup (msgid)
  (let ((value (fnn-core-state 'fn-store-sn-lookup (fnn-octet-list msgid))))
    (if (null value) (fnn-make-octets 0) (fnn-as-octets value))))
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
                     :max-inbound :max-text :max-blob)))
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

(defun fnn-seal (prefix)
  (concatenate 'fnn-octets (fnn-octets prefix) (fnn-sha256 prefix)))

(defun fnn-digest-of (framed)
  (if (< (length framed) (fnn-constant :trailer))
      nil
      (fnn-octet-list (fnn-sha256 (subseq framed 0 (- (length framed) (fnn-constant :trailer)))))))

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
  (fnn-as-octets (fnn-core 'fn-store-subject-id (fnn-octet-list (fnn-sha256 payload)))))

(defun fnn-obligation-id (msgid subject)
  (let ((preimage (fnn-as-octets (fnn-core 'fn-store-obligation-preimage
                                           (fnn-octet-list msgid) (fnn-octet-list subject)))))
    (fnn-as-octets (fnn-core 'fn-store-obligation-id (fnn-octet-list (fnn-sha256 preimage))))))

(defun fnn-post-boundary (msgid payload-length group-count charge)
  (let ((value (fnn-core 'fn-store-post-boundary (fnn-octet-list msgid) payload-length
                         group-count charge)))
    (unless (keywordp value) (fnn-refuse "ACL2 returned an unexpected boundary verdict"))
    value))

(defun fnn-charge (length)
  (let ((value (fnn-core 'fn-store-charge length)))
    (unless (and (integerp value) (> value 0)) (fnn-refuse "ACL2 returned a non-positive charge"))
    value))

(defun fnn-group-table-id ()
  (fnn-octets-string (fnn-as-octets (fnn-core 'fn-store-group-table-id))))

(defun fnn-group-codes (names)
  (let ((value (fnn-core 'fn-store-group-codes
                         (mapcar (lambda (n) (fnn-octet-list (fnn-string-octets n))) names))))
    (when (or (keywordp value) (not (listp value)) (/= (length value) (length names)))
      (fnn-refuse "unknown or duplicate configured group"))
    value))

;;; ---------------------------------------------------------------------------
;;; The store: tools/run_store.py's Store, decision for decision.

(defconstant +fnn-max-transactions+ 128)
(defconstant +fnn-max-recovery-record-bytes+ (* 128 65538))
(defconstant +fnn-max-payload-bytes+ 32768)
(defconstant +fnn-uint32-max+ (1- (ash 1 32)))
(defconstant +fnn-max-staging-report+ 64)
(defparameter +fnn-group-table+ "fn-store-groups-1")
(defparameter +fnn-frontier-format+ "fn-store-allocation-frontier-1")

(defun fnn-default-config ()
  (list :object
        (cons "format" "fn-store-experiment-4")
        (cons "group_table" +fnn-group-table+)
        (cons "capacity" 1048576)
        (cons "max_payload_bytes" +fnn-max-payload-bytes+)
        (cons "max_recovery_record_bytes" +fnn-max-recovery-record-bytes+)
        (cons "max_transactions" +fnn-max-transactions+)
        (cons "allocation_frontier_format" +fnn-frontier-format+)))

(defun fnn-with-checksum (object)
  "OBJECT with a checksum field over its canonical form without one."
  (let* ((body (cons :object (remove "checksum" (cdr object) :key #'car :test #'string=)))
         (digest (fnn-hex (fnn-sha256 (fnn-string-octets (fnn-json-canonical body))))))
    (cons :object (append (cdr body) (list (cons "checksum" digest))))))

(defun fnn-frontier-with-checksum (next-txid)
  (fnn-with-checksum (list :object (cons "format" +fnn-frontier-format+)
                           (cons "next_txid" next-txid))))

(defun fnn-canonical-line (object)
  (fnn-string-octets (fnn-concat (fnn-json-canonical object) (string #\Newline))))

(defun fnn-seq-name-p (name)
  (and (= (length name) 24)
       (every (lambda (c) (char<= #\0 c #\9)) (subseq name 0 20))
       (string= (subseq name 20) ".txn")))

(defstruct (fnn-store (:constructor %make-fnn-store))
  root writable lock-fd config frontier fenced (orphans nil) (completion-pending nil)
  ;; The one scripted fault point, or NIL: tools/run_store.py's ScriptedFaults.
  (fault-point nil) (fault-class nil) (fault-message nil))

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
    (error (fnn-store-fault-class store) :message (fnn-store-fault-message store))))

(defun fnn-config-path (s) (fnn-join (fnn-store-root s) "config.json"))
(defun fnn-transactions (s) (fnn-join (fnn-store-root s) "transactions"))
(defun fnn-staging (s) (fnn-join (fnn-store-root s) "staging"))
(defun fnn-lock-path (s) (fnn-join (fnn-store-root s) "writer.lock"))
(defun fnn-frontier-path (s) (fnn-join (fnn-store-root s) "allocation-frontier.json"))

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

(defun fnn-safe-directory (path &optional create)
  (let ((st (fnn-lstat path)))
    (when (null st)
      (unless create (fnn-fault "missing store directory: ~a" path))
      (fnn-mkdir path #o700)
      (fnn-fsync-dir (fnn-parent path))
      (setq st (fnn-lstat path)))
    (when (or (null st) (not (fnn-directory-p st)) (fnn-symlink-p st))
      (fnn-fault "refusing non-directory store path: ~a" path))
    st))

(defun fnn-publish-initial-file (store final contents)
  "Stage, barrier, link and barrier one initialization metadata file."
  (let* ((stage (fnn-join (fnn-staging store)
                          (format nil ".init-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600)))
    (unwind-protect (progn (fnn-write-all fd contents) (fnn-fsync-file fd))
      (fnn-close fd))
    (unwind-protect
         (progn
           (handler-case (fnn-link stage final)
             (fnn-os-error (e)
               (if (= (fnn-os-errno e) sb-posix:eexist)
                   (return-from fnn-publish-initial-file nil)
                   (error e))))
           (fnn-fsync-dir (fnn-store-root store))
           t)
      (ignore-errors (fnn-unlink stage)))))

(defun fnn-transaction-files (store)
  "Sorted (sequence . path) pairs of the final namespace, gap-free or a fault."
  (let ((files nil)
        (names (handler-case (fnn-list-directory (fnn-transactions store))
                 (fnn-os-error () (fnn-fault "cannot enumerate transactions")))))
    (dolist (name names)
      (when (>= (length files) +fnn-max-transactions+)
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
  (let ((config (handler-case (fnn-json-parse (fnn-read-regular-bounded (fnn-config-path store) 16384))
                  ((or fnn-os-error fnn-json-error) (e)
                    (fnn-fault "invalid durable config: ~a" e)))))
    (unless (and (fnn-json-object-p config)
                 (string= (fnn-json-canonical (fnn-with-checksum config))
                          (fnn-json-canonical config)))
      (fnn-fault "config checksum mismatch"))
    (unless (string= (fnn-json-canonical config)
                     (fnn-json-canonical (fnn-with-checksum (fnn-default-config))))
      (fnn-fault "unsupported store configuration"))
    (setf (fnn-store-config store) config)))

(defun fnn-load-frontier (store)
  (fnn-check-regular (fnn-frontier-path store))
  (let ((frontier (handler-case (fnn-json-parse (fnn-read-regular-bounded (fnn-frontier-path store) 4096))
                    ((or fnn-os-error fnn-json-error) (e)
                      (fnn-fault "invalid durable allocation frontier: ~a" e)))))
    (unless (fnn-json-object-p frontier)
      (fnn-fault "allocation frontier must be an object"))
    (let ((next (fnn-json-get frontier "next_txid")))
      (unless (and (integerp next) (<= 0 next +fnn-uint32-max+)
                   (string= (fnn-json-canonical frontier)
                            (fnn-json-canonical (fnn-frontier-with-checksum next))))
        (fnn-fault "allocation frontier checksum or range mismatch"))
      (setf (fnn-store-frontier store) next))))

(defun fnn-initialize (store)
  (fnn-safe-directory (fnn-store-root store) t)
  (let ((lock-fd (fnn-open-lock store t t)))
    (unwind-protect
         (progn
           (fnn-safe-directory (fnn-transactions store) t)
           (fnn-safe-directory (fnn-staging store) t)
           (let ((config (fnn-with-checksum (fnn-default-config))))
             (if (fnn-publish-initial-file store (fnn-config-path store) (fnn-canonical-line config))
                 (setf (fnn-store-config store) config)
                 (fnn-load-config store)))
           ;; A missing allocator alongside committed history would permit
           ;; reuse of an aborted ID.  It is a fault, never an implicit 0.
           (when (and (null (fnn-check-regular (fnn-frontier-path store)))
                      (fnn-transaction-files store))
             (fnn-fault "refusing missing allocator frontier with committed history"))
           (if (fnn-publish-initial-file store (fnn-frontier-path store)
                                         (fnn-canonical-line (fnn-frontier-with-checksum 0)))
               (setf (fnn-store-frontier store) 0)
               (fnn-load-frontier store))
           (fnn-fsync-regular (fnn-config-path store))
           (fnn-fsync-regular (fnn-frontier-path store))
           (fnn-fsync-dir (fnn-transactions store))
           (fnn-fsync-dir (fnn-store-root store))
           (fnn-fsync-dir (fnn-parent (fnn-store-root store))))
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
        (when (> aggregate +fnn-max-recovery-record-bytes+)
          (fnn-fault "transaction recovery input exceeds configured bound"))
        (unless (= (fnn-bridge-record-sequence record) sequence)
          (fnn-fault "record sequence does not match immutable filename"))
        (push record records)))
    (nreverse records)))

(defun fnn-observe (store operation &optional (result :ok))
  "Submit one already-observed filesystem result and keep failure fenced."
  (handler-case (fnn-bridge-io operation result)
    ((or fnn-store-error fnn-os-error) ()
      (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil)
      (fnn-indeterminate "ACL2 could not record ~(~a~) observation" operation))))

(defun fnn-recover (store)
  (setf (fnn-store-fenced store) t (fnn-store-completion-pending store) nil)
  (let ((records nil))
    (handler-case
        (progn
          (fnn-load-frontier store)
          (setq records (fnn-durable-records store))
          (setf (fnn-store-orphans store) (fnn-staging-orphans store))
          (unless (eq (fnn-bridge-recover records (fnn-store-frontier store)) :recovering)
            (fnn-fault "ACL2 replay rejected committed transaction history")))
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
  (when (or (< current-txid 0) (>= current-txid +fnn-uint32-max+))
    (fnn-refuse "finite transaction-ID domain exhausted"))
  (let* ((next (1+ current-txid))
         (contents (fnn-canonical-line (fnn-frontier-with-checksum next)))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".allocation-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))
         (attempted nil))
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
          (handler-case (fnn-fsync-dir (fnn-store-root store))
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
  (let* ((final (fnn-join (fnn-transactions store) (format nil "~20,'0d.txn" sequence)))
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
          (handler-case (fnn-fsync-dir (fnn-transactions store))
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
  (let ((completion (handler-case (fnn-bridge-finish)
                      ((or fnn-store-error fnn-os-error) ()
                        (setf (fnn-store-fenced store) t)
                        (fnn-indeterminate "ACL2 completion failed after publication")))))
    (unless (eq completion :durable)
      (setf (fnn-store-fenced store) t)
      (fnn-indeterminate "ACL2 rejected durable completion after publication"))
    (setf (fnn-store-fenced store) nil)
    (fnn-at store :finish-durable)
    completion))

(defun fnn-metadata (msgid payload)
  "Content identity, derived in ACL2 by books/identity over host digests."
  (let* ((subject (handler-case (fnn-subject-id payload)
                    (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity"))))
         (obligation (handler-case (fnn-obligation-id msgid subject)
                       (fnn-store-error () (fnn-refuse "ACL2 refused to derive content identity")))))
    (values obligation subject (fnn-string-octets "unsigned-legacy-v0"))))

(defun fnn-group-codes-for (groups)
  (unless (string= +fnn-group-table+ (fnn-group-table-id))
    (fnn-fault "store was written under a different group table"))
  (when (null groups) (fnn-refuse "provide one or more distinct configured groups"))
  (fnn-group-codes groups))

(defun fnn-validate-post-boundary (msgid payload groups charge)
  (when (> +fnn-max-payload-bytes+ (fnn-constant :max-store))
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

(defun fnn-command-init (root)
  (let ((store (make-fnn-store root :writable t)))
    (unwind-protect
         (progn (fnn-initialize store)
                (fnn-acquire store)
                (fnn-out "initialized ~a" (fnn-store-root store)))
      (fnn-store-close store))
    +fnn-exit-ok+))

(defparameter +fnn-cli-faults+
  (list (cons "prepublish" (list :record-staged-durable 'fnn-store-error
                                 "injected known abort before publication"))
        (cons "postpublish" (list :record-attempted 'fnn-store-indeterminate
                                  "indeterminate injected failure after final publication"))))

(defun fnn-command-post (root message-id payload-path charge-text inject groups)
  (let* ((msgid (fnn-octets (fnn-ascii-octet-list message-id)))
         (payload (fnn-read-regular-bounded payload-path +fnn-max-payload-bytes+))
         (fault (and inject (cdr (assoc inject +fnn-cli-faults+ :test #'string=)))))
    (when (and inject (null fault)) (error 'fnn-usage-error :message "unknown fault point"))
    (multiple-value-bind (store records) (fnn-open-live-store root t fault)
      (unwind-protect
           (let* ((codes (fnn-group-codes-for groups))
                  (charge (if charge-text (parse-integer charge-text) (fnn-charge (length payload)))))
             (fnn-validate-post-boundary msgid payload codes charge)
             (let ((existing (fnn-bridge-existing-action msgid payload codes)))
               (when (eq existing :duplicate)
                 (fnn-out "duplicate")
                 (return-from fnn-command-post +fnn-exit-ok+))
               (when (eq existing :conflict)
                 (fnn-refuse "conflicting immutable Message-ID")))
             (when (>= (length records) +fnn-max-transactions+)
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

(defun fnn-command-recover (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (unwind-protect
         (progn (fnn-out "recovered transactions=~d articles=~d ~a"
                         (length records) (fnn-bridge-article-count) (fnn-orphan-report store))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-command-status (root)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (unwind-protect
         (progn (fnn-out "transactions=~d articles=~d ~a unsigned-legacy-experiment"
                         (length records) (fnn-bridge-article-count) (fnn-orphan-report store))
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
         (payload (make-array +fnn-max-payload-bytes+ :element-type '(unsigned-byte 8)
                                                        :initial-element (char-code #\x)))
         (store (make-fnn-store root :writable t)))
    (fnn-initialize store)
    (fnn-acquire store)
    (fnn-bridge-reset)
    (fnn-recover store)
    (dotimes (sequence count)
      (let ((msgid (fnn-octets (fnn-ascii-octet-list
                                (format nil "<capacity-~d@example.invalid>" sequence)))))
        (multiple-value-bind (obligation subject evidence) (fnn-metadata msgid payload)
          (fnn-advance-frontier store (fnn-bridge-next-txid))
          (unless (eq (fnn-bridge-prepare msgid payload '(0 1) obligation subject evidence
                                          (fnn-charge (length payload)))
                      :prepared)
            (fnn-fault "probe prepare refused"))
          (unless (eq (fnn-publish store sequence (fnn-bridge-pending-record)) :durable)
            (fnn-fault "probe publish refused"))
          (unless (eq (fnn-finish store) :durable) (fnn-fault "probe finish refused")))))
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
                            count +fnn-max-payload-bytes+ commit-seconds reopen-seconds))
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
  (let ((selection (fnn-core-state (if with-store 'fn-reader-use-store 'fn-reader-use-seed))))
    (unless (member selection '(:ready :refused))
      (fnn-refuse "unexpected ACL2 archive-selection result"))
    (unless (eq selection :ready)
      (fnn-refuse "reader archive is not NNTP-projectable"))))

(defun fnn-reader-octets (global)
  (let ((value (fnn-global global)))
    (unless (fnn-octet-list-p value) (fnn-refuse "unexpected ACL2 octet-list result"))
    value))

(defun fnn-reader-reset ()
  (fnn-core-state 'fn-reader-reset)
  (fnn-octets (fnn-reader-octets 'fn-reader-output)))

(defun fnn-reader-chunk (octets)
  "One call consumes at most one wire event: (values reply closing suffix)."
  (if (null octets)
      (values (fnn-make-octets 0) nil nil)
      (progn
        (fnn-core-state 'fn-reader-chunk octets)
        (let ((closing (fnn-global 'fn-reader-closep)))
          (unless (member closing '(t nil)) (fnn-refuse "unexpected ACL2 boolean result"))
          (values (fnn-octets (fnn-reader-octets 'fn-reader-output))
                  closing
                  (fnn-reader-octets 'fn-reader-suffix))))))

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

(defun fnn-serve-client (socket)
  "Serve one connection; a broken peer cannot end the listener.  A core
failure that leaves the reader unable to correlate replies is a bridge fault."
  (let ((fd (sb-bsd-sockets:socket-file-descriptor socket)))
    (unwind-protect
         (handler-case
             (progn
               (fnn-send-all fd (fnn-reader-reset) 10)
               (let ((pending nil))
                 (loop
                   (let ((incoming (fnn-recv fd 10)))
                     (when (or (eq incoming :timeout) (zerop (length incoming)))
                       (return))
                     (setq pending (append pending (fnn-octet-list incoming)))
                     (loop while pending do
                       (multiple-value-bind (reply closing suffix)
                           (handler-case (fnn-reader-chunk pending)
                             (fnn-store-error ()
                               ;; An invalid bridge result is not a protocol
                               ;; reply; this connection's input is dropped.
                               (return-from fnn-serve-client nil)))
                         (setq pending suffix)
                         (when (> (length reply) 0) (fnn-send-all fd reply 10))
                         (when closing
                           (fnn-graceful-close fd)
                           (return-from fnn-serve-client nil))
                         (unless pending (return))))))))
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
      (sb-bsd-sockets:socket-close socket))))

(defun fnn-command-reader (port once store-root)
  (let ((store nil) (listener nil))
    (unwind-protect
         (progn
           (when store-root
             ;; A shared lock fixes this recovered snapshot; posting needs the
             ;; incompatible exclusive writer lock and is therefore refused.
             (setq store (make-fnn-store store-root :writable nil))
             (fnn-acquire store)
             (fnn-bridge-reset)
             (fnn-recover store))
           (fnn-reader-select (not (null store-root)))
           (setq listener (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp))
           (setf (sb-bsd-sockets:sockopt-reuse-address listener) t)
           (sb-bsd-sockets:socket-bind listener #(127 0 0 1) port)
           (sb-bsd-sockets:socket-listen listener 1)
           (multiple-value-bind (address bound-port) (sb-bsd-sockets:socket-name listener)
             (declare (ignore address))
             (fnn-out "LISTENING ~d" bound-port))
           (loop
             (let ((client (sb-bsd-sockets:socket-accept listener)))
               (handler-case (fnn-serve-client client)
                 (fnn-reader-bridge-fault (fault)
                   ;; Fail closed rather than answer the next client from a
                   ;; core whose replies can no longer be matched to commands.
                   (fnn-err "reader: ~a" fault)
                   (return-from fnn-command-reader +fnn-exit-fault+))))
             (when once (return)))
           +fnn-exit-ok+)
      (when listener (ignore-errors (sb-bsd-sockets:socket-close listener)))
      (when store (fnn-store-close store)))))

;;; ---------------------------------------------------------------------------
;;; Entry.  tools/fn_native.py validates the command line with the Python
;;; parsers and hands over a fixed positional protocol after "--fn":
;;;   store ROOT init | recover | status
;;;   store ROOT post MESSAGE-ID PAYLOAD CHARGE|- FAULT|- GROUP...
;;;   store ROOT inspect MESSAGE-ID
;;;   store ROOT probe COUNT
;;;   reader PORT ONCE(0|1) STORE-ROOT|-
;;;   sha256 PATH

(defun fnn-dash-nil (text) (if (string= text "-") nil text))

(defun fnn-dispatch (args)
  (flet ((need (n) (when (< (length args) n) (error 'fnn-usage-error :message "missing arguments"))))
    (need 1)
    (let ((verb (first args)))
      (cond
        ((string= verb "store")
         (need 3)
         (let ((root (second args)) (command (third args)) (rest (cdddr args)))
           (cond ((string= command "init") (fnn-command-init root))
                 ((string= command "recover") (fnn-command-recover root))
                 ((string= command "status") (fnn-command-status root))
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
