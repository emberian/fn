;;; fn native host: the LZ4 block ENCODER (lane compression-extents-2).
;;; Loaded after io.lisp and extent.lisp by host/native/build.lisp (and the
;;; DTN and store-test builds).
;;;
;;; The library is lib/libfn-lz4 beside the image's core (tools/build_lz4.sh
;;; over the vendored LZ4 1.10.0, third_party/lz4/UPSTREAM.txt), or the file
;;; FN_LZ4_LIBRARY names; host/native/fn-lz4.c is its one entry.  It is an
;;; UNTRUSTED encoder: the append (host/native/io.lisp fnn-log-compress) calls
;;; it only for a CANDIDATE block of a record's payload span that ACL2 planned
;;; (books/payload-lz-append.lisp fn-lzr-append-plan), and hands the candidate
;;; to ACL2's decision (fn-lzr-append-decide), which runs the proved decoder
;;; over it before anything is taken.  Nothing reads through this library.

(in-package "ACL2")

(define-condition fnn-lz4-unsupported (error)
  ((detail :initarg :detail :reader fnn-lz4-detail))
  (:report (lambda (c s) (format s "LZ4 encoder unavailable: ~a" (fnn-lz4-detail c)))))

;; The pinned vendored version (third_party/lz4/UPSTREAM.txt): 1.10.0.
(defconstant +fnn-lz4-version+ 11000)
;; HC level 9, LZ4HC_CLEVEL_DEFAULT: the level codec-c1 measured.
(defconstant +fnn-lz4-level+ 9)

(defvar *fnn-lz4-state* :uninitialized)
(defvar *fnn-lz4-library* nil)
(defvar *fnn-lz4-lock* (sb-thread:make-mutex :name "fn LZ4 initialization"))

(defun fnn-lz4-library-name ()
  (if (member :darwin *features*) "libfn-lz4.dylib" "libfn-lz4.so"))

(defun fnn-lz4-library-candidates ()
  "FN_LZ4_LIBRARY when the operator names one, else lib/ beside the core."
  (let ((named (sb-ext:posix-getenv "FN_LZ4_LIBRARY"))
        (core sb-ext:*core-pathname*))
    (cond ((and named (plusp (length named)))
           (if (find (code-char 0) named)
               (error 'fnn-lz4-unsupported :detail "invalid FN_LZ4_LIBRARY")
             (list named)))
          (core
           (list (namestring
                  (merge-pathnames (concatenate 'string "lib/" (fnn-lz4-library-name))
                                   (make-pathname :name nil :type nil :version nil
                                                  :defaults core)))))
          (t nil))))

(sb-alien:define-alien-routine ("fn_lz4_compress_hc" fnn-%lz4-compress-hc) sb-alien:int
  (dict (* sb-alien:unsigned-char)) (dict-len sb-alien:int)
  (src (* sb-alien:unsigned-char)) (src-len sb-alien:int)
  (dst (* sb-alien:unsigned-char)) (dst-cap sb-alien:int)
  (level sb-alien:int))
(sb-alien:define-alien-routine ("fn_lz4_version" fnn-%lz4-version) sb-alien:int)

(defun fnn-lz4-initialize ()
  "Load lib/libfn-lz4 once and check its version is the pinned one."
  (sb-thread:with-mutex (*fnn-lz4-lock*)
    (case *fnn-lz4-state*
      (:ready t)
      (:unsupported (error 'fnn-lz4-unsupported :detail "the library did not load"))
      (t
       (let ((last-error nil) (loaded nil))
         (dolist (candidate (fnn-lz4-library-candidates))
           (unless loaded
             (handler-case
                 (progn (sb-alien:load-shared-object candidate :dont-save t)
                        (setq loaded candidate))
               (error (condition) (setq last-error condition)))))
         (unless loaded
           (setq *fnn-lz4-state* :unsupported)
           (error 'fnn-lz4-unsupported
                  :detail (if last-error (format nil "~a" last-error)
                            "no lib/libfn-lz4 beside the core")))
         (let ((version (fnn-%lz4-version)))
           (unless (eql version +fnn-lz4-version+)
             (setq *fnn-lz4-state* :unsupported)
             (error 'fnn-lz4-unsupported
                    :detail (format nil "~a is version ~a, not the pinned ~a"
                                    loaded version +fnn-lz4-version+))))
         (setq *fnn-lz4-library* loaded
               *fnn-lz4-state* :ready)
         t)))))

(defun fnn-lz4-reset ()
  "A restarted image re-loads the library from its own lib/ (the core does
not carry the loaded object: :dont-save)."
  (sb-thread:with-mutex (*fnn-lz4-lock*)
    (setq *fnn-lz4-state* :uninitialized *fnn-lz4-library* nil))
  t)

(defun fnn-lz4-candidate (dict src start n cap)
  "The encoder's candidate block for SRC's octets [START, START+N) against
DICT (an octet vector, empty for dictionary 0), in at most CAP octets: an
octet vector, :NONE when no block fits CAP (the encoder's answer, which ACL2's
policy reads as no gain), or a store fault naming the encoder's failure (a
code outside its domain: ACL2 planned the span, so this is a defect)."
  (fnn-lz4-initialize)
  (unless (and (integerp start) (integerp n) (<= 0 start) (<= 0 n) (<= (+ start n) (length src)))
    (fnn-fault "lz4-encoder: the span is not inside the record"))
  (when (<= cap 0) (return-from fnn-lz4-candidate :none))
  (let* ((dst (make-array cap :element-type '(unsigned-byte 8)))
         (src (coerce src '(simple-array (unsigned-byte 8) (*))))
         (dict (coerce dict '(simple-array (unsigned-byte 8) (*))))
         (got (sb-sys:with-pinned-objects (dict src dst)
                (fnn-%lz4-compress-hc
                 (sb-alien:sap-alien (sb-sys:vector-sap dict) (* sb-alien:unsigned-char))
                 (length dict)
                 (sb-alien:sap-alien (sb-sys:sap+ (sb-sys:vector-sap src) start)
                                     (* sb-alien:unsigned-char))
                 n
                 (sb-alien:sap-alien (sb-sys:vector-sap dst) (* sb-alien:unsigned-char))
                 cap +fnn-lz4-level+))))
    (cond ((plusp got) (subseq dst 0 got))
          ((zerop got) :none)
          (t (fnn-fault "lz4-encoder: the encoder refused a planned span (code ~a)" got)))))
