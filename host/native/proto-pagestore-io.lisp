;;; host/native/proto-pagestore-io.lisp -- the page-store prototype's two
;;; byte primitives and its barrier/open wrappers (lane proto-pagestore,
;;; 2026-09-27).  Plain SBCL: no ACL2 needed, so the primitives can be tested
;;; alone (tools/proto/pagestore_io_test.lisp, on Linux and OpenBSD).  The
;;; driver host/native/proto-pagestore.lisp loads this file; the header there
;;; states the trust boundary and the assumptions A-PGS-HOST-IO, A-PGS-LE.
;;; Package: whatever package the loader is in (ACL2 for the driver,
;;; CL-USER for the standalone test).

;; ---------------------------------------------------------------------------
;; The syscalls.

(define-condition fnps-io-error (error)
  ((call :initarg :call :reader fnps-io-error-call)
   (errno :initarg :errno :reader fnps-io-error-errno)
   (detail :initarg :detail :reader fnps-io-error-detail))
  (:report (lambda (c s)
             (format s "fnps-io-error: ~a errno ~a (~a)"
                     (fnps-io-error-call c) (fnps-io-error-errno c)
                     (fnps-io-error-detail c)))))

(sb-alien:define-alien-routine ("pread" fnps-%pread) sb-alien:long
  (fd sb-alien:int) (buf sb-sys:system-area-pointer)
  (n sb-alien:unsigned-long) (off sb-alien:long))
(sb-alien:define-alien-routine ("pwrite" fnps-%pwrite) sb-alien:long
  (fd sb-alien:int) (buf sb-sys:system-area-pointer)
  (n sb-alien:unsigned-long) (off sb-alien:long))
(sb-alien:define-alien-routine ("fdatasync" fnps-%fdatasync) sb-alien:int
  (fd sb-alien:int))
(sb-alien:define-alien-routine ("fsync" fnps-%fsync) sb-alien:int
  (fd sb-alien:int))

(defconstant +fnps-eintr+ 4)

(defun fnps-elt-bytes (vec)
  (etypecase vec
    ((simple-array (unsigned-byte 8) (*)) 1)
    ((simple-array (unsigned-byte 64) (*)) 8)))

;; The syscall seam: nil in production.  A test binds it to a function of
;; (WRITE-P FD SAP N OFFSET) returning (values RESULT ERRNO-OR-NIL), to
;; inject EINTR, short counts and errors (a regular file's pread cannot be
;; interrupted by a signal, so EINTR is exercised through this seam).
(defvar *fnps-syscall-hook* nil)

(defun fnps-transfer (write-p fd byte-offset vec start count)
  (let* ((eb (fnps-elt-bytes vec))
         (total (* count eb))
         (done 0))
    (unless (and (integerp start) (integerp count) (<= 0 start) (<= 0 count)
                 (<= (+ start count) (length vec)) (integerp byte-offset)
                 (<= 0 byte-offset))
      (error 'fnps-io-error :call (if write-p "pwrite" "pread") :errno 0
             :detail (format nil "range ~a+~a outside vector of ~a" start count
                             (length vec))))
    (sb-sys:with-pinned-objects (vec)
      (let ((base (sb-sys:sap+ (sb-sys:vector-sap vec) (* start eb))))
        (loop while (< done total) do
          (multiple-value-bind (r injected-errno)
              (let ((sap (sb-sys:sap+ base done)) (n (- total done)) (off (+ byte-offset done)))
                (cond (*fnps-syscall-hook*
                       (funcall *fnps-syscall-hook* write-p fd sap n off))
                      (write-p (fnps-%pwrite fd sap n off))
                      (t (fnps-%pread fd sap n off))))
            (cond ((> r 0) (incf done r))
                  ((and (= r 0) (not write-p))
                   (error 'fnps-io-error :call "pread" :errno 0
                          :detail (format nil "end of file at byte ~a"
                                          (+ byte-offset done))))
                  ((= r 0)
                   (error 'fnps-io-error :call "pwrite" :errno 0
                          :detail "wrote nothing"))
                  (t (let ((e (or injected-errno (sb-alien:get-errno))))
                       (unless (= e +fnps-eintr+)
                         (error 'fnps-io-error :call (if write-p "pwrite" "pread")
                                :errno e
                                :detail (format nil "at byte ~a"
                                                (+ byte-offset done)))))))))))
    count))

(defun fnps-fill-from-file (fd byte-offset vec start count)
  "Primitive 1 (read): VEC[START, START+COUNT) := the file's octets at BYTE-OFFSET."
  (fnps-transfer nil fd byte-offset vec start count))

(defun fnps-write-to-file (fd byte-offset vec start count)
  "Primitive 2 (write): the file's octets at BYTE-OFFSET := VEC[START, START+COUNT)."
  (fnps-transfer t fd byte-offset vec start count))

;; A-PGS-LE, checked at load: a u64 written through primitive 2 reads back
;; through primitive 1 as its little-endian octets.
(let* ((path (format nil "/tmp/fnps-le-check-~a" (sb-unix:unix-getpid)))
       (fd (sb-unix:unix-open path (logior sb-unix:o_rdwr sb-unix:o_creat sb-unix:o_trunc) #o600))
       (w (make-array 1 :element-type '(unsigned-byte 64)
                        :initial-element #x0807060504030201))
       (b (make-array 8 :element-type '(unsigned-byte 8) :initial-element 0)))
  (unwind-protect
       (progn (fnps-write-to-file fd 0 w 0 1)
              (fnps-fill-from-file fd 0 b 0 8)
              (unless (equalp b #(1 2 3 4 5 6 7 8))
                (error "A-PGS-LE fails: this host does not store u64 little-endian ~a" b)))
    (sb-unix:unix-close fd)
    (sb-unix:unix-unlink path)))

(defvar *fnps-syncs* 0)

(defun fnps-datasync (fd)
  (incf *fnps-syncs*)
  (unless (zerop (fnps-%fdatasync fd))
    (error 'fnps-io-error :call "fdatasync" :errno (sb-alien:get-errno) :detail "")))

(defun fnps-fullsync (fd)
  (incf *fnps-syncs*)
  (unless (zerop (fnps-%fsync fd))
    (error 'fnps-io-error :call "fsync" :errno (sb-alien:get-errno) :detail "")))

(defun fnps-open-file (path &key create)
  (multiple-value-bind (fd err)
      (sb-unix:unix-open path (if create (logior sb-unix:o_rdwr sb-unix:o_creat) sb-unix:o_rdwr) #o644)
    (unless fd
      (error 'fnps-io-error :call "open" :errno err :detail path))
    fd))

(defun fnps-sync-dir (dir)
  (let ((fd (sb-unix:unix-open dir sb-unix:o_rdonly 0)))
    (unless fd (error 'fnps-io-error :call "open" :errno 0 :detail dir))
    (unwind-protect (fnps-fullsync fd) (sb-unix:unix-close fd))))

