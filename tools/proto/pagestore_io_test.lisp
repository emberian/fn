;;; tools/proto/pagestore_io_test.lisp -- the page store's two byte primitives
;;; alone, in plain SBCL (lane proto-pagestore, 2026-09-27; Q5).
;;;   sbcl --dynamic-space-size 6000 --non-interactive --load tools/proto/pagestore_io_test.lisp DIR [BIG-MIB]
;;; Loads host/native/proto-pagestore-io.lisp (the primitives, the
;;; little-endian check at load) and checks, printing one PGSIO line per case:
;;; u8 and u64 round trips at unaligned byte offsets and element starts; the
;;; file's octets are the words' little-endian octets; a BIG-MIB range (one
;;; vector, written, zeroed, read back, checked by formula); EOF during a
;;; fill and a file shorter than the range are the named error (never a zero
;;; fill); a pipe is refused by name (pread: ESPIPE); EINTR is retried and a
;;; short count is continued (through the syscall seam: a regular file's
;;; pread is not interruptible); another errno is the named error.
(require :sb-posix)
(defpackage :pgsio (:use :cl))
(in-package :pgsio)
(defvar *here* (directory-namestring *load-truename*))
(load (merge-pathnames "../../host/native/proto-pagestore-io.lisp" *here*))

(defvar *dir* (or (second sb-ext:*posix-argv*) "/tmp"))
(defvar *big-mib* (parse-integer (or (third sb-ext:*posix-argv*) "2600")))
(defvar *fails* 0)

(defun pgsio-report (name ok &rest kv)
  (unless ok (incf *fails*))
  (format t "PGSIO ~a ~a~{ ~a=~a~}~%" (if ok "ok  " "FAIL") name kv)
  (finish-output))

(defun path (n) (format nil "~a/pgsio-~a-~a" *dir* (sb-posix:getpid) n))
(defun fopen (p) (fnps-open-file p :create t))

(defmacro expect-io-error ((detail-var errno-var) form &body check)
  `(handler-case (progn ,form nil)
     (fnps-io-error (e)
       (let ((,detail-var (fnps-io-error-detail e)) (,errno-var (fnps-io-error-errno e)))
         (declare (ignorable ,detail-var ,errno-var))
         ,@check))))

(let* ((p (path "u8")) (fd (fopen p))
       (a (make-array 100003 :element-type '(unsigned-byte 8)))
       (b (make-array 100010 :element-type '(unsigned-byte 8) :initial-element 0)))
  (dotimes (i (length a)) (setf (aref a i) (mod (* i 131) 251)))
  (fnps-write-to-file fd 12345 a 7 99990)          ; unaligned offset and start
  (fnps-fill-from-file fd 12345 b 3 99990)
  (pgsio-report "u8-roundtrip-unaligned" (equalp (subseq a 7 99997) (subseq b 3 99993))
          "offset" 12345 "count" 99990)
  (sb-unix:unix-close fd) (sb-posix:unlink p))

(let* ((p (path "u64")) (fd (fopen p))
       (w (make-array 1003 :element-type '(unsigned-byte 64)))
       (r (make-array 1010 :element-type '(unsigned-byte 64) :initial-element 0))
       (bytes (make-array 16 :element-type '(unsigned-byte 8))))
  (dotimes (i (length w)) (setf (aref w i) (logand (* (1+ i) #x0102030405060708) #xffffffffffffffff)))
  (fnps-write-to-file fd 1001 w 1 1000)            ; odd byte offset
  (fnps-fill-from-file fd 1001 bytes 0 16)
  (pgsio-report "u64-little-endian-in-file"
          (and (= (aref w 1) (loop for k below 8 sum (ash (aref bytes k) (* 8 k))))
               (= (aref bytes 0) (ldb (byte 8 0) (aref w 1)))
               (= (aref bytes 7) (ldb (byte 8 56) (aref w 1))))
          "first-octets" (format nil "~{~2,'0x~}" (coerce (subseq bytes 0 8) 'list)))
  (fnps-fill-from-file fd 1001 r 5 1000)
  (pgsio-report "u64-roundtrip-unaligned" (equalp (subseq w 1 1001) (subseq r 5 1005)))
  (sb-unix:unix-close fd) (sb-posix:unlink p))

(let* ((p (path "big")) (fd (fopen p))
       (n (floor (* *big-mib* 1048576) 8))
       (v (make-array n :element-type '(unsigned-byte 64)))
       (t0 (get-internal-real-time)))
  (dotimes (i n) (setf (aref v i) (logxor i #x5a5a5a5a5a5a5a5a)))
  (fnps-write-to-file fd 3 v 0 n)
  (fill v 0)
  (fnps-fill-from-file fd 3 v 0 n)
  (pgsio-report "big-range" (loop for i below n always (= (aref v i) (logxor i #x5a5a5a5a5a5a5a5a)))
          "mib" *big-mib* "bytes" (* 8 n) "over-2GiB" (> (* 8 n) 2147483648)
          "seconds" (float (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
  (sb-unix:unix-close fd) (sb-posix:unlink p))

(let* ((p (path "short")) (fd (fopen p))
       (a (make-array 100 :element-type '(unsigned-byte 8) :initial-element 7))
       (b (make-array 200 :element-type '(unsigned-byte 8) :initial-element 9)))
  (fnps-write-to-file fd 0 a 0 100)
  (pgsio-report "file-shorter-than-range-is-named-eof"
          (expect-io-error (d e) (fnps-fill-from-file fd 0 b 0 200)
            (search "end of file at byte 100" d))
          "detail" "end of file at byte 100")
  (pgsio-report "eof-at-offset-past-end"
          (expect-io-error (d e) (fnps-fill-from-file fd 5000 b 0 1) (search "end of file" d)))
  (pgsio-report "range-outside-vector-refused"
          (expect-io-error (d e) (fnps-fill-from-file fd 0 b 150 100) (search "outside vector" d)))
  ;; injected: EINTR first, then a short count, then the rest
  (let ((calls 0) (c (make-array 100 :element-type '(unsigned-byte 8) :initial-element 0)))
    (let ((*fnps-syscall-hook*
            (lambda (write-p fd sap n off)
              (incf calls)
              (case calls
                (1 (values -1 4))                                  ; EINTR
                (2 (values (fnps-%pread fd sap (min n 13) off) nil)) ; short count
                (t (values (if write-p (fnps-%pwrite fd sap n off) (fnps-%pread fd sap n off)) nil))))))
      (fnps-fill-from-file fd 0 c 0 100))
    (pgsio-report "eintr-retried-and-short-count-continued" (and (= calls 3) (every (lambda (x) (= x 7)) c))
            "calls" calls))
  (let ((*fnps-syscall-hook* (lambda (w fd sap n off) (declare (ignore w fd sap n off)) (values -1 5))))
    (pgsio-report "other-errno-is-named-error"
            (expect-io-error (d e) (fnps-fill-from-file fd 0 b 0 10) (= e 5)) "errno" 5))
  (sb-unix:unix-close fd) (sb-posix:unlink p))

(multiple-value-bind (rfd wfd) (sb-posix:pipe)
  (let ((b (make-array 10 :element-type '(unsigned-byte 8))))
    (sb-posix:write wfd (sb-sys:vector-sap (make-array 10 :element-type '(unsigned-byte 8))) 10)
    (pgsio-report "pipe-refused-by-name"
            (expect-io-error (d e) (fnps-fill-from-file rfd 0 b 0 10) (format t "  (errno ~a)~%" e) (> e 0)))
    (sb-posix:close rfd) (sb-posix:close wfd)))

;; A real signal during a (slow) transfer: a SIGALRM timer firing every 1 ms
;; while 256 MiB are written and read back; SBCL's handler runs, the
;; syscalls are restarted or retried; the data must be intact.
(let* ((p (path "sig")) (fd (fopen p)) (hits 0)
       (n (floor (* 256 1048576) 8))
       (v (make-array n :element-type '(unsigned-byte 64))))
  (dotimes (i n) (setf (aref v i) (* 3 i)))
  (sb-sys:enable-interrupt sb-unix:sigalrm (lambda (&rest r) (declare (ignore r)) (incf hits)))
  (sb-unix:unix-setitimer :real 0 1000 0 1000)
  (dotimes (k 4) (fnps-write-to-file fd 0 v 0 n) (fill v 0) (fnps-fill-from-file fd 0 v 0 n))
  (sb-unix:unix-setitimer :real 0 0 0 0)
  (pgsio-report "under-sigalrm-1ms" (loop for i below n always (= (aref v i) (* 3 i))) "signals" hits)
  (sb-unix:unix-close fd) (sb-posix:unlink p))

(format t "PGSIO summary fails=~a lisp=~a ~a machine=~a ~a~%" *fails*
        (lisp-implementation-type) (lisp-implementation-version) (software-type) (machine-type))
(sb-ext:exit :code (if (zerop *fails*) 0 1))
