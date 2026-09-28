;;; fn native host: the NNTP COMPRESS DEFLATE layer's two halves (lane
;;; compress; RFC 8054).  Loaded after io.lisp and lz4.lisp by
;;; host/native/build.lisp.
;;;
;;; INBOUND: the client's raw DEFLATE stream is decoded by ACL2
;;; (books/deflate-inflate.lisp fn-zin-feed, PRF-909/910).  This file holds a
;;; connection's private buffers for it (the state stobj, the 32 KiB window,
;;; the table, the output and the input) and calls the entry; every octet the
;;; served step sees is one ACL2 produced, within the per-call bound LIM and
;;; the stream's ratio bound, and a refused stream is named by ACL2's line.
;;;
;;; OUTBOUND: lib/libfn-deflate beside the image's core (tools/build_deflate.sh
;;; over the vendored zlib 1.3.2, third_party/zlib/UPSTREAM.txt), or the file
;;; FN_DEFLATE_LIBRARY names; host/native/fn-deflate.c is its one entry.  It
;;; compresses the reply windows ACL2 rendered, with a sync flush after each.
;;; A fault there garbles only what the server sends.  The parameters are
;;; ACL2's (books/nntp-compress.lisp fn-zc-deflate-params).

(in-package "ACL2")

(define-condition fnn-deflate-unsupported (error)
  ((detail :initarg :detail :reader fnn-deflate-detail))
  (:report (lambda (c s) (format s "DEFLATE compressor unavailable: ~a" (fnn-deflate-detail c)))))

;; The pinned vendored version (third_party/zlib/UPSTREAM.txt): 1.3.2.
(defconstant +fnn-deflate-version+ #x1320)

(defvar *fnn-deflate-state* :uninitialized)
(defvar *fnn-deflate-library* nil)
(defvar *fnn-deflate-lock* (sb-thread:make-mutex :name "fn DEFLATE initialization"))

(defun fnn-deflate-library-name ()
  (if (member :darwin *features*) "libfn-deflate.dylib" "libfn-deflate.so"))

(defun fnn-deflate-library-candidates ()
  "FN_DEFLATE_LIBRARY when the operator names one, else lib/ beside the core."
  (let ((named (sb-ext:posix-getenv "FN_DEFLATE_LIBRARY"))
        (core sb-ext:*core-pathname*))
    (cond ((and named (plusp (length named)))
           (if (find (code-char 0) named)
               (error 'fnn-deflate-unsupported :detail "invalid FN_DEFLATE_LIBRARY")
             (list named)))
          (core
           (list (namestring
                  (merge-pathnames (concatenate 'string "lib/" (fnn-deflate-library-name))
                                   (make-pathname :name nil :type nil :version nil
                                                  :defaults core)))))
          (t nil))))

(sb-alien:define-alien-routine ("fn_deflate_new" fnn-%deflate-new) sb-sys:system-area-pointer
  (level sb-alien:int) (window-bits sb-alien:int) (mem-level sb-alien:int))
(sb-alien:define-alien-routine ("fn_deflate_bound" fnn-%deflate-bound) sb-alien:long
  (h sb-sys:system-area-pointer) (src-len sb-alien:long))
(sb-alien:define-alien-routine ("fn_deflate_sync" fnn-%deflate-sync) sb-alien:long
  (h sb-sys:system-area-pointer)
  (src (* sb-alien:unsigned-char)) (src-len sb-alien:long)
  (dst (* sb-alien:unsigned-char)) (dst-cap sb-alien:long))
(sb-alien:define-alien-routine ("fn_deflate_free" fnn-%deflate-free) sb-alien:void
  (h sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn_deflate_version" fnn-%deflate-version) sb-alien:int)

(defun fnn-deflate-initialize ()
  "Load lib/libfn-deflate once and check its version is the pinned one."
  (sb-thread:with-mutex (*fnn-deflate-lock*)
    (case *fnn-deflate-state*
      (:ready t)
      (:unsupported (error 'fnn-deflate-unsupported :detail "the library did not load"))
      (t
       (let ((last-error nil) (loaded nil))
         (dolist (candidate (fnn-deflate-library-candidates))
           (unless loaded
             (handler-case
                 (progn (sb-alien:load-shared-object candidate :dont-save t)
                        (setq loaded candidate))
               (error (condition) (setq last-error condition)))))
         (unless loaded
           (setq *fnn-deflate-state* :unsupported)
           (error 'fnn-deflate-unsupported
                  :detail (if last-error (format nil "~a" last-error)
                            "no lib/libfn-deflate beside the core")))
         (let ((version (fnn-%deflate-version)))
           (unless (eql version +fnn-deflate-version+)
             (setq *fnn-deflate-state* :unsupported)
             (error 'fnn-deflate-unsupported
                    :detail (format nil "~a is version ~x, not the pinned ~x"
                                    loaded version +fnn-deflate-version+))))
         (setq *fnn-deflate-library* loaded
               *fnn-deflate-state* :ready)
         t)))))

(defun fnn-deflate-reset ()
  "A restarted image re-loads the library from its own lib/ (:dont-save)."
  (sb-thread:with-mutex (*fnn-deflate-lock*)
    (setq *fnn-deflate-state* :uninitialized *fnn-deflate-library* nil))
  t)

;;; ---------------------------------------------------------------------------
;;; The outbound stream of one connection.

(defstruct (fnn-zout (:constructor %make-fnn-zout)) handle)

(defun fnn-zout-new ()
  "A raw-DEFLATE stream with ACL2's parameters (level window-bits
mem-level), or a store fault when zlib refuses them or memory runs out."
  (fnn-deflate-initialize)
  (destructuring-bind (level window-bits mem-level) (fnn-core 'fn-zc-deflate-params)
    (let ((h (fnn-%deflate-new level window-bits mem-level)))
      (when (zerop (sb-sys:sap-int h))
        (error 'fnn-owner-connection-fault :operation :compress
               :cause (format nil "zlib refused the stream (~a ~a ~a)" level window-bits mem-level)))
      (%make-fnn-zout :handle h))))

(defun fnn-zout-free (zout)
  (when (and zout (fnn-zout-handle zout))
    (fnn-%deflate-free (fnn-zout-handle zout))
    (setf (fnn-zout-handle zout) nil))
  nil)

(defun fnn-zout-sync (zout octets)
  "OCTETS (a byte vector ACL2 rendered) compressed and sync-flushed: the
octets to send.  A failure is a fault on this connection (the stream is
unusable after it)."
  (let* ((h (or (fnn-zout-handle zout)
                (error 'fnn-owner-connection-fault :operation :compress
                       :cause "the stream is closed")))
         (src (coerce octets '(simple-array (unsigned-byte 8) (*))))
         (cap (fnn-%deflate-bound h (length src))))
    (unless (plusp cap)
      (error 'fnn-owner-connection-fault :operation :compress
             :cause (format nil "no bound for ~a octets" (length src))))
    (let* ((dst (make-array cap :element-type '(unsigned-byte 8)))
           (got (sb-sys:with-pinned-objects (src dst)
                  (fnn-%deflate-sync
                   h
                   (sb-alien:sap-alien (sb-sys:vector-sap src) (* sb-alien:unsigned-char))
                   (length src)
                   (sb-alien:sap-alien (sb-sys:vector-sap dst) (* sb-alien:unsigned-char))
                   cap))))
      (if (>= got 0)
          (subseq dst 0 got)
        (error 'fnn-owner-connection-fault :operation :compress
               :cause (format nil "zlib failed (code ~a)" got))))))

;;; ---------------------------------------------------------------------------
;;; The inbound stream of one connection: ACL2's inflater over private
;;; buffers.

(defstruct (fnn-zin (:constructor %make-fnn-zin))
  st win tab out in
  ;; compressed octets received and not yet consumed (after a :full stop)
  (pending nil))

(defun fnn-zin-private-octets (n)
  (fn-octets$c-reserve n (create-fn-octets$c)))

(defun fnn-zin-new ()
  "A connection's inflater, reset, its window and table at their fixed
lengths (ACL2's fn-zin-reset and fn-zin-buffers-ready)."
  (let* ((sizes (fnn-core 'fn-zin-buffer-sizes))
         (zin (%make-fnn-zin :st (create-fn-zin-st)
                             :win (fnn-zin-private-octets (getf sizes :window))
                             :tab (fnn-zin-private-octets (getf sizes :table))
                             :out (fnn-zin-private-octets 4096)
                             :in (fnn-zin-private-octets 4096))))
    (setf (fnn-zin-st zin) (first (fnn-call 'fn-zin-reset (fnn-zin-st zin))))
    (destructuring-bind (win tab) (fnn-call 'fn-zin-buffers-ready (fnn-zin-win zin) (fnn-zin-tab zin))
      (setf (fnn-zin-win zin) win (fnn-zin-tab zin) tab))
    zin))

(defun fnn-zin-fill-input (zin octets)
  (let* ((buf (fnn-zin-in zin)) (n (length octets)))
    (fn-octets$c-reserve n buf)
    (replace (the fnn-octets (svref buf 0)) octets)
    (setf (svref buf 1) n)
    buf))

(defun fnn-zin-inflate (zin octets lim)
  "Feed the compressed OCTETS (appended to what an earlier call left) to
ACL2's inflater with output bound LIM: (values PLAINTEXT STATUS), PLAINTEXT
a byte vector of at most LIM octets, STATUS :more (every octet taken; read
more), :full (LIM reached; octets remain pending for the next call) or the
refusal's line (a string: the connection closes).  The budget covers the
whole call (at most one action per input bit and per output octet, plus the
table builds), so :yield only loops."
  (let* ((input (if (fnn-zin-pending zin)
                    (concatenate '(simple-array (unsigned-byte 8) (*)) (fnn-zin-pending zin) octets)
                  octets))
         (n (length input))
         (buf (fnn-zin-fill-input zin input))
         (out (fnn-zin-out zin))
         (ip 0))
    (setf (svref out 1) 0)
    (loop
      (destructuring-bind (status b2 ip2 st win tab out2)
          (fnn-call 'fn-zin-feed (+ 1024 (* 16 (- n ip)) (* 2 lim)) (fnn-zin-st zin) ip n lim
                    buf (fnn-zin-win zin) (fnn-zin-tab zin) out)
        (declare (ignore b2))
        (setf (fnn-zin-st zin) st (fnn-zin-win zin) win (fnn-zin-tab zin) tab
              (fnn-zin-out zin) out2 out out2)
        (unless (and (integerp ip2) (<= ip ip2 n))
          (fnn-fault "compress: ACL2 returned a malformed input position"))
        (setq ip ip2)
        (case status
          (:yield nil)
          ((:more :full)
           (setf (fnn-zin-pending zin) (if (< ip n) (subseq input ip) nil))
           (return (values (subseq (svref out2 0) 0 (svref out2 1)) status)))
          (t
           (setf (fnn-zin-pending zin) nil)
           (return (values (subseq (svref out2 0) 0 (svref out2 1))
                           (if (and (consp status) (eq (first status) :refused))
                               (fnn-core 'fn-zin-refusal-text (second status))
                             "compress-fault: the inflater answered no status")))))))))
