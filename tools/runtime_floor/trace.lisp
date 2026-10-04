;;; tools/runtime_floor/trace.lisp -- record every host-to-core call of a
;;; native image (lane runtime-floor).  Loaded into a DERIVED developer image
;;; (tools/image_anatomy/derive.sh); never in a release.  When FN_RF_TRACE
;;; names a file, fnn-call (host/native/io.lisp) appends one line per call:
;;;   (NAME ARGS RESULTS BUFFERS)
;;; each encoded by serial.lisp; BUFFERS holds the contents of the octet
;;; buffers (fn-octets, fn-octets-pub: the host fills them in place) as they
;;; were when the call began, so a replay can install the same bytes.
(in-package "ACL2")
(declaim (optimize (safety 3) (debug 1) (speed 0)))

(defvar *rf-trace-stream* nil)
(defvar *rf-trace-lock* (sb-thread:make-mutex :name "rf trace"))
(defvar *rf-trace-depth* 0)

(defun rf-live-stobj-name (x)
  (cond ((eq x *the-live-state*) "STATE")
        ((or (simple-vector-p x) (typep x 'structure-object))
         (let ((hit (rassoc x (user-stobj-alist *the-live-state*) :test #'eq)))
           (and hit (symbol-name (car hit)))))
        (t nil)))

(defun rf-buffer-snapshot (name)
  (let ((st (cdr (assoc name (user-stobj-alist *the-live-state*)))))
    (when st
      (let ((fill (svref st 1)))
        (list (symbol-name name) fill (subseq (svref st 0) 0 fill))))))

(defun rf-trace-open ()
  (let ((path (sb-ext:posix-getenv "FN_RF_TRACE")))
    (when (and path (null *rf-trace-stream*))
      ;; a directory: one trace per process (the operator's init and the
      ;; owner are separate processes with separate ACL2 states)
      (when (and (> (length path) 0) (char= (char path (1- (length path))) #\/))
        (setq path (format nil "~a~d.trace" path (sb-unix:unix-getpid))))
      (setq *rf-trace-stream*
            (open path :direction :output :if-exists :append :if-does-not-exist :create
                       :external-format :latin-1))
      ;; The fn state globals as they stand before the first call (the host
      ;; never writes them itself: every write is an ACL2 entry, traced).
      (let ((rf-serial:*stobj-namer* #'rf-live-stobj-name) (pairs nil))
        (do-symbols (s (find-package "ACL2_GLOBAL_ACL2"))
          (when (and (eq (symbol-package s) (find-package "ACL2_GLOBAL_ACL2"))
                     (boundp s) (>= (length (symbol-name s)) 3)
                     (string= "FN-" (symbol-name s) :end2 3))
            (push (cons (symbol-name s) (symbol-value s)) pairs)))
        (write-line (format nil "(:GLOBALS ~a)" (rf-serial:enc-string pairs)) *rf-trace-stream*)))
    *rf-trace-stream*))

(defvar *rf-original-fnn-call* #'fnn-call)

(defun fnn-call (name &rest args)
  (if (or (> *rf-trace-depth* 0) (not (rf-trace-open)))
      (apply *rf-original-fnn-call* name args)
      (let* ((rf-serial:*stobj-namer* #'rf-live-stobj-name)
             (bufs (remove nil (list (rf-buffer-snapshot 'fn-octets)
                                     (rf-buffer-snapshot 'fn-octets-pub))))
             (eargs (rf-serial:enc-string args))
             (ebufs (rf-serial:enc-string bufs))
             (t0 (get-internal-real-time))
             (result (let ((*rf-trace-depth* 1))
                       (handler-case (apply *rf-original-fnn-call* name args)
                         (error (c) (list :rf-fault (princ-to-string c) c))))))
        (let ((line (format nil "(~a ~a ~a ~a ~d)" (rf-serial:enc-string name) eargs
                            (rf-serial:enc-string (if (and (consp result) (eq (car result) :rf-fault))
                                                      (list :rf-fault (cadr result))
                                                      result))
                            ebufs (- (get-internal-real-time) t0))))
          (sb-thread:with-mutex (*rf-trace-lock*)
            (write-line line *rf-trace-stream*)
            (finish-output *rf-trace-stream*)))
        (if (and (consp result) (eq (car result) :rf-fault))
            (error (caddr result))
            result))))

;;; The extent realizer's file registrations (host/native/extent.lisp): a
;;; replay reads the same durable files by the same ids.
(defvar *rf-original-extent-register* #'fnn-extent-register)
(defun fnn-extent-register (path)
  (let ((id (funcall *rf-original-extent-register* path)))
    (when (rf-trace-open)
      (write-line (format nil "(:EXTENT ~d ~s)" id (namestring path)) *rf-trace-stream*)
      (finish-output *rf-trace-stream*))
    id))
