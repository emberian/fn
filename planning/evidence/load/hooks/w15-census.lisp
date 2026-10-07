;;; One-off W15 heap census (no image change).  A thread polls FN_LOAD_CENSUS_DIR/go; on seeing it,
;;; it writes SBCL's own accounting of the dynamic space to FN_LOAD_CENSUS_DIR/census.txt:
;;;   RAW   the heap as it is (garbage included)
;;;   LIVE  after a full collection
;;; each as `room` (by object type) and sb-vm:instance-usage (structure instances, which are the stobjs),
;;; then creates FN_LOAD_CENSUS_DIR/done.  Loaded through the same path as w13-idle-gc.lisp.
(in-package "ACL2")

(defun fnl-owner-type-p (name)
  (let ((s (symbol-name name)))
    (or (eql 0 (search "FN-" s)) (eql 0 (search "PGS-" s)) (eql 0 (search "FNN-CONNECTION-CUSTODY" s)))))

(defun fnl-owner-census (stream)
  "OWNER lines: instances of the owner's structures, each with its own size and the size of the
vectors it points to (two levels, shared vectors counted once).  instance-usage counts only the
instance headers, which for a stobj is almost nothing."
  (let ((objs '()))
    (sb-sys:without-gcing
      (sb-vm::map-allocated-objects
       (lambda (obj type size)
         (declare (ignore type size))
         (when (typep obj 'structure-object)
           (let ((n (type-of obj)))
             (when (and (symbolp n) (fnl-owner-type-p n)) (push obj objs)))))
       :dynamic))
    (let ((tab (make-hash-table :test 'eq)) (seen (make-hash-table :test 'eq)))
      (labels ((own (v)
                 (when (and (typep v '(or vector bignum double-float)) (not (gethash v seen)))
                   (setf (gethash v seen) t)
                   (sb-ext:primitive-object-size v)))
               (deep (v)
                 (let ((b (or (own v) 0)))
                   (when (typep v 'simple-vector)
                     (loop for e across v do (incf b (or (own e) 0))))
                   b)))
        (dolist (obj objs)
          (let* ((n (type-of obj)) (cell (or (gethash n tab) (setf (gethash n tab) (list 0 0 0)))))
            (incf (first cell))
            (incf (second cell) (sb-ext:primitive-object-size obj))
            (let ((dd (sb-kernel:find-defstruct-description n)))
              (when dd
                (dolist (dsd (sb-kernel:dd-slots dd))
                  (when (eq (sb-kernel:dsd-raw-type dsd) t)
                    (incf (third cell) (deep (sb-kernel:%instance-ref obj (sb-kernel:dsd-index dsd)))))))))))
      (maphash (lambda (n c) (format stream "OWNER ~a instances ~d self ~d slots ~d~%" n (first c) (second c) (third c))) tab))))

(let ((dir (sb-ext:posix-getenv "FN_LOAD_CENSUS_DIR")))
  (when (and dir (plusp (length dir)))
    (sb-thread:make-thread
     (lambda ()
       (loop
         (sleep 0.5)
         (when (probe-file (concatenate 'string dir "/go"))
           (delete-file (concatenate 'string dir "/go"))
           (handler-case
               (with-open-file (out (concatenate 'string dir "/census.txt") :direction :output :if-exists :supersede)
                 (let ((*standard-output* out))
                   (dolist (phase '(:raw :live))
                     (when (eq phase :live) (sb-ext:gc :full t))
                     (format t "~&=== ~a dynamic-usage ~d~%" phase (sb-kernel:dynamic-usage))
                     (format t "~&--- room~%")
                     (room t)
                     (format t "~&--- instance-usage~%")
                     (sb-vm:instance-usage :dynamic :top-n 80)
                     (format t "~&--- owner~%")
                     (fnl-owner-census out))))
             (error (e) (with-open-file (o (concatenate 'string dir "/census.err") :direction :output :if-exists :supersede)
                          (format o "~a~%" e))))
           (with-open-file (o (concatenate 'string dir "/done") :direction :output :if-exists :supersede)
             (format o "done~%")))))
     :name "fn-load-census")))
