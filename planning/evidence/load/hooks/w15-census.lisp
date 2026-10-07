;;; One-off W15 heap census (no image change).  A thread polls FN_LOAD_CENSUS_DIR/go; on seeing it,
;;; it writes SBCL's own accounting of the dynamic space to FN_LOAD_CENSUS_DIR/census.txt:
;;;   RAW   the heap as it is (garbage included)
;;;   LIVE  after a full collection
;;; each as `room` (by object type) and sb-vm:instance-usage (structure instances, which are the stobjs),
;;; then creates FN_LOAD_CENSUS_DIR/done.  Loaded through the same path as w13-idle-gc.lisp.
(in-package "ACL2")

(defun fnl-deep-size (v seen depth)
  "Octets reachable from V through arrays and structure slots (DEPTH levels), shared objects once."
  (cond ((or (null v) (symbolp v) (typep v 'fixnum) (typep v 'character) (functionp v)) 0)
        ((gethash v seen) 0)
        ((typep v '(or array bignum double-float structure-object))
         (setf (gethash v seen) t)
         (let ((b (sb-ext:primitive-object-size v)))
           (when (> depth 0)
             (cond ((typep v 'simple-vector)
                    (loop for e across v do (incf b (fnl-deep-size e seen (1- depth)))))
                   ((typep v 'structure-object)
                    (let ((dd (sb-kernel:find-defstruct-description (type-of v))))
                      (when dd
                        (dolist (dsd (sb-kernel:dd-slots dd))
                          (when (eq (sb-kernel:dsd-raw-type dsd) t)
                            (incf b (fnl-deep-size (sb-kernel:%instance-ref v (sb-kernel:dsd-index dsd)) seen (1- depth))))))))))
           b))
        (t 0)))

(defun fnl-large-census (stream)
  "LARGE lines: dynamic-space arrays of at least 256 KiB, grouped by element type, with count, total octets
and the largest length; then the 12 biggest singly.  A stobj is a vector of arrays, so its big parts show here."
  (let ((tab (make-hash-table :test 'equal)) (singles '()))
    (dolist (o (sb-vm:list-allocated-objects :dynamic :larger 262144))
      (when (arrayp o)
        (let* ((key (format nil "~a" (array-element-type o))) (sz (sb-ext:primitive-object-size o))
               (c (or (gethash key tab) (setf (gethash key tab) (list 0 0 0)))))
          (incf (first c)) (incf (second c) sz) (setf (third c) (max (third c) (length o)))
          (push (list sz key (length o)) singles))))
    (maphash (lambda (k c) (format stream "LARGE ~a count ~d bytes ~d maxlen ~d~%" (substitute #\_ #\Space k) (first c) (second c) (third c))) tab)
    (loop for x in (subseq (sort singles #'> :key #'first) 0 (min 12 (length singles)))
          do (format stream "LARGE1 ~a bytes ~d len ~d~%" (substitute #\_ #\Space (second x)) (first x) (third x)))))

(defun fnl-owner-census (stream)
  "OWNER lines: each live stobj the owner holds (S3: simple-vectors, one slot per defstobj field), the octets
reachable from each top-level slot, shared parts counted once.  Handles: host/native/io.lisp:431-462."
  (let ((seen (make-hash-table :test 'eq)))
    (dolist (spec '((cat fnn-live-cat) (arena fnn-live-arena) (hist fnn-live-hist) (owner fnn-live-owner-st)))
      (let* ((fn (second spec))
             (obj (handler-case (and (fboundp fn) (funcall fn))
                    (error (e) (format stream "OWNER-ERROR ~a ~a~%" (first spec) (substitute #\Space #\Newline (format nil "~a" e))) nil))))
        (if (not (simple-vector-p obj))
            (format stream "OWNER-MISSING ~a ~a~%" (first spec) (type-of obj))
            (loop for slot across obj for i from 0
                  do (format stream "OWNER ~a slot ~d type ~a bytes ~d~%" (first spec) i
                             (substitute #\_ #\Space (format nil "~a" (if (arrayp slot) (array-element-type slot) (type-of slot))))
                             (fnl-deep-size slot seen 6))))))))

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
                     (fnl-owner-census out)
                     (format t "~&--- large~%")
                     (fnl-large-census out))))
             (error (e) (with-open-file (o (concatenate 'string dir "/census.err") :direction :output :if-exists :supersede)
                          (format o "~a~%" e))))
           (with-open-file (o (concatenate 'string dir "/done") :direction :output :if-exists :supersede)
             (format o "done~%")))))
     :name "fn-load-census")))
