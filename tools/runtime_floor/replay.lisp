;;; tools/runtime_floor/replay.lisp -- replay a boundary trace (trace.lisp)
;;; against the exported definitions in a plain CL (lane runtime-floor).
;;; Portable CL: runs on bare SBCL and on ECL.  For each recorded call: install
;;; the octet buffers' recorded contents, apply NAME's exported definition to
;;; the decoded arguments (the live stobjs and state by name), and compare the
;;; encoded results with the recorded ones.  Prints RP- lines.
(in-package "ACL2")

(defvar *rp-live* nil)
(defvar *rp-extent-paths* (make-hash-table))

(defun rp-live-by-name (name)
  (if (string= name "STATE")
      *the-live-state*
      (let ((hit (assoc name *rf-user-stobj-alist* :key #'symbol-name :test #'string=)))
        (if hit (cdr hit) (error "no live stobj ~a" name)))))

(defun rp-namer (x)
  (cond ((eq x *the-live-state*) "STATE")
        ((or (simple-vector-p x) (hash-table-p x) (typep x '(simple-array (unsigned-byte 8) (*))))
         (let ((hit (rassoc x *rf-user-stobj-alist* :test #'eq)))
           (and hit (symbol-name (car hit)))))
        (t nil)))

(defun rp-install-buffers (bufs)
  (dolist (b bufs)
    (let ((st (rp-live-by-name (first b))) (fill (second b)) (vec (third b)))
      (let ((a (make-array (max fill (length vec)) :element-type '(unsigned-byte 8) :initial-element 0)))
        (replace a vec)
        (setf (svref st 0) a (svref st 1) fill)))))

(defun rp-rss-kib ()
  (with-open-file (in "/proc/self/status" :if-does-not-exist nil)
    (when in
      (loop for line = (read-line in nil) while line
            when (and (> (length line) 6) (string= "VmRSS:" line :end2 6))
              return (parse-integer line :start 6 :junk-allowed t)))))

(defvar *rp-error-hook* nil)
(defun rp-call (sym args)
  (let ((outcome :thrown) (vals nil))
    (setq vals
          (catch 'raw-ev-fncall
            (handler-case
                (handler-bind ((error (lambda (c) (when *rp-error-hook* (funcall *rp-error-hook* c)))))
                  (prog1 (multiple-value-list (apply sym args)) (setq outcome :ok)))
              (error (c) (setq outcome (list :error (princ-to-string c))) nil))))
    (if (eq outcome :ok) vals (list :rf-fault outcome))))

(defun rp-replay (path &key (report 20))
  (let ((rf-serial::*stobj-namer* #'rp-namer)
        (rf-serial::*stobj-of-name* #'rp-live-by-name)
        (n 0) (same 0) (diff 0) (faults-both 0) (t-rec 0) (t-rep 0)
        (by-name (make-hash-table :test 'equal))
        (*read-default-float-format* 'single-float))
    (with-open-file (in path :external-format :latin-1)
      (let ((*package* (find-package "RF-SERIAL")))
        (loop for form = (read in nil in) until (eq form in) do
          (cond
            ((eq (car form) :extent)
             (setf (gethash (second form) *rp-extent-paths*) (third form))
             (when (fboundp 'rp-extent-registered) (funcall 'rp-extent-registered (second form) (third form))))
            ((eq (car form) :globals)
              (dolist (p (rf-serial:dec (second form)))
                (setf (symbol-value (intern (car p) "ACL2_GLOBAL_ACL2")) (cdr p))))
            (t
              (destructuring-bind (ename eargs eresult ebufs us) form
                (incf n)
                (let* ((name (rf-serial:dec ename))
                       (args (rf-serial:dec eargs))
                       (bufs (rf-serial:dec ebufs)))
                  (rp-install-buffers bufs)
                  (let* ((t0 (get-internal-real-time))
                         (result (rp-call (intern (symbol-name name)
                                                  (concatenate 'string "ACL2_*1*_" (package-name (symbol-package name))))
                                          args))
                         (el (- (get-internal-real-time) t0))
                         (got (rf-serial:enc result))
                         (row (or (gethash (symbol-name name) by-name)
                                  (setf (gethash (symbol-name name) by-name) (list 0 0 0 0)))))
                    (incf t-rec us) (incf t-rep el)
                    (incf (first row)) (incf (second row) us) (incf (third row) el)
                    (cond ((equal got eresult) (incf same))
                          ((and (consp got) (eq (car got) :l) (consp eresult)
                                (equal (rf-serial:enc :rf-fault) (third got))
                                (equal (rf-serial:enc :rf-fault) (third eresult)))
                           (incf faults-both))
                          (t (incf diff) (incf (fourth row))
                             (when (> report 0)
                               (decf report)
                               (let ((g (rf-serial:enc-string result)))
                                 (format t "~&RP-DIFF #~d ~a~%  want ~a~%  got  ~a~%" n (symbol-name name)
                                         (subseq (prin1-to-string eresult) 0 (min 400 (length (prin1-to-string eresult))))
                                         (subseq g 0 (min 400 (length g))))))))))))))))
    (format t "~&RP-SUMMARY calls ~d identical ~d both-fault ~d differ ~d recorded-us ~d replay-us ~d rss-kib ~a~%"
            n same faults-both diff t-rec
            (round (* t-rep 1000000) internal-time-units-per-second) (rp-rss-kib))
    (let ((rows nil))
      (maphash (lambda (k v) (push (cons k v) rows)) by-name)
      (dolist (r (sort rows #'> :key #'third))
        (format t "~&RP-NAME ~a calls ~d rec-us ~d rep-us ~d differ ~d~%" (car r) (second r) (third r)
                (round (* (fourth r) 1000000) internal-time-units-per-second) (fifth r))))
    diff))
