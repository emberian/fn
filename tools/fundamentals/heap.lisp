; Scratch-only heap hook (rep-wave-d lane), loaded at run time through
; FN_PROF_LOAD (prof-raw.lisp loads it before fnn-main).  A thread waits for
; FN_HEAP_DIR/go, whose content is a tag, and writes heap-<tag>.txt: the
; process-wide allocation counter, the dynamic-space usage, and, when the
; tag begins with "gc", the usage after a full collection (the live heap)
; and the seconds it took; then done-<tag>.  Any error goes to error.txt.
(in-package "ACL2")
(defvar *fnh-dir* (sb-ext:posix-getenv "FN_HEAP_DIR"))
(defun fnh-read-tag (path)
  (with-open-file (s path)
    (string-trim (list (code-char 32) (code-char 10) (code-char 13)) (read-line s))))
(defun fnh-report (dir tag)
  (let* ((consed (sb-ext:get-bytes-consed))
         (usage (sb-kernel:dynamic-usage))
         (gcp (and (>= (length tag) 2) (string= "gc" tag :end2 2)))
         (t0 (get-internal-real-time))
         (after (when gcp (sb-ext:gc :full t) (sb-kernel:dynamic-usage)))
         (t1 (get-internal-real-time)))
    (with-open-file (s (concatenate (quote string) dir "/heap-" tag ".txt")
                       :direction :output :if-exists :supersede)
      (format s "bytes-consed ~d~%dynamic-usage ~d~%" consed usage)
      (when gcp
        (format s "dynamic-usage-after-gc ~d~%gc-seconds ~,3f~%" after
                (/ (- t1 t0) (float internal-time-units-per-second))))
      (format s "bytes-consed-between-gcs ~d~%gc-run-time-ms ~d~%"
              (sb-ext:bytes-consed-between-gcs)
              (floor (* 1000 sb-ext:*gc-run-time*) internal-time-units-per-second)))))
(defun fnh-thread (dir)
  (flet ((f (n) (concatenate (quote string) dir "/" n)))
    (loop
      (handler-case
          (progn
            (loop until (probe-file (f "go")) do (sleep 0.02))
            (let ((tag (fnh-read-tag (f "go"))))
              (delete-file (f "go"))
              (fnh-report dir tag)
              (with-open-file (s (f (concatenate (quote string) "done-" tag))
                                 :direction :output :if-exists :supersede)
                (print :done s))))
        (serious-condition (c)
          (with-open-file (s (f "error.txt") :direction :output :if-exists :append
                             :if-does-not-exist :create)
            (format s "~a~%" c))
          (sleep 1))))))
(when *fnh-dir*
  (sb-thread:make-thread (lambda () (fnh-thread *fnh-dir*)) :name "fn-heap"))
(format *error-output* "fnh: heap hook installed~%")
