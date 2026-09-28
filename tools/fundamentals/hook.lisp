; Scratch heap hook (reservation-after-flip): FN_HEAP_DIR/go holds a tag; writes heap-TAG.txt with
; the allocation counter, dynamic usage, and for tags "gc*" the usage after a full collection and
; ROOM's per-type breakdown (the live heap by object type).
(in-package "ACL2")
(defvar *rafh-dir* (sb-ext:posix-getenv "FN_HEAP_DIR"))
(defun rafh-report (dir tag)
  (let* ((usage (sb-kernel:dynamic-usage))
         (gcp (and (>= (length tag) 2) (or (string= "gc" tag :end2 2) (string= "st" tag :end2 2))))
         (after (when gcp (sb-ext:gc :full t) (sb-kernel:dynamic-usage))))
    (with-open-file (s (concatenate 'string dir "/heap-" tag ".txt")
                       :direction :output :if-exists :supersede)
      (format s "bytes-consed ~d~%dynamic-usage ~d~%dynamic-space-size ~d~%bytes-consed-between-gcs ~d~%"
              (sb-ext:get-bytes-consed) usage (sb-ext:dynamic-space-size) (sb-ext:bytes-consed-between-gcs))
      (when gcp
        (format s "dynamic-usage-after-gc ~d~%" after)
        (unless (string= "st" tag :end2 2) (let ((*standard-output* s)) (room t))))
      (when (and (>= (length tag) 3) (string= "str" tag :end2 3))
        (let ((tab (make-hash-table :test 'equal)) (n 0))
          (sb-vm:map-allocated-objects
           (lambda (obj type size)
             (declare (ignore type))
             (when (and (typep obj '(simple-array character (*))) (>= (length obj) 8))
               (incf n)
               (let ((k (subseq obj 0 (min 24 (length obj)))))
                 (let ((e (gethash k tab))) (if e (progn (incf (car e)) (incf (cdr e) size)) (setf (gethash k tab) (cons 1 size)))))))
           :dynamic)
          (let ((rows nil)) (maphash (lambda (k v) (push (list (cdr v) (car v) k) rows)) tab)
            (setq rows (sort rows #'> :key #'car))
            (format s "strings>=8 ~d~%" n)
            (loop for r in rows repeat 40 do (format s "~d ~d ~s~%" (first r) (second r) (third r)))))))))
(defun rafh-thread (dir)
  (flet ((f (n) (concatenate 'string dir "/" n)))
    (loop
      (handler-case
          (progn
            (loop until (probe-file (f "go")) do (sleep 0.02))
            (let ((tag (with-open-file (s (f "go")) (string-trim '(#\Space #\Newline #\Return) (read-line s)))))
              (delete-file (f "go"))
              (rafh-report dir tag)
              (with-open-file (s (f (concatenate 'string "done-" tag)) :direction :output :if-exists :supersede)
                (print :done s))))
        (serious-condition (c)
          (with-open-file (s (f "error.txt") :direction :output :if-exists :append :if-does-not-exist :create)
            (format s "~a~%" c))
          (sleep 1))))))
(when *rafh-dir* (sb-thread:make-thread (lambda () (rafh-thread *rafh-dir*)) :name "raf-heap"))
