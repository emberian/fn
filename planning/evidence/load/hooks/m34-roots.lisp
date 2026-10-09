;;; Builder M, memory landing 3+4 (2026-10-09): what holds the large u64 arrays the W1 census finds live
;;; after a full collection (eight of 17.5 MB at 16,000 records on fn-core).  Polls FN_LOAD_CENSUS_DIR/roots-go
;;; (the census hook's directory) and writes roots.txt there, then roots-done:
;;;   HROOTS  the owner's history-root generations held in custody (host/native/history-root.lisp
;;;           *fnn-history-roots*), each with its largest array's octets
;;;   PATH    sb-ext:search-roots of each live (unsigned-byte 64) array of at least 8 MiB, at most four,
;;;           after a full collection: the chain from a root to the array
;;; Measurement only: it reads and prints, it changes nothing the node decides.
(in-package "ACL2")

(defun fnl-roots-report (out)
  (sb-ext:gc :full t)
  (let* ((sym (find-symbol "*FNN-HISTORY-ROOTS*" "ACL2"))
         (h (and sym (boundp sym) (symbol-value sym))))
    (if (hash-table-p h)
        (progn
          (format out "HROOTS count ~d~%" (hash-table-count h))
          (maphash (lambda (k v)
                     (format out "HROOT generation ~a type ~a largest ~d~%" k (type-of v)
                             (if (simple-vector-p v)
                                 (loop for s across v maximize (if (arrayp s) (sb-ext:primitive-object-size s) 0))
                               0)))
                   h))
      (format out "HROOTS absent ~a~%" sym)))
  (let ((targets '()))
    (dolist (o (sb-vm:list-allocated-objects :dynamic :larger (* 8 1048576)))
      (when (and (typep o '(simple-array (unsigned-byte 64) (*))) (< (length targets) 4))
        (push (sb-ext:make-weak-pointer o) targets)))
    (format out "TARGETS ~d~%" (length targets))
    (dolist (w targets)
      (format out "PATH for array of ~d octets~%" (sb-ext:primitive-object-size (sb-ext:weak-pointer-value w)))
      (handler-case
          (let ((*standard-output* out))
            (sb-ext:search-roots w :criterion :oldest :print :verbose))
        (error (e) (format out "PATH-ERROR ~a~%" (substitute #\Space #\Newline (format nil "~a" e)))))
      (terpri out))))

(let ((dir (sb-ext:posix-getenv "FN_LOAD_CENSUS_DIR")))
  (when (and dir (plusp (length dir)))
    (sb-thread:make-thread
     (lambda ()
       (loop
         (sleep 0.5)
         (when (probe-file (concatenate 'string dir "/roots-go"))
           (delete-file (concatenate 'string dir "/roots-go"))
           (handler-case
               (with-open-file (out (concatenate 'string dir "/roots.txt") :direction :output :if-exists :supersede)
                 (fnl-roots-report out))
             (error (e) (with-open-file (o (concatenate 'string dir "/roots.err") :direction :output :if-exists :supersede)
                          (format o "~a~%" e))))
           (with-open-file (o (concatenate 'string dir "/roots-done") :direction :output :if-exists :supersede)
             (format o "done~%")))))
     :name "fn-load-roots")))
