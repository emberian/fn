;;; tools/runtime_floor/export-run.lisp -- run the export (lane runtime-floor).
;;; tools/runtime_floor/rf-start.sh DEVELOPER-IMAGE export-run.lisp, with
;;; RF_HERE (this directory, trailing /), RF_TREE (the image's source tree,
;;; trailing /), RF_ACL2_SOURCES (ACL2 8.7's source directory, trailing /) and
;;; RF_OUT (the output directory, trailing /).  Prints RF4 lines (closure,
;;; cuts, the ACL2 functions kept, the memoize table) and RF-EMIT.
(in-package "ACL2")
(declaim (optimize (safety 3)))
(setq *print-pretty* nil)
(load (concatenate 'string (sb-ext:posix-getenv "RF_HERE") "extract.lisp"))
(rf-scan-world)
(rf-read-acl2-sources (sb-ext:posix-getenv "RF_ACL2_SOURCES"))
(defvar *roots* (rf-roots (directory (concatenate 'string (sb-ext:posix-getenv "RF_TREE") "host/native/*.lisp"))))
(setq *rf-boundary* (rf-boundary-names (directory (concatenate 'string (sb-ext:posix-getenv "RF_TREE") "host/native/*.lisp"))))
(let ((pre (rf-predefined-boundary (directory (concatenate 'string (sb-ext:posix-getenv "RF_TREE") "host/native/*.lisp")))))
  (format t "~&RF4 predefined boundary ~d: ~{~s ~}~%" (length pre) pre)
  (setq *rf-boundary* (append pre *rf-boundary*)))
(format t "~&RF4 boundary ~d~%" (length *rf-boundary*))
(format t "~&RF4 closure ~d~%" (rf-full-closure *roots*))
(format t "~&RF4 host constants ~d~%" (rf-host-constants (directory (concatenate 'string (sb-ext:posix-getenv "RF_TREE") "host/native/*.lisp"))))
(format t "~&RF4 star1 wrappers ~d~%" (hash-table-count *rf-star1-wrappers*))
(format t "~&RF4 cut met: ~{~s ~}~%" (loop for k being the hash-keys of *rf-cutmet* collect k))
(format t "~&RF4 missing: ~{~s ~}~%" (loop for k being the hash-keys of *rf-missing* collect (cons k (rf-why (gethash k *rf-parent*)))))
(format t "~&RF4 nonportable: ~{~s ~}~%" (loop for k being the hash-keys of *rf-nonportable* collect k))
(format t "~&RF4 predef ~{~s ~}~%" (sort (loop for k being the hash-keys of *rf-closure* when (rf-predefined-p k) collect k) #'string< :key #'symbol-name))
(format t "~&RF4 rawonly ~{~s ~}~%" (sort (loop for k being the hash-keys of *rf-closure* when (and (not (rf-predefined-p k)) (not (member (gethash k *rf-def-origin*) '(:world :stobj)))) collect k) #'string< :key #'symbol-name))
(format t "~&RF4 memoize-table ~s~%" (table-alist 'memoize-table (w *the-live-state*)))
(format t "~&RF4 failed: ~{~s ~}~%" (loop for k being the hash-keys of *rf-closure* using (hash-value v) unless (consp v) collect k))
(let ((kinds (make-hash-table :test 'equal)))
  (dolist (e *rf-log*) (push (cdr e) (gethash (car e) kinds)))
  (maphash (lambda (k v) (format t "~&RF4 LOG ~s ~d ~{~s ~}~%" k (length v) (subseq v 0 (min 12 (length v))))) kinds))
(ensure-directories-exist (sb-ext:posix-getenv "RF_OUT"))
(rf-emit (sb-ext:posix-getenv "RF_OUT"))
