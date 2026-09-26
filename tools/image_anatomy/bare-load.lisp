; tools/image_anatomy/bare-load.lisp -- load fn books' compiled files into a
; bare SBCL (no ACL2) with only ACL2's package names defined, and report
; what they need from ACL2 (lane image-anatomy, 2026-09-26).  Each load-time
; call of an undefined function is recorded and stubbed, and the load is
; retried; afterwards every function the loaded code calls that is not
; defined is listed.  BARE_FASLS names the files in load order, one per line.
; A measurement only.
; BARE_PKGS lists the image's package names (every package but SBCL's own).
(with-open-file (in (sb-ext:posix-getenv "BARE_PKGS"))
  (loop for p = (read-line in nil) while p
        do (unless (find-package p) (make-package p :use nil))))
; ACL2's include-book protocol around a compiled file (the Essay on Hash
; Table Support for Compilation): no-ops here, listed separately.
(defvar *protocol* '("HCOMP-INIT" "INCLUDE-BOOK-RAW" "DEFPKG-RAW" "MAYBE-MAKE-THREE-PACKAGES"
                     "MAYBE-INTRODUCE-EMPTY-PKG-1" "MAYBE-INTRODUCE-EMPTY-PKG-2"))
(dolist (n *protocol*)
  (setf (fdefinition (intern n "ACL2")) (lambda (&rest a) (declare (ignore a)) nil)))
(defvar *stubbed* nil)
(defvar *unbound-vars* nil)
(defun bare-load-one (f)
  (loop repeat 400 do
    (block try
      (handler-bind
          ((undefined-function
             (lambda (c)
               (let ((n (cell-error-name c)))
                 (push n *stubbed*)
                 (setf (fdefinition n) (lambda (&rest a) (declare (ignore a)) nil))
                 (return-from try nil))))
           (unbound-variable
             (lambda (c)
               (let ((n (cell-error-name c)))
                 (push n *unbound-vars*)
                 (proclaim `(special ,n))
                 (setf (symbol-value n) nil)
                 (return-from try nil))))
           (warning #'muffle-warning))
        (load f)
        (return-from bare-load-one :loaded))))
  :gave-up)
(defvar *files* (with-open-file (in (sb-ext:posix-getenv "BARE_FASLS"))
                  (loop for l = (read-line in nil) while l collect l)))
(defun bare-describe (e)
  (or (ignore-errors (let ((*print-length* 5) (*print-level* 3))
                       (format nil "~a: ~a" (type-of e) e)))
      (format nil "~a" (type-of e))))
(defvar *results* (mapcar (lambda (f) (cons f (handler-case (bare-load-one f)
                                                (error (e) (bare-describe e)))))
                          *files*))
(format t "~&BARE-LOADED ~d of ~d~%" (count :loaded *results* :key #'cdr) (length *results*))
(dolist (r *results*) (unless (eq (cdr r) :loaded) (format t "~&BARE-FAIL ~a ~a~%" (car r) (cdr r))))
(format t "~&BARE-STUBBED-AT-LOAD ~d~%~{  ~s~%~}" (length (remove-duplicates *stubbed*))
        (remove-duplicates *stubbed*))
(format t "~&BARE-UNBOUND-AT-LOAD ~d~%~{  ~s~%~}" (length (remove-duplicates *unbound-vars*))
        (remove-duplicates *unbound-vars*))
; Functions the loaded code calls that nothing defines: every function name
; in a non-SBCL package that compiled code refers to (SBCL 2.6 gives such a
; name a linkage index; calls go through linkage cells, not code constants)
; and that is not fbound.
(let ((names nil) (defined 0))
  (dolist (p (list-all-packages))
    (unless (or (eql 0 (search "SB-" (package-name p)))
                (member (package-name p) '("COMMON-LISP" "KEYWORD") :test #'equal))
      (do-symbols (s p)
        (when (eq (symbol-package s) p)
          (when (fboundp s) (incf defined))
          (when (and (not (fboundp s))
                     (not (eql 0 (or (ignore-errors (sb-vm::fname-linkage-index s)) 0))))
            (push s names))))))
  (setq names (sort names #'string< :key (lambda (x) (format nil "~s" x))))
  (format t "~&BARE-DEFINED ~d~%BARE-UNDEFINED-CALLED ~d~%~{  ~s~%~}" defined (length names) names))
(sb-ext:exit :code 0 :abort t)
