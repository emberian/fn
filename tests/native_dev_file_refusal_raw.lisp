;;; Run after loading actual native developer admission/loader definitions into
;;; an existing ACL2 process. ROOT is a new private diagnostic directory. No
;;; owner hooks, production definitions, or existing Store are changed here.
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-dev-load-file (path admitp step-limit)
  (declare (ignorable path admitp step-limit))
  (harness-stub-reached 'fnn-dev-load-file "host/native/dev-repl.lisp"))
;;; ---- derived stubs: END ----

(defvar *fndfr-prefix* nil)

(defun fndfr-source (root name text)
 (let ((path (merge-pathnames name root)))
  (with-open-file (out path :direction :output :if-exists :error)
   (write-string text out))
  path))

(defun fndfr-check (path expected &optional admitp)
 (let ((*fnn-dev-admission-failed* nil)
       (out (make-string-output-stream)))
  (let ((*standard-output* out) (*error-output* out))
  (let ((actual (multiple-value-list
                (if admitp (fnn-dev-admit-file path :step-limit 10000)
                  (fnn-dev-load path)))))
   (assert (equal actual expected))
   (assert (eq (not (null *fnn-dev-admission-failed*))
               (not (null (member (first expected) '(:refused :partial)
                                  :test #'eq)))))))
  (when (member (first expected) '(:refused :partial))
   (assert (search "Developer file" (get-output-stream-string out))))))

(defun fndfr-run (root)
 (let ((*fndfr-prefix* nil))
  (ensure-directories-exist root)
  (fndfr-check (fndfr-source root "empty.lisp" "") '(:loaded 0 0))
  (fndfr-check (merge-pathnames "missing.lisp" root)
              '(:refused :open-error 0 0))
  (fndfr-check (fndfr-source root "bad-first.lisp" ")")
              '(:refused :reader-error 0 0))
  (fndfr-check (fndfr-source root "unclosed.lisp" "(list 1")
              '(:refused :reader-error 0 0))
  (fndfr-check (fndfr-source root "reader-eval.lisp"
                            "#.(setf *fndfr-prefix* :unsafe)")
              '(:refused :reader-error 0 0))
  (assert (null *fndfr-prefix*))
  (assert (handler-case
              (progn (fnn-dev-read-form "#.(setf *fndfr-prefix* :unsafe)") nil)
            (reader-error () t)))
  (assert (null *fndfr-prefix*))
  (fndfr-check (fndfr-source root "partial.lisp"
                            "(setf *fndfr-prefix* :retained) )")
              '(:partial :reader-error 1 1))
  (assert (eq *fndfr-prefix* :retained))
  (fndfr-check (fndfr-source root "continue.lisp"
                            "(setf *fndfr-prefix* :continued)")
              '(:loaded 1 1))
  (assert (eq *fndfr-prefix* :continued))
  ;; Only OPEN/READ errors are caught. Evaluation faults, including FILE-ERROR,
  ;; still escape to the actual owner's normal fault/fence boundary.
  (dolist (entry '(("eval-error.lisp" "(error \"deliberate evaluation fault\")")
                   ("eval-file-error.lisp"
                    "(error 'file-error :pathname \"evaluated-storage-fault\")")))
   (let ((path (fndfr-source root (first entry) (second entry))))
    (assert (handler-case (progn (fnn-dev-load path) nil)
              (error () t)))))
  (let ((path (fndfr-source root "throw.lisp" "(throw 'fndfr-cut :escaped)")))
   (assert (eq (catch 'fndfr-cut (fnn-dev-load path)) :escaped)))
  ;; The production admission function, not an LD stub, executes these events.
  ;; This is an ordinary ACL2 event frame even when the native fixture was
  ;; loaded in a one-form raw diagnostic frame. Restore mode on every exit.
  (let ((old-raw (f-get-global 'acl2-raw-mode-p *the-live-state*))
        (old-ld-ok (f-get-global 'ld-okp *the-live-state*)))
   (unwind-protect
    (progn
     (f-put-global 'acl2-raw-mode-p nil *the-live-state*)
     ;; PROGN! disables nested LD by default; the native owner invokes this
     ;; facility outside that event frame. Reproduce that authorized context.
     (f-put-global 'ld-okp t *the-live-state*)
     (fndfr-check (fndfr-source root "admit-partial.lisp"
                  "(defun fn-dfr-admitted-one (x) (declare (xargs :guard t)) x) )")
                 '(:partial :reader-error 1 1) t)
     (assert (equal (funcall (symbol-function 'fn-dfr-admitted-one) 17) 17))
     (fndfr-check (fndfr-source root "admit-refused.lisp"
                  "(defun fn-dfr-admitted-two (x) (declare (xargs :guard t)) x)
                    (defthm fn-dfr-false (equal 1 2) :rule-classes nil)
                    (defun fn-dfr-not-reached (x) x)")
                 '(:partial :acl2-refusal 2 1) t)
     (assert (equal (funcall (symbol-function 'fn-dfr-admitted-two) 23) 23))
     (assert (not (getpropc 'fn-dfr-not-reached 'formals nil
                            (w *the-live-state*))))
     (fndfr-check (fndfr-source root "admit-continue.lisp"
                  "(defun fn-dfr-after-refusal (x) (declare (xargs :guard t)) x)")
                 '(:admitted 1 1) t)
     (assert (equal (funcall (symbol-function 'fn-dfr-after-refusal) 29) 29)))
    (f-put-global 'ld-okp old-ld-ok *the-live-state*)
    (f-put-global 'acl2-raw-mode-p old-raw *the-live-state*)))
  (format t "NATIVE_DEV_FILE_REFUSAL_PASS~%")
  :passed))
