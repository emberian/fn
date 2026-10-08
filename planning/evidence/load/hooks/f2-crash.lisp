;;; F2 process-death hook. Load before ACL2::SBCL-RESTART, never into a live node.
;;; FN_LOAD_CRASH_AT=function:k (or *:1 for first recovery boundary).
;;; FN_LOAD_CRASH_COUNT=path: append function/count rows in a reference run.
;;; FN_LOAD_CRASH_GO=path: ignore boundaries until this file exists (workload
;;; rather than initial open). Omit for the recovery arm.
;;; FN_LOAD_CRASH_RECORD=existing-path: fsync the witness BEFORE abort exit.
;;; This is process death, NOT power loss or filesystem qualification.
(in-package "ACL2")
(require :sb-posix)
(defvar *fnl-f2-lock* (sb-thread:make-mutex :name "load-f2"))
(defvar *fnl-f2-counts* (make-hash-table :test 'equal))
(defparameter *fnl-f2-boundaries*
  '(fnn-durable-barrier fnn-log-fdatasync fnn-checkpoint-yield
    fnn-checkpoint-write-arena-steps fnn-checkpoint-write-steps
    fnn-state-checkpoint-install fnn-owner-publish-captured))
(defun fnl-f2-write (path name count sync)
  (with-open-file (s path :direction :output :if-exists :append :if-does-not-exist :create)
    (format s "~a ~d~%" name count)
    (finish-output s)
    (when sync (sb-posix:fsync (sb-sys:fd-stream-fd s)))))
(let* ((at (sb-ext:posix-getenv "FN_LOAD_CRASH_AT"))
       (colon (and at (position #\: at :from-end t)))
       (selected (and colon (string-downcase (subseq at 0 colon))))
       (nth (and colon (parse-integer at :start (1+ colon))))
       (record (sb-ext:posix-getenv "FN_LOAD_CRASH_RECORD"))
       (counts (sb-ext:posix-getenv "FN_LOAD_CRASH_COUNT"))
       (go (sb-ext:posix-getenv "FN_LOAD_CRASH_GO")))
  (when (and at (not (and selected nth (plusp nth) record)))
    (error "F2 requires function:k and FN_LOAD_CRASH_RECORD"))
  (when (or at counts)
    (dolist (sym *fnl-f2-boundaries*)
      (unless (fboundp sym) (error "F2 missing boundary ~a" sym))
      (let ((name (string-downcase (symbol-name sym))))
        (sb-int:encapsulate
         sym 'fn-load-f2
         (lambda (original &rest args)
           (when (or (null go) (probe-file go))
             (sb-thread:with-mutex (*fnl-f2-lock*)
               (let ((n (incf (gethash name *fnl-f2-counts* 0))))
                 (when counts (fnl-f2-write counts name n nil))
                 (when (and selected (or (string= selected name) (string= selected "*")) (= nth n))
                   (fnl-f2-write record name n t)
                   (sb-ext:exit :code 86 :abort t)))))
           (apply original args)))))))
