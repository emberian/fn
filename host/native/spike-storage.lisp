;;; host/native/spike-storage.lisp -- spike/storage (D28).  Native host side of
;;; the storage-at-scale spike.  Loaded last by host/native/build.lisp.  Every
;;; decision the host makes here that ACL2 should own is marked SPIKE; the
;;; record is planning/evidence/spike-storage-2026-09-25.md.
(in-package "ACL2")

(require :sb-sprof)

;;; ---------------------------------------------------------------------------
;;; B. Developer profiling: FN_SPIKE_SPROF=PATH wraps the dispatch in the
;;; statistical profiler and writes the flat report to PATH at the end.
;;; SPIKE: a diagnostic only; it changes no outcome.

(defvar *fnn-spk-dispatch* #'fnn-dispatch)

(defun fnn-dispatch (args)
  (let ((path (sb-posix:getenv "FN_SPIKE_SPROF")))
    (if (and path (plusp (length path)))
        (let ((code nil))
          (sb-sprof:start-profiling :max-samples 400000 :mode :cpu
                                    :sample-interval 0.005 :threads :all)
          (unwind-protect (setq code (funcall *fnn-spk-dispatch* args))
            (sb-sprof:stop-profiling)
            (with-open-file (out path :direction :output :if-exists :supersede)
              (let ((*standard-output* out))
                (sb-sprof:report :type :flat :max 60)
                (sb-sprof:report :type :graph :max 25))))
          code)
        (funcall *fnn-spk-dispatch* args))))

;;; ---------------------------------------------------------------------------
;;; E. BP journal generation cleanup, called by fnn-bps-open once the service
;;; holds the journal locks and has read the durable selection.

(defun fnn-spk-remove-tree (path depth)
  "Unlink PATH: a file or symlink directly, a directory after its entries.
Never follows a symlink.  DEPTH bounds the recursion (work, not data)."
  (let ((st (fnn-lstat path)))
    (cond ((null st) 0)
          ((and (fnn-directory-p st) (not (fnn-symlink-p st)))
           (when (<= depth 0) (fnn-fault "BP cleanup: directory nesting exceeds bound at ~a" path))
           (let ((n 0))
             (dolist (name (fnn-list-directory path))
               (incf n (fnn-spk-remove-tree (fnn-join path name) (1- depth))))
             (fnn-fsync-dir path)
             (sb-posix:rmdir path)
             (1+ n)))
          (t (fnn-unlink path) 1))))

(defun fnn-spk-bp-cleanup (root plan)
  "SPIKE: host-driven removal of the generation directories ACL2's plan
(fn-spk-bp-cleanup-plan) names.  Each unlink and rmdir is a crash cut; a
partial removal leaves an unselected directory the next open finishes."
  (let* ((names (fnn-list-directory root))
         (answer (fnn-core 'fn-spk-bp-cleanup-plan names plan))
         (old (first answer)) (later (second answer)) (strays (third answer))
         (removed 0) (kept nil))
    (dolist (name strays)
      (let ((p (fnn-join root name)))
        (when (fnn-check-regular p) (fnn-unlink p) (incf removed))))
    (dolist (name old)
      (incf removed (fnn-spk-remove-tree (fnn-join root name) 4)))
    (dolist (name later)
      (let ((p (fnn-join root name)))
        (if (null (fnn-list-directory p))
            (progn (sb-posix:rmdir p) (incf removed))
            (push name kept))))
    (when (or old strays later)
      (fnn-fsync-dir root)
      (fnn-out "BP journal cleanup generations=~d strays=~d removed-entries=~d kept-nonempty=~d"
               (length old) (length strays) removed (length kept)))
    removed))
