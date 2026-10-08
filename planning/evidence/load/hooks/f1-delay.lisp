;;; F1 private developer-image hook. Never load into a live node.
;;; Hold the Nth cache-eligible fnn-extent-window-release after ARM exists.
;;; RELEASE ends the hold; SECONDS bounds it, including harness failure.
;;; The owner may hold its mutex here: never unlock it or fabricate a release
;;; receipt. No publication/reuse witness means NOT MEASURED, not a pass.
(in-package "ACL2")
(defvar *fnl-f1-lock* (sb-thread:make-mutex :name "load-f1"))
(defvar *fnl-f1-holding* nil)
(defvar *fnl-f1-calls* 0)
(defvar *fnl-f1-installs* 0)
(defvar *fnl-f1-drops* 0)
(defvar *fnl-f1-evictions* 0)
(defvar *fnl-f1-xc* 0)
(defun fnl-f1-write (path format-string &rest args)
  (with-open-file (s path :direction :output :if-exists :append :if-does-not-exist :create)
    (apply #'format s format-string args)
    (finish-output s)))
(let ((arm (sb-ext:posix-getenv "FN_LOAD_F1_ARM"))
      (release (sb-ext:posix-getenv "FN_LOAD_F1_RELEASE"))
      (witness (sb-ext:posix-getenv "FN_LOAD_F1_WITNESS"))
      (nth (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_N") "1")))
      (seconds (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_SECONDS") "180")))
      (cache (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_CACHE") "1"))))
  (when arm
    (unless (and release witness (plusp nth) (plusp seconds) (plusp cache))
      (error "F1 requires release/witness paths and positive bounds"))
    (dolist (sym '(fnn-extent-window-release fnn-extent-window-cache-insert
                   fnn-extent-cache-drop-files fnn-extent-cache-limit))
      (unless (fboundp sym) (error "F1 missing boundary ~a" sym)))
    ;; Restrict this experiment's cache, without enlarging ACL2's allowance.
    (sb-int:encapsulate 'fnn-extent-cache-limit 'fn-load-f1
      (lambda (original) (min cache (funcall original))))
    ;; This tree uses the window-cache insertion boundary, not fn-xc-install.
    ;; Count real returned eviction tokens, not just calls into an empty cache.
    (sb-int:encapsulate 'fnn-extent-window-cache-insert 'fn-load-f1
      (lambda (original &rest args)
        (let ((evicted (apply original args)))
          (sb-thread:with-mutex (*fnl-f1-lock*)
            (when *fnl-f1-holding*
              (incf *fnl-f1-installs*)
              (incf *fnl-f1-evictions* (length evicted))))
          evicted)))
    (sb-int:encapsulate 'fnn-extent-cache-drop-files 'fn-load-f1
      (lambda (original &rest args)
        (multiple-value-prog1 (apply original args)
          (sb-thread:with-mutex (*fnl-f1-lock*)
            (when *fnl-f1-holding* (incf *fnl-f1-drops*))))))
    (if (fboundp 'fn-xc-install)
        (sb-int:encapsulate 'fn-xc-install 'fn-load-f1
          (lambda (original &rest args)
            (multiple-value-prog1 (apply original args)
              (sb-thread:with-mutex (*fnl-f1-lock*)
                (when *fnl-f1-holding* (incf *fnl-f1-xc*))))))
      (fnl-f1-write witness "fn-xc-install unavailable; using window-cache evictions~%"))
    (sb-int:encapsulate 'fnn-extent-window-release 'fn-load-f1
      (lambda (original worker token &optional cachep)
        (let ((hold nil) (counts nil) (triggered nil))
          (sb-thread:with-mutex (*fnl-f1-lock*)
            (when (and cachep (probe-file arm) (= nth (incf *fnl-f1-calls*)))
              (setq hold t *fnl-f1-holding* t)
              (fnl-f1-write witness "held~%")))
          (when hold
            (unwind-protect
                (let ((end (+ (get-internal-real-time) (* seconds internal-time-units-per-second))))
                  (loop until (or (probe-file release) (>= (get-internal-real-time) end))
                        do (sleep 0.01))
                  (setq triggered (and (probe-file release) t)))
              (sb-thread:with-mutex (*fnl-f1-lock*)
                (setq *fnl-f1-holding* nil
                      counts (list *fnl-f1-installs* *fnl-f1-drops* *fnl-f1-evictions* *fnl-f1-xc*)))))
          (multiple-value-prog1 (funcall original worker token cachep)
            (when hold
              (apply #'fnl-f1-write witness
                     (if triggered "released ~d ~d ~d ~d~%" "timeout ~d ~d ~d ~d~%") counts))))))))
