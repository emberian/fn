;;; F1 private developer-image hook. Never load into a live node.
;;; E (default): hold BEFORE the Nth fnn-extent-cache-store after ARM.
;;; W: hold BEFORE the Nth cache-eligible fnn-extent-window-release.
;;; RELEASE ends the hold; SECONDS bounds it, including harness failure.
;;; Keep every caller lock: NEVER unlock the owner or extent mutex here.
;;; No publication/reuse witness means NOT-MEASURED, never a pass.
(in-package "ACL2")
(defvar *fnl-f1-lock* (sb-thread:make-mutex :name "load-f1"))
(defvar *fnl-f1-holding* nil)
(defvar *fnl-f1-calls* 0)
(defvar *fnl-f1-installs* 0)
(defvar *fnl-f1-drops* 0)
(defvar *fnl-f1-evictions* 0)
(defvar *fnl-f1-reuses* 0)
(defvar *fnl-f1-vacancies* 0)
(defvar *fnl-f1-pool* :unobserved)
(defun fnl-f1-write (path format-string &rest args)
  (let ((*print-pretty* nil))
    (with-open-file (s path :direction :output :if-exists :append :if-does-not-exist :create)
      (apply #'format s format-string args)
      (finish-output s))))
(defun fnl-f1-hold (route boundary token eligible arm release witness nth seconds thunk)
  (let ((hold nil) (counts nil) (triggered nil))
    (sb-thread:with-mutex (*fnl-f1-lock*)
      (when (and eligible (probe-file arm) (= nth (incf *fnl-f1-calls*)))
        (setq hold t *fnl-f1-holding* t)
        (fnl-f1-write witness "held ~a ~a ~d~%token ~a ~s~%"
                      route boundary *fnl-f1-calls* route token)))
    (when hold
      (unwind-protect
          (let ((end (+ (get-internal-real-time) (* seconds internal-time-units-per-second))))
            (setq triggered
                  (loop
                    (when (>= (get-internal-real-time) end) (return nil))
                    (when (probe-file release) (return t))
                    (sleep 0.01))))
        (sb-thread:with-mutex (*fnl-f1-lock*)
          ;; Close the interval BEFORE the held call installs/evicts anything.
          (setq *fnl-f1-holding* nil
                counts (list *fnl-f1-installs* *fnl-f1-drops*
                             *fnl-f1-evictions* *fnl-f1-reuses*)))))
    (multiple-value-prog1 (funcall thunk)
      (when hold
        (sb-thread:with-mutex (*fnl-f1-lock*)
          (apply #'fnl-f1-write witness "~a ~a ~a ~d ~d ~d ~d~%"
                 (if triggered "released" "timeout") route boundary counts))))))
(let* ((arm (sb-ext:posix-getenv "FN_LOAD_F1_ARM"))
       (release (sb-ext:posix-getenv "FN_LOAD_F1_RELEASE"))
       (witness (sb-ext:posix-getenv "FN_LOAD_F1_WITNESS"))
       (route (or (sb-ext:posix-getenv "FN_LOAD_F1_ROUTE") "E"))
       (nth (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_N") "1")))
       (seconds (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_SECONDS") "180")))
       (cache (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_F1_CACHE") "1")))
       (entryp (equal route "E")))
  (when arm
    (unless (and release witness (member route '("E" "W") :test #'equal)
                 (plusp nth) (plusp seconds) (plusp cache))
      (error "F1 requires route E/W, release/witness paths and positive bounds"))
    (dolist (sym (append '(fnn-extent-cache-drop-files fnn-extent-cache-limit)
                         (if entryp '(fnn-extent-cache-store fnn-extent-cache-forget)
                           '(fnn-extent-window-release fnn-extent-window-cache-insert
                             fnn-extent-pool-funded-p))))
      (unless (fboundp sym) (error "F1 missing boundary ~a" sym)))
    ;; Restrict the experiment, never enlarge ACL2's allowance (including zero).
    (sb-int:encapsulate 'fnn-extent-cache-limit 'fn-load-f1
      (lambda (original) (min cache (funcall original))))
    (sb-int:encapsulate 'fnn-extent-cache-drop-files 'fn-load-f1
      (lambda (original files)
        (multiple-value-prog1 (funcall original files)
          (sb-thread:with-mutex (*fnl-f1-lock*)
            (when *fnl-f1-holding* (incf *fnl-f1-drops*))))))
    (if entryp
        (progn
          ;; FORGET receives actual removed entries. Offline entries have NIL
          ;; tokens: counting only returned tokens would miss their eviction.
          (sb-int:encapsulate 'fnn-extent-cache-forget 'fn-load-f1
            (lambda (original entries)
              (multiple-value-prog1 (funcall original entries)
                (sb-thread:with-mutex (*fnl-f1-lock*)
                  (when *fnl-f1-holding*
                    (incf *fnl-f1-evictions* (length entries))
                    (incf *fnl-f1-vacancies* (length entries)))))))
          (sb-int:encapsulate 'fnn-extent-cache-store 'fn-load-f1
            (lambda (original file eoff elen trailer octets &optional token)
              (fnl-f1-hold route "fnn-extent-cache-store" token t
                arm release witness nth seconds
                (lambda ()
                  (multiple-value-bind (keptp evicted)
                      (funcall original file eoff elen trailer octets token)
                    (sb-thread:with-mutex (*fnl-f1-lock*)
                      (when (and *fnl-f1-holding* keptp)
                        (incf *fnl-f1-installs*)
                        (when (plusp *fnl-f1-vacancies*)
                          (decf *fnl-f1-vacancies*)
                          (incf *fnl-f1-reuses*))))
                    (values keptp evicted)))))))
      (progn
        ;; Observe the actual image's route decision; do not force a pool mode.
        (sb-int:encapsulate 'fnn-extent-pool-funded-p 'fn-load-f1
          (lambda (original)
            (let ((funded (funcall original)))
              (sb-thread:with-mutex (*fnl-f1-lock*)
                (when (and (probe-file arm) (not (eql funded *fnl-f1-pool*)))
                  (setq *fnl-f1-pool* funded)
                  (fnl-f1-write witness "pool W ~a~%" (if funded "funded" "unfunded"))))
              funded)))
        (sb-int:encapsulate 'fnn-extent-window-cache-insert 'fn-load-f1
          (lambda (original token plan window)
            (let ((evicted (funcall original token plan window)))
              (sb-thread:with-mutex (*fnl-f1-lock*)
                (when *fnl-f1-holding*
                  (incf *fnl-f1-installs*)
                  (incf *fnl-f1-evictions* (length evicted))
                  ;; This insert replaced an occupied cache position.
                  (when evicted (incf *fnl-f1-reuses*))))
              evicted)))
        (sb-int:encapsulate 'fnn-extent-window-release 'fn-load-f1
          (lambda (original worker token &optional cachep)
            (fnl-f1-hold route "fnn-extent-window-release" token
              (and cachep (plusp (fnn-extent-cache-limit)))
              arm release witness nth seconds
              (lambda () (funcall original worker token cachep)))))))))
