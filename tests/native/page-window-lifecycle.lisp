; Trusted native test driver, to be loaded only into a matching developer
; image. NOT run by the source gate. The caller first installs one fresh,
; admitted complete supported profile, prewarms roster21, starts its actual
; executor, registers actual fixture files and supplies core descriptors.
; This file neither invents funding nor installs a second/reentrant service.
(in-package "ACL2")


; Trusted test callbacks only; disabled does not evaluate observation fields.
; Caller retains an external journal; no callback establishes funding or join.
(defvar *fnn-test-window-observer* nil)
(defmacro fnn-test-window-note (event &rest fields)
  `(when *fnn-test-window-observer*
     (funcall *fnn-test-window-observer* ,event (list ,@fields))))
(defmacro fnn-test-window-answer (event form expected &rest fields)
  `(let ((answer ,form))
     (fnn-test-window-note ,event :answer answer ,@fields)
     (assert (eq answer ,expected))
     nil))

(defun fnn-test-window-await (worker)
  (let ((until (+ (get-internal-real-time) (* 30 internal-time-units-per-second))))
    (loop until (fnn-extent-executor-returned-p worker) do
      (when (> (get-internal-real-time) until) (error "window test actual return timed out"))
      (fnn-extent-executor-wait worker 0.05)))
  (fnn-test-window-note :worker-returned
    :worker-row (copy-list (fnn-cold-worker-row worker))
    :returned-p t :thread-alive-p (sb-thread:thread-alive-p (fnn-cold-worker-thread worker))
    :join-observation :unobserved)
  nil)

(defun fnn-test-window-file-held (file)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-test-window-answer :file-held
      (fnn-core 'fn-prl-close-preview
        (fnn-core 'fn-owner-page-read-ledger (fnn-live-page-read-pool)) file)
      :read-file-held :file file)))

(defun fnn-test-window-publication (descriptor payload-i expected-byte)
  (multiple-value-bind (token word worker) (fnn-extent-issue-window descriptor)
    (assert (eq word :admitted))
    (fnn-test-window-note :issued :token token :answer word
      :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-await worker)
    (destructuring-bind (file eoff elen poff plen offset trailer) descriptor
      (declare (ignore offset))
      (fnn-test-window-file-held file)
      (multiple-value-bind (answer byte)
          (fnn-extent-window-byte-at worker token file eoff elen poff plen trailer payload-i)
        (assert (eq answer :byte)) (assert (eql byte expected-byte))
        (fnn-test-window-note :scalar-published :token token :answer answer :byte byte))
      ;; The scalar activation above has returned. No window/vector alias is
      ;; retained by this driver; file ownership still persists until release.
      (fnn-test-window-file-held file))
    (fnn-test-window-answer :released (fnn-extent-window-release worker token) :released
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-answer :release-stale (fnn-extent-window-release worker token) :stale-job
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    :passed))

(defun fnn-test-window-cancel-after-return (descriptor payload-i)
  (multiple-value-bind (token word worker) (fnn-extent-issue-window descriptor)
    (assert (eq word :admitted))
    (fnn-test-window-note :issued :token token :answer word
      :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-await worker)
    (fnn-test-window-answer :publication-ready (fnn-extent-window-outcome worker token) :ready
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-answer :cancelled (fnn-extent-window-cancel worker token) :cancelled
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-answer :publication-cancelled (fnn-extent-window-outcome worker token) :cancelled
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (destructuring-bind (file eoff elen poff plen offset trailer) descriptor
      (declare (ignore offset))
      (fnn-test-window-file-held file)
      (multiple-value-bind (answer byte)
          (fnn-extent-window-byte-at worker token file eoff elen poff plen trailer payload-i)
        (assert (eq answer :cancelled)) (assert (null byte))
        (fnn-test-window-note :revoked-publication-refused :token token :answer answer :byte byte)))
    (fnn-test-window-answer :release-stale (fnn-extent-window-release worker token) :stale-job
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-answer :cancelled-settled (fnn-extent-window-settle-cancelled worker token) :released
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    (fnn-test-window-answer :settlement-stale (fnn-extent-window-settle-cancelled worker token) :stale-job
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
    :passed))

(defun fnn-test-window-cancel-held (worker token file release-device)
  ; The caller observed WINDOW-IO held for this exact actual issued token.
  ; RELEASE-DEVICE is trusted test code releasing the existing device gate.
  (assert (not (fnn-extent-executor-returned-p worker)))
  (fnn-test-window-note :worker-still-held :token token :returned-p nil
    :worker-row (copy-list (fnn-cold-worker-row worker)))
  (fnn-test-window-answer :cancelled (fnn-extent-window-cancel worker token) :cancelled
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
  (fnn-test-window-file-held file)
  (fnn-test-window-answer :settlement-stale (fnn-extent-window-settle-cancelled worker token) :stale-job
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
  (funcall release-device)
  (fnn-test-window-await worker)
  (fnn-test-window-answer :publication-cancelled (fnn-extent-window-outcome worker token) :cancelled
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
  (fnn-test-window-file-held file)
  (fnn-test-window-answer :cancelled-settled (fnn-extent-window-settle-cancelled worker token) :released
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
  (fnn-test-window-answer :settlement-stale (fnn-extent-window-settle-cancelled worker token) :stale-job
      :token token :worker-row (copy-list (fnn-cold-worker-row worker)))
  :passed)

(defun fnn-test-window-current-relocation (owner-lock view h i expected-byte reseat)
  ; H/I come from the fixture's captured provider row. RESEAT performs the
  ; actual guard-verified faithful reseat under the same owner mutex.
  (multiple-value-bind (word byte token0 worker0)
      (sb-thread:with-mutex (owner-lock)
        (fnn-extent-window-current-acquire view h i))
    (declare (ignore byte))
    (assert (eq word :admitted))
    (fnn-test-window-note :issued :token token0 :answer word
      :worker-row (copy-list (fnn-cold-worker-row worker0)))
    (fnn-test-window-await worker0)
    (sb-thread:with-mutex (owner-lock) (funcall reseat))
    (multiple-value-bind (word byte token1 worker1)
        (sb-thread:with-mutex (owner-lock)
          (fnn-extent-window-current-acquire view h i))
      (declare (ignore byte))
      (assert (eq word :admitted))
      (fnn-test-window-note :issued :token token1 :answer word
        :worker-row (copy-list (fnn-cold-worker-row worker1)))
      (assert (not (equal token0 token1)))
      (fnn-test-window-await worker1)
      (dolist (pair (list (cons token0 worker0) (cons token1 worker1)))
        (let ((token (car pair)) (worker (cdr pair)))
          (destructuring-bind (file eoff elen poff plen offset trailer) (cddr token)
            (declare (ignore offset))
            (fnn-test-window-file-held file)
            (multiple-value-bind (answer byte)
                (fnn-extent-window-byte-at worker token file eoff elen poff plen trailer i)
              (assert (eq answer :byte)) (assert (eql byte expected-byte))
              (fnn-test-window-note :scalar-published :token token :answer answer :byte byte)))))
      (fnn-test-window-answer :released (fnn-extent-window-release worker0 token0) :released
        :token token0 :worker-row (copy-list (fnn-cold-worker-row worker0)))
      (fnn-test-window-file-held (third token1))
      (fnn-test-window-answer :released (fnn-extent-window-release worker1 token1) :released
        :token token1 :worker-row (copy-list (fnn-cold-worker-row worker1)))
      (assert (sb-thread:with-mutex (owner-lock)
                (fnn-snapshot-payload-view-live-p view)))
      :passed)))
