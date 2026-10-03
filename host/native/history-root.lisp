;;; Live P3 history authority. Each candidate is private through row ticks,
;;; indexing and adoption. The owner alone chooses generations, credit and
;;; frontier agreement; the host carries the corresponding physical handle.
(in-package "ACL2")
(defvar *fnn-history-roots* (make-hash-table :test 'eql))

(defun fnn-owner-history-root-release (service generation)
  (when generation
    (let ((word (fnn-owner-gated (service :control)
                  (fnn-owner-core 'fn-owner-hroot-retire generation))))
      (when (eq word :released) (remhash generation *fnn-history-roots*)))))

(defun fnn-owner-history-root-fund (service generation amount)
  (let ((word (fnn-owner-gated (service :control)
                (first (fnn-call 'fn-owner-hroot-resize generation amount *the-live-state*)))))
    (unless (eq word :funded)
      (fnn-refuse-io "live history root allocation refused: ~a" word))))

(defun fnn-owner-history-root-row (service generation ev ordinal stage)
  (fnn-owner-history-root-fund service generation
                              (fnn-core 'fn-hroot-event-demand ev ordinal stage))
  (let ((answer (fnn-call 'fn-his-row-begin ev stage)))
    (loop
      (destructuring-bind (verdict cursor &rest ignored) answer
        (declare (ignore ignored))
        (when (eq verdict :done) (return t))
        (let ((grow (and (consp verdict) (eq (car verdict) :grow-image))))
          (unless (or (eq verdict :yield) grow)
            (fnn-refuse-io "live history root row refused: ~a" verdict))
          (fnn-checkpoint-yield "live-history-pages" ordinal)
          (sb-thread:thread-yield)
          (when grow
            (fnn-owner-history-root-fund service generation
              (fnn-core 'fn-hroot-grow-demand (second cursor) ordinal stage)))
          (setq answer (fnn-call (if grow 'fn-his-row-grow 'fn-his-row-step) cursor stage)))))))

(defun fnn-owner-history-root-refresh (service)
  "Build from exact installed events, never checkpoint-canonical handles.
Refusal leaves the installed history intact. A same-count rewrite changes
ACL2's source incarnation and refuses the candidate before installation."
  (let ((generation nil) (stage nil) (candidate nil) (installed nil)
        (source-incarnation nil) (ordinal 0))
    (unwind-protect
        (progn
          (let ((word (fnn-owner-gated (service :control)
                        (fnn-owner-core 'fn-owner-hroot-begin))))
            (unless (and (consp word) (eq (first word) :building))
              (return-from fnn-owner-history-root-refresh word))
            (setq generation (second word)
                  source-incarnation
                  (fourth (fnn-owner-gated (service :control)
                            (fnn-owner-core 'fn-owner-hroot-frontier-value)))))
          ;; The generation grant precedes both private creators.
          (setq stage (fnn-core 'create-fn-hrecs$s)
                candidate (fnn-core 'create-fn-hist$p))
          (fnn-call 'fn-his-build-begin
                    (fnn-owner-gated (service :control)
                      (fnn-owner-core 'fn-owner-orcp-salt)) stage)
          (loop
            (let ((row (fnn-owner-gated (service :control)
                         (fnn-owner-core 'fn-owner-hroot-row ordinal source-incarnation))))
              (case (first row)
                (:event (fnn-owner-history-root-row service generation (second row) ordinal stage)
                        (incf ordinal))
                (:done (return))
                (otherwise (fnn-refuse-io "live history source refused: ~a" row)))))
          (fnn-owner-history-root-fund service generation (fnn-core 'fn-hroot-retain-demand stage))
          (destructuring-bind (empty root &rest ignored)
              (fnn-call 'fn-hist$p-adopt-stage generation stage candidate)
            (declare (ignore ignored))
            (setq stage empty candidate root))
          (loop for index from 0 do
            (fnn-checkpoint-yield "live-history-index" index)
            (destructuring-bind (verdict amount &rest ignored)
                (fnn-call 'fn-hroot-index-demand index candidate)
              (declare (ignore ignored))
              (unless (eq verdict :ok) (fnn-refuse-io "history index demand refused: ~a" verdict))
              (fnn-owner-history-root-fund service generation amount))
            (let ((word (first (fnn-call 'fn-hist$p-root-index-next index candidate))))
              (when (eq word :done) (return))
              (unless (eq word :yield) (fnn-refuse-io "live history index refused: ~a" word))))
          (fnn-owner-history-root-fund service generation (fnn-core 'fn-hroot-root-retain-demand candidate))
          ;; An append during construction becomes this root's ordinary tail.
          ;; Done + frontier decision + pointer install share one owner quantum.
          (loop
            (let ((row nil) (old nil))
              (fnn-owner-gated (service :control)
                (setq row (fnn-owner-core 'fn-owner-hroot-row ordinal source-incarnation))
                (when (eq (first row) :done)
                  (let ((word (fnn-owner-core 'fn-owner-hroot-activate generation ordinal (second row))))
                    (unless (and (consp word) (eq (first word) :installed))
                      (fnn-refuse-io "live history installation refused: ~a" word))
                    (setq old (third word))
                    (setf (gethash generation *fnn-history-roots*) candidate)
                    (fnn-install-history-root candidate)
                    (setq installed t))))
              (when installed
                (fnn-owner-history-root-release service old)
                (return (list :installed generation)))
              (unless (eq (first row) :event) (fnn-refuse-io "live history catchup refused: ~a" row))
              (fnn-owner-history-root-fund service generation
                (fnn-core 'fn-hroot-tail-demand (second row) ordinal candidate))
              (fnn-call 'fn-hist$p-append (second row) candidate)
              (incf ordinal)
              (fnn-checkpoint-yield "live-history-tail" ordinal))))
      (when stage (fnn-call 'fn-his-release stage))
      (when (and generation (not installed))
        (fnn-owner-gated (service :control)
          (fnn-owner-core 'fn-owner-hroot-abandon generation))))))

(defun fnn-install-history-root (root)
  ;; Only the successful same-quantum ACL2 activation reaches this installer.
  (let ((cell (assoc 'fn-hist (user-stobj-alist *the-live-state*))))
    (unless cell (fnn-fault "history authority missing from image"))
    (setf (cdr cell) root)
    (setq *fnn-hist* root)))

(defun fnn-owner-history-root-pin (service)
  "Return (SOURCE PHYSICAL) under the owner gate; SOURCE is ACL2-owned."
  (fnn-owner-gated (service :control)
    (let* ((physical (fnn-live-hist))
           (generation (fnn-core 'fn-hist$p-root-generation physical))
           (source (fnn-owner-core 'fn-owner-hroot-pin-funded generation)))
      (when (and (consp source) (eq (first source) :history-root))
        (list source physical)))))

(defun fnn-owner-history-root-at (service pin ordinal)
  (let ((plan (fnn-owner-gated (service :control)
                (fnn-owner-core 'fn-owner-hroot-read-plan (first pin) ordinal))))
    (unless (and (consp plan) (eq (first plan) :read))
      (fnn-refuse-io "history source read refused: ~a" plan))
    (let ((retained (fnn-owner-gated (service :control)
                      (fnn-owner-core 'fn-owner-hroot-read-owned (first pin)))))
      (destructuring-bind (verdict amount &rest ignored)
          (fnn-call 'fn-hroot-read-demand (third plan) retained (second pin))
        (declare (ignore ignored))
        (unless (eq verdict :ok) (fnn-refuse-io "history read demand refused: ~a" verdict))
        (let ((word (fnn-owner-gated (service :control)
                      (fnn-owner-core 'fn-owner-hroot-read-fund (first pin) amount))))
          (unless (eq word :funded) (fnn-refuse-io "history decode credit refused: ~a" word)))))
    (let ((row (fnn-core 'fn-hist$p-read (third plan) (second pin))))
      (unless (eq (first row) :ok) (fnn-refuse-io "history row refused: ~a" row))
      (second row))))

(defun fnn-owner-history-root-unpin (service pin)
  ;; Discard physical custody before returning its lease. Cancellation does
  ;; not call this until the actual consuming walk has reached its cleanup.
  (let ((source (first pin)))
    (setf (second pin) nil)
    (let ((word (fnn-owner-gated (service :control)
                  (fnn-owner-core 'fn-owner-hroot-return source))))
      (unless (eq word :returned) (fnn-fault "history source return refused: ~a" word)))
    (fnn-owner-history-root-release service (third source))))

(defun fnn-history-root-pin-held ()
  (let* ((physical (fnn-live-hist))
         (generation (fnn-core 'fn-hist$p-root-generation physical))
         (source (fnn-owner-core 'fn-owner-hroot-pin-funded generation)))
    (when (and (consp source) (eq (first source) :history-root))
      (list source physical))))

(defun fnn-owner-history-root-maintain (service)
  (let ((*fnn-checkpoint-stop-test*
          (lambda () (fnn-owner-service-stopping service))))
    (handler-case (fnn-owner-history-root-refresh service)
      (fnn-store-io-refusal (e)
        (fnn-err "HISTORY root retained current representation: ~a" e)
        :refused))))

(defun fnn-owner-history-root-chunk-return (service pin)
  (let ((word (fnn-owner-gated (service :control)
                (fnn-owner-core 'fn-owner-hroot-read-fund (first pin) 0))))
    (unless (eq word :funded) (fnn-fault "history chunk credit return refused: ~a" word))))
