; Teeth of FN2-COMMIT-ACK-IMPLIES-RECOVERABLE: concrete devices in place of
; FN2-A-CRASH-IMAGE, every action through fn2-env-run / fn2-env-recover.
(in-package "ACL2")
(include-book "../books/commit-durable-all")

; B's commit profile (sim/commit-history.lisp's fn2-b-test-profile of tiny):
; a 4096-octet pool class, sixteen sectors of five extents, MODE's barrier.
(defun fn2-cda-profile (mode)
  (declare (xargs :verify-guards nil))
  (let* ((p *fn2-profile-tiny*)
         (p (put-assoc-equal :sim-sectors 16 p))
         (p (put-assoc-equal :extent-slots 5 p))
         (p (put-assoc-equal :pool-classes (append (fn2-profile-pool-classes p) '((8 . 4096))) p)))
    (put-assoc-equal :commit-barrier-mode mode p)))

; The storage takes in the newest-first RLOG with no answer newer than them.
(defun fn2-cda-unanswered (rlog newer)
  (declare (xargs :verify-guards nil))
  (cond ((atom rlog) nil)
        ((and (fn2-dev-takep (car rlog))
              (member-equal (nth 3 (car rlog)) (list *fn2-action-write* *fn2-action-fence* *fn2-action-read*))
              (not (fn2-dev-answer (nth 1 (car rlog)) (nth 2 (car rlog)) newer)))
         (cons (car rlog) (fn2-cda-unanswered (cdr rlog) (append newer (list (car rlog))))))
        (t (fn2-cda-unanswered (cdr rlog) (append newer (list (car rlog)))))))

; The honest device's answer for take entry E: done, every octet moved.
(defun fn2-cda-answer (e)
  (declare (xargs :verify-guards nil))
  (let* ((kind (nth 3 e))
         (len (cond ((equal kind *fn2-action-fence*) 0) (t (len (nth 6 e))))))
    (mv-let (outcome reason count aux0 aux1) (fn2-host-result kind :ok len 0 len nil)
      (list :post-result 0 (nth 1 e) (nth 2 e) (fn2-terminal-event kind)
            outcome reason count aux0 aux1))))

; The scheduler: take whatever the outbox holds, answer the oldest storage
; operation honestly, else turn. (mv actions rlog fn2-core), ACTIONS in order.
(defun fn2-cda-auto (fuel recoveryp image actions rlog fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv (reverse actions) rlog fn2-core)
    (let* ((pending (fn2-cda-unanswered rlog nil))
           (action (cond ((< 0 (fn2-host-outbox-queued fn2-core)) '(:take))
                         ((consp pending) (fn2-cda-answer (car (last pending))))
                         (t '(:turn)))))
      (mv-let (entry fn2-core) (fn2-env-step action recoveryp image rlog fn2-core)
        (fn2-cda-auto (- fuel 1) recoveryp image (cons action actions)
                      (if entry (cons entry rlog) rlog) fn2-core)))))

(defun fn2-cda-run-actions (profile prefix fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (actions fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv & & fn2-core) (fn2-env-steps prefix (fn2-env-commit-ids profile) nil nil fn2-core))
           ((mv actions & fn2-core) (fn2-cda-auto fuel nil nil nil nil fn2-core)))
        (mv (append prefix actions) fn2-core))
      actions)))
(defun fn2-cda-recovery-actions (profile image fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (actions fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :null nil fn2-core))
           ((mv & fn2-core) (fn2-recovery-start (fn2-env-recovery-id profile)
                                                *fn2-env-recovery-assume* 0 fn2-core))
           ((mv actions & fn2-core) (fn2-cda-auto fuel t image nil nil fn2-core)))
        (mv actions fn2-core))
      actions)))

; The honest device: every write answered done, applied in answer order.
(defun fn2-cda-completed-image (log seen image)
  (declare (xargs :verify-guards nil))
  (if (atom log) image
    (let ((e (car log)))
      (fn2-cda-completed-image
       (cdr log) (cons e seen)
       (if (and (fn2-dev-resultp e) (equal (nth 3 e) *fn2-dev-write-result*)
                (equal (nth 4 e) *fn2-dev-done*))
           (let ((take (fn2-env-taken (nth 1 e) (nth 2 e) seen)))
             (if take (cons (fn2-dev-segment take) image) image))
         image)))))
; IMAGE as A-FENCE-PERSISTS admits it: every fenced write kept.
(defun fn2-cda-admitted-p (w log image)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-dev-fenced-write-p fn2-dev-image-keeps-p)))))
  (if (or (not (natp w)) (>= w (len log))) t
    (and (or (not (fn2-dev-fenced-write-p w log)) (fn2-dev-image-keeps-p w log image))
         (fn2-cda-admitted-p (+ 1 w) log image))))
(defun fn2-cda-last-fenced (w log best)
  (declare (xargs :verify-guards nil :measure (nfix (- (len log) (nfix w)))
                  :hints (("Goal" :in-theory (disable fn2-dev-fenced-write-p)))))
  (if (or (not (natp w)) (>= w (len log))) best
    (fn2-cda-last-fenced (+ 1 w) log (if (fn2-dev-fenced-write-p w log) w best))))
; The lying device: the honest image without write W's segment.
(defun fn2-cda-drop (seg image)
  (declare (xargs :verify-guards nil))
  (if (atom image) nil
    (if (equal (car image) seg) (fn2-cda-drop seg (cdr image))
      (cons (car image) (fn2-cda-drop seg (cdr image))))))

(defun fn2-cda-scenario (mode lie)
  (declare (xargs :verify-guards nil))
  (b* ((profile (fn2-cda-profile mode))
       (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600))
       (run (fn2-env-run profile actions))
       (log (fn2-env-device-log run))
       (honest (fn2-cda-completed-image log nil nil))
       (w (fn2-cda-last-fenced 0 log nil))
       (image (if (and lie w) (fn2-cda-drop (fn2-dev-segment (nth w log)) honest) honest))
       (rec (fn2-env-recover profile image (fn2-cda-recovery-actions profile image 4000))))
    (list (fn2-env-acknowledged-batches run) (fn2-env-recovery-done-p rec)
          (fn2-env-recovered-batches rec) (fn2-cda-admitted-p 0 log image) w (len log)
          (fn2-env-image-holds-prefix-p 2 log image))))

;; RESULT: (acknowledged done recovered admitted last-fenced log-length
;; holds-batches-1-2).
;; Positive: two admitted batches, the honest device (every write answered
;; done, applied in answer order); A-FENCE-PERSISTS admits its image;
;; acknowledged (1 2) and recovered (1 2).
; Each scenario runs once (a make-event: the run calls attachments, which a
; defconst may not); the teeth read its result.
(make-event `(defconst *fn2-cda-honest* ',(fn2-cda-scenario 0 nil)))
(make-event `(defconst *fn2-cda-honest-fua* ',(fn2-cda-scenario 1 nil)))
(make-event `(defconst *fn2-cda-lying* ',(fn2-cda-scenario 0 t)))
(defun fn2-cda-positive (r)
  (declare (xargs :verify-guards nil))
  (let ((r r))
    (and (subsetp-equal (nth 0 r) '(1 2)) (subsetp-equal '(1 2) (nth 0 r))
         (nth 1 r) (equal (nth 2 r) '(1 2)) (nth 3 r))))
(defun fn2-commit-recoverable-positive ()
  (declare (xargs :verify-guards nil))
  (fn2-cda-positive *fn2-cda-honest*))
(defun fn2-commit-recoverable-positive-fua ()
  (declare (xargs :verify-guards nil))
  (fn2-cda-positive *fn2-cda-honest-fua*))
;; Fence removal: the same run, a device that loses the last fenced write
;; (the lying flush). Its image is outside A-FENCE-PERSISTS, both batches
;; were acknowledged, and recovery reports only batch 1: without the
;; assumption the statement is false.
(defun fn2-commit-recoverable-fence-removal ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-cda-lying*))
    (and (subsetp-equal (nth 0 r) '(1 2)) (subsetp-equal '(1 2) (nth 0 r))
         (nth 1 r) (equal (nth 2 r) '(1)) (not (nth 3 r)))))

;; FN2-RECOVERY-CHAIN-COMPLETE. Positive: the honest image holds batches 1
;; and 2 of the run's log and recovery reports both. Hypothesis removal: the
;; image without batch 2's seal does not hold batch 2, and recovery reports
;; (1): the chain bound needs the held batches.
(defun fn2-recovery-complete-positive ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-cda-honest*))
    (and (nth 6 r) (nth 1 r) (subsetp-equal '(1 2) (nth 2 r)))))
(defun fn2-recovery-complete-held-removal ()
  (declare (xargs :verify-guards nil))
  (let ((r *fn2-cda-lying*))
    (and (not (nth 6 r)) (nth 1 r) (equal (nth 2 r) '(1)))))

(assert-event (fn2-commit-recoverable-positive))
(assert-event (fn2-commit-recoverable-positive-fua))
(assert-event (fn2-commit-recoverable-fence-removal))
(assert-event (fn2-recovery-complete-positive))
(assert-event (fn2-recovery-complete-held-removal))
