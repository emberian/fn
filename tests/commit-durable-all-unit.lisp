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

;; THE STRENGTHENED INVARIANT ON LIVE RUNS. FN2-ENV-DUR-INV (J1-J4 and the
;; evidence projection) holds after every action of the honest runs above,
;; in both barrier modes, from genesis: the positions of the actions after
;; which it fails (expected none), the run's length, and its acknowledged
;; batches (expected 1 and 2, so the acknowledging steps were checked).
(defun fn2-cda-j-trace (actions i ids rlog acked fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom actions) (mv nil acked fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (let* ((rlog (if entry (cons entry rlog) rlog))
             (acked (fn2-env-observe ids acked fn2-core))
             (ok (fn2-env-dur-inv ids acked (reverse rlog) fn2-core)))
        (mv-let (bad acked fn2-core) (fn2-cda-j-trace (cdr actions) (+ 1 i) ids rlog acked fn2-core)
          (mv (if ok bad (cons i bad)) acked fn2-core))))))
(defun fn2-cda-j-scenario (mode)
  (declare (xargs :verify-guards nil))
  (let* ((profile (fn2-cda-profile mode))
         (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600)))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             (ids (fn2-env-commit-ids profile))
             (pre (fn2-env-dur-inv ids nil nil fn2-core))
             ((mv bad acked fn2-core) (fn2-cda-j-trace actions 0 ids nil nil fn2-core)))
          (mv (list pre bad (len actions) acked) fn2-core))
        result))))
(make-event `(defconst *fn2-cda-j-honest* ',(fn2-cda-j-scenario 0)))
(make-event `(defconst *fn2-cda-j-honest-fua* ',(fn2-cda-j-scenario 1)))
(defun fn2-cda-j-positive (r)
  (declare (xargs :verify-guards nil))
  (and (nth 0 r) (null (nth 1 r)) (< 100 (nth 2 r))
       (subsetp-equal '(1 2) (nth 3 r))))
(assert-event (fn2-cda-j-positive *fn2-cda-j-honest*))
(assert-event (fn2-cda-j-positive *fn2-cda-j-honest-fua*))
;; Positive witness of FN2-ENV-DUR-TURN-PRESERVES: both honest runs keep the
;; strengthened invariant through every fn2-turn and acknowledge 1 and 2.
(defun fn2-dur-turn-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-cda-j-positive *fn2-cda-j-honest*) (fn2-cda-j-positive *fn2-cda-j-honest-fua*)))
(assert-event (fn2-dur-turn-positive))

;; J5 AND J6 ON LIVE RUNS (FN2-ENV-J5-ROWS), checked before they are proved:
;; after every action of both honest runs no row breaks them (expected nil),
;; and the runs reach every state the clauses read: each role's write queued,
;; taken, and posted unharvested, and the fence live.
(defun fn2-cda-role-state (id role fn2-core)
  ; (ROLE OP-PHASE C0-POSTED) of the role's live write, else nil
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (fn2-env-role-live id role fn2-core)
      (let ((op (fn2-env-op (nth 1 (fn2-env-role-io id role fn2-core)) fn2-core)))
        (list role (nth 2 op) (nth 13 op)))
    nil))
(defun fn2-cda-j5-trace (actions i ids rlog fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom actions) (mv nil nil fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (let* ((rlog (if entry (cons entry rlog) rlog))
             (ok (fn2-env-j5-rows ids (reverse rlog) fn2-core))
             (id (car ids))
             (seen (list (fn2-machine-phase id fn2-core)
                         (fn2-machine-cb-fence-live id fn2-core)
                         (fn2-cda-role-state id 0 fn2-core) (fn2-cda-role-state id 1 fn2-core)
                         (fn2-cda-role-state id 2 fn2-core))))
        (mv-let (bad seens fn2-core) (fn2-cda-j5-trace (cdr actions) (+ 1 i) ids rlog fn2-core)
          (mv (if ok bad (cons i bad)) (add-to-set-equal seen seens) fn2-core))))))
(defun fn2-cda-j5-scenario (mode)
  (declare (xargs :verify-guards nil))
  (let* ((profile (fn2-cda-profile mode))
         (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600)))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             (ids (fn2-env-commit-ids profile))
             (pre (fn2-env-j5-rows ids nil fn2-core))
             ((mv bad seen fn2-core) (fn2-cda-j5-trace actions 0 ids nil fn2-core)))
          (mv (list pre bad (len actions) seen) fn2-core))
        result))))
(make-event `(defconst *fn2-cda-j5-honest* ',(fn2-cda-j5-scenario 0)))
(make-event `(defconst *fn2-cda-j5-honest-fua* ',(fn2-cda-j5-scenario 1)))
(defun fn2-cda-j5-reached (seen)
  ; queued (2), taken (3), and posted (3 1) for role 0 at :dependencies and
  ; roles 1 and 2 at :log-write, and the live fence at :fence
  (declare (xargs :verify-guards nil))
  (and (member-equal '(3 0 (0 2 0) nil nil) seen) (member-equal '(3 0 (0 3 0) nil nil) seen)
       (member-equal '(3 0 (0 3 1) nil nil) seen)
       (member-equal (list 4 0 nil '(1 2 0) nil) seen) (member-equal (list 4 0 nil '(1 3 1) nil) seen)
       (member-equal (list 4 0 nil nil '(2 2 0)) seen) (member-equal (list 4 0 nil nil '(2 3 1)) seen)
       (member-equal '(5 1 nil nil nil) seen)))
(defun fn2-cda-j5-positive (r)
  (declare (xargs :verify-guards nil))
  (and (nth 0 r) (null (nth 1 r)) (< 100 (nth 2 r)) (fn2-cda-j5-reached (nth 3 r))))
(assert-event (fn2-cda-j5-positive *fn2-cda-j5-honest*))
(assert-event (fn2-cda-j5-positive *fn2-cda-j5-honest-fua*))

;; J6L AND J6S ON LIVE RUNS: after every action of both honest runs each
;; row's roles hold three pool rows at their units' generations, and a live
;; role's row is leased out, in a write phase or settling (expected nil: no
;; action breaks it).
(defun fn2-cda-j6l-trace (actions i ids rlog fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom actions) (mv nil fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (let ((rlog (if entry (cons entry rlog) rlog)) (ok (and (fn2-env-j6l-rows ids fn2-core) (fn2-env-j6s-rows ids fn2-core))))
        (mv-let (bad fn2-core) (fn2-cda-j6l-trace (cdr actions) (+ 1 i) ids rlog fn2-core)
          (mv (if ok bad (cons i bad)) fn2-core))))))
(defun fn2-cda-j6l-scenario (mode)
  (declare (xargs :verify-guards nil))
  (let* ((profile (fn2-cda-profile mode))
         (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600)))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv bad fn2-core) (fn2-cda-j6l-trace actions 0 (fn2-env-commit-ids profile) nil fn2-core)))
          (mv (list (len actions) bad) fn2-core))
        result))))
(assert-event (let ((r (fn2-cda-j6l-scenario 0))) (and (< 100 (car r)) (null (cadr r)))))
(assert-event (let ((r (fn2-cda-j6l-scenario 1))) (and (< 100 (car r)) (null (cadr r)))))

;; THE J5 CONTROL: what J5 carries that FN2-ENV-DUR-INV does not. Stop the
;; mode-0 run when the first row's role-0 write is posted and unharvested,
;; and cut one octet from that write's take in the log (a device log whose
;; take is not the 4096 octets the core submitted). Both logs satisfy
;; FN2-ENV-DUR-INV (nothing is counted yet); only the honest one satisfies
;; J5. One fn2-turn harvests and counts the write: the honest log still
;; satisfies FN2-ENV-DUR-INV, the cut one breaks J3 (the counted write is no
;; done write in full). Result: (dur-honest j5-honest dur-cut j5-cut done
;; dur-honest-after dur-cut-after), expected (t t t nil 1 t nil).
(defun fn2-cda-cut-take (slot gen log)
  (declare (xargs :verify-guards nil))
  (if (atom log) nil
    (cons (let ((e (car log)))
            (if (and (fn2-dev-takep e) (equal (nth 1 e) slot) (equal (nth 2 e) gen))
                (update-nth 6 (cdr (nth 6 e)) e)
              e))
          (fn2-cda-cut-take slot gen (cdr log)))))
(defun fn2-cda-role-posted (id role fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-role-live id role fn2-core)
       (let ((op (fn2-env-op (nth 1 (fn2-env-role-io id role fn2-core)) fn2-core)))
         (and (equal (nth 2 op) *fn2-op-phase-submitted*) (equal (nth 13 op) 1)))))
(defun fn2-cda-j5-control-trace (actions ids rlog acked fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom actions) (mv nil fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (let* ((rlog (if entry (cons entry rlog) rlog))
             (acked (fn2-env-observe ids acked fn2-core))
             (id (car ids)))
        (if (and (equal (fn2-machine-phase id fn2-core) *fn2-commit-state-dependencies*)
                 (fn2-cda-role-posted id 0 fn2-core))
            (b* ((log (reverse rlog))
                 (io (fn2-env-role-io id 0 fn2-core))
                 (cut (fn2-cda-cut-take (nth 1 io) (nth 2 io) log))
                 (pre (list (fn2-env-dur-inv ids acked log fn2-core) (fn2-env-j5-rows ids log fn2-core)
                            (fn2-env-dur-inv ids acked cut fn2-core) (fn2-env-j5-rows ids cut fn2-core)))
                 ((mv & fn2-core) (fn2-env-step '(:turn) nil nil rlog fn2-core))
                 (acked (fn2-env-observe ids acked fn2-core)))
              (mv (append pre (list (fn2-machine-cb-done id fn2-core)
                                    (fn2-env-dur-inv ids acked log fn2-core) (fn2-env-dur-inv ids acked cut fn2-core)))
                  fn2-core))
          (fn2-cda-j5-control-trace (cdr actions) ids rlog acked fn2-core))))))
(defun fn2-cda-j5-control (mode)
  (declare (xargs :verify-guards nil))
  (let* ((profile (fn2-cda-profile mode))
         (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600)))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv r fn2-core) (fn2-cda-j5-control-trace actions (fn2-env-commit-ids profile) nil nil fn2-core)))
          (mv r fn2-core))
        result))))
(make-event `(defconst *fn2-cda-j5-control* ',(fn2-cda-j5-control 0)))
(defun fn2-cda-j5-removal ()
  (declare (xargs :verify-guards nil))
  (equal *fn2-cda-j5-control* '(t t t nil 1 t nil)))
(assert-event (fn2-cda-j5-removal))
;; THE RELEASE-CELL CONTROL (J5's one-terminal-cell clause): stop the
;; same run at the same point. A host post on the write's release cell
;; (cell 1) is refused, since a write may not release, and J5 still holds;
;; the core with that cell set by hand breaks J5. Result: (j5 j5-after-post
;; cell-1-still-clear j5-cell-set), expected (t t t nil).
(defun fn2-cda-set-c1 (s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
    (if (fn2-op-slotp s fn2-ops) (fn2-ops-put s (c1-posted 1)) fn2-ops)
    fn2-core))
(defun fn2-cda-j5-c1-trace (actions ids rlog fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom actions) (mv nil fn2-core)
    (mv-let (entry fn2-core) (fn2-env-step (car actions) nil nil rlog fn2-core)
      (let* ((rlog (if entry (cons entry rlog) rlog)) (id (car ids)))
        (if (and (equal (fn2-machine-phase id fn2-core) *fn2-commit-state-dependencies*)
                 (fn2-cda-role-posted id 0 fn2-core))
            (b* ((log (reverse rlog))
                 (io (fn2-env-role-io id 0 fn2-core))
                 (j5 (fn2-env-j5-rows ids log fn2-core))
                 ((mv entry fn2-core)
                  (fn2-env-step (list :post-result 1 (nth 1 io) (nth 2 io) *fn2-event-write-result* 0 0 4096 0 0)
                                nil nil rlog fn2-core))
                 (log (if entry (append log (list entry)) log))
                 (j5-post (fn2-env-j5-rows ids log fn2-core))
                 (clear (equal (nth 19 (fn2-env-op (nth 1 io) fn2-core)) 0))
                 (fn2-core (fn2-cda-set-c1 (nth 1 io) fn2-core)))
              (mv (list j5 j5-post clear (fn2-env-j5-rows ids log fn2-core)) fn2-core))
          (fn2-cda-j5-c1-trace (cdr actions) ids rlog fn2-core))))))
(defun fn2-cda-j5-c1-control (mode)
  (declare (xargs :verify-guards nil))
  (let* ((profile (fn2-cda-profile mode))
         (actions (fn2-cda-run-actions profile (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode)) 600)))
    (with-local-stobj fn2-core
      (mv-let (result fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv r fn2-core) (fn2-cda-j5-c1-trace actions (fn2-env-commit-ids profile) nil fn2-core)))
          (mv r fn2-core))
        result))))
(make-event `(defconst *fn2-cda-j5-c1-control* ',(fn2-cda-j5-c1-control 0)))
(assert-event (equal *fn2-cda-j5-c1-control* '(t t t nil)))
