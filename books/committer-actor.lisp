; Private committer control, using immutable values (no STATE, hons,
; memoize or protected abstract stobj). Actual native loop is its consumer.
; The inner batch driver keeps owner-queued-work's existing effect order,
; operation generations/outcomes and serialized shared-state sections.
(in-package "ACL2")

(defun fn-cmt-field (n x)
  (declare (xargs :guard t))
  (if (true-listp x) (nth (nfix n) x) nil))

(defun fn-cmt-init ()
  (declare (xargs :guard t))
  (list :idle 0 nil nil))

(defun fn-cmt-state (phase serial capture receipt)
  (declare (xargs :guard t))
  (list phase (nfix serial)
        (if (true-listp capture) capture nil)
        (if (true-listp receipt) receipt nil)))

(defun fn-cmt-invp (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 4)
       (member-equal (fn-cmt-field 0 s) '(:idle :snapshot :passing :pipeline :stopped))
       (natp (fn-cmt-field 1 s))
       (true-listp (fn-cmt-field 2 s)) (true-listp (fn-cmt-field 3 s))))

; Shared declaration of live actions for the native interpreter / HM mapper.
; A label names the actual subject, native primitive/consumer and capability.
(defconst *fn-cmt-action-declarations*
  '((:committer-observe fn-cmt-step :observation :commit-lock)
    (:committer-snapshot fn-cmt-step fnn-owner-loops-snapshot :commit-lock)
    (:committer-wait fn-cmt-step "sb-thread:condition-wait" :commit-lock)
    (:committer-pipeline fn-cmt-step fnn-owner-commit-pipeline :owner-sections)
    (:committer-return fn-cmt-step :receipt :operation-and-physical-custody)))

; Result (STATE ACTION). Snapshot has the ticket reserved by this actor;
; an observation of pass completion belongs to its retained immutable capture.
; Pipeline return carries the actual operation generation, outcome and
; physical lifecycle/custody readout, never a boolean 'completed' receipt.
(defun fn-cmt-step (s event)
  (declare (xargs :guard t))
  (let* ((phase (fn-cmt-field 0 s)) (serial (nfix (fn-cmt-field 1 s)))
         (capture (fn-cmt-field 2 s)) (receipt (fn-cmt-field 3 s))
         (tag (fn-cmt-field 0 event))
         (stop (fn-cmt-field 1 event)) (queued (fn-cmt-field 2 event))
         (passed (fn-cmt-field 3 event)))
    (cond
     ((equal phase :stopped)
      (list (fn-cmt-state :stopped serial capture receipt)
            (list :exit (if (equal (fn-cmt-field 0 receipt) :fault) :fault :ok))))
     ((and (equal tag :observe) stop)
      (list (fn-cmt-state :stopped serial capture receipt) '(:exit :ok)))
     ((and (equal phase :idle) (equal tag :observe))
      (if queued
          (list (fn-cmt-state :snapshot (+ 1 serial) nil receipt)
                (list :snapshot (+ 1 serial)))
        (list (fn-cmt-state :idle serial nil receipt) '(:wait))))
     ((and (equal phase :snapshot) (equal tag :snapshot)
           (equal (fn-cmt-field 1 event) serial)
           (true-listp (fn-cmt-field 2 event)))
      (list (fn-cmt-state :passing serial (fn-cmt-field 2 event) receipt) '(:again)))
     ((and (equal phase :passing) (equal tag :observe))
      (if passed
          (list (fn-cmt-state :pipeline serial capture receipt)
                (list :pipeline serial capture))
        (list (fn-cmt-state :passing serial capture receipt) '(:wait))))
     ((and (equal phase :pipeline) (equal tag :pipeline-returned)
           (member-equal (fn-cmt-field 2 event) '(:none :fenced :failed :fault))
           (true-listp event))
      (if (equal (fn-cmt-field 2 event) :fault)
          (list (fn-cmt-state :stopped serial capture '(:fault)) '(:exit :fault))
        (list (fn-cmt-state :idle serial nil event) '(:again))))
     (t (list (fn-cmt-state :stopped serial capture '(:fault)) '(:exit :fault))))))

(defun fn-cmt-run (s events)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-cmt-run (car (fn-cmt-step s (car events))) (cdr events))
    s))

(defun fn-cmt-pass-target (passes polling)
  (declare (xargs :guard t))
  (+ (nfix passes) (if polling 1 2)))

(defun fn-cmt-pass-ready (passes polling target)
  (declare (xargs :guard t))
  (or (>= (nfix passes) (nfix target))
      (and polling (>= (nfix passes) (- (nfix target) 1)))))

(defthm fn-cmt-init-is-valid
  (fn-cmt-invp (fn-cmt-init)))

; Normalize every input, so preservation needs no hidden shape assumption.
(defthm fn-cmt-step-state-is-valid
  (fn-cmt-invp (car (fn-cmt-step s event))))

(defthm fn-cmt-run-keeps-the-private-invariant
  (implies (fn-cmt-invp s) (fn-cmt-invp (fn-cmt-run s events))))

(defthm fn-cmt-stop-observation-never-enters-a-pipeline
  (implies (and (equal (fn-cmt-field 0 event) :observe)
                (fn-cmt-field 1 event))
           (not (equal (car (cadr (fn-cmt-step s event))) :pipeline))))

(defthm fn-cmt-pipeline-requires-its-captured-passes
  (implies (equal (car (cadr (fn-cmt-step s event))) :pipeline)
           (and (equal (fn-cmt-field 0 s) :passing)
                (equal (fn-cmt-field 0 event) :observe)
                (not (fn-cmt-field 1 event)) (fn-cmt-field 3 event)
                (equal (fn-cmt-field 1 (cadr (fn-cmt-step s event)))
                       (nfix (fn-cmt-field 1 s)))
                (equal (fn-cmt-field 2 (cadr (fn-cmt-step s event)))
                       (fn-cmt-field 2 s)))))

(defthm fn-cmt-wrong-snapshot-ticket-faults
  (implies (and (equal (fn-cmt-field 0 s) :snapshot)
                (equal (fn-cmt-field 0 event) :snapshot)
                (not (equal (fn-cmt-field 1 event) (nfix (fn-cmt-field 1 s)))))
           (equal (cadr (fn-cmt-step s event)) '(:exit :fault))))

; Reached positive schedule and explicit missing-pass / wrong-ticket teeth.
(assert-event
 (let* ((issued (car (fn-cmt-step (fn-cmt-init) '(:observe nil t nil))))
        (captured (car (fn-cmt-step issued '(:snapshot 1 ((0 2)))))))
   (and (fn-cmt-invp captured)
        (equal (cadr (fn-cmt-step captured '(:observe nil t t)))
               '(:pipeline 1 ((0 2))))
        (equal (cadr (fn-cmt-step captured '(:observe nil t nil))) '(:wait))
        (equal (cadr (fn-cmt-step captured '(:observe t t t))) '(:exit :ok))
        (equal (cadr (fn-cmt-step issued '(:snapshot 2 ((0 2))))) '(:exit :fault)))))

(in-theory (disable fn-cmt-step fn-cmt-pass-target fn-cmt-pass-ready))
