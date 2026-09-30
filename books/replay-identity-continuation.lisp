; Selected snapshot constructors for a retained replay continuation.
; No execution capability is issued here. SELECTED is obtained only from the
; same captured ORIGINAL context through the existing one-cell RSC machine.
(in-package "ACL2")
(include-book "replay-snapshot-cursor")
(include-book "replay-produced-evidence")

(defun fn-rpx-apply-selected-snapshot (ctx e selected)
  (declare (xargs :guard t))
  (cond
   ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
   ((not (fn-stxk-p e)) (fn-stxk-fault ctx :malformed-snapshot))
   ((not (equal (fn-stxk-sequence e) (fn-stxk-context-next ctx)))
    (fn-stxk-fault ctx :sequence))
   (t
    (let ((old selected))
      (cond
       ((and old (not (fn-stxk-same-snapshotp old e)))
        (fn-stxk-fault ctx :conflicting-keyring-generation))
       (old
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (fn-stxk-context-snapshots ctx)
                         (fn-stxk-context-verdicts ctx)
                         (fn-stxk-context-current-generation ctx) nil))
       ((and (natp (fn-stxk-context-current-generation ctx))
             (not (equal (fn-stxk-keyring-generation e)
                         (1+ (fn-stxk-context-current-generation ctx)))))
        (fn-stxk-fault ctx :keyring-generation-order))
       (t
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (cons e (fn-stxk-context-snapshots ctx))
                         (fn-stxk-context-verdicts ctx)
                         (fn-stxk-keyring-generation e) nil)))))))

(defun fn-rpx-apply-selected-verdict (ctx e selected)
  (declare (xargs :guard t))
  (cond
   ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
   ((not (fn-stxe-p e)) (fn-stxk-fault ctx :malformed-verdict))
   ((not (equal (fn-stxe-sequence e) (fn-stxk-context-next ctx)))
    (fn-stxk-fault ctx :sequence))
   (t
    (let ((snapshot
           selected))
      (cond
       ((not snapshot)
        (fn-stxk-fault ctx :missing-keyring-generation))
       ((not (equal (fn-stxe-keyring-profile (fn-stxe-profile e))
                    (fn-stxk-profile snapshot)))
        (fn-stxk-fault ctx :keyring-profile-mismatch))
       (t
        (fn-stxk-context :ok (1+ (fn-stxk-context-next ctx))
                         (fn-stxk-context-snapshots ctx)
                         (cons e (fn-stxk-context-verdicts ctx))
                         (fn-stxk-context-current-generation ctx) nil)))))))


(defthm fn-rpx-selected-snapshot-has-complete-public-result
 (equal (fn-rpx-apply-selected-snapshot
         ctx e (fn-stxk-find (fn-stxk-keyring-generation e)
                            (fn-stxk-context-snapshots ctx)))
        (fn-stxk-apply-snapshot ctx e))
 :hints (("Goal" :in-theory
  (e/d (fn-rpx-apply-selected-snapshot fn-stxk-apply-snapshot)
       (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp
        fn-stxk-context fn-stxk-fault)))))
(defthm fn-rpx-selected-verdict-has-complete-public-result
 (equal (fn-rpx-apply-selected-verdict
         ctx e (fn-stxk-find (fn-stxe-keyring-generation e)
                            (fn-stxk-context-snapshots ctx)))
        (fn-stxk-apply-verdict ctx e))
 :hints (("Goal" :in-theory
  (e/d (fn-rpx-apply-selected-verdict fn-stxk-apply-verdict)
       (fn-stxe-p fn-stxk-find fn-stxe-keyring-profile
        fn-stxk-context fn-stxk-fault)))))

; Eight fixed fields: phase, ORIGINALctx, original event, captured source,
; wire event, retained evidence, one-cell selector, completed four-result.
(defun fn-rpx-state (phase ctx event source wire evidence selector result)
 (declare (xargs :guard t))
 (list phase ctx event source wire evidence selector result))
(defun fn-rpx-complete (ctx event source wire evidence checked effect child sizes)
 (declare (xargs :guard t))
 (fn-rpx-state :done ctx event source wire evidence nil
               (list checked effect child sizes)))
(defun fn-rpx-verdict-result (checked child sizes)
 (declare (xargs :guard t))
 (mv-let (ctx effect value lengths) (fn-rpe-verdict-effect checked child sizes)
  (list ctx effect value lengths)))
(defun fn-rpx-begin (ctx event source)
 (declare (xargs :guard t :verify-guards nil))
 (cond
  ((not (equal (fn-stxk-context-kind ctx) :ok))
   (fn-rpx-complete ctx event source nil nil ctx :none nil nil))
  ((not (equal (fn-store-event-sequence event) (fn-stxk-context-next ctx)))
   (fn-rpx-complete ctx event source nil nil
                    (fn-stxk-fault ctx :sequence) :none nil nil))
  (t
   (let ((wire (fn-replay-identity-wire event)))
    (cond
     ((fn-stxk-p wire)
      (fn-rpx-state :snapshot ctx event source wire nil
       (fn-rsc-begin (fn-stxk-keyring-generation wire)
                     (fn-stxk-context-snapshots ctx) source) nil))
     ((fn-stxe-p wire)
      (fn-rpx-state :verdict ctx event source wire nil
       (fn-rsc-begin (fn-stxe-keyring-generation wire)
                     (fn-stxk-context-snapshots ctx) source) nil))
     ((not (fn-stxa-p wire))
      (fn-rpx-complete ctx event source wire nil
                       (fn-replay-identity-advance ctx) :none nil nil))
     (t
      (let* ((evidence (fn-rpe-produce wire))
             (child (fn-stmt-value (fn-rpe-result evidence)))
             (sizes (fn-rpe-lengths evidence)))
       (cond
        ((fn-rpe-carried-bindsp evidence)
         (fn-rpx-state :done ctx event source wire evidence nil
          (fn-rpx-verdict-result (fn-replay-apply-carried-verdict ctx child)
                                 child sizes)))
        ((fn-rpe-revoked-bindsp evidence)
         (fn-rpx-state :done ctx event source wire evidence nil
          (fn-rpx-verdict-result
           (fn-replay-apply-revoked-verdict
            ctx child (fn-hsig-article-event-carrier-keys wire)) child sizes)))
        (t
         (fn-rpx-state :composite-snapshot ctx event source wire evidence
          (fn-rsc-begin (fn-stxa-keyring-generation wire)
                        (fn-stxk-context-snapshots ctx) source) nil))))))))))
(defun fn-rpx-step (s)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-rsc-widthp 8 s)) (mv :refused s)
  (let* ((phase (fn-rsc-at 0 s)) (ctx (fn-rsc-at 1 s))
         (event (fn-rsc-at 2 s)) (source (fn-rsc-at 3 s))
         (wire (fn-rsc-at 4 s)) (evidence (fn-rsc-at 5 s)))
   (cond
    ((eq phase :done) (mv :done s))
    ((not (member-eq phase '(:snapshot :verdict :composite-snapshot :composite-verdict)))
     (mv :refused s))
    (t
     (mv-let (status selector) (fn-rsc-step (fn-rsc-at 6 s))
      (cond
       ((not (eq status :done))
        (mv status (fn-rpx-state phase ctx event source wire evidence selector nil)))
       ((eq phase :snapshot)
        (let* ((checked (fn-rpx-apply-selected-snapshot ctx wire (fn-rsc-at 3 selector)))
               (changed (not (equal (fn-stxk-context-current-generation checked)
                                    (fn-stxk-context-current-generation ctx)))))
         (mv :done (fn-rpx-complete ctx event source wire evidence checked
                     (if changed :snapshot :none) (if changed wire nil) nil))))
       ((eq phase :verdict)
        (let ((checked (fn-rpx-apply-selected-verdict ctx wire (fn-rsc-at 3 selector))))
         (mv :done
          (fn-rpx-complete ctx event source wire evidence
           (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
            (fn-stxk-context :ok (fn-stxk-context-next checked)
             (fn-stxk-context-snapshots checked) (fn-stxk-context-verdicts ctx)
             (fn-stxk-context-current-generation checked) nil)) :none nil nil))))
       ((eq phase :composite-verdict)
        (let ((child (fn-stmt-value (fn-rpe-result evidence))))
         (mv :done (fn-rpx-state :done ctx event source wire evidence nil
          (fn-rpx-verdict-result
           (fn-rpx-apply-selected-verdict ctx child (fn-rsc-at 3 selector))
           child (fn-rpe-lengths evidence))))))
       (t
        (let ((snapshot (fn-rsc-at 3 selector)))
         (cond
          ((or (not (fn-rpe-stxa-bindsp evidence)) (not snapshot)
               (not (fn-rpe-snapshot-bindsp evidence snapshot)))
           (mv :done (fn-rpx-complete ctx event source wire evidence
                       (fn-stxk-fault ctx :composite-binding) :none nil nil)))
          ((not (fn-stmt-okp (fn-rpe-result evidence)))
           (mv :done (fn-rpx-complete ctx event source wire evidence
                       (fn-stxk-fault ctx :composite-verdict) :none nil nil)))
          (t
           ; Child generation may differ on arbitrary calls. Preserve the
           ; public second lookup with another one-cell continuation.
           (mv :working
            (fn-rpx-state :composite-verdict ctx event source wire evidence
             (fn-rsc-begin
              (fn-stxe-keyring-generation (fn-stmt-value (fn-rpe-result evidence)))
              (fn-stxk-context-snapshots ctx) source) nil)))))))))))))

; Logical selected-value relation. This carries the old retained-state search
; meaning through pending state; it is never a runtime readiness validator.
(defun fn-rpx-selected-relationp (s)
 (declare (xargs :guard t))
 (let* ((phase (fn-rsc-at 0 s)) (ctx (fn-rsc-at 1 s))
        (wire (fn-rsc-at 4 s)) (evidence (fn-rsc-at 5 s))
        (selector (fn-rsc-at 6 s)))
  (and (fn-rsc-widthp 8 s)
   (if (eq phase :done) t
    (and (member-eq phase '(:snapshot :verdict :composite-snapshot :composite-verdict))
         (fn-rsc-invariantp selector)
         (equal (fn-rsc-at 4 selector) (fn-rsc-at 3 s))
         (equal (fn-rsc-abstract selector)
          (fn-stxk-find
           (cond ((eq phase :snapshot) (fn-stxk-keyring-generation wire))
                 ((eq phase :verdict) (fn-stxe-keyring-generation wire))
                 ((eq phase :composite-snapshot) (fn-stxa-keyring-generation wire))
                 (t (fn-stxe-keyring-generation
                     (fn-stmt-value (fn-rpe-result evidence)))))
           (fn-stxk-context-snapshots ctx))))))))

; Four-result readout only. The current-slot wrapper must independently check
; the actual token/epoch/predecessor and retain BASE through uncertainty.
(defun fn-rpx-readout (s)
 (declare (xargs :guard t))
 (if (and (fn-rsc-widthp 8 s) (eq (fn-rsc-at 0 s) :done)
          (fn-rsc-widthp 4 (fn-rsc-at 7 s)))
  (mv :done (fn-rsc-at 7 s)) (mv :working nil)))
(verify-guards fn-rpx-begin
 :hints (("Goal" :in-theory
  (disable fn-rpe-produce fn-rpe-result fn-rpe-lengths fn-rpe-carried-bindsp
           fn-rpe-revoked-bindsp fn-rpx-state fn-rpx-complete
           fn-rpx-verdict-result fn-rsc-begin))))
(verify-guards fn-rpx-step
 :hints (("Goal" :in-theory
  (disable fn-rsc-step fn-rsc-at fn-rsc-widthp fn-rpx-state fn-rpx-complete
           fn-rpx-verdict-result fn-rpe-result fn-rpe-lengths
           fn-rpe-stxa-bindsp fn-rpe-snapshot-bindsp
           fn-rpx-apply-selected-snapshot fn-rpx-apply-selected-verdict
           fn-rsc-begin))))

; Proof abstraction for every in-progress phase. Only this logical abstraction
; uses FN-STXK-FIND; execution advances the already captured selector instead.
(defun fn-rpx-outcome (s)
 (declare (xargs :guard t))
 (let* ((phase (fn-rsc-at 0 s)) (ctx (fn-rsc-at 1 s))
        (wire (fn-rsc-at 4 s)) (evidence (fn-rsc-at 5 s))
        (selected (fn-rsc-abstract (fn-rsc-at 6 s))))
  (cond
   ((eq phase :done) (fn-rsc-at 7 s))
   ((eq phase :snapshot)
    (let* ((checked (fn-rpx-apply-selected-snapshot ctx wire selected))
           (changed (not (equal (fn-stxk-context-current-generation checked)
                                (fn-stxk-context-current-generation ctx)))))
     (list checked (if changed :snapshot :none) (if changed wire nil) nil)))
   ((eq phase :verdict)
    (let ((checked (fn-rpx-apply-selected-verdict ctx wire selected)))
     (list (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
            (fn-stxk-context :ok (fn-stxk-context-next checked)
             (fn-stxk-context-snapshots checked) (fn-stxk-context-verdicts ctx)
             (fn-stxk-context-current-generation checked) nil)) :none nil nil)))
   ((eq phase :composite-verdict)
    (let ((child (fn-stmt-value (fn-rpe-result evidence))))
     (fn-rpx-verdict-result (fn-rpx-apply-selected-verdict ctx child selected)
                            child (fn-rpe-lengths evidence))))
   ((eq phase :composite-snapshot)
    (cond
     ((or (not (fn-rpe-stxa-bindsp evidence)) (not selected)
          (not (fn-rpe-snapshot-bindsp evidence selected)))
      (list (fn-stxk-fault ctx :composite-binding) :none nil nil))
     ((not (fn-stmt-okp (fn-rpe-result evidence)))
      (list (fn-stxk-fault ctx :composite-verdict) :none nil nil))
     (t
      (let ((child (fn-stmt-value (fn-rpe-result evidence))))
       (fn-rpx-verdict-result
        (fn-rpx-apply-selected-verdict ctx child
         (fn-stxk-find (fn-stxe-keyring-generation child)
                       (fn-stxk-context-snapshots ctx)))
        child (fn-rpe-lengths evidence))))))
   (t nil))))
(defthm fn-rpx-begin-has-complete-produced-result
 (equal (fn-rpx-outcome (fn-rpx-begin ctx event source))
        (mv-let (checked effect child sizes) (fn-rpe-produced-effects ctx event)
         (list checked effect child sizes)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rpx-outcome fn-rpx-begin fn-rpx-complete fn-rpx-state
         fn-rpx-verdict-result fn-rsc-begin fn-rsc-at fn-rsc-abstract
         fn-rpe-produced-effects)
       (fn-rpe-produce fn-rpe-result fn-rpe-lengths fn-rpe-stxa-bindsp
        fn-rpe-snapshot-bindsp fn-rpe-carried-bindsp fn-rpe-revoked-bindsp
        fn-rpe-verdict-effect fn-stxk-apply-snapshot fn-stxk-apply-verdict
        fn-rpx-apply-selected-snapshot fn-rpx-apply-selected-verdict
        fn-stxk-find fn-stxk-context fn-stxk-fault
        fn-stxk-context-snapshots fn-stxk-context-verdicts
        fn-stxk-context-current-generation fn-stxk-context-next
        fn-stxk-context-kind fn-replay-identity-wire fn-store-event-sequence
        fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-keyring-generation
        fn-stxe-keyring-generation fn-stxa-keyring-generation)))))
(local (defthm fn-rpx-selector-step-status
 (implies (fn-rsc-invariantp selector)
  (and (member-eq (mv-nth 0 (fn-rsc-step selector)) '(:working :done))
       (implies (eq (mv-nth 0 (fn-rsc-step selector)) :done)
        (equal (fn-rsc-abstract (mv-nth 1 (fn-rsc-step selector)))
               (fn-rsc-at 3 (mv-nth 1 (fn-rsc-step selector)))))))
 :hints (("Goal" :in-theory
  (e/d (fn-rsc-invariantp fn-rsc-step fn-rsc-abstract fn-rsc-at fn-rsc-widthp)
       (fn-rsc-typed-snapshotsp fn-stxk-keyring-generation))))))
(local (defthm fn-rpx-selector-begin-meaning
 (equal (fn-rsc-abstract (fn-rsc-begin generation snapshots source))
        (fn-stxk-find generation snapshots))
 :hints (("Goal" :in-theory (enable fn-rsc-abstract fn-rsc-begin fn-rsc-at)))))
(defthm fn-rpx-one-step-preserves-complete-outcome
 (implies (and (fn-rsc-widthp 8 s)
               (member-eq (fn-rsc-at 0 s)
                          '(:snapshot :verdict :composite-snapshot :composite-verdict))
               (fn-rsc-invariantp (fn-rsc-at 6 s)))
  (equal (fn-rpx-outcome (mv-nth 1 (fn-rpx-step s)))
         (fn-rpx-outcome s)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rsc-step-preserves-actual-selected-snapshot
                   (cursor (fn-rsc-at 6 s)))
        (:instance fn-rpx-selector-step-status (selector (fn-rsc-at 6 s))))
  :in-theory
  (e/d (fn-rpx-step fn-rpx-outcome fn-rpx-state fn-rpx-complete
         fn-rsc-at)
       (fn-rsc-begin fn-rpx-selector-step-status fn-rsc-abstract fn-rsc-step fn-rsc-invariantp fn-rsc-widthp
        fn-rpe-result fn-rpe-lengths fn-rpe-stxa-bindsp fn-rpe-snapshot-bindsp
        fn-rpx-verdict-result fn-rpx-apply-selected-snapshot
        fn-rpx-apply-selected-verdict fn-stxk-find fn-stxk-context
        fn-stxk-fault fn-stxk-context-kind fn-stxk-context-next
        fn-stxk-context-snapshots fn-stxk-context-verdicts
        fn-stxk-context-current-generation fn-stxe-keyring-generation)))))
(defun fn-rpx-invariantp (s)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 8 s)
      (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots (fn-rsc-at 1 s)))
      (if (eq (fn-rsc-at 0 s) :done) (fn-rsc-widthp 4 (fn-rsc-at 7 s))
       (and (member-eq (fn-rsc-at 0 s)
                      '(:snapshot :verdict :composite-snapshot :composite-verdict))
            (fn-rsc-invariantp (fn-rsc-at 6 s))
            (equal (fn-rsc-at 4 (fn-rsc-at 6 s)) (fn-rsc-at 3 s))))))
(local (defthm fn-rpx-begin-selector-invariant
 (implies (fn-rsc-typed-snapshotsp snapshots)
          (fn-rsc-invariantp (fn-rsc-begin generation snapshots source)))
 :hints (("Goal" :in-theory
  (enable fn-rsc-invariantp fn-rsc-begin fn-rsc-at fn-rsc-widthp)))))
(local (defthm fn-rpx-selector-begin-source
 (equal (fn-rsc-at 4 (fn-rsc-begin generation snapshots source)) source)
 :hints (("Goal" :in-theory (enable fn-rsc-begin fn-rsc-at)))))
(local (defthm fn-rpx-selector-preserves-source
 (equal (fn-rsc-at 4 (mv-nth 1 (fn-rsc-step selector)))
        (fn-rsc-at 4 selector))
 :hints (("Goal" :in-theory
  (e/d (fn-rsc-step fn-rsc-at fn-rsc-widthp)
       (fn-stxk-keyring-generation))))))
(defthm fn-rpx-begin-establishes-owned-invariant
 (implies (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
          (fn-rpx-invariantp (fn-rpx-begin ctx event source)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rpx-invariantp fn-rpx-begin fn-rpx-state fn-rpx-complete
         fn-rpx-verdict-result fn-rsc-widthp fn-rsc-at fn-rpe-verdict-effect
         fn-rsc-invariantp fn-rsc-begin)
       (fn-rsc-typed-snapshotsp
        fn-rpe-produce fn-rpe-result fn-rpe-lengths fn-rpe-carried-bindsp
        fn-rpe-revoked-bindsp fn-stxk-context-snapshots
        fn-stxk-context-kind fn-stxk-context-next fn-replay-identity-wire
        fn-store-event-sequence fn-stxk-p fn-stxe-p fn-stxa-p
        fn-stxk-keyring-generation fn-stxe-keyring-generation
        fn-stxa-keyring-generation fn-replay-apply-carried-verdict
        fn-replay-apply-revoked-verdict)))))
(defthm fn-rpx-step-preserves-owned-invariant
 (implies (fn-rpx-invariantp s)
          (fn-rpx-invariantp (mv-nth 1 (fn-rpx-step s))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rsc-step-preserves-actual-selected-snapshot
                   (cursor (fn-rsc-at 6 s))))
  :in-theory
  (e/d (fn-rpx-invariantp fn-rpx-step fn-rpx-state fn-rpx-complete
         fn-rpx-verdict-result fn-rpe-verdict-effect fn-rsc-at fn-rsc-widthp)
       (fn-rsc-step fn-rsc-invariantp fn-rsc-begin fn-rsc-typed-snapshotsp
        fn-rpe-result fn-rpe-lengths fn-rpe-stxa-bindsp fn-rpe-snapshot-bindsp
        fn-rpx-apply-selected-snapshot fn-rpx-apply-selected-verdict
        fn-stxk-context-kind fn-stxk-context-next fn-stxk-context-snapshots
        fn-stxk-context-verdicts fn-stxk-context-current-generation)))))
(local (defthm fn-rpx-done-step-is-idempotent
 (implies (and (fn-rsc-widthp 8 s) (eq (fn-rsc-at 0 s) :done))
          (equal (mv-nth 1 (fn-rpx-step s)) s))
 :hints (("Goal" :in-theory (e/d (fn-rpx-step) (fn-rsc-at fn-rsc-widthp))))))
(local (defthm fn-rpx-step-invariant-rewrite
 (implies (fn-rpx-invariantp s)
          (fn-rpx-invariantp (mv-nth 1 (fn-rpx-step s))))
 :hints (("Goal" :use fn-rpx-step-preserves-owned-invariant))))
(local (defthm fn-rpx-step-outcome-rewrite
 (implies (fn-rpx-invariantp s)
  (equal (fn-rpx-outcome (mv-nth 1 (fn-rpx-step s))) (fn-rpx-outcome s)))
 :hints (("Goal" :use fn-rpx-one-step-preserves-complete-outcome
  :in-theory (e/d (fn-rpx-invariantp)
                 (fn-rpx-step fn-rpx-outcome fn-rsc-at fn-rsc-widthp)))
         ("Subgoal 1" :in-theory
          (e/d (fn-rpx-step fn-rpx-outcome)
               (fn-rsc-at fn-rsc-widthp))))))
; Arbitrary fuel partition is a proof driver, never a served callback.
(defun fn-rpx-run (fuel s)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (eq (fn-rsc-at 0 s) :done)) s
  (mv-let (word next) (fn-rpx-step s)
   (declare (ignore word)) (fn-rpx-run (1- fuel) next))))
(defthm fn-rpx-run-preserves-owned-result
 (implies (fn-rpx-invariantp s)
  (and (fn-rpx-invariantp (fn-rpx-run fuel s))
       (equal (fn-rpx-outcome (fn-rpx-run fuel s)) (fn-rpx-outcome s))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-rpx-run fuel s)
  :in-theory (e/d (fn-rpx-run)
                 (fn-rpx-invariantp fn-rpx-outcome fn-rpx-step fn-rsc-at)))))
(local (defthm fn-rpx-done-outcome-is-readout
 (implies (eq (fn-rsc-at 0 s) :done)
          (equal (fn-rpx-outcome s) (fn-rsc-at 7 s)))
 :hints (("Goal" :in-theory (e/d (fn-rpx-outcome) (fn-rsc-at))))))
(defthm fn-rpx-completed-continuation-has-whole-public-result
 (implies
  (and (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
       (eq (fn-rsc-at 0 (fn-rpx-run fuel (fn-rpx-begin ctx event source))) :done))
  (equal (fn-rsc-at 7 (fn-rpx-run fuel (fn-rpx-begin ctx event source)))
         (mv-let (checked effect child sizes) (fn-rpe-produced-effects ctx event)
          (list checked effect child sizes))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rpx-begin-establishes-owned-invariant)
        (:instance fn-rpx-begin-has-complete-produced-result)
        (:instance fn-rpx-run-preserves-owned-result
                   (s (fn-rpx-begin ctx event source))))
  :in-theory
  (e/d ()
       (fn-rpx-outcome fn-rpx-run fn-rpx-begin fn-rpx-step fn-rpe-produced-effects
        fn-rpx-invariantp fn-rsc-at fn-rsc-typed-snapshotsp)))))
