; PRF-267 / PRF-901: statement-first review, lane p-ocs-reach.
; B for both OCS properties; A for the wake. No original theorem is changed.
; The plan adds :completed-stopping and :frames-fenced to completion words.
; The old protocol embeds with no held or next batch and maps its unknown
; events to :ocs-unknown. This preserves every old action and next phase,
; decoding :sync as the old :barrier. The bridge below is over ALL old inputs.
; Only after the successor and bridge prove do the registry citations move.

(defthm fn-otm-held-plan-complete-only-after-the-barrier
  (implies (equal (mv-nth 0 (fn-otm-held-plan s event)) :complete)
           (and (equal (fn-otm-phase-of s) :staged) (equal event :fenced)))
  :rule-classes nil)

(defthm fn-otm-held-plan-in-flight-until-completed
  (implies (and (fn-ocs-in-flight-p (fn-otm-phase-of s))
                (not (member-equal event
                                   '(:completed :completed-stopping :frames-fenced))))
           (fn-ocs-in-flight-p
            (fn-otm-phase-of (mv-nth 1 (fn-otm-held-plan s event)))))
  :rule-classes nil)

; Interpretation of an old protocol event; new protocol words were invalid
; in OCS and remain invalid in the embedding, rather than acquiring meaning.
(defun fn-otm-ocs-event (event)
  (declare (xargs :guard t))
  (if (member-equal event '(:started :started-none :started-uncertain
                           :fenced :failed :completed))
      event :ocs-unknown))

(defthm fn-otm-held-plan-carries-the-whole-ocs-step
  (equal (fn-ocs-commit-step phase event)
         (let* ((s (fn-otm-with-step (fn-otm-init) phase nil nil))
                (plan (fn-otm-held-plan s (fn-otm-ocs-event event))))
           (list (if (equal (mv-nth 0 plan) :sync) :barrier (mv-nth 0 plan))
                 (fn-otm-phase-of (mv-nth 1 plan)))))
  :rule-classes nil)

; Derived using the successor plus the whole-step bridge, with the old
; theorem and step definition disabled: these are the unchanged old claims.
(defthm fn-otm-held-plan-implies-ocs-barrier-property
  (implies (equal (mv-nth 0 (fn-ocs-commit-step phase event)) :complete)
           (and (equal phase :staged) (equal event :fenced)))
  :rule-classes nil)

(defthm fn-otm-held-plan-implies-ocs-in-flight-property
  (implies (and (fn-ocs-in-flight-p phase) (not (equal event :completed)))
           (fn-ocs-in-flight-p (mv-nth 1 (fn-ocs-commit-step phase event))))
  :rule-classes nil)

; The actual hosted wake entry, rather than the plan's event entry, owns wake
; decisions. HELD batches wait; the unheld arm is the original wake exactly.
(defthm fn-otm-held-committer-wake-is-ocp-when-unheld
  (implies (not (fn-otm-held s))
           (equal (fn-ocp-committer-wake (fn-otm-ocp s) returned queued w)
                  (fn-otm-held-committer-wake s returned queued w)))
  :rule-classes nil)

; Also prove the property on BOTH arms so holding a batch cannot hide a gap.
(defthm fn-otm-held-wake-no-start-next-while-a-shut-out-class-waits
  (implies (and (fn-ocp-excluded-waits-p w)
                (<= *fn-ocp-pass-bound* (fn-ocp-passes (fn-otm-ocp s))))
           (not (equal (fn-otm-held-committer-wake s returned queued w) :start-next)))
  :rule-classes nil)
