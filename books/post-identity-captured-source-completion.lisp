; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Completed paid source byte trace at the actual controller effect boundary.
(in-package "ACL2")
(include-book "post-identity-captured-source-trace")
(local (defthm fn-pic-sf-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-sf-second-slot
 (equal (nth 1 x) (cadr x)) :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-pic-sf-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) p incoming held)
   (fn-psc-model-byte-run b (fn-psc-model-byte-run a p incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a p incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-model-demanded-byte nth len))))))
(local (defthm fn-pic-sf-run-successor
 (implies (natp ticks)
  (equal (fn-psc-model-byte-run (+ 1 ticks) origin incoming held)
   (fn-psc-step (fn-psc-model-byte-run ticks origin incoming held)
    (fn-psc-model-demanded-byte (fn-psc-model-byte-run ticks origin incoming held) incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-pic-sf-run-addition (a ticks) (b 1) (p origin))
  :expand ((:free (p) (fn-psc-model-byte-run 1 p incoming held))
           (:free (p) (fn-psc-model-byte-run 0 p incoming held)))
  :in-theory (disable fn-psc-model-byte-run fn-pic-sf-run-addition fn-psc-step fn-psc-model-demanded-byte nth len)))))
(local (defthm fn-pic-sf-incoming-byte-is-model-byte
 (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
               (equal (fn-pic-at 0 (fn-pic-demand c)) :incoming))
  (equal (fn-pic-observed-byte (fn-pic-demand c)
          (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
           (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))
         (fn-psc-model-demanded-byte (fn-pic-parser c) fn-octets held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-demand fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
  (fn-pic-parser fn-psc-demand fn-octets-get len update-nth))))))
(local (defthm fn-pic-sf-control-byte-is-model-byte
 (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
               (equal (fn-pic-demand c) :control))
  (equal (fn-pic-observed-byte (fn-pic-demand c) :control)
         (fn-psc-model-demanded-byte (fn-pic-parser c) fn-octets held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-demand fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
  (fn-pic-parser fn-psc-demand len update-nth))))))
(defthm fn-pic-next-incoming-source-completion-is-paid-effect
 (let* ((d (mv-nth 1 (fn-pic-next c fuel fn-octets)))
        (p (fn-psc-model-byte-run (+ 1 ticks) origin fn-octets held))
        (r (fn-psc-result p))
        (e (fn-pic-set incoming-desc (fn-pic-source-result r (fn-pic-get incoming-n c))
                        (fn-pic-set parser p c))))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (equal (fn-pic-get phase c) :source-incoming)
                (member-eq (fn-pic-get phase d) '(:source-held :magic)))
   (and (not (equal r :pending))
        (equal d (if (< (nfix (fn-pic-get held-n c)) *fn-rcl-tombstone-fixed*)
                     (fn-pic-start-parser :source-held :source-held e)
                   (fn-pic-set phase :magic (fn-pic-set pos 0 e)))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-sf-incoming-byte-is-model-byte fn-pic-sf-control-byte-is-model-byte)
 :in-theory (e/d (fn-pic-source-tracep fn-pic-next fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-parser)
  (fn-pic-source-continuationp fn-pic-start-parser fn-psc-step fn-psc-result fn-psc-done-result-is-stored
   fn-psc-model-byte-run fn-pic-sf-incoming-byte-is-model-byte fn-pic-sf-control-byte-is-model-byte
   fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result fn-psc-model-demanded-byte
   fn-pic-at fn-pic-sf-second-slot fn-octets-get nth len update-nth)))))

(local (defthm fn-pic-sf-trace-source-phase
 (implies (fn-pic-source-tracep c ticks origin incoming held)
  (member-eq (fn-pic-get phase c) '(:source-incoming :source-held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-tracep fn-pic-source-continuationp)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-psc-source-contextp fn-psc-source-resumep
   fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-parser
   fn-psc-model-byte-run fn-pic-at nth len update-nth))))))
(local (defthm fn-pic-sf-start-phase
 (equal (nth 0 (fn-pic-start-parser mode phase c)) phase)
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser) (fn-psc-begin fn-pic-at nth update-nth))))))
(defthm fn-pic-funded-source-completion-is-paid-compare-effect
 (let* ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel)))
        (p (fn-psc-model-byte-run (+ 1 ticks) origin incoming held))
        (r (fn-psc-result p)))
  (implies (and (fn-pic-source-tracep c ticks origin incoming held)
                (equal (fn-pic-observed-byte (fn-pic-demand c) observation)
                       (fn-psc-model-demanded-byte (fn-pic-parser c) incoming held))
                (or (equal (fn-pic-get phase d) :compare-incoming)
                    (and (equal (fn-pic-get phase d) :done)
                         (equal (fn-pic-get result d) :conflict))))
   (and (not (equal r :pending))
        (equal d (fn-pic-compare-start
                  (fn-pic-set held-desc (fn-pic-source-result r (fn-pic-get held-n c))
                   (fn-pic-set parser p c)))))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-sf-trace-source-phase
  :in-theory (e/d
  (fn-pic-source-tracep fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-parser)
  (fn-pic-source-continuationp fn-pic-start-parser fn-pic-compare-start fn-psc-step fn-psc-result
   fn-psc-done-result-is-stored fn-psc-model-byte-run fn-pic-demand fn-pic-observation-okp
   fn-pic-observed-byte fn-pic-source-result fn-psc-model-demanded-byte fn-pic-at
   fn-pic-sf-second-slot nth len update-nth)))))

(defthm fn-pic-next-source-completion-is-paid-compare-effect
 (let* ((d (mv-nth 1 (fn-pic-next c fuel fn-octets)))
        (p (fn-psc-model-byte-run (+ 1 ticks) origin fn-octets held))
        (r (fn-psc-result p)))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (or (equal (fn-pic-get phase d) :compare-incoming)
                    (and (equal (fn-pic-get phase d) :done)
                         (equal (fn-pic-get result d) :conflict))))
   (and (not (equal r :pending))
        (equal d (fn-pic-compare-start
                  (fn-pic-set held-desc (fn-pic-source-result r (fn-pic-get held-n c))
                   (fn-pic-set parser p c)))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-sf-trace-source-phase (incoming fn-octets))
   fn-pic-sf-incoming-byte-is-model-byte fn-pic-sf-control-byte-is-model-byte)
  :in-theory (e/d
  (fn-pic-source-tracep fn-pic-next fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-parser)
  (fn-pic-source-continuationp fn-pic-start-parser fn-pic-compare-start fn-psc-step fn-psc-result
   fn-psc-done-result-is-stored fn-psc-model-byte-run fn-pic-demand fn-pic-observation-okp
   fn-pic-observed-byte fn-pic-source-result fn-psc-model-demanded-byte fn-pic-at
   fn-pic-sf-incoming-byte-is-model-byte fn-pic-sf-control-byte-is-model-byte
   fn-pic-sf-second-slot fn-octets-get nth len update-nth)))))
(defthm fn-pic-held-next-incoming-source-completion-is-paid-effect
 (let* ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
        (p (fn-psc-model-byte-run (+ 1 ticks) origin fn-octets held))
        (r (fn-psc-result p))
        (e (fn-pic-set incoming-desc (fn-pic-source-result r (fn-pic-get incoming-n c))
                        (fn-pic-set parser p c))))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (equal (fn-pic-get phase c) :source-incoming)
                (member-eq (fn-pic-get phase d) '(:source-held :magic)))
   (and (equal (fn-ioh-access (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                             (fn-pic-get incoming-token c) :read) :holder-readonly)
        (not (equal r :pending))
        (equal d (if (< (nfix (fn-pic-get held-n c)) *fn-rcl-tombstone-fixed*)
                     (fn-pic-start-parser :source-held :source-held e)
                   (fn-pic-set phase :magic (fn-pic-set pos 0 e)))))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-incoming-source-completion-is-paid-effect
  :in-theory (e/d (fn-pic-held-next)
   (fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-pic-parser fn-pic-source-tracep
    fn-pic-at fn-psc-model-byte-run fn-psc-result fn-pic-source-result
    fn-pic-start-parser nth len update-nth)))))
(defthm fn-pic-held-next-source-completion-is-paid-compare-effect
 (let* ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
        (p (fn-psc-model-byte-run (+ 1 ticks) origin fn-octets held))
        (r (fn-psc-result p)))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (or (equal (fn-pic-get phase d) :compare-incoming)
                    (and (equal (fn-pic-get phase d) :done)
                         (equal (fn-pic-get result d) :conflict))))
   (and (equal (fn-ioh-access (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                             (fn-pic-get incoming-token c) :read) :holder-readonly)
        (not (equal r :pending))
        (equal d (fn-pic-compare-start
                  (fn-pic-set held-desc (fn-pic-source-result r (fn-pic-get held-n c))
                   (fn-pic-set parser p c)))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-next-source-completion-is-paid-compare-effect (:instance fn-pic-sf-trace-source-phase (incoming fn-octets)))
  :in-theory (e/d (fn-pic-held-next)
   (fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-pic-parser fn-pic-source-tracep
    fn-pic-at fn-psc-model-byte-run fn-psc-result fn-pic-source-result
    fn-pic-compare-start nth len update-nth)))))

; Output/fuel equations accompany the semantic state effects above. These
; definitional boundary equations are not cited as semantic keystones.
(defthm fn-pic-funded-source-completion-output-unfolds
 (let ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
                (not (equal (fn-pic-get phase d) (fn-pic-get phase c))))
   (equal (mv-list 3 (fn-pic-feed-funded c observation fuel))
          (list (if (equal (fn-pic-get phase d) :done) (fn-pic-get result d) :continue)
                d (- fuel 1)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-feed-funded) (fn-pic-feed fn-pic-at)))))
(defthm fn-pic-next-source-completion-output-unfolds
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
                (not (equal (fn-pic-get phase d) (fn-pic-get phase c)))
                (or (member-eq (fn-pic-get phase d) '(:source-held :magic :compare-incoming))
                    (and (equal (fn-pic-get phase d) :done)
                         (equal (fn-pic-get result d) :conflict))))
   (equal (mv-list 3 (fn-pic-next c fuel fn-octets))
          (list (if (equal (fn-pic-get phase d) :done) (fn-pic-get result d) :continue)
                d (- fuel (if (equal (fn-pic-demand c) :control) 1 2))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-feed fn-pic-demand fn-pic-at fn-octets-get fn-octets-len)))))
