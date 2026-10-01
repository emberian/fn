; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Paid immutable byte trace at the actual readonly source controller boundary.
(in-package "ACL2")
(include-book "post-identity-captured-source-continuation")
(defun fn-pic-source-tracep (c ticks origin incoming held)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-pic-source-continuationp c incoming held) (natp ticks)
      (equal (fn-pic-parser c) (fn-psc-model-byte-run ticks origin incoming held))))
(local (defthm fn-pic-st-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-st-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) p incoming held)
   (fn-psc-model-byte-run b (fn-psc-model-byte-run a p incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a p incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-model-demanded-byte nth len))))))
(local (defthm fn-pic-st-run-successor
 (implies (natp ticks)
  (equal (fn-psc-model-byte-run (+ 1 ticks) origin incoming held)
   (fn-psc-step (fn-psc-model-byte-run ticks origin incoming held)
    (fn-psc-model-demanded-byte (fn-psc-model-byte-run ticks origin incoming held) incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-pic-st-run-addition (a ticks) (b 1) (p origin))
  :expand ((:free (p) (fn-psc-model-byte-run 1 p incoming held))
           (:free (p) (fn-psc-model-byte-run 0 p incoming held)))
  :in-theory (disable fn-psc-model-byte-run fn-pic-st-run-addition fn-psc-step fn-psc-model-demanded-byte nth len)))))
(local (defthm fn-pic-st-compare-phase
 (and (not (equal (nth 0 (fn-pic-compare-start c)) :source-incoming))
      (not (equal (nth 0 (fn-pic-compare-start c)) :source-held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-compare-start fn-pic-finish)
  (fn-pic-span-length fn-pic-at nth update-nth))))))
(local (defthm fn-pic-st-start-phase
 (equal (nth 0 (fn-pic-start-parser mode phase c)) phase)
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser) (fn-psc-begin fn-pic-at nth update-nth))))))
(local (defthm fn-pic-st-feed-same-source-phase-is-step
 (let ((d (fn-pic-feed c observation)))
  (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
                (equal (fn-pic-get phase d) (fn-pic-get phase c)))
   (equal (fn-pic-parser d)
    (fn-psc-step (fn-pic-parser c) (fn-pic-observed-byte (fn-pic-demand c) observation)))))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-finish fn-pic-parser)
  (fn-pic-at fn-pic-start-parser fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
   fn-pic-source-result fn-pic-compare-start fn-psc-step fn-psc-result fn-pic-span-length
   fn-pic-groups-start fn-pic-groups-step fn-pic-hash-start fn-pic-block-add nth len update-nth))))))
(defthm fn-pic-start-parser-establishes-paid-source-trace
 (let ((d (fn-pic-start-parser mode mode c)))
  (implies (and (fn-pic-source-pair-agent-contextp c incoming held)
                (fn-pic-agent-shapep c) (member-eq mode '(:source-incoming :source-held)))
   (fn-pic-source-tracep d 0 (fn-pic-parser d) incoming held)))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-start-parser-establishes-source-continuation
 :expand ((:free (p) (fn-psc-model-byte-run 0 p incoming held)))
 :in-theory (e/d (fn-pic-source-tracep)
  (fn-pic-source-continuationp fn-pic-source-pair-agent-contextp fn-pic-agent-shapep
   fn-pic-start-parser fn-pic-parser fn-psc-model-byte-run fn-pic-at nth len update-nth)))))
(defthm fn-pic-feed-funded-same-source-phase-preserves-paid-trace
 (let ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (fn-pic-source-tracep c ticks origin incoming held)
                (equal (fn-pic-observed-byte (fn-pic-demand c) observation)
                       (fn-psc-model-demanded-byte (fn-pic-parser c) incoming held))
                (equal (fn-pic-get phase d) (fn-pic-get phase c)))
   (or (fn-pic-source-tracep d ticks origin incoming held)
       (fn-pic-source-tracep d (+ 1 ticks) origin incoming held))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-feed-funded-preserves-source-continuation
   fn-pic-st-feed-same-source-phase-is-step)
 :in-theory (e/d (fn-pic-source-tracep fn-pic-source-continuationp fn-pic-feed-funded)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-psc-source-contextp fn-psc-source-resumep
   fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-feed fn-pic-parser
   fn-psc-model-byte-run fn-psc-model-demanded-byte fn-psc-step fn-pic-demand fn-pic-observed-byte
   fn-pic-at nth len update-nth)))))
(local (defthm fn-pic-st-trace-has-source-phase
 (implies (fn-pic-source-tracep c ticks origin incoming held)
  (member-eq (fn-pic-get phase c) '(:source-incoming :source-held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-tracep fn-pic-source-continuationp)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-psc-source-contextp fn-psc-source-resumep
   fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-parser
   fn-psc-model-byte-run fn-pic-at nth len update-nth))))))
(local (defthm fn-pic-st-second-slot
 (equal (nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable nth)))))
(local (defthm fn-pic-st-incoming-byte-is-model-byte
 (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
               (equal (fn-pic-at 0 (fn-pic-demand c)) :incoming))
  (equal (fn-pic-observed-byte (fn-pic-demand c)
          (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
           (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))
         (fn-psc-model-demanded-byte (fn-pic-parser c) fn-octets held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-demand fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
  (fn-pic-parser fn-psc-demand fn-octets-get len update-nth))))))
(local (defthm fn-pic-st-control-byte-is-model-byte
 (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
               (equal (fn-pic-demand c) :control))
  (equal (fn-pic-observed-byte (fn-pic-demand c) :control)
         (fn-psc-model-demanded-byte (fn-pic-parser c) fn-octets held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-demand fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
  (fn-pic-parser fn-psc-demand len update-nth))))))
(defthm fn-pic-next-same-source-phase-preserves-paid-trace
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (equal (fn-pic-get phase d) (fn-pic-get phase c)))
   (or (fn-pic-source-tracep d ticks origin fn-octets held)
       (fn-pic-source-tracep d (+ 1 ticks) origin fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-st-trace-has-source-phase (incoming fn-octets))
   (:instance fn-pic-feed-funded-same-source-phase-preserves-paid-trace
    (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-same-source-phase-preserves-paid-trace
    (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets))))
   fn-pic-st-incoming-byte-is-model-byte fn-pic-st-control-byte-is-model-byte)
 :in-theory (e/d (fn-pic-next fn-pic-finish)
  (fn-pic-source-tracep fn-pic-feed-funded fn-pic-demand fn-pic-observed-byte fn-psc-model-demanded-byte
   fn-pic-st-trace-has-source-phase fn-pic-st-incoming-byte-is-model-byte fn-pic-st-control-byte-is-model-byte
   fn-pic-at fn-octets-get nth len update-nth)))))
(defthm fn-pic-held-next-same-source-phase-preserves-paid-trace
 (let ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))))
  (implies (and (fn-pic-source-tracep c ticks origin fn-octets held)
                (equal (fn-pic-get phase d) (fn-pic-get phase c)))
   (or (fn-pic-source-tracep d ticks origin fn-octets held)
       (fn-pic-source-tracep d (+ 1 ticks) origin fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-same-source-phase-preserves-paid-trace
 :in-theory (e/d (fn-pic-held-next)
  (fn-pic-source-tracep fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-prp-incoming-slot
   fn-pic-at nth len update-nth)))))
(local (defthm fn-pic-st-len-cons
 (equal (len (cons a x)) (+ 1 (len x)))
 :hints (("Goal" :in-theory (enable len)))))
(local (defthm fn-pic-st-agent-source-entry-parser-origin
 (let ((d (fn-pic-feed c observation)))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (equal (fn-pic-parser d)
          (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d)))))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-parser fn-pic-finish)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-psc-begin
   fn-pic-source-result fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result
   fn-pic-st-second-slot nth len update-nth))))))
(local (defthm fn-pic-st-next-source-entry-parser-origin
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (equal (fn-pic-parser d)
          (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d)))))
 :hints (("Goal" :use
  ((:instance fn-pic-st-agent-source-entry-parser-origin (observation :control))
   (:instance fn-pic-st-agent-source-entry-parser-origin
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-st-agent-source-entry-parser-origin fn-pic-feed fn-pic-parser fn-pic-start-parser
   fn-pic-demand fn-pic-at fn-octets-get fn-pic-st-second-slot nth len update-nth))))))
(defthm fn-pic-next-agent-completion-establishes-paid-source-trace
 (let* ((d (mv-nth 1 (fn-pic-next c fuel fn-octets)))
        (origin (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d))))
  (implies (and (fn-pic-source-pair-contextp c fn-octets held)
                (fn-pic-agent-tracep c ticks fn-octets)
                (equal (fn-pic-get phase d) :source-incoming))
   (fn-pic-source-tracep d 0 origin fn-octets held)))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-next-agent-completion-establishes-source-continuation
                      fn-pic-st-next-source-entry-parser-origin)
 :expand ((:free (p) (fn-psc-model-byte-run 0 p fn-octets held)))
 :in-theory (e/d (fn-pic-source-tracep fn-pic-agent-tracep)
  (fn-pic-source-continuationp fn-pic-source-pair-contextp fn-pic-agent-trace-start
   fn-pic-source-contextp fn-pic-next fn-pic-parser fn-pic-start-parser fn-pic-st-next-source-entry-parser-origin
   fn-psc-model-byte-run fn-pic-at fn-pic-st-second-slot nth len update-nth)))))
(defthm fn-pic-held-next-agent-completion-establishes-paid-source-trace
 (let* ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
        (origin (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d))))
  (implies (and (fn-pic-source-pair-contextp c fn-octets held)
                (fn-pic-agent-tracep c ticks fn-octets)
                (equal (fn-pic-get phase d) :source-incoming))
   (and (equal (fn-ioh-access (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                              (fn-pic-get incoming-token c) :read) :holder-readonly)
        (fn-pic-source-tracep d 0 origin fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-agent-completion-establishes-paid-source-trace
 :in-theory (e/d (fn-pic-held-next fn-pic-agent-tracep)
  (fn-pic-source-tracep fn-pic-next fn-pic-agent-trace-start fn-pic-source-contextp
   fn-pic-parser fn-pic-start-parser fn-pic-st-next-source-entry-parser-origin
   fn-ioh-access fn-ibc-carrier-row fn-prp-incoming-slot fn-pic-at fn-pic-st-second-slot nth len update-nth)))))
(in-theory (disable fn-pic-source-tracep))
