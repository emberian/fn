; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only post-length geometry of both immutable source extents.
(in-package "ACL2")
(include-book "post-identity-captured-agent-join")
(defun fn-pic-source-pair-contextp (c incoming held)
 (and (fn-pic-source-contextp c incoming) (true-listp held)
      (not (equal (fn-pic-get phase c) :held-length))
      (equal (fn-pic-get held-n c) (len held))
      (or (not (fn-pic-get held-desc c))
          (fn-pic-spanp (fn-pic-get held-desc c) (len held)))))
(local (defthm fn-pic-sp-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-sp-other-update-preserves-held-geometry
 (implies (and (natp i) (not (member-equal i '(0 6 12))))
  (equal (and (equal (fn-pic-get held-n (update-nth i value c)) (len held))
              (or (not (fn-pic-get held-desc (update-nth i value c)))
                  (fn-pic-spanp (fn-pic-get held-desc (update-nth i value c)) (len held))))
         (and (equal (fn-pic-get held-n c) (len held))
              (or (not (fn-pic-get held-desc c)) (fn-pic-spanp (fn-pic-get held-desc c) (len held))))))
 :hints (("Goal" :in-theory (disable fn-pic-spanp fn-pic-at nth update-nth)))))
(local (defthm fn-pic-sp-source-result-is-legal
 (or (not (fn-pic-source-result r n)) (fn-pic-spanp (fn-pic-source-result r n) n))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-result) (fn-pic-at fn-pic-spanp))))))
(local (defthm fn-pic-sp-zero-span-is-legal
 (implies (natp n) (fn-pic-spanp '(0 0 0) n))
 :hints (("Goal" :in-theory (enable fn-pic-spanp fn-pic-at)))))
(local (defthm fn-pic-sp-feed-preserves-held-n-after-length
 (implies (not (equal (fn-pic-get phase c) :held-length))
  (equal (fn-pic-get held-n (fn-pic-feed c observation)) (fn-pic-get held-n c)))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-finish
   fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result
   fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result fn-psc-begin nth update-nth))))))
(local (defthm fn-pic-sp-feed-does-not-reenter-length
 (not (equal (fn-pic-get phase (fn-pic-feed c observation)) :held-length))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-finish
   fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result
   fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result fn-psc-begin nth update-nth))))))
(local (defthm fn-pic-sp-feed-preserves-held-descriptor
 (implies (and (equal (fn-pic-get held-n c) (len held))
               (or (not (fn-pic-get held-desc c)) (fn-pic-spanp (fn-pic-get held-desc c) (len held))))
  (or (not (fn-pic-get held-desc (fn-pic-feed c observation)))
      (fn-pic-spanp (fn-pic-get held-desc (fn-pic-feed c observation)) (len held))))
 :hints (("Goal" :use (:instance fn-pic-sp-source-result-is-legal
  (r (fn-psc-result (fn-psc-step (fn-pic-parser c) (fn-pic-observed-byte (fn-pic-demand c) observation))))
  (n (len held)))
 :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-finish
   fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result
   fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result fn-psc-begin nth update-nth))))))
(defthm fn-pic-feed-funded-preserves-source-pair-context
 (implies (fn-pic-source-pair-contextp c incoming held)
  (fn-pic-source-pair-contextp (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-feed-funded-preserves-source-context fn-pic-sp-feed-does-not-reenter-length fn-pic-sp-feed-preserves-held-n-after-length fn-pic-sp-feed-preserves-held-descriptor)
 :in-theory (e/d (fn-pic-source-pair-contextp fn-pic-feed-funded)
  (fn-pic-source-contextp fn-pic-feed fn-pic-at fn-pic-spanp fn-pic-sp-feed-does-not-reenter-length fn-pic-sp-feed-preserves-held-n-after-length fn-pic-sp-feed-preserves-held-descriptor nth update-nth)))))
(local (defthm fn-pic-sp-finish-preserves-pair-context
 (implies (fn-pic-source-pair-contextp c incoming held)
  (fn-pic-source-pair-contextp (fn-pic-finish result c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-pair-contextp fn-pic-source-contextp fn-pic-finish)
  (fn-pic-at fn-pic-spanp nth update-nth))))))
(defthm fn-pic-next-preserves-source-pair-context
 (implies (fn-pic-source-pair-contextp c fn-octets held)
  (fn-pic-source-pair-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-source-pair-context (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-preserves-source-pair-context (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next)
  (fn-pic-source-pair-contextp fn-pic-feed-funded fn-pic-demand fn-pic-finish fn-pic-at fn-octets-get nth update-nth)))))
(defthm fn-pic-digest-next-preserves-source-pair-context
 (implies (fn-pic-source-pair-contextp c incoming held)
  (fn-pic-source-pair-contextp (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pic-feed-funded-preserves-source-pair-context
    (observation (mv-nth 1 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))
    (fuel (+ 1 (mv-nth 2 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))))
 :in-theory (e/d (fn-pic-digest-next)
  (fn-pic-source-pair-contextp fn-pic-feed-funded fn-pic-digest-effect fn-pic-finish fn-pic-at nth update-nth)))))
(local (defthm fn-pic-sp-valid-begin-effect-is-length
 (let ((c (fn-pic-begin selected grant row incoming-token (len incoming) msgid binding groups)))
  (implies (fn-pic-observation-okp c (fn-pic-demand c) observation)
   (equal (fn-pic-get phase c) :held-length)))
 :hints (("Goal" :in-theory (e/d (fn-pic-begin fn-pic-finish fn-pic-demand fn-pic-observation-okp)
  (fn-ab-held-binding-action fn-pic-at nth update-nth))))))
(defthm fn-pic-begin-length-feedback-establishes-source-pair-context
 (let* ((c (fn-pic-begin selected grant row incoming-token (len incoming) msgid binding groups))
        (d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (true-listp incoming) (true-listp held) (not (zp fuel))
                (fn-pic-observation-okp c (fn-pic-demand c) observation)
                (equal (fn-pic-at 4 observation) (len held)))
   (fn-pic-source-pair-contextp d incoming held)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pic-sp-valid-begin-effect-is-length
        (:instance fn-pic-begin-establishes-source-context (held row))
        (:instance fn-pic-feed-funded-preserves-source-context
         (c (fn-pic-begin selected grant row incoming-token (len incoming) msgid binding groups))))
  :in-theory (e/d (fn-pic-source-pair-contextp fn-pic-feed-funded fn-pic-feed fn-pic-start-parser fn-pic-begin fn-pic-finish)
   (fn-pic-source-contextp fn-pic-sp-valid-begin-effect-is-length fn-ab-held-binding-action
    fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-at fn-pic-spanp
    fn-psc-begin fn-psc-step fn-psc-result nth len update-nth)))))
(defthm fn-pic-source-pair-context-implies-hash-choice-context-unfolds
 (implies (and (fn-pic-source-pair-contextp c incoming held)
               (<= *fn-rcl-tombstone-fixed* (len held)))
  (fn-pic-choice-contextp c incoming held))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-source-pair-contextp fn-pic-source-contextp fn-pic-choice-contextp)
  (fn-pic-at fn-pic-spanp nth len update-nth)))))
; Once actual agent completion enters source parsing, retain both extents
; and the old incoming-derived agent interpretation through every action.
(defun fn-pic-source-pair-agent-contextp (c incoming held)
 (and (fn-pic-source-pair-contextp c incoming held)
      (fn-pic-agent-contextp c incoming)
      (not (equal (fn-pic-get phase c) :agent))))
(local (defthm fn-pic-sp-feed-does-not-reenter-agent
 (implies (not (member-eq (fn-pic-get phase c) '(:held-length :agent)))
  (not (equal (fn-pic-get phase (fn-pic-feed c observation)) :agent)))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-finish
   fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result
   fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result fn-psc-begin nth update-nth))))))
(defthm fn-pic-next-source-entry-establishes-source-pair-agent-context
 (implies (and (fn-pic-source-pair-contextp c fn-octets held)
               (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-get phase (mv-nth 1 (fn-pic-next c fuel fn-octets))) :source-incoming))
  (fn-pic-source-pair-agent-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-next-preserves-source-pair-context fn-pic-next-source-entry-establishes-agent-context)
  :in-theory (e/d (fn-pic-source-pair-agent-contextp)
  (fn-pic-source-pair-contextp fn-pic-agent-contextp fn-pic-agent-tracep fn-pic-next fn-pic-at nth update-nth)))))
(defthm fn-pic-feed-funded-preserves-source-pair-agent-context
 (implies (fn-pic-source-pair-agent-contextp c incoming held)
  (fn-pic-source-pair-agent-contextp (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-feed-funded-preserves-source-pair-context
      fn-pic-feed-funded-preserves-agent-context-after-agent fn-pic-sp-feed-does-not-reenter-agent)
  :in-theory (e/d (fn-pic-source-pair-agent-contextp fn-pic-source-pair-contextp fn-pic-feed-funded)
   (fn-pic-source-contextp fn-pic-agent-contextp fn-pic-feed fn-pic-sp-feed-does-not-reenter-agent
    fn-pic-sp-feed-does-not-reenter-length fn-pic-sp-feed-preserves-held-n-after-length fn-pic-sp-feed-preserves-held-descriptor
    fn-pic-at fn-pic-spanp nth update-nth)))))
(local (defthm fn-pic-sp-finish-preserves-pair-agent-context
 (implies (fn-pic-source-pair-agent-contextp c incoming held)
  (fn-pic-source-pair-agent-contextp (fn-pic-finish result c) incoming held))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-pair-agent-contextp fn-pic-source-pair-contextp
  fn-pic-agent-contextp fn-pic-source-contextp fn-pic-retained-agent fn-pic-finish)
  (fn-pic-at fn-pic-spanp fn-pb-path-agent fn-record-string-octets nth nthcdr take update-nth))))))
(defthm fn-pic-next-preserves-source-pair-agent-context
 (implies (fn-pic-source-pair-agent-contextp c fn-octets held)
  (fn-pic-source-pair-agent-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-source-pair-agent-context (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-preserves-source-pair-agent-context (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next)
  (fn-pic-source-pair-agent-contextp fn-pic-feed-funded fn-pic-demand fn-pic-finish fn-pic-at fn-octets-get nth update-nth)))))
(defthm fn-pic-digest-next-preserves-source-pair-agent-context
 (implies (fn-pic-source-pair-agent-contextp c incoming held)
  (fn-pic-source-pair-agent-contextp (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pic-feed-funded-preserves-source-pair-agent-context
    (observation (mv-nth 1 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))
    (fuel (+ 1 (mv-nth 2 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))))
 :in-theory (e/d (fn-pic-digest-next)
  (fn-pic-source-pair-agent-contextp fn-pic-feed-funded fn-pic-digest-effect fn-pic-finish fn-pic-at nth update-nth)))))
; This definitional corollary transports the producer-derived agent to the
; old tombstone decision; the complete source-index inverse is still separate.
(defthm fn-pic-retained-source-choice-is-current-agent-choice-unfolds
 (implies (fn-pic-agent-contextp c incoming)
  (equal (fn-pic-retained-source-choicep c incoming held)
   (and (fn-rcl-tomb-sourcep held) (fn-pic-get incoming-desc c)
        (equal (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))
               (fn-rcl-tomb-agent held)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-contextp fn-pic-retained-source-choicep)
   (fn-pic-source-contextp fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets
    fn-rcl-tomb-sourcep fn-rcl-tomb-agent fn-pic-at nth update-nth)))))
