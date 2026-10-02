; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Actual source parser begin receives a producer-established retained agent.
(in-package "ACL2")
(include-book "post-identity-captured-source-pair-context")
(include-book "post-identity-source-cursor-source-context")
(include-book "post-identity-captured-holder")
(defun fn-pic-agent-shapep (c)
 (let ((a (fn-pic-get agent c)))
  (and (true-listp a) (equal (len a) 3) (equal (car a) :agent))))
(local (defthm fn-pic-sx-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(defthm fn-pic-begin-establishes-agent-shape
 (fn-pic-agent-shapep (fn-pic-begin selected grant held token n msgid binding groups))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-shapep fn-pic-begin fn-pic-finish)
  (fn-ab-held-binding-action fn-pic-at nth update-nth)))))
(local (defthm fn-pic-sx-len-three
 (equal (len (list a b c)) 3)
 :hints (("Goal" :in-theory (enable len)))))
(local (defthm fn-pic-sx-feed-preserves-agent-shape
 (implies (fn-pic-agent-shapep c) (fn-pic-agent-shapep (fn-pic-feed c observation)))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-shapep fn-pic-feed fn-pic-start-parser
   fn-pic-compare-start fn-pic-finish fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-source-result
   fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result fn-psc-begin nth len update-nth))))))
(defthm fn-pic-feed-funded-preserves-agent-shape
 (implies (fn-pic-agent-shapep c) (fn-pic-agent-shapep (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-feed-funded) (fn-pic-agent-shapep fn-pic-feed)))))
(local (defthm fn-pic-sx-finish-preserves-agent-shape
 (equal (fn-pic-agent-shapep (fn-pic-finish result c)) (fn-pic-agent-shapep c))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-shapep fn-pic-finish) (fn-pic-at nth len update-nth))))))
(defthm fn-pic-next-preserves-agent-shape
 (implies (fn-pic-agent-shapep c) (fn-pic-agent-shapep (mv-nth 1 (fn-pic-next c fuel fn-octets))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-agent-shape (observation :control))
   (:instance fn-pic-feed-funded-preserves-agent-shape (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next)
  (fn-pic-agent-shapep fn-pic-feed-funded fn-pic-demand fn-pic-finish fn-pic-at fn-octets-get nth update-nth)))))
(defthm fn-pic-digest-next-preserves-agent-shape
 (implies (fn-pic-agent-shapep c)
  (fn-pic-agent-shapep (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pic-feed-funded-preserves-agent-shape
    (observation (mv-nth 1 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))
    (fuel (+ 1 (mv-nth 2 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))))
 :in-theory (e/d (fn-pic-digest-next)
  (fn-pic-agent-shapep fn-pic-feed-funded fn-pic-digest-effect fn-pic-finish fn-pic-at nth update-nth)))))
(local (defthm fn-pic-sx-take-is-current-take
 (implies (and (natp n) (<= n (len x))) (equal (fn-inj-take n x) (take n x)))
 :hints (("Goal" :induct (fn-inj-take n x) :in-theory (enable fn-inj-take take len nfix)))))
(local (defthm fn-pic-sx-nthcdr-length
 (implies (and (natp start) (<= start (len x)))
  (equal (len (nthcdr start x)) (- (len x) start)))
 :hints (("Goal" :induct (nthcdr start x) :in-theory (enable nthcdr len)))))
(local (defthm fn-pic-sx-second-third-slots
 (and (equal (fn-pic-at 1 x) (cadr x)) (equal (fn-pic-at 2 x) (caddr x)))
 :hints (("Goal" :in-theory (enable fn-pic-at)))))
(local (defthm fn-pic-sx-len-cons
 (equal (len (cons a x)) (+ 1 (len x)))
 :hints (("Goal" :in-theory (enable len)))))
(defthm fn-pic-start-parser-establishes-exact-source-context
 (implies (and (fn-pic-source-pair-agent-contextp c incoming held)
               (fn-pic-agent-shapep c)
               (member-eq mode '(:source-incoming :source-held)))
  (let* ((d (fn-pic-start-parser mode phase c)) (p (fn-pic-parser d)))
   (and (fn-psc-source-contextp p incoming held)
        (equal (fn-psc-model-retained-agent p incoming)
         (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-pic-source-pair-agent-contextp fn-pic-source-pair-contextp fn-pic-agent-contextp
  fn-pic-source-contextp fn-pic-agent-shapep fn-pic-start-parser fn-pic-parser fn-psc-begin
  fn-psc-source-contextp fn-psc-model-retained-agent fn-psc-model-source fn-pic-retained-agent)
  (fn-pic-at fn-pic-spanp fn-pb-path-agent fn-record-string-octets fn-inj-take take nthcdr nth len update-nth)))))
(local (defthm fn-pic-sx-source-entry-from-agent
 (let ((d (fn-pic-feed c observation)))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (and (fn-pic-agent-shapep d)
        (equal (fn-pic-parser d)
         (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d))))))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-agent-shapep fn-pic-start-parser fn-pic-parser fn-pic-finish)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-psc-begin
   fn-pic-source-result fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result
   fn-pic-sx-second-third-slots nth len update-nth))))))
(local (defthm fn-pic-sx-readonly-source-entry-from-agent
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (and (fn-pic-agent-shapep d)
        (equal (fn-pic-parser d)
         (fn-pic-parser (fn-pic-start-parser :source-incoming :source-incoming d))))))
 :hints (("Goal" :use
  ((:instance fn-pic-sx-source-entry-from-agent (observation :control))
   (:instance fn-pic-sx-source-entry-from-agent
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-sx-source-entry-from-agent fn-pic-agent-shapep fn-pic-feed fn-pic-parser fn-pic-start-parser
   fn-pic-demand fn-pic-at fn-octets-get fn-pic-sx-second-third-slots nth update-nth))))))
(defthm fn-pic-next-source-entry-establishes-exact-parser-context
 (implies (and (fn-pic-source-pair-contextp c fn-octets held)
               (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-get phase (mv-nth 1 (fn-pic-next c fuel fn-octets))) :source-incoming))
  (let* ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))) (p (fn-pic-parser d)))
   (and (fn-psc-source-contextp p fn-octets held)
        (equal (fn-psc-model-retained-agent p fn-octets)
         (fn-pb-path-agent fn-octets (fn-record-string-octets (fn-pic-get msgid d)))))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-next-source-entry-establishes-source-pair-agent-context
   fn-pic-sx-readonly-source-entry-from-agent
   (:instance fn-pic-start-parser-establishes-exact-source-context
    (c (mv-nth 1 (fn-pic-next c fuel fn-octets))) (incoming fn-octets)
    (mode :source-incoming) (phase :source-incoming)))
 :in-theory (e/d (fn-pic-agent-tracep)
  (fn-pic-source-pair-contextp fn-pic-source-pair-agent-contextp fn-pic-agent-trace-start
   fn-pic-sx-readonly-source-entry-from-agent fn-pic-next fn-pic-parser fn-pic-start-parser fn-pic-agent-shapep
   fn-psc-source-contextp fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets
   fn-pic-at fn-pic-sx-second-third-slots nth len update-nth)))))
(local (defthm fn-pic-sx-start-incoming-parser-context
 (implies (and (fn-pic-agent-contextp c incoming) (fn-pic-agent-shapep c))
  (let* ((d (fn-pic-start-parser :source-incoming phase c)) (p (fn-pic-parser d)))
   (and (fn-psc-source-contextp p incoming held)
        (equal (fn-psc-model-retained-agent p incoming)
         (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))))))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-pic-agent-contextp fn-pic-source-contextp fn-pic-agent-shapep
  fn-pic-start-parser fn-pic-parser fn-psc-begin fn-psc-source-contextp
  fn-psc-model-retained-agent fn-psc-model-source fn-pic-retained-agent)
  (fn-pic-at fn-pic-spanp fn-pb-path-agent fn-record-string-octets fn-inj-take take nthcdr nth len update-nth))))))
; Incoming parser entry does not require a separate held extent premise.
(defthm fn-pic-next-agent-completion-establishes-exact-parser-context
 (implies (and (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-get phase (mv-nth 1 (fn-pic-next c fuel fn-octets))) :source-incoming))
  (let* ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))) (p (fn-pic-parser d)))
   (and (fn-psc-source-contextp p fn-octets held)
        (equal (fn-psc-model-retained-agent p fn-octets)
         (fn-pb-path-agent fn-octets (fn-record-string-octets (fn-pic-get msgid d)))))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-next-source-entry-establishes-agent-context fn-pic-sx-readonly-source-entry-from-agent
   (:instance fn-pic-sx-start-incoming-parser-context
    (c (mv-nth 1 (fn-pic-next c fuel fn-octets))) (incoming fn-octets) (phase :source-incoming)))
 :in-theory (e/d (fn-pic-agent-tracep)
  (fn-pic-source-contextp fn-pic-agent-contextp fn-pic-agent-trace-start fn-pic-sx-start-incoming-parser-context
   fn-pic-sx-readonly-source-entry-from-agent fn-pic-next fn-pic-parser fn-pic-start-parser fn-pic-agent-shapep
   fn-psc-source-contextp fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets
   fn-pic-at fn-pic-sx-second-third-slots nth len update-nth)))))
; The pooled host-facing entry derives its current row internally. Entry
; implies the exact current readonly holder verdict, rather than a host row.
(defthm fn-pic-held-next-agent-completion-establishes-exact-parser-context
 (implies (and (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-get phase (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
                      :source-incoming))
  (let* ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))) (p (fn-pic-parser d)))
   (and (equal (fn-ioh-access (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                             (fn-pic-get incoming-token c) :read) :holder-readonly)
        (fn-psc-source-contextp p fn-octets held)
        (equal (fn-psc-model-retained-agent p fn-octets)
         (fn-pb-path-agent fn-octets (fn-record-string-octets (fn-pic-get msgid d)))))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-agent-completion-establishes-exact-parser-context
 :in-theory (e/d (fn-pic-held-next fn-pic-agent-tracep)
  (fn-pic-next fn-pic-parser fn-pic-agent-trace-start fn-pic-source-contextp
   fn-ioh-access fn-ibc-carrier-row fn-prp-incoming-slot fn-pic-at
   fn-psc-source-contextp fn-psc-model-retained-agent fn-pb-path-agent fn-record-string-octets nth len update-nth)))))
(defthm fn-pic-held-next-preserves-agent-shape
 (implies (fn-pic-agent-shapep c)
  (fn-pic-agent-shapep (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-preserves-agent-shape
 :in-theory (e/d (fn-pic-held-next)
  (fn-pic-agent-shapep fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-prp-incoming-slot fn-pic-at nth update-nth)))))
