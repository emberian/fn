; Carried source parser context through the actual funded controller actions.
(in-package "ACL2")
(include-book "post-identity-captured-source-parser-context")
(local (defthm fn-pic-sc-parser-configuration-frame
 (and (equal (fn-psc-get mode (fn-psc-step p byte)) (fn-psc-get mode p))
      (equal (fn-psc-get n (fn-psc-step p byte)) (fn-psc-get n p))
      (equal (fn-psc-get incoming-n (fn-psc-step p byte)) (fn-psc-get incoming-n p))
      (equal (fn-psc-get msgid (fn-psc-step p byte)) (fn-psc-get msgid p)))
 :hints (("Goal" :use (:instance fn-psc-step-preserves-configuration (c p))
 :in-theory (e/d (fn-psc-configuration)
  (fn-psc-step fn-psc-step-preserves-configuration nth len update-nth))))))
(local (defthm fn-pic-sc-parser-step-preserves-context
 (implies (and (fn-psc-source-contextp p incoming held) (fn-psc-source-resumep p))
  (and (fn-psc-source-contextp (fn-psc-step p byte) incoming held)
       (equal (fn-psc-model-retained-agent (fn-psc-step p byte) incoming)
              (fn-psc-model-retained-agent p incoming))))
 :hints (("Goal" :use (:instance fn-psc-source-step-preserves-incoming-agent (c p))
 :in-theory (e/d (fn-psc-source-contextp fn-psc-model-retained-agent fn-psc-model-source)
  (fn-psc-step fn-psc-source-resumep fn-inj-take nthcdr nth len update-nth))))))
(defun fn-pic-source-continuationp (c incoming held)
 (and (fn-pic-source-pair-agent-contextp c incoming held)
      (fn-pic-agent-shapep c)
      (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
      (fn-psc-source-contextp (fn-pic-parser c) incoming held)
      (fn-psc-source-resumep (fn-pic-parser c))
      (equal (fn-psc-get mode (fn-pic-parser c)) (fn-pic-get phase c))
      (equal (fn-psc-get msgid (fn-pic-parser c)) (fn-pic-get msgid c))
      (equal (fn-psc-get incoming-n (fn-pic-parser c)) (fn-pic-get incoming-n c))
      (equal (fn-psc-model-retained-agent (fn-pic-parser c) incoming)
             (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c))))))
(local (defthm fn-pic-sc-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-sc-len-cons
 (equal (len (cons a x)) (+ 1 (len x)))
 :hints (("Goal" :in-theory (enable len)))))
(local (defthm fn-pic-sc-start-preserves-carried-context
 (implies (and (fn-pic-source-pair-agent-contextp c incoming held)
               (fn-pic-agent-shapep c) (member-eq mode '(:source-incoming :source-held)))
  (and (fn-pic-source-pair-agent-contextp (fn-pic-start-parser mode mode c) incoming held)
       (fn-pic-agent-shapep (fn-pic-start-parser mode mode c))))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-pair-agent-contextp fn-pic-source-pair-contextp
  fn-pic-agent-contextp fn-pic-source-contextp fn-pic-agent-shapep fn-pic-retained-agent fn-pic-start-parser)
  (fn-pic-at fn-psc-begin fn-pic-spanp fn-pb-path-agent fn-record-string-octets nthcdr take nth len update-nth))))))
(local (defthm fn-pic-sc-agent-coordinate-slots
 (and (equal (fn-pic-at 1 a) (cadr a)) (equal (fn-pic-at 2 a) (caddr a)))
 :hints (("Goal" :in-theory (enable fn-pic-at)))))
(local (defthm fn-pic-sc-start-parser-frame
 (implies (and (fn-pic-source-pair-agent-contextp c incoming held)
               (fn-pic-agent-shapep c) (member-eq mode '(:source-incoming :source-held)))
  (let* ((d (fn-pic-start-parser mode mode c)) (p (fn-pic-parser d)))
   (and (fn-psc-source-resumep p)
        (equal (fn-psc-get mode p) mode)
        (equal (fn-pic-get phase d) mode)
        (equal (fn-psc-get msgid p) (fn-pic-get msgid d))
        (equal (fn-pic-get msgid d) (fn-pic-get msgid c))
        (equal (fn-psc-get incoming-n p) (fn-pic-get incoming-n d)))))
 :hints (("Goal" :use (:instance fn-psc-begin-establishes-source-resumes
  (n (if (equal mode :source-held) (nfix (fn-pic-get held-n c)) (nfix (fn-pic-get incoming-n c))))
  (msgid (fn-pic-get msgid c)) (agent-span (fn-pic-get agent c))
  (incoming-n (nfix (fn-pic-get incoming-n c)))) :in-theory (e/d (fn-pic-source-pair-agent-contextp fn-pic-source-pair-contextp
  fn-pic-source-contextp fn-pic-agent-contextp fn-pic-agent-shapep fn-pic-start-parser fn-pic-parser fn-psc-begin)
  (fn-psc-source-resumep fn-psc-begin-establishes-source-resumes fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-at fn-pic-spanp nth len update-nth))))))
(defthm fn-pic-start-parser-establishes-source-continuation
 (implies (and (fn-pic-source-pair-agent-contextp c incoming held)
               (fn-pic-agent-shapep c) (member-eq mode '(:source-incoming :source-held)))
  (fn-pic-source-continuationp (fn-pic-start-parser mode mode c) incoming held))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-sc-start-preserves-carried-context fn-pic-sc-start-parser-frame
   (:instance fn-pic-start-parser-establishes-exact-source-context (phase mode)))
 :in-theory (e/d (fn-pic-source-continuationp)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-pic-start-parser fn-pic-parser
   fn-pic-sc-start-preserves-carried-context fn-pic-sc-start-parser-frame
   fn-psc-source-contextp fn-psc-source-resumep fn-psc-model-retained-agent
   fn-pic-at fn-pb-path-agent fn-record-string-octets nth len update-nth)))))
(local (defthm fn-pic-sc-pending-parser-frame
 (implies (fn-pic-source-continuationp c incoming held)
  (let ((d (fn-pic-set parser (fn-psc-step (fn-pic-parser c) byte) c)))
   (and (fn-psc-source-contextp (fn-pic-parser d) incoming held)
        (fn-psc-source-resumep (fn-pic-parser d))
        (equal (fn-psc-get mode (fn-pic-parser d)) (fn-pic-get phase d))
        (equal (fn-psc-get msgid (fn-pic-parser d)) (fn-pic-get msgid d))
        (equal (fn-psc-get incoming-n (fn-pic-parser d)) (fn-pic-get incoming-n d))
        (equal (fn-psc-model-retained-agent (fn-pic-parser d) incoming)
         (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid d)))))))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-continuationp fn-pic-parser)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-psc-source-contextp
   fn-psc-source-resumep fn-psc-model-retained-agent fn-psc-step fn-pb-path-agent
   fn-record-string-octets fn-pic-at nth len update-nth))))))
(local (defthm fn-pic-sc-repeat-update
 (equal (update-nth i value (update-nth i value x)) (update-nth i value x))
 :hints (("Goal" :induct (update-nth i value x) :in-theory (enable update-nth)))))
(local (defthm fn-pic-sc-update-cdr
 (implies (and (natp i) (< 0 i))
  (equal (cdr (update-nth i value x)) (update-nth (- i 1) value (cdr x))))
 :hints (("Goal" :in-theory (enable update-nth)))))
(local (defthm fn-pic-sc-source-start-idempotent-slots
 (equal (update-nth 0 phase (update-nth 9 parser (update-nth 0 phase (update-nth 9 parser c))))
        (update-nth 0 phase (update-nth 9 parser c)))
 :hints (("Goal" :expand ((:free (x) (update-nth 0 phase x))
  (:free (x) (update-nth 9 parser x))) :in-theory (enable update-nth)))))
(local (defthm fn-pic-sc-source-switch-is-actual-start
 (let ((d (fn-pic-feed c observation)))
  (implies (and (equal (fn-pic-get phase c) :source-incoming)
                (not (equal (fn-psc-result (fn-psc-step (fn-pic-parser c)
                       (fn-pic-observed-byte (fn-pic-demand c) observation))) :pending))
                (equal (fn-pic-get phase d) :source-held))
   (equal (fn-pic-start-parser :source-held :source-held d) d)))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-start-parser fn-pic-finish)
  (fn-pic-at fn-pic-parser fn-psc-step fn-psc-result fn-psc-begin fn-pic-source-result
   fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-sc-agent-coordinate-slots nth len update-nth))))))
(local (defthm fn-pic-sc-compare-start-leaves-source
 (and (not (equal (nth 0 (fn-pic-compare-start c)) :source-incoming))
      (not (equal (nth 0 (fn-pic-compare-start c)) :source-held)))
 :hints (("Goal" :in-theory (e/d (fn-pic-compare-start fn-pic-finish)
  (fn-pic-span-length fn-pic-at nth update-nth))))))
(local (defthm fn-pic-sc-start-parser-phase
 (equal (nth 0 (fn-pic-start-parser mode phase c)) phase)
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser) (fn-psc-begin fn-pic-at nth update-nth))))))
(local (defthm fn-pic-sc-held-start-is-idempotent
 (equal (fn-pic-start-parser :source-held :source-held
         (fn-pic-start-parser :source-held :source-held c))
        (fn-pic-start-parser :source-held :source-held c))
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser)
  (fn-psc-begin fn-pic-at nth update-nth))))))
(local (defthm fn-pic-sc-feed-source-continuation-cases
 (let* ((p (fn-psc-step (fn-pic-parser c) (fn-pic-observed-byte (fn-pic-demand c) observation)))
        (d (fn-pic-feed c observation)))
  (implies (and (member-eq (fn-pic-get phase c) '(:source-incoming :source-held))
                (member-eq (fn-pic-get phase d) '(:source-incoming :source-held)))
   (or (equal d (fn-pic-set parser p c))
       (equal d (fn-pic-start-parser :source-held :source-held d)))))
 :hints (("Goal" :use fn-pic-sc-source-switch-is-actual-start
 :in-theory (e/d (fn-pic-feed fn-pic-finish)
  (fn-pic-sc-source-switch-is-actual-start fn-pic-start-parser fn-pic-compare-start fn-pic-parser
   fn-psc-step fn-psc-result fn-pic-source-result fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
   fn-pic-span-length fn-pic-groups-step fn-pic-block-add fn-pic-hash-start fn-pic-groups-start
   fn-pic-sc-agent-coordinate-slots fn-pic-at nth len update-nth))))))
(defthm fn-pic-feed-funded-preserves-source-continuation
 (let ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (fn-pic-source-continuationp c incoming held)
                (member-eq (fn-pic-get phase d) '(:source-incoming :source-held)))
   (fn-pic-source-continuationp d incoming held)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-feed-funded-preserves-source-pair-agent-context fn-pic-feed-funded-preserves-agent-shape
   (:instance fn-pic-sc-pending-parser-frame
    (byte (fn-pic-observed-byte (fn-pic-demand c) observation)))
   fn-pic-sc-feed-source-continuation-cases
   (:instance fn-pic-start-parser-establishes-source-continuation
    (c (fn-pic-feed c observation)) (mode :source-held)))
 :in-theory (e/d (fn-pic-source-continuationp fn-pic-feed-funded)
  (fn-pic-source-pair-agent-contextp fn-pic-agent-shapep fn-pic-sc-pending-parser-frame
   fn-pic-sc-feed-source-continuation-cases fn-pic-sc-agent-coordinate-slots fn-pic-start-parser
   fn-pic-parser fn-psc-source-contextp fn-psc-source-resumep fn-psc-model-retained-agent
   fn-psc-step fn-psc-result fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
   fn-pic-feed fn-pic-source-result fn-pic-compare-start fn-pb-path-agent fn-record-string-octets nth len update-nth)))))
(defthm fn-pic-next-preserves-source-continuation
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (fn-pic-source-continuationp c fn-octets held)
                (member-eq (fn-pic-get phase d) '(:source-incoming :source-held)))
   (fn-pic-source-continuationp d fn-octets held)))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-source-continuation (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-preserves-source-continuation (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-finish)
  (fn-pic-source-continuationp fn-pic-feed-funded fn-pic-demand fn-pic-at fn-octets-get
   fn-pic-sc-agent-coordinate-slots nth len update-nth)))))
(defthm fn-pic-held-next-preserves-source-continuation
 (let ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))))
  (implies (and (fn-pic-source-continuationp c fn-octets held)
                (member-eq (fn-pic-get phase d) '(:source-incoming :source-held)))
   (fn-pic-source-continuationp d fn-octets held)))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-preserves-source-continuation
 :in-theory (e/d (fn-pic-held-next)
  (fn-pic-source-continuationp fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-prp-incoming-slot
   fn-pic-at nth len update-nth)))))
(local (defthm fn-pic-sc-incoming-start-is-idempotent
 (equal (fn-pic-start-parser :source-incoming :source-incoming
         (fn-pic-start-parser :source-incoming :source-incoming c))
        (fn-pic-start-parser :source-incoming :source-incoming c))
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser)
  (fn-psc-begin fn-pic-at nth update-nth))))))
(local (defthm fn-pic-sc-agent-source-entry-is-start
 (let ((d (fn-pic-feed c observation)))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (equal d (fn-pic-start-parser :source-incoming :source-incoming d))))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-finish)
  (fn-pic-at fn-pic-start-parser fn-pic-parser fn-psc-step fn-psc-result fn-psc-begin
   fn-pic-source-result fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
   fn-pic-span-length fn-pic-groups-step fn-pic-block-add fn-pic-hash-start fn-pic-groups-start
   fn-pic-compare-start fn-pic-sc-agent-coordinate-slots nth len update-nth))))))
(local (defthm fn-pic-sc-next-source-entry-is-start
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (equal d (fn-pic-start-parser :source-incoming :source-incoming d))))
 :hints (("Goal" :use
  ((:instance fn-pic-sc-agent-source-entry-is-start (observation :control))
   (:instance fn-pic-sc-agent-source-entry-is-start
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-sc-agent-source-entry-is-start fn-pic-feed fn-pic-start-parser fn-pic-demand fn-pic-at
   fn-octets-get fn-pic-sc-agent-coordinate-slots nth len update-nth))))))
(local (defthm fn-pic-sc-agent-source-entry-shape
 (let ((d (fn-pic-feed c observation)))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (fn-pic-agent-shapep d)))
 :hints (("Goal" :in-theory (e/d (fn-pic-feed fn-pic-agent-shapep fn-pic-start-parser fn-pic-finish)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-psc-begin
   fn-pic-source-result fn-pic-spanp fn-pic-span-length fn-pic-groups-step fn-psc-step fn-psc-result
   fn-pic-compare-start fn-pic-sc-agent-coordinate-slots nth len update-nth))))))
(local (defthm fn-pic-sc-next-source-entry-shape
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (equal (fn-pic-get phase c) :agent)
                (equal (fn-pic-get phase d) :source-incoming))
   (fn-pic-agent-shapep d)))
 :hints (("Goal" :use
  ((:instance fn-pic-sc-agent-source-entry-shape (observation :control))
   (:instance fn-pic-sc-agent-source-entry-shape
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-sc-next-source-entry-is-start fn-pic-sc-agent-source-entry-is-start
   fn-pic-sc-agent-source-entry-shape fn-pic-feed fn-pic-agent-shapep fn-pic-start-parser fn-pic-demand fn-pic-at
   fn-octets-get fn-pic-sc-agent-coordinate-slots nth len update-nth))))))
(defthm fn-pic-next-agent-completion-establishes-source-continuation
 (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
  (implies (and (fn-pic-source-pair-contextp c fn-octets held)
                (fn-pic-agent-tracep c ticks fn-octets)
                (equal (fn-pic-get phase d) :source-incoming))
   (fn-pic-source-continuationp d fn-octets held)))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-next-source-entry-establishes-source-pair-agent-context
   fn-pic-sc-next-source-entry-is-start
   fn-pic-sc-next-source-entry-shape
   (:instance fn-pic-start-parser-establishes-source-continuation
    (c (mv-nth 1 (fn-pic-next c fuel fn-octets))) (incoming fn-octets) (mode :source-incoming)))
 :in-theory (e/d (fn-pic-agent-tracep)
  (fn-pic-source-pair-contextp fn-pic-agent-trace-start fn-pic-source-pair-agent-contextp
   fn-pic-source-continuationp fn-pic-sc-next-source-entry-is-start fn-pic-agent-shapep
   fn-pic-next fn-pic-start-parser fn-pic-at fn-pic-sc-agent-coordinate-slots nth len update-nth)))))
(defthm fn-pic-held-next-agent-completion-establishes-source-continuation
 (let ((d (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))))
  (implies (and (fn-pic-source-pair-contextp c fn-octets held)
                (fn-pic-agent-tracep c ticks fn-octets)
                (equal (fn-pic-get phase d) :source-incoming))
   (and (equal (fn-ioh-access (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                              (fn-pic-get incoming-token c) :read) :holder-readonly)
        (fn-pic-source-continuationp d fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-next-agent-completion-establishes-source-continuation
 :in-theory (e/d (fn-pic-held-next fn-pic-agent-tracep)
  (fn-pic-source-continuationp fn-pic-next fn-pic-agent-trace-start fn-pic-source-contextp
   fn-pic-parser fn-pic-sc-next-source-entry-is-start fn-ioh-access fn-ibc-carrier-row
   fn-prp-incoming-slot fn-pic-at nth len update-nth)))))
(in-theory (disable fn-pic-source-continuationp))
