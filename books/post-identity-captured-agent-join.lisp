; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Exact retained incoming agent at the actual funded controller boundary.
; Trace counters and octet-list denotations below are proof-only.
(in-package "ACL2")
(include-book "post-identity-captured-source-context")
(include-book "post-identity-source-cursor-agent-terminal")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pic-agent-trace-start (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-begin :agent (len incoming) (fn-pic-get msgid c)
               '(:agent 0 0) (len incoming)))

(defun fn-pic-agent-tracep (c ticks incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-pic-source-contextp c incoming) (stringp (fn-pic-get msgid c))
      (equal (fn-pic-get phase c) :agent) (natp ticks)
      (equal (fn-pic-parser c)
             (fn-psc-model-byte-run ticks (fn-pic-agent-trace-start c incoming) incoming nil))))

(local (defthm fn-pic-aj-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))

(local (defthm fn-pic-aj-step-done-is-unchanged
 (implies (equal (fn-psc-get phase c) :done) (equal (fn-psc-step c byte) c))
 :hints (("Goal" :in-theory (e/d (fn-psc-step) (nth len update-nth))))))

(local (defthm fn-pic-aj-run-done-is-unchanged
 (implies (equal (fn-psc-get phase c) :done)
  (equal (fn-psc-model-byte-run fuel c incoming held) c))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-model-demanded-byte nth len))))))

(local (defthm fn-pic-aj-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
   (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-model-demanded-byte nth len))))))

(local (defthm fn-pic-aj-run-successor
 (implies (natp n)
  (equal (fn-psc-model-byte-run (+ 1 n) c incoming held)
   (fn-psc-step (fn-psc-model-byte-run n c incoming held)
    (fn-psc-model-demanded-byte (fn-psc-model-byte-run n c incoming held) incoming held))))
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-pic-aj-run-addition (a n) (b 1))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held))
           (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (disable fn-psc-model-byte-run fn-pic-aj-run-addition fn-psc-step fn-psc-model-demanded-byte nth len)))))

(local (defthm fn-pic-aj-terminal-traces-agree
 (implies (and (natp n) (natp m)
               (equal (fn-psc-get phase (fn-psc-model-byte-run n c incoming held)) :done)
               (equal (fn-psc-get phase (fn-psc-model-byte-run m c incoming held)) :done))
  (equal (fn-psc-model-byte-run n c incoming held)
         (fn-psc-model-byte-run m c incoming held)))
 :hints (("Goal" :do-not-induct t :cases ((<= n m))
  :use ((:instance fn-pic-aj-run-addition (a n) (b (- m n)))
        (:instance fn-pic-aj-run-addition (a m) (b (- n m)))
        (:instance fn-pic-aj-run-done-is-unchanged
          (fuel (- m n)) (c (fn-psc-model-byte-run n c incoming held)))
        (:instance fn-pic-aj-run-done-is-unchanged
          (fuel (- n m)) (c (fn-psc-model-byte-run m c incoming held))))
  :in-theory (disable fn-psc-model-byte-run fn-pic-aj-run-addition
                     fn-pic-aj-run-done-is-unchanged nth len)))))

(local (defthm fn-pic-aj-nonpending-result-is-done
 (implies (not (equal (fn-psc-result c) :pending))
  (equal (fn-psc-get phase c) :done))
 :hints (("Goal" :in-theory (enable fn-psc-result)))))

(defthm fn-pic-agent-trace-completion-is-exact-and-bounded
 (implies
  (and (fn-pic-agent-tracep c ticks incoming)
       (not (equal (fn-psc-result
         (fn-psc-step (fn-pic-parser c)
          (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))) :pending)))
  (let ((p (fn-psc-step (fn-pic-parser c)
            (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))))
   (and (fn-psc-agent-resultp (fn-psc-result p) (len incoming))
        (equal (fn-psc-model-agent-span-octets p incoming)
               (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pic-aj-run-successor (n ticks) (held nil)
          (c (fn-pic-agent-trace-start c incoming)))
        (:instance fn-pic-aj-terminal-traces-agree (n (+ 1 ticks))
          (m (fn-psc-model-agent-cost (fn-pic-agent-trace-start c incoming) incoming))
          (held nil) (c (fn-pic-agent-trace-start c incoming)))
        (:instance fn-psc-agent-begin-paid-result-is-exact-and-bounded (msgid (fn-pic-get msgid c)))
        (:instance fn-psc-agent-begin-establishes-complete-state (msgid (fn-pic-get msgid c)))
        (:instance fn-psc-agent-completion-is-done-unfolds (c (fn-pic-agent-trace-start c incoming)))
        (:instance fn-psc-agent-complete-is-actual-paid-steps (c (fn-pic-agent-trace-start c incoming))))
  :in-theory (e/d (fn-pic-agent-tracep fn-pic-agent-trace-start fn-pic-source-contextp)
   (fn-psc-begin fn-psc-step fn-psc-result fn-psc-agent-resultp fn-psc-model-agent-span-octets
    fn-psc-model-agent-complete fn-psc-model-agent-cost fn-psc-model-byte-run fn-psc-model-demanded-byte
    fn-pb-path-agent fn-record-string-octets fn-pic-aj-run-successor fn-pic-aj-terminal-traces-agree
    fn-psc-agent-begin-paid-result-is-exact-and-bounded fn-psc-agent-begin-establishes-complete-state
    fn-psc-agent-completion-is-done-unfolds fn-psc-agent-complete-is-actual-paid-steps
    fn-pic-at fn-pic-spanp nth len update-nth)))))

(defthm fn-pic-begin-length-feed-establishes-agent-trace
 (let* ((c (fn-pic-begin selected grant held incoming-token (len incoming) msgid binding groups))
        (d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (true-listp incoming) (stringp msgid) (not (zp fuel))
                (equal (fn-pic-get phase c) :held-length)
                (fn-pic-observation-okp c (fn-pic-demand c) observation))
   (fn-pic-agent-tracep d 0 incoming)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-pic-begin fn-pic-finish fn-pic-feed-funded fn-pic-feed fn-pic-start-parser
                   fn-pic-agent-tracep fn-pic-agent-trace-start fn-pic-source-contextp fn-pic-parser fn-psc-begin)
   (fn-ab-held-binding-action fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
    fn-psc-step fn-psc-result fn-psc-done-result-is-stored fn-pic-at fn-pic-spanp
     nth len update-nth))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming nil))))))

; A valid effect at BEGIN already implies the held-length branch: no
; independent phase premise is needed at this actual producer boundary.
(defthm fn-pic-begin-length-feedback-establishes-agent-trace
 (let* ((c (fn-pic-begin selected grant held incoming-token (len incoming) msgid binding groups))
        (d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
  (implies (and (true-listp incoming) (stringp msgid) (not (zp fuel))
                (fn-pic-observation-okp c (fn-pic-demand c) observation))
   (fn-pic-agent-tracep d 0 incoming)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use fn-pic-begin-length-feed-establishes-agent-trace
  :in-theory (e/d (fn-pic-begin fn-pic-finish fn-pic-demand fn-pic-observation-okp)
   (fn-pic-feed-funded fn-pic-agent-tracep fn-ab-held-binding-action fn-pic-at nth len update-nth)))))

(local (defthm fn-pic-aj-run-preserves-proper-state
 (implies (true-listp c) (true-listp (fn-psc-model-byte-run fuel c incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run) (fn-psc-step fn-psc-model-demanded-byte nth len))))))

(local (defthm fn-pic-aj-trace-parser-is-proper
 (implies (fn-pic-agent-tracep c ticks incoming) (true-listp (fn-pic-parser c)))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-tracep fn-pic-agent-trace-start fn-psc-begin)
  (fn-psc-model-byte-run fn-pic-parser nth len update-nth))))))

(defthm fn-pic-feed-funded-pending-agent-preserves-trace
 (implies
  (and (fn-pic-agent-tracep c ticks incoming) (not (zp fuel))
       (fn-pic-observation-okp c (fn-pic-demand c) observation)
       (equal (fn-pic-observed-byte (fn-pic-demand c) observation)
              (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))
       (equal (fn-psc-result
         (fn-psc-step (fn-pic-parser c)
          (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))) :pending))
  (fn-pic-agent-tracep (mv-nth 1 (fn-pic-feed-funded c observation fuel)) (+ 1 ticks) incoming))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pic-feed-funded-preserves-source-context fn-pic-aj-trace-parser-is-proper
        (:instance fn-pic-aj-run-successor (n ticks) (held nil)
          (c (fn-pic-agent-trace-start c incoming))))
  :in-theory (e/d (fn-pic-feed-funded fn-pic-feed fn-pic-agent-tracep fn-pic-agent-trace-start fn-pic-parser)
   (fn-pic-source-contextp fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
    fn-psc-begin fn-psc-step fn-psc-result fn-psc-done-result-is-stored fn-psc-model-byte-run fn-psc-model-demanded-byte
    fn-pic-aj-trace-parser-is-proper fn-pic-aj-run-successor 
    fn-pic-at fn-pic-spanp nth len update-nth)))))

(local (defthm fn-pic-aj-take-is-current-take
 (implies (and (natp n) (<= n (len x)))
  (equal (fn-inj-take n x) (take n x)))
 :hints (("Goal" :induct (fn-inj-take n x)
  :in-theory (enable fn-inj-take take len nfix)))))

(local (defthm fn-pic-aj-nthcdr-length
 (implies (and (natp start) (<= start (len x)))
  (equal (len (nthcdr start x)) (- (len x) start)))
 :hints (("Goal" :induct (nthcdr start x) :in-theory (enable nthcdr len)))))

(local (defthm fn-pic-aj-first-three-slots
 (and (equal (nth 0 x) (car x)) (equal (nth 1 x) (cadr x))
      (equal (nth 2 x) (caddr x)))
 :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-pic-aj-zero-take
 (equal (take 0 x) nil)
 :hints (("Goal" :in-theory (enable take)))))

(local (defthm fn-pic-aj-sanitized-agent-is-exact-span
 (implies (and (fn-psc-agent-resultp (fn-psc-result p) (len incoming))
               (equal (fn-pic-get incoming-n c) (len incoming)))
  (equal
   (fn-pic-retained-agent
    (fn-pic-start-parser :source-incoming :source-incoming
     (fn-pic-set agent
      (let ((r (fn-psc-result p)))
       (if (and (equal (fn-pic-at 0 r) :agent)
                (natp (fn-pic-at 1 r)) (natp (fn-pic-at 2 r))
                (<= (fn-pic-at 1 r) (fn-pic-at 2 r))
                (<= (fn-pic-at 2 r) (nfix (fn-pic-get incoming-n c))))
        (list :agent (fn-pic-at 1 r) (fn-pic-at 2 r)) '(:agent 0 0)))
      (fn-pic-set parser p c))) incoming)
   (fn-psc-model-agent-span-octets p incoming)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-agent-resultp fn-pic-retained-agent fn-psc-model-agent-span-octets fn-pic-start-parser)
   (fn-psc-result fn-psc-done-result-is-stored fn-psc-begin fn-inj-take take nthcdr nth len update-nth fn-pic-at))))))

(local (defthm fn-pic-aj-context-implies-captured-length
 (implies (fn-pic-source-contextp c incoming)
  (equal (fn-pic-get incoming-n c) (len incoming)))
 :hints (("Goal" :in-theory (enable fn-pic-source-contextp)))))

(defthm fn-pic-feed-funded-agent-completion-retains-current-agent
 (implies
  (and (fn-pic-agent-tracep c ticks incoming) (not (zp fuel))
       (fn-pic-observation-okp c (fn-pic-demand c) observation)
       (equal (fn-pic-observed-byte (fn-pic-demand c) observation)
              (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))
       (not (equal (fn-psc-result
         (fn-psc-step (fn-pic-parser c)
          (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))) :pending)))
  (let ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
   (and (equal (fn-pic-get phase d) :source-incoming)
        (fn-pic-source-contextp d incoming)
        (equal (fn-pic-retained-agent d incoming)
               (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pic-agent-trace-completion-is-exact-and-bounded
        fn-pic-feed-funded-preserves-source-context
        fn-pic-aj-context-implies-captured-length
        (:instance fn-pic-aj-sanitized-agent-is-exact-span
         (p (fn-psc-step (fn-pic-parser c)
               (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil)))))
  :in-theory (e/d (fn-pic-agent-tracep fn-pic-feed-funded fn-pic-feed fn-pic-start-parser)
   (fn-pic-source-contextp fn-pic-agent-trace-start fn-pic-parser fn-pic-aj-first-three-slots
    fn-psc-agent-resultp fn-pic-aj-context-implies-captured-length
    fn-pic-aj-sanitized-agent-is-exact-span fn-pic-retained-agent fn-psc-model-agent-span-octets
    fn-pb-path-agent fn-record-string-octets fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
    fn-psc-step fn-psc-result fn-psc-done-result-is-stored fn-psc-model-demanded-byte fn-psc-begin
    fn-pic-at fn-pic-spanp nth len update-nth)))))

(local (defthm fn-pic-aj-step-preserves-mode
 (equal (fn-psc-get mode (fn-psc-step c byte)) (fn-psc-get mode c))
 :hints (("Goal" :use fn-psc-step-preserves-configuration
  :in-theory (e/d (fn-psc-configuration)
   (fn-psc-step-preserves-configuration fn-pic-aj-first-three-slots fn-psc-step nth len update-nth))))))

(local (defthm fn-pic-aj-run-preserves-mode
 (equal (fn-psc-get mode (fn-psc-model-byte-run fuel c incoming held)) (fn-psc-get mode c))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run)
   (fn-pic-aj-first-three-slots fn-psc-step fn-psc-model-demanded-byte nth len))))))

(local (defthm fn-pic-aj-trace-parser-is-agent-mode
 (implies (fn-pic-agent-tracep c ticks incoming)
  (equal (fn-psc-get mode (fn-pic-parser c)) :agent))
 :hints (("Goal" :use (:instance fn-pic-aj-run-preserves-mode
   (fuel ticks) (c (fn-pic-agent-trace-start c incoming)) (held nil))
  :in-theory (e/d (fn-pic-agent-tracep fn-pic-agent-trace-start fn-psc-begin)
  (fn-pic-source-contextp fn-pic-aj-first-three-slots fn-pic-aj-run-preserves-mode
   fn-pic-parser fn-psc-model-byte-run nth len update-nth))))))

(local (defthm fn-pic-aj-trace-demand-is-parser-demand
 (implies (fn-pic-agent-tracep c ticks incoming)
  (equal (fn-pic-demand c) (fn-psc-demand (fn-pic-parser c))))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-tracep fn-pic-demand)
  (fn-pic-source-contextp fn-pic-aj-first-three-slots fn-pic-parser fn-psc-demand fn-pic-at nth len update-nth))))))

(defthm fn-pic-feed-funded-source-entry-retains-current-agent
 (implies
  (and (fn-pic-agent-tracep c ticks incoming)
       (equal (fn-pic-observed-byte (fn-pic-demand c) observation)
              (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil))
       (equal (fn-pic-get phase (mv-nth 1 (fn-pic-feed-funded c observation fuel))) :source-incoming))
  (let ((d (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
   (and (fn-pic-source-contextp d incoming)
        (equal (fn-pic-retained-agent d incoming)
               (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use fn-pic-feed-funded-agent-completion-retains-current-agent
  :in-theory (e/d (fn-pic-agent-tracep fn-pic-feed-funded fn-pic-feed fn-pic-start-parser fn-pic-finish)
   (fn-pic-source-contextp fn-pic-parser fn-pic-agent-trace-start fn-pic-aj-first-three-slots
    fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-psc-step fn-psc-result
    fn-psc-done-result-is-stored fn-psc-begin fn-psc-model-demanded-byte
    fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-at nth len update-nth)))))

(local (defthm fn-pic-aj-trace-implies-agent-phase
 (implies (fn-pic-agent-tracep c ticks incoming) (equal (fn-pic-get phase c) :agent))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-tracep)
  (fn-pic-source-contextp fn-pic-parser fn-pic-agent-trace-start fn-pic-aj-first-three-slots nth len))))))

(local (defthm fn-pic-aj-incoming-read-is-model-byte
 (implies (and (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-at 0 (fn-pic-demand c)) :incoming))
  (equal
   (fn-pic-observed-byte (fn-pic-demand c)
     (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
        (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))
   (fn-psc-model-demanded-byte (fn-pic-parser c) fn-octets nil)))
 :hints (("Goal" :use (:instance fn-pic-aj-trace-demand-is-parser-demand (incoming fn-octets))
  :in-theory (e/d (fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
   (fn-pic-agent-tracep fn-pic-parser fn-pic-demand fn-psc-demand fn-pic-aj-trace-demand-is-parser-demand))))))

(local (defthm fn-pic-aj-control-is-model-byte
 (implies (and (fn-pic-agent-tracep c ticks incoming) (equal (fn-pic-demand c) :control))
  (equal (fn-pic-observed-byte (fn-pic-demand c) :control)
         (fn-psc-model-demanded-byte (fn-pic-parser c) incoming nil)))
 :hints (("Goal" :use fn-pic-aj-trace-demand-is-parser-demand
  :in-theory (e/d (fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-at nth)
   (fn-pic-agent-tracep fn-pic-parser fn-pic-demand fn-psc-demand fn-pic-aj-trace-demand-is-parser-demand))))))

(defthm fn-pic-next-source-entry-retains-current-agent
 (implies
  (and (fn-pic-agent-tracep c ticks fn-octets)
       (equal (fn-pic-get phase (mv-nth 1 (fn-pic-next c fuel fn-octets))) :source-incoming))
  (let ((d (mv-nth 1 (fn-pic-next c fuel fn-octets))))
   (and (fn-pic-source-contextp d fn-octets)
        (equal (fn-pic-retained-agent d fn-octets)
               (fn-pb-path-agent fn-octets (fn-record-string-octets (fn-pic-get msgid c)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pic-feed-funded-source-entry-retains-current-agent
          (incoming fn-octets) (observation :control))
        (:instance fn-pic-feed-funded-source-entry-retains-current-agent
          (incoming fn-octets) (fuel (- fuel 1))
          (observation (list :incoming-byte (fn-pic-get incoming-token c)
            (fn-pic-at 1 (fn-pic-demand c)) (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets))))
        (:instance fn-pic-aj-trace-implies-agent-phase (incoming fn-octets))
        fn-pic-aj-incoming-read-is-model-byte
        (:instance fn-pic-aj-control-is-model-byte (incoming fn-octets)))
  :in-theory (e/d (fn-pic-next fn-pic-finish)
   (fn-pic-feed-funded fn-pic-agent-tracep fn-pic-source-contextp fn-pic-demand fn-pic-parser fn-psc-demand
    fn-pic-observed-byte fn-psc-model-demanded-byte fn-pic-aj-first-three-slots
    fn-pic-aj-incoming-read-is-model-byte fn-pic-aj-control-is-model-byte fn-pic-aj-trace-implies-agent-phase
    fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-at nth len update-nth)))))

(defun fn-pic-agent-contextp (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-pic-source-contextp c incoming) (stringp (fn-pic-get msgid c))
      (equal (fn-pic-retained-agent c incoming)
             (fn-pb-path-agent incoming (fn-record-string-octets (fn-pic-get msgid c))))))

(local (defthm fn-pic-aj-other-update-preserves-agent-context
 (implies (and (natp slot) (not (member-equal slot '(5 7 10 11))))
  (equal (fn-pic-agent-contextp (update-nth slot value c) incoming)
         (fn-pic-agent-contextp c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-pic-agent-contextp fn-pic-source-contextp fn-pic-retained-agent)
  (fn-pic-aj-first-three-slots fn-pb-path-agent fn-record-string-octets fn-pic-at fn-pic-spanp nth len update-nth))))))

(local (defthm fn-pic-aj-feed-preserves-retained-agent-after-agent
 (implies (not (equal (fn-pic-get phase c) :agent))
  (and (equal (fn-pic-retained-agent (fn-pic-feed c observation) incoming) (fn-pic-retained-agent c incoming))
       (equal (fn-pic-get msgid (fn-pic-feed c observation)) (fn-pic-get msgid c))))
 :hints (("Goal" :in-theory
  (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-hash-start fn-pic-groups-start
         fn-pic-finish fn-pic-block-add fn-pic-retained-agent)
   (fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-at fn-pic-spanp
    fn-pic-groups-step fn-pic-source-result fn-pic-span-length fn-psc-step fn-psc-result fn-psc-begin
    fn-pic-aj-first-three-slots take nthcdr nth len update-nth))))))

(defthm fn-pic-feed-funded-preserves-agent-context-after-agent
 (implies (and (fn-pic-agent-contextp c incoming) (not (equal (fn-pic-get phase c) :agent)))
  (fn-pic-agent-contextp (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming))
 :rule-classes nil
 :hints (("Goal" :use fn-pic-feed-funded-preserves-source-context
  :in-theory (e/d (fn-pic-agent-contextp fn-pic-feed-funded)
   (fn-pic-source-contextp fn-pic-feed fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets
    fn-pic-aj-first-three-slots nth len update-nth)))))

(defthm fn-pic-next-preserves-agent-context-after-agent
 (implies (and (fn-pic-agent-contextp c fn-octets) (not (equal (fn-pic-get phase c) :agent)))
  (fn-pic-agent-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-agent-context-after-agent (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-preserves-agent-context-after-agent (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
  :in-theory (e/d (fn-pic-next fn-pic-agent-contextp fn-pic-finish)
   (fn-pic-source-contextp fn-pic-feed-funded fn-pic-demand fn-pic-retained-agent fn-pb-path-agent
    fn-record-string-octets fn-pic-aj-first-three-slots fn-pic-at nth len update-nth)))))

(local (defthm fn-pic-aj-feed-preserves-msgid
 (equal (fn-pic-get msgid (fn-pic-feed c observation)) (fn-pic-get msgid c))
 :hints (("Goal" :in-theory
  (e/d (fn-pic-feed fn-pic-start-parser fn-pic-compare-start fn-pic-hash-start fn-pic-groups-start fn-pic-finish fn-pic-block-add)
   (fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-at fn-pic-spanp fn-pic-groups-step
    fn-pic-source-result fn-pic-span-length fn-psc-step fn-psc-result fn-psc-begin
    fn-pic-aj-first-three-slots nth len update-nth))))))

(local (defthm fn-pic-aj-next-preserves-msgid
 (equal (fn-pic-get msgid (mv-nth 1 (fn-pic-next c fuel fn-octets))) (fn-pic-get msgid c))
 :hints (("Goal" :use ((:instance fn-pic-aj-feed-preserves-msgid (observation :control))
  (:instance fn-pic-aj-feed-preserves-msgid
   (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
    (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
  :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
  (fn-pic-aj-feed-preserves-msgid fn-pic-feed fn-pic-demand fn-pic-at fn-pic-aj-first-three-slots nth len update-nth))))))

(defthm fn-pic-next-source-entry-establishes-agent-context
 (implies (and (fn-pic-agent-tracep c ticks fn-octets)
               (equal (fn-pic-get phase (mv-nth 1 (fn-pic-next c fuel fn-octets))) :source-incoming))
  (fn-pic-agent-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-next-source-entry-retains-current-agent fn-pic-aj-next-preserves-msgid)
  :in-theory (e/d (fn-pic-agent-contextp fn-pic-agent-tracep)
   (fn-pic-source-contextp fn-pic-next fn-pic-parser fn-pic-agent-trace-start fn-pic-aj-next-preserves-msgid
    fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-aj-first-three-slots nth len update-nth)))))

(local (defthm fn-pic-aj-digest-effect-ready-excludes-agent-phase
 (implies (equal (mv-nth 0 (fn-pic-digest-effect c fuel pgs-digest-state)) :ready)
  (not (equal (fn-pic-get phase c) :agent)))
 :hints (("Goal" :cases ((equal (fn-pic-get phase c) :agent))
  :in-theory (e/d (fn-pic-digest-effect)
   (fn-pic-digest-scalar-guardp fn-pic-span-length fn-pic-at fn-pic-aj-first-three-slots
    pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets pgs-dcb-read-demand pgs-dcb-next-byte-offset
    fn-pic-digest-block nth len update-nth))))))

(defthm fn-pic-digest-next-preserves-agent-context
 (implies (fn-pic-agent-contextp c incoming)
  (fn-pic-agent-contextp (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-aj-digest-effect-ready-excludes-agent-phase (fuel (- fuel 1)))
  (:instance fn-pic-feed-funded-preserves-agent-context-after-agent
   (observation (mv-nth 1 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))
   (fuel (+ 1 (mv-nth 2 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state))))))
  :in-theory (e/d (fn-pic-digest-next fn-pic-agent-contextp fn-pic-finish)
   (fn-pic-aj-digest-effect-ready-excludes-agent-phase fn-pic-source-contextp fn-pic-feed-funded fn-pic-digest-effect fn-pic-at
    fn-pic-retained-agent fn-pb-path-agent fn-record-string-octets fn-pic-aj-first-three-slots nth len update-nth)))))
