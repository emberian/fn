; Producer-established legal retained incoming geometry, without parser semantics.
(in-package "ACL2")
(include-book "post-identity-captured-hash-choice")
(defun fn-pic-source-contextp (c incoming)
 (let ((a (fn-pic-get agent c)) (d (fn-pic-get incoming-desc c)))
  (and (true-listp incoming) (equal (fn-pic-get incoming-n c) (len incoming))
       (natp (fn-pic-at 1 a)) (natp (fn-pic-at 2 a))
       (<= (fn-pic-at 1 a) (fn-pic-at 2 a)) (<= (fn-pic-at 2 a) (len incoming))
       (or (not d) (fn-pic-spanp d (len incoming))))))
(local (defthm fn-pic-sc-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-sc-other-update-preserves-context
 (implies (and (natp i) (not (member-equal i '(5 10 11))))
  (equal (fn-pic-source-contextp (update-nth i value c) incoming)
         (fn-pic-source-contextp c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp) (nth update-nth fn-pic-at fn-pic-spanp))))))
(local (defthm fn-pic-sc-source-result-is-legal
 (or (not (fn-pic-source-result r n)) (fn-pic-spanp (fn-pic-source-result r n) n))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-result) (fn-pic-at fn-pic-spanp))))))
(local (defthm fn-pic-sc-zero-span-is-legal
 (implies (natp n) (fn-pic-spanp '(0 0 0) n))
 :hints (("Goal" :in-theory (enable fn-pic-spanp fn-pic-at)))))
(local (defthm fn-pic-sc-start-parser-preserves-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp (fn-pic-start-parser mode phase c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-start-parser) (fn-pic-source-contextp nth update-nth))))))
(local (defthm fn-pic-sc-compare-start-preserves-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp (fn-pic-compare-start c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-compare-start fn-pic-source-contextp fn-pic-finish)
  (fn-pic-at fn-pic-spanp fn-pic-span-length nth update-nth))))))
(local (defthm fn-pic-sc-finish-preserves-context
 (equal (fn-pic-source-contextp (fn-pic-finish result c) incoming)
        (fn-pic-source-contextp c incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-finish) (fn-pic-source-contextp nth update-nth))))))
(defthm fn-pic-begin-establishes-source-context
 (implies (true-listp incoming)
  (fn-pic-source-contextp
   (fn-pic-begin selected grant held incoming-token (len incoming) msgid binding groups) incoming))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-begin fn-pic-source-contextp fn-pic-finish)
  (fn-ab-held-binding-action fn-pic-at fn-pic-spanp nth update-nth)))))
(local (defthm fn-pic-sc-valid-source-result-preserves-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp (fn-pic-set incoming-desc (fn-pic-source-result r (fn-pic-get incoming-n c)) c) incoming))
 :hints (("Goal" :use (:instance fn-pic-sc-source-result-is-legal (n (len incoming)))
 :in-theory (e/d (fn-pic-source-contextp)
  (fn-pic-at fn-pic-source-result fn-pic-spanp nth update-nth))))))
(local (defthm fn-pic-sc-valid-agent-result-preserves-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp
   (fn-pic-set agent
    (if (and (equal (fn-pic-at 0 r) :agent)
             (natp (fn-pic-at 1 r)) (natp (fn-pic-at 2 r))
             (<= (fn-pic-at 1 r) (fn-pic-at 2 r))
             (<= (fn-pic-at 2 r) (nfix (fn-pic-get incoming-n c))))
     (list :agent (fn-pic-at 1 r) (fn-pic-at 2 r)) '(:agent 0 0)) c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp)
  (fn-pic-at fn-pic-spanp nth update-nth))))))
(local (defthm fn-pic-sc-agent-after-parser-update
 (equal (fn-pic-source-contextp (update-nth 10 a (update-nth 9 p c)) incoming)
        (fn-pic-source-contextp (update-nth 10 a c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp) (fn-pic-at fn-pic-spanp nth update-nth))))))
(local (defthm fn-pic-sc-source-after-parser-update
 (equal (fn-pic-source-contextp (update-nth 11 d (update-nth 9 p c)) incoming)
        (fn-pic-source-contextp (update-nth 11 d c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp) (fn-pic-at fn-pic-spanp nth update-nth))))))
(local (defthm fn-pic-sc-context-implies-captured-extent
 (implies (fn-pic-source-contextp c incoming) (equal (fn-pic-get incoming-n c) (len incoming)))
 :rule-classes (:forward-chaining)
 :hints (("Goal" :in-theory (enable fn-pic-source-contextp)))))
(local (defthm fn-pic-sc-context-of-legal-descriptor
 (implies (and (fn-pic-source-contextp c incoming)
               (or (not d) (fn-pic-spanp d (len incoming))))
  (fn-pic-source-contextp (fn-pic-set incoming-desc d c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp) (fn-pic-at fn-pic-spanp nth update-nth))))))
(local (defthm fn-pic-sc-context-of-legal-agent
 (implies (and (fn-pic-source-contextp c incoming) (natp start) (natp end)
               (<= start end) (<= end (len incoming)))
  (fn-pic-source-contextp (fn-pic-set agent (list :agent start end) c) incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-contextp) (fn-pic-at fn-pic-spanp nth update-nth))))))
(defthm fn-pic-feed-funded-preserves-source-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming))
 :rule-classes nil
 :hints (("Goal" :use (fn-pic-sc-context-implies-captured-extent
  (:instance fn-pic-sc-source-result-is-legal
   (r (fn-psc-result (fn-psc-step (fn-pic-parser c) (fn-pic-observed-byte (fn-pic-demand c) observation))))
   (n (len incoming))))
 :in-theory (e/d (fn-pic-feed-funded fn-pic-feed fn-pic-hash-start fn-pic-groups-start fn-pic-block-add)
  (fn-pic-source-contextp fn-pic-at fn-pic-spanp fn-pic-source-result fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte
   fn-pic-start-parser fn-pic-compare-start fn-pic-finish fn-psc-step fn-psc-result fn-psc-begin
   fn-pic-groups-step nth update-nth)))))
(defthm fn-pic-next-preserves-source-context
 (implies (fn-pic-source-contextp c fn-octets)
  (fn-pic-source-contextp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-preserves-source-context (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-preserves-source-context (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next)
  (fn-pic-source-contextp fn-pic-feed-funded fn-pic-demand fn-pic-finish fn-pic-at fn-octets-get nth update-nth)))))
(defthm fn-pic-digest-next-preserves-source-context
 (implies (fn-pic-source-contextp c incoming)
  (fn-pic-source-contextp (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pic-feed-funded-preserves-source-context
    (observation (mv-nth 1 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))
    (fuel (+ 1 (mv-nth 2 (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)))))
 :in-theory (e/d (fn-pic-digest-next)
  (fn-pic-source-contextp fn-pic-feed-funded fn-pic-digest-effect fn-pic-finish fn-pic-at nth update-nth)))))
