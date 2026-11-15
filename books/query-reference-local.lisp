; Actual raw C callees and pool frame obligations. All new proof events
; are UNRUN source proposals, not admission/certification evidence.
(in-package "ACL2")
(include-book "query-reference-model")
(include-book "machines-c-groups")
(include-book "pool-ranges")
(include-book "arm-children")
(fn2-book-layer :c)

; The paired one-row/count deltas are separate proof questions from
; post-state source validity. In particular the start rollback must be
; shown to cancel its first acquisition when the second is refused.
(defthm fn2-id-query-release-query-reference-delta
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code d p) (fn2-id-query-release tx fn2-id-decides fn2-pool)
   (declare (ignore code))
   (fn2-qr-local-deltap tx fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-id-query-release fn2-qr-local-deltap)
          :use (fn2-pool-query-acquire-counter-effect fn2-pool-query-release-counter-effect))))
(defthm fn2-id-decide-start-query-reference-delta
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code t2 d f2 p) (fn2-id-decide-start tx mslot mgen moff mlen dslot dgen doff ok os og b0 fn2-succ-txns fn2-id-decides fn2-fields fn2-pool)
   (declare (ignore code t2 f2))
   (fn2-qr-local-deltap tx fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-id-decide-start fn2-qr-local-deltap)
          :use (fn2-pool-query-acquire-counter-effect fn2-pool-query-release-counter-effect))))

(defthm fn2-id-query-release-query-reference-transfer
 (implies (and (fn2-pool-semanticp fn2-pool)
               (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code d p) (fn2-id-query-release tx fn2-id-decides fn2-pool)
   (declare (ignore code))
   (fn2-qr-transitionp fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-id-query-release fn2-qr-transitionp)
                                 (fn2-query-references-accountedp fn2-pool-semanticp
                                  fn2-qr-reference-count fn2-qr-counts-matchp
                                  fn2-qr-descriptors-validp)))))

(defthm fn2-id-decide-start-query-reference-transfer
 (implies (and (fn2-succ-txnsp fn2-succ-txns) (fn2-succ-txns-wfp fn2-succ-txns)
               (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
               (fn2-pool-semanticp fn2-pool)
               (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code t2 d f2 p) (fn2-id-decide-start tx mslot mgen moff mlen dslot dgen doff ok os og b0 fn2-succ-txns fn2-id-decides fn2-fields fn2-pool)
   (declare (ignore code t2 f2))
   (fn2-qr-transitionp fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-id-decide-start fn2-qr-transitionp)
                                 (fn2-query-references-accountedp fn2-pool-semanticp
                                  fn2-qr-reference-count fn2-qr-counts-matchp
                                  fn2-qr-descriptors-validp)))))

(defthm fn2-id-decide-step-query-reference-transfer
 (implies (and (fn2-succ-txnsp fn2-succ-txns) (fn2-succ-txns-wfp fn2-succ-txns)
               (fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)
               (fn2-overlay-indexp fn2-overlay-index) (fn2-overlay-index-wfp fn2-overlay-index)
               (fn2-run-installedp fn2-run-installed) (fn2-run-installed-wfp fn2-run-installed)
               (fn2-run-cursorsp fn2-run-cursors) (fn2-run-cursors-wfp fn2-run-cursors)
               (fn2-run-pathsp fn2-run-paths) (fn2-run-paths-wfp fn2-run-paths)
               (fn2-run-cachep fn2-run-cache) (fn2-run-cache-wfp fn2-run-cache)
               (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
               (fn2-pool-semanticp fn2-pool)
               (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code t2 d c2 r2 f2 p) (fn2-id-decide-step tx budget b0 fn2-succ-txns fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
   (declare (ignore code t2 c2 r2 f2))
   (fn2-qr-transitionp fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-id-decide-step fn2-qr-transitionp)
                                 (fn2-query-references-accountedp fn2-pool-semanticp
                                  fn2-qr-reference-count fn2-qr-counts-matchp
                                  fn2-qr-descriptors-validp)))))

(defthm fn2-succ-release-query-reference-transfer
 (implies (and (fn2-succ-txnsp fn2-succ-txns) (fn2-succ-txns-wfp fn2-succ-txns)
               (fn2-succ-slotsp fn2-succ-slots) (fn2-succ-slots-wfp fn2-succ-slots)
               (fn2-pool-semanticp fn2-pool)
               (fn2-query-references-accountedp fn2-pool fn2-id-decides))
  (mv-let (code t2 s2 d p) (fn2-succ-release tx fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-pool)
   (declare (ignore code t2 s2))
   (fn2-qr-transitionp fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-succ-release fn2-qr-transitionp)
                                 (fn2-query-references-accountedp fn2-pool-semanticp
                                  fn2-qr-reference-count fn2-qr-counts-matchp
                                  fn2-qr-descriptors-validp)))))

; Ordinary pool APIs leave descriptors untouched. Positive counted refs
; force a refusal of destructive operations; mutations of other slots, or
; I/O loans on readable slots, preserve every named window/count relation.
; Query acquire/release are NOT in this frame: they require the paired C
; transition lemmas above. Init is a separate cold/bootstrap boundary.
(defconst *fn2-qr-framed-pool-operations*
 '(:reserve :release :lease-in :adapter-write :complete-in :lease-out :release-out
   :hand :accept-hand :read :write :reset))
(defthm fn2-qr-ordinary-pool-operation-frame
 (implies (and (member-eq op *fn2-qr-framed-pool-operations*) (fn2-pool-semanticp p)
               (fn2-query-references-accountedp p d))
          (fn2-query-references-accountedp (cadr (fn2-pool-operation op a p)) d))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-pool-operation fn2-pool-workspace-code
                                   fn2-query-references-accountedp))))
(defthm fn2-pool-copy-range-query-reference-frame
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool d))
          (fn2-query-references-accountedp (mv-nth 1 (fn2-pool-copy-range src sgen soff dst dgen doff len ok os og fn2-pool)) d))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-pool-copy-range fn2-pool-workspace-code
                                   fn2-query-references-accountedp))))
(defthm fn2-pool-drop-prefix-query-reference-frame
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool d))
          (fn2-query-references-accountedp (mv-nth 2 (fn2-pool-drop-prefix slot gen k cursor limit ok os og fn2-pool)) d))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-pool-drop-prefix fn2-pool-workspace-code
                                   fn2-query-references-accountedp))))
(defthm fn2-pool-truncate-query-reference-frame
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool d))
          (fn2-query-references-accountedp (mv-nth 1 (fn2-pool-truncate slot gen n ok os og fn2-pool)) d))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-pool-truncate fn2-pool-workspace-code
                                   fn2-query-references-accountedp))))
(defthm fn2-pool-accept-own-query-reference-frame
 (implies (and (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool d))
          (fn2-query-references-accountedp (mv-nth 1 (fn2-pool-accept-own slot gen ok os og fn2-pool)) d))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-pool-accept-own fn2-pool-workspace-code
                                   fn2-query-references-accountedp))))

; Published/replay cleanup is an actual caller, not implicitly covered by
; the three-case observer dispatcher. Its guard rejects active replay rows.
(defthm fn2-succ-replay-sweep-query-reference-transfer
 (implies (and (fn2-succ-txnsp fn2-succ-txns) (fn2-succ-txns-wfp fn2-succ-txns)
               (fn2-succ-slotsp fn2-succ-slots) (fn2-succ-slots-wfp fn2-succ-slots)
               (fn2-pool-semanticp fn2-pool) (fn2-query-references-accountedp fn2-pool fn2-id-decides)
               (natp tx))
  (mv-let (code t2 s2 d p) (fn2-succ-replay-sweep k tx fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-pool)
   (declare (ignore code t2 s2))
   (fn2-qr-transitionp fn2-pool p fn2-id-decides d)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-succ-replay-sweep k tx fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-pool)
          :in-theory (enable fn2-succ-replay-sweep fn2-qr-transitionp)
          :use fn2-succ-release-query-reference-transfer)))

; Active descriptor -> counted held source -> stable bytes under every
; ordinary pool export. Raw byte loops are not standalone exports here.
(defthm fn2-qr-first-held-window-pool-frame
 (implies (and (member-eq op *fn2-qr-framed-pool-operations*) (fn2-pool-semanticp p)
               (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
               (logbitp 0 (fn2-id-decides-qmask i d)))
  (let* ((q (cadr (fn2-pool-operation op a p))) (s (fn2-id-decides-q1slot i d))
         (off (fn2-id-decides-q1off i d)) (len (fn2-id-decides-q1len i d)))
   (and (equal (fn2-pool-gen s q) (fn2-pool-gen s p))
        (equal (fn2-pool-logical-octets len (+ (fn2-pool-base s q) off) q)
               (fn2-pool-logical-octets len (+ (fn2-pool-base s p) off) p)))))
 :rule-classes nil
 :hints (("Goal" :use fn2-qr-first-active-reference-positive
          :in-theory (enable fn2-pool-operation fn2-pool-workspace-code))))
(defthm fn2-qr-second-held-window-pool-frame
 (implies (and (member-eq op *fn2-qr-framed-pool-operations*) (fn2-pool-semanticp p)
               (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
               (logbitp 1 (fn2-id-decides-qmask i d)))
  (let* ((q (cadr (fn2-pool-operation op a p))) (s (fn2-id-decides-q2slot i d))
         (off (fn2-id-decides-q2off i d)) (len (fn2-id-decides-q2len i d)))
   (and (equal (fn2-pool-gen s q) (fn2-pool-gen s p))
        (equal (fn2-pool-logical-octets len (+ (fn2-pool-base s q) off) q)
               (fn2-pool-logical-octets len (+ (fn2-pool-base s p) off) p)))))
 :rule-classes nil
 :hints (("Goal" :use fn2-qr-second-active-reference-positive
          :in-theory (enable fn2-pool-operation fn2-pool-workspace-code))))
