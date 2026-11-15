; Independent query-descriptor accounting. These table traversals are proof/
; test observers only, never served guards or a query implementation.
(in-package "ACL2")
(include-book "query-reference-local")
(include-book "assembly-callbacks-c")
(include-book "owed-discharge")
(fn2-book-layer :c)

(defun fn2-core-query-references-accountedp (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))) (answer)
  (fn2-query-references-accountedp fn2-pool fn2-id-decides) answer))

; Separate the independent named-window domain from its exact-count claim
; so the hypothesis-removal witness can retain all physical/typed premises.
(defun fn2-core-query-reference-domainp (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))) (answer)
   (and (fn2-pool-semanticp fn2-pool)
        (fn2-qr-descriptors-validp (fn2-id-decides-rows fn2-id-decides) fn2-id-decides fn2-pool)) answer)))
(defun fn2-core-query-counts-matchp (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))) (answer)
  (fn2-qr-counts-matchp (fn2-pool-rows fn2-pool) fn2-pool fn2-id-decides) answer))

; Proof-only dispatcher calls the ACTUAL served core subjects. The model
; above does not obtain its expected counts from any of these operations.
(defconst *fn2-query-reference-operations* '(:start :step :cancel))
(defun-nx fn2-query-reference-step (op a core)
 (case op
  (:start (mv-let (code after)
           (fn2-identity-decide-start (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a) (nth 4 a)
             (nth 5 a) (nth 6 a) (nth 7 a) (nth 8 a) (nth 9 a) (nth 10 a) core)
           (declare (ignore code)) after))
  (:step (mv-let (code after) (fn2-identity-decide (nth 0 a) (nth 1 a) core) (declare (ignore code)) after))
  (:cancel (mv-let (code after) (fn2-successor-release (nth 0 a) core) (declare (ignore code)) after))
  (otherwise core)))
(defun-nx fn2-query-reference-hyps (op core)
 (and (member-eq op *fn2-query-reference-operations*)
      (fn2-core-query-reference-domainp core) (fn2-core-query-counts-matchp core)))
(defun fn2-query-reference-afterp (domain counts same-rows same-output-counts)
 (declare (xargs :guard t))
 (and domain counts same-rows same-output-counts))
(defun-nx fn2-query-reference-conclusion (op a core)
 (let ((after (fn2-query-reference-step op a core)))
  (fn2-query-reference-afterp (fn2-core-query-reference-domainp after) (fn2-core-query-counts-matchp after)
       (equal (fn2-pool-rows (fn2-core-pool after)) (fn2-pool-rows (fn2-core-pool core)))
       (equal (fn2-query-output-counts (fn2-pool-rows (fn2-core-pool core)) (fn2-core-pool after))
              (fn2-query-output-counts (fn2-pool-rows (fn2-core-pool core)) (fn2-core-pool core))))))
(defthm-owed fn2-core-query-reference-accounting (op a core)
 (implies (fn2-query-reference-hyps op core) (fn2-query-reference-conclusion op a core))
 :schema :invariant :from (:columns fn2-id-decides)
 :teeth (fn2-query-reference-accounting-teeth)
 :doc "Actual generic identity start/step/cancellation preserve exact active-window multiplicity over current pool generations, valid readable source ownership and bounds, and the separate OpRef output-loan count. Model traversals are proof/test-only; no served scan establishes these premises.")

; Actual core callee corollaries, UNRUN. The hypothesis is precisely the
; existing H's state part, not a new caller readiness flag or a dispatcher
; summary. Scheduler/trace wake effects are outside the two observed children.
(defun-nx fn2-query-reference-core-resultp (before after)
 (fn2-query-reference-afterp (fn2-core-query-reference-domainp after) (fn2-core-query-counts-matchp after)
  (equal (fn2-pool-rows (fn2-core-pool after)) (fn2-pool-rows (fn2-core-pool before)))
  (equal (fn2-query-output-counts (fn2-pool-rows (fn2-core-pool before)) (fn2-core-pool after))
         (fn2-query-output-counts (fn2-pool-rows (fn2-core-pool before)) (fn2-core-pool before)))))
(defthm fn2-identity-decide-start-query-references-accounted
 (implies (and (fn2-core-query-reference-domainp fn2-core) (fn2-core-query-counts-matchp fn2-core))
          (fn2-query-reference-core-resultp fn2-core (mv-nth 1 (fn2-identity-decide-start tx ms mg mo ml ds dg doff ok os og fn2-core))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn2-id-decide-start-query-reference-transfer
                 (fn2-pool (fn2-core-pool fn2-core))
                 (fn2-id-decides (fn2-core-id-decides fn2-core))
                 (fn2-succ-txns (fn2-core-succ-txns fn2-core))
                 (fn2-fields (fn2-core-fields fn2-core))
                 (mslot ms)
                 (mgen mg)
                 (moff mo)
                 (mlen ml)
                 (dslot ds)
                 (dgen dg)
                 (b0 (mv-nth 1 (fn2-idc-stripe tx (fn2-fc-rows (fn2-core-fc fn2-core)) (fn2-core-id-decides fn2-core) (fn2-core-fields fn2-core))))
)
          :in-theory (enable fn2-identity-decide-start fn2-query-reference-core-resultp fn2-query-reference-afterp
                             fn2-core-query-reference-domainp fn2-core-query-counts-matchp))))
(defthm fn2-identity-decide-query-references-accounted
 (implies (and (fn2-core-query-reference-domainp fn2-core) (fn2-core-query-counts-matchp fn2-core))
          (fn2-query-reference-core-resultp fn2-core (mv-nth 1 (fn2-identity-decide tx budget fn2-core))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn2-id-decide-step-query-reference-transfer
                 (fn2-pool (fn2-core-pool fn2-core))
                 (fn2-id-decides (fn2-core-id-decides fn2-core))
                 (fn2-succ-txns (fn2-core-succ-txns fn2-core))
                 (fn2-fields (fn2-core-fields fn2-core))
                 (fn2-overlays (fn2-core-overlays fn2-core))
                 (fn2-overlay-index (fn2-core-overlay-index fn2-core))
                 (fn2-run-installed (fn2-core-run-installed fn2-core))
                 (fn2-run-cursors (fn2-core-run-cursors fn2-core))
                 (fn2-run-paths (fn2-core-run-paths fn2-core))
                 (fn2-run-cache (fn2-core-run-cache fn2-core))
                 (b0 (mv-nth 1 (fn2-idc-stripe tx (fn2-fc-rows (fn2-core-fc fn2-core)) (fn2-core-id-decides fn2-core) (fn2-core-fields fn2-core))))
)
          :in-theory (enable fn2-identity-decide fn2-query-reference-core-resultp fn2-query-reference-afterp
                             fn2-core-query-reference-domainp fn2-core-query-counts-matchp))))
(defthm fn2-successor-release-query-references-accounted
 (implies (and (fn2-core-query-reference-domainp fn2-core) (fn2-core-query-counts-matchp fn2-core))
          (fn2-query-reference-core-resultp fn2-core (mv-nth 1 (fn2-successor-release tx fn2-core))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn2-succ-release-query-reference-transfer
                 (fn2-pool (fn2-core-pool fn2-core))
                 (fn2-id-decides (fn2-core-id-decides fn2-core))
                 (fn2-succ-txns (fn2-core-succ-txns fn2-core))
                 (fn2-succ-slots (fn2-core-succ-slots fn2-core))
)
          :in-theory (enable fn2-successor-release fn2-query-reference-core-resultp fn2-query-reference-afterp
                             fn2-core-query-reference-domainp fn2-core-query-counts-matchp))))

(defthm fn2-query-reference-dispatch-from-callees
 (implies (fn2-query-reference-hyps op core) (fn2-query-reference-conclusion op a core))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-query-reference-hyps fn2-query-reference-conclusion fn2-query-reference-step)
          :use ((:instance fn2-identity-decide-start-query-references-accounted (fn2-core core)
                 (tx (nth 0 a)) (ms (nth 1 a)) (mg (nth 2 a)) (mo (nth 3 a)) (ml (nth 4 a))
                 (ds (nth 5 a)) (dg (nth 6 a)) (doff (nth 7 a)) (ok (nth 8 a)) (os (nth 9 a)) (og (nth 10 a)))
                (:instance fn2-identity-decide-query-references-accounted (fn2-core core) (tx (nth 0 a)) (budget (nth 1 a)))
                (:instance fn2-successor-release-query-references-accounted (fn2-core core) (tx (nth 0 a)))))))
; No discharge declaration is emitted until these events actually admit.
