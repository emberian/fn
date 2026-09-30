; Actual ORIGINALctx decision shared with the Store core's legacy reduced
; context. The projection removes prior verdict accumulation, not the newly
; produced verdict. Source/event/epoch/lifetime association is the outer owner
; invariant, never established by executing this logical equality over graphs.
(in-package "ACL2")
(include-book "replay-identity-produced")

(defun fn-ripc-without-prior-verdicts (ctx)
 (declare (xargs :guard t))
 (fn-stxk-context (fn-stxk-context-kind ctx) (fn-stxk-context-next ctx)
                  (fn-stxk-context-snapshots ctx) nil
                  (fn-stxk-context-current-generation ctx) (fn-stxk-context-tail ctx)))
(defun fn-ripc-core-checked-context (checked effect child)
 (declare (xargs :guard t))
 (fn-stxk-context (fn-stxk-context-kind checked) (fn-stxk-context-next checked)
                  (fn-stxk-context-snapshots checked)
                  (if (equal effect :verdict) (list child) nil)
                  (fn-stxk-context-current-generation checked)
                  (fn-stxk-context-tail checked)))

(local (defthm fn-ripc-snapshot-erasure
 (equal (fn-stxk-apply-snapshot (fn-ripc-without-prior-verdicts ctx) event)
        (fn-ripc-without-prior-verdicts (fn-stxk-apply-snapshot ctx event)))
 :hints (("Goal" :in-theory
  (e/d (fn-ripc-without-prior-verdicts fn-stxk-apply-snapshot fn-stxk-fault
        fn-stxk-context fn-stxk-context-kind fn-stxk-context-next
        fn-stxk-context-snapshots fn-stxk-context-verdicts
        fn-stxk-context-current-generation fn-stxk-context-tail)
       (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp))))))
(local (defthm fn-ripc-verdict-projection
 (implies (equal (fn-stxk-context-kind ctx) :ok)
  (equal (fn-stxk-apply-verdict (fn-ripc-without-prior-verdicts ctx) event)
   (let ((checked (fn-stxk-apply-verdict ctx event)))
    (fn-ripc-core-checked-context checked
      (if (equal (fn-stxk-context-kind checked) :ok) :verdict :none) event))))
 :hints (("Goal" :in-theory
  (e/d (fn-ripc-without-prior-verdicts fn-ripc-core-checked-context
        fn-stxk-apply-verdict fn-stxk-fault fn-stxk-context
        fn-stxk-context-kind fn-stxk-context-next fn-stxk-context-snapshots
        fn-stxk-context-verdicts fn-stxk-context-current-generation fn-stxk-context-tail)
       (fn-stxe-p fn-stxk-find fn-stxe-keyring-profile))))))
(local (defthm fn-ripc-carried-projection
 (implies (equal (fn-stxk-context-kind ctx) :ok)
  (equal (fn-replay-apply-carried-verdict (fn-ripc-without-prior-verdicts ctx) event)
   (let ((checked (fn-replay-apply-carried-verdict ctx event)))
    (fn-ripc-core-checked-context checked
      (if (equal (fn-stxk-context-kind checked) :ok) :verdict :none) event))))
 :hints (("Goal" :in-theory
  (e/d (fn-ripc-without-prior-verdicts fn-ripc-core-checked-context
        fn-replay-apply-carried-verdict fn-stxk-fault fn-stxk-context
        fn-stxk-context-kind fn-stxk-context-next fn-stxk-context-snapshots
        fn-stxk-context-verdicts fn-stxk-context-current-generation fn-stxk-context-tail)
       (fn-stxe-p))))))
(local (defthm fn-ripc-revoked-projection
 (implies (equal (fn-stxk-context-kind ctx) :ok)
  (equal (fn-replay-apply-revoked-verdict (fn-ripc-without-prior-verdicts ctx) event keys)
   (let ((checked (fn-replay-apply-revoked-verdict ctx event keys)))
    (fn-ripc-core-checked-context checked
      (if (equal (fn-stxk-context-kind checked) :ok) :verdict :none) event))))
 :hints (("Goal" :in-theory
  (e/d (fn-ripc-without-prior-verdicts fn-ripc-core-checked-context
        fn-replay-apply-revoked-verdict fn-stxk-fault fn-stxk-context
        fn-stxk-context-kind fn-stxk-context-next fn-stxk-context-snapshots
        fn-stxk-context-verdicts fn-stxk-context-current-generation fn-stxk-context-tail)
       (fn-stxe-p fn-hsig-revoked-tombstone-bindsp))))))

(defthm fn-ripc-one-original-decision-is-the-core-decision
 (equal (fn-replay-identity-step (fn-ripc-without-prior-verdicts ctx) event)
  (fn-ripc-core-checked-context
   (mv-nth 0 (fn-replay-identity-produced-effects ctx event))
   (mv-nth 1 (fn-replay-identity-produced-effects ctx event))
   (mv-nth 2 (fn-replay-identity-produced-effects ctx event))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-replay-identity-produced-has-original-context-and-effects
         (:instance fn-ripc-snapshot-erasure (event (fn-replay-identity-wire event)))
         (:instance fn-ripc-verdict-projection (event (fn-replay-identity-wire event)))
         (:instance fn-ripc-verdict-projection
          (event (fn-stmt-value (fn-stxe-decode-exact
           (fn-stxa-verdict-event (fn-replay-identity-wire event))))))
         (:instance fn-ripc-carried-projection
          (event (fn-stmt-value (fn-stxe-decode-exact
           (fn-stxa-verdict-event (fn-replay-identity-wire event))))))
         (:instance fn-ripc-revoked-projection
          (event (fn-stmt-value (fn-stxe-decode-exact
           (fn-stxa-verdict-event (fn-replay-identity-wire event)))))
          (keys (fn-hsig-article-event-carrier-keys (fn-replay-identity-wire event)))))
  :in-theory
   (e/d (fn-replay-identity-step fn-replay-identity-effects
         fn-replay-identity-verdict-effect fn-replay-identity-advance
         fn-ripc-without-prior-verdicts fn-ripc-core-checked-context
         fn-stxk-fault fn-stxk-context fn-stxk-context-kind fn-stxk-context-next
         fn-stxk-context-snapshots fn-stxk-context-verdicts
         fn-stxk-context-current-generation fn-stxk-context-tail)
        (fn-ripc-snapshot-erasure fn-ripc-verdict-projection
         fn-ripc-carried-projection fn-ripc-revoked-projection
         fn-replay-identity-produced-effects fn-replay-identity-wire
         fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-replay-apply-carried-verdict
         fn-replay-apply-revoked-verdict fn-stxk-p fn-stxe-p fn-stxa-p
         fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp
         fn-hsig-article-event-snapshot-bindsp fn-stxa-bindsp fn-stxk-find
         fn-stxe-decode-exact fn-stmt-okp fn-stmt-value)))))
(in-theory (disable fn-ripc-without-prior-verdicts fn-ripc-core-checked-context))
