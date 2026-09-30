; Actual identity replay effects adjunct over unchanged current public replay.
; It runs the selected decision once, returning the actual shared-list effect.
; Sized child provenance and caller funding are separate obligations.
(in-package "ACL2")

(include-book "replay")

(defun fn-replay-identity-verdict-effect (ctx child)
  (declare (xargs :guard t))
  (mv ctx (if (equal (fn-stxk-context-kind ctx) :ok) :verdict :none)
      (if (equal (fn-stxk-context-kind ctx) :ok) child nil)))

(defun fn-replay-identity-effects (ctx event)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal (fn-stxk-context-kind ctx) :ok)) (mv ctx :none nil)
    (if (not (equal (fn-store-event-sequence event)
                    (fn-stxk-context-next ctx)))
        (mv (fn-stxk-fault ctx :sequence) :none nil)
     (let ((event (fn-replay-identity-wire event)))
      (cond
       ((fn-stxk-p event)
        (let* ((checked (fn-stxk-apply-snapshot ctx event))
               (changed (not (equal (fn-stxk-context-current-generation checked)
                                    (fn-stxk-context-current-generation ctx)))))
          (mv checked (if changed :snapshot :none) (if changed event nil))))
       ((fn-stxe-p event)
        (let ((checked (fn-stxk-apply-verdict ctx event)))
          (mv (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
                (fn-stxk-context :ok (fn-stxk-context-next checked)
                                 (fn-stxk-context-snapshots checked)
                                 (fn-stxk-context-verdicts ctx)
                                 (fn-stxk-context-current-generation checked) nil))
              :none nil)))
       ((fn-hsig-article-event-carried-bindsp event)
        (let ((child (fn-stmt-value (fn-stxe-decode-exact
                                    (fn-stxa-verdict-event event)))))
          (fn-replay-identity-verdict-effect
           (fn-replay-apply-carried-verdict ctx child) child)))
       ((fn-hsig-article-event-revoked-bindsp event)
        (let ((child (fn-stmt-value (fn-stxe-decode-exact
                                    (fn-stxa-verdict-event event)))))
          (fn-replay-identity-verdict-effect
           (fn-replay-apply-revoked-verdict
            ctx child (fn-hsig-article-event-carrier-keys event)) child)))
       ((fn-stxa-p event)
        (let ((snapshot
               (fn-stxk-find (fn-stxa-keyring-generation event)
                              (fn-stxk-context-snapshots ctx))))
          (if (or (not (fn-stxa-bindsp event))
                  (not snapshot)
                  (not (fn-hsig-article-event-snapshot-bindsp event snapshot)))
              (mv (fn-stxk-fault ctx :composite-binding) :none nil)
            (let ((decoded (fn-stxe-decode-exact
                            (fn-stxa-verdict-event event))))
              (if (not (fn-stmt-okp decoded))
                  (mv (fn-stxk-fault ctx :composite-verdict) :none nil)
                (fn-replay-identity-verdict-effect
                 (fn-stxk-apply-verdict ctx (fn-stmt-value decoded))
                 (fn-stmt-value decoded)))))))
       (t (mv (fn-replay-identity-advance ctx) :none nil)))))))

(verify-guards fn-replay-identity-effects)

(defthm fn-replay-identity-effects-context-is-original-by-definition
 (equal (mv-nth 0 (fn-replay-identity-effects ctx event))
        (fn-replay-identity-step ctx event))
 :rule-classes nil
 :hints (("Goal" :in-theory
           (e/d (fn-replay-identity-effects fn-replay-identity-verdict-effect
                 fn-replay-identity-step)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-apply-snapshot
                 fn-stxk-apply-verdict fn-replay-identity-wire
                 fn-hsig-article-event-carried-bindsp
                 fn-hsig-article-event-revoked-bindsp
                 fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict
                 fn-stxk-find fn-stxa-bindsp
                 fn-hsig-article-event-snapshot-bindsp
                 fn-stxe-decode-exact fn-stmt-okp)))))

(in-theory (disable fn-replay-identity-verdict-effect fn-replay-identity-effects))
