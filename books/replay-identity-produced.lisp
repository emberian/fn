; Actual single produced replay decision; binding predicate work remains separate.
(in-package "ACL2")
(include-book "replay-identity-effects")
(include-book "stx-evidence-size-reader")
(defun fn-replay-identity-produced-verdict-effect (ctx child sizes)
 (declare (xargs :guard t))
 (mv ctx (if (equal (fn-stxk-context-kind ctx) :ok) :verdict :none)
     (if (equal (fn-stxk-context-kind ctx) :ok) child nil)
     (if (equal (fn-stxk-context-kind ctx) :ok) sizes nil)))

(defun fn-replay-identity-produced-effects (ctx event)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal (fn-stxk-context-kind ctx) :ok)) (mv ctx :none nil nil)
    (if (not (equal (fn-store-event-sequence event)
                    (fn-stxk-context-next ctx)))
        (mv (fn-stxk-fault ctx :sequence) :none nil nil)
     (let ((event (fn-replay-identity-wire event)))
      (cond
       ((fn-stxk-p event)
        (let* ((checked (fn-stxk-apply-snapshot ctx event))
               (changed (not (equal (fn-stxk-context-current-generation checked)
                                    (fn-stxk-context-current-generation ctx)))))
          (mv checked (if changed :snapshot :none) (if changed event nil) nil)))
       ((fn-stxe-p event)
        (let ((checked (fn-stxk-apply-verdict ctx event)))
          (mv (if (not (equal (fn-stxk-context-kind checked) :ok)) checked
                (fn-stxk-context :ok (fn-stxk-context-next checked)
                                 (fn-stxk-context-snapshots checked)
                                 (fn-stxk-context-verdicts ctx)
                                 (fn-stxk-context-current-generation checked) nil))
              :none nil nil)))
       ((fn-hsig-article-event-carried-bindsp event)
        (mv-let (decoded sizes) (fn-stxs-decode (fn-stxa-verdict-event event))
         (let ((child (fn-stmt-value decoded)))
          (fn-replay-identity-produced-verdict-effect
           (fn-replay-apply-carried-verdict ctx child) child sizes))))
       ((fn-hsig-article-event-revoked-bindsp event)
        (mv-let (decoded sizes) (fn-stxs-decode (fn-stxa-verdict-event event))
         (let ((child (fn-stmt-value decoded)))
          (fn-replay-identity-produced-verdict-effect
           (fn-replay-apply-revoked-verdict
            ctx child (fn-hsig-article-event-carrier-keys event)) child sizes))))
       ((fn-stxa-p event)
        (let ((snapshot
               (fn-stxk-find (fn-stxa-keyring-generation event)
                              (fn-stxk-context-snapshots ctx))))
          (if (or (not (fn-stxa-bindsp event))
                  (not snapshot)
                  (not (fn-hsig-article-event-snapshot-bindsp event snapshot)))
              (mv (fn-stxk-fault ctx :composite-binding) :none nil nil)
            (mv-let (decoded sizes) (fn-stxs-decode (fn-stxa-verdict-event event))
              (if (not (fn-stmt-okp decoded))
                  (mv (fn-stxk-fault ctx :composite-verdict) :none nil nil)
                (fn-replay-identity-produced-verdict-effect
                 (fn-stxk-apply-verdict ctx (fn-stmt-value decoded))
                 (fn-stmt-value decoded) sizes))))))
       (t (mv (fn-replay-identity-advance ctx) :none nil nil)))))))
(verify-guards fn-replay-identity-produced-effects)
(defthm fn-replay-identity-produced-has-original-context-and-effects
 (and (equal (mv-nth 0 (fn-replay-identity-produced-effects ctx event))
             (mv-nth 0 (fn-replay-identity-effects ctx event)))
      (equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event))
             (mv-nth 1 (fn-replay-identity-effects ctx event)))
      (equal (mv-nth 2 (fn-replay-identity-produced-effects ctx event))
             (mv-nth 2 (fn-replay-identity-effects ctx event))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-stxs-decode-ok-is-public
          (octets (fn-stxa-verdict-event (fn-replay-identity-wire event))))
        (:instance fn-stxs-decode-success-value-is-public
          (octets (fn-stxa-verdict-event (fn-replay-identity-wire event))))
        (:instance fn-hsig-article-event-carried-bindsp-facts
          (event (fn-replay-identity-wire event)))
        (:instance fn-hsig-article-event-revoked-bindsp-facts
          (event (fn-replay-identity-wire event))))
  :in-theory
   (e/d (fn-replay-identity-produced-effects fn-replay-identity-effects
         fn-replay-identity-produced-verdict-effect fn-replay-identity-verdict-effect)
        (fn-replay-identity-wire fn-stxs-decode fn-stxe-decode-exact
         fn-stmt-okp fn-stmt-value fn-stxk-p fn-stxe-p fn-stxa-p
         fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-stxk-find
         fn-stxa-bindsp fn-hsig-article-event-carried-bindsp
         fn-hsig-article-event-revoked-bindsp fn-hsig-article-event-snapshot-bindsp
         fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict)))))
