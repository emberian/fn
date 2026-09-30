; Actual single produced replay decision; binding predicate work remains separate.
(in-package "ACL2")
(include-book "replay-identity-effects")
(include-book "stx-evidence-size-reader")
(include-book "replay-produced-evidence")
(defun fn-replay-identity-produced-verdict-effect (ctx child sizes)
 (declare (xargs :guard t))
 (mv ctx (if (equal (fn-stxk-context-kind ctx) :ok) :verdict :none)
     (if (equal (fn-stxk-context-kind ctx) :ok) child nil)
     (if (equal (fn-stxk-context-kind ctx) :ok) sizes nil)))

(defun fn-replay-identity-produced-effects (ctx event)
 (declare (xargs :guard t))
 (fn-rpe-produced-effects ctx event))
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
  :use fn-rpe-produced-preserves-original-context-and-effects
  :in-theory (e/d (fn-replay-identity-produced-effects)
                 (fn-rpe-produced-effects fn-replay-identity-effects)))))
