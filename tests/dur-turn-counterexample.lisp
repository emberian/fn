; Refutes the arbitrary-state owed turn invariant; this is not an ACK counterexample.
(in-package "ACL2")
(include-book "../books/commit-durable-all")

; The original predicate is non-executable. This executable view is proved
; equal for every ghost/context pair, so the control checks the whole claim.
(defun fn2-dur-turn-probe-inv (g fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (fn2-env-j-rows (nth 0 g) (nth 2 g) fn2-core)
       (fn2-env-j3-rows (nth 0 g) (nth 2 g) fn2-core)
       (fn2-env-j-frontier (nth 2 g) fn2-core)
       (fn2-env-acked-durable-p (nth 1 g) (nth 2 g))))
(defthm fn2-dur-turn-probe-inv-by-definition
  (equal (fn2-dur-turn-probe-inv g c) (fn2-env-dur-turn-inv g c))
  :hints (("Goal" :in-theory '(fn2-dur-turn-probe-inv fn2-env-dur-turn-inv))))

(defun fn2-turn-empty-ghost-build (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (ids (fn2-env-commit-ids *fn2-profile-tiny*))
       (id (car ids)) (partner (cadr ids))
       (fn2-core (fn2-commit-put-core id (phase *fn2-commit-state-install*)
                    (batch-no 1) (member-count 1) (cb-acks 0) (partner partner))))
    (fn2-exec-wake id fn2-core)))

(defun fn2-dur-turn-counterexample-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-turn-empty-ghost-build fn2-core))
       (g '(nil nil nil))
       (antecedent (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                        (fn2-dur-turn-probe-inv g fn2-core)))
       (before (fn2-env-root fn2-core))
       ((mv & & visits & fn2-core) (fn2-turn fn2-core)))
    (mv (list antecedent (not (fn2-dur-turn-probe-inv g fn2-core))
              (< 0 visits) before (fn2-env-root fn2-core)) fn2-core)))
(defun fn2-dur-turn-counterexample-values ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-dur-turn-counterexample-core fn2-core) result)))

; The omitted ghost ids let an unfenced install escape J/J3. The real turn
; installs batch 1, falsifying the fixed empty log's durable frontier.
(assert-event
 (equal (fn2-dur-turn-counterexample-values) '(t t t (t 0 0) (t 1 0))))
