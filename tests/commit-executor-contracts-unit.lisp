; The consumer interface must not turn an evidence projection into an
; inductive invariant.  A well-formed but unreachable unfenced notify state
; refutes that attempted lift.  J1-J4 must rule this state out.
(in-package "ACL2")
(include-book "../books/commit-durable-all")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-cet-unfenced-notify-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (ids (fn2-env-commit-ids *fn2-profile-tiny*))
       (id (car ids)) (partner (cadr ids))
       (fn2-core (fn2-commit-put-core id (phase *fn2-commit-state-notify*)
                         (batch-no 1) (member-count 1) (cb-acks 0) (partner partner)))
       (fn2-core (fn2-exec-wake id fn2-core))
       (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-env-inv ids nil nil fn2-core)))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core))
       (acked (fn2-env-observe ids nil fn2-core)))
    (declare (ignore status obs actions))
    (mv (list pre (< 0 visits) (member-equal 1 acked)
              (not (fn2-env-inv ids acked nil fn2-core))) fn2-core)))
(defun fn2-cet-unfenced-notify ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-cet-unfenced-notify-core fn2-core) result)))
(assert-event (equal (fn2-cet-unfenced-notify) '(t t (1) t)))

; The intended instance is executable proof syntax in the consumer.  It
; must remain refused until its predicate includes the phase/history facts;
; this is paired with the actual fn2-turn counterexample, not a search claim.
(local (set-prover-step-limit 10000))
(must-fail (fn2-env-turn-instance))
