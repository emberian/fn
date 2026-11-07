; Whole-antecedent witnesses and two omitted-preservation controls on the
; actual executor.  No replacement loop is used.
(in-package "ACL2")
(include-book "../books/executor-contracts")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-ect-service-ready (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (ready) (fn2-sched-service-ready 0 fn2-sched) ready))
(defun fn2-ect-service-set (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
    (fn2-sched) (fn2-sched-set-service 0 1 fn2-sched) fn2-core))

(defun fn2-ect-witnesses-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core))
       (positive (and pre (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                      (eq status :more) (equal obs 0) (< 0 visits) (< 0 actions)))
       (fn2-core (fn2-exec-set-turn-steps 0 fn2-core))
       (account-pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                         (equal (fn2-exec-turn-steps fn2-core) 0)))
       (fn2-core (fn2-exec-account-work 0 1 fn2-core))
       (account-negative (and account-pre (equal (fn2-exec-turn-steps fn2-core) 1)))
       (fn2-core (fn2-ect-service-set fn2-core))
       (service-pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                         (fn2-ect-service-ready fn2-core)))
       ((mv & & & & & fn2-core) (fn2-exec-service 0 0 0 fn2-core)))
    (mv (list positive account-negative
              (and service-pre (not (fn2-ect-service-ready fn2-core)))) fn2-core)))
(defun fn2-ect-witnesses ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-ect-witnesses-core fn2-core) result)))
(assert-event (equal (fn2-ect-witnesses) '(t t t)))

; Removing either obligation cannot be repaired by the turn induction.
; These are rejected functional instances, paired with the concrete
; before/after counterexamples above (proof failure alone is not evidence).
(defun-nx fn2-ect-no-account-inv (g c)
  (declare (ignorable g))
  (equal (fn2-exec-turn-steps c) 0))
(defun-nx fn2-ect-no-account-rel (tag args g before after)
  (declare (ignorable args))
  (or (equal tag 'fn2-exec-account-work)
      (implies (fn2-ect-no-account-inv g before) (fn2-ect-no-account-inv g after))))
(defun-nx fn2-ect-no-service-inv (g c)
  (declare (ignorable g))
  (fn2-ect-service-ready c))
(defun-nx fn2-ect-no-service-rel (tag args g before after)
  (declare (ignorable args))
  (or (equal tag 'fn2-exec-clear-service)
      (implies (fn2-ect-no-service-inv g before) (fn2-ect-no-service-inv g after))))
(set-prover-step-limit 10000)
(must-fail
 (defthm fn2-ect-account-omission
   (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-ect-no-account-inv g fn2-core))
            (fn2-ect-no-account-inv g (mv-nth 4 (fn2-turn fn2-core))))
   :hints (("Goal" :use ((:functional-instance fn2-executor-inv-turn
                           (fn2-executor-inv fn2-ect-no-account-inv)
                           (fn2-executor-rel fn2-ect-no-account-rel)))
            :in-theory (disable fn2-corep fn2-core-wfp fn2-turn fn2-exec-turn-steps)
            :do-not-induct t))))
(must-fail
 (defthm fn2-ect-service-omission
   (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-ect-no-service-inv g fn2-core))
            (fn2-ect-no-service-inv g (mv-nth 4 (fn2-turn fn2-core))))
   :hints (("Goal" :use ((:functional-instance fn2-executor-inv-turn
                           (fn2-executor-inv fn2-ect-no-service-inv)
                           (fn2-executor-rel fn2-ect-no-service-rel)))
            :in-theory (disable fn2-corep fn2-core-wfp fn2-turn fn2-ect-service-ready)
            :do-not-induct t))))
