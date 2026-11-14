; Conditional calendar progress of the loop actually called by fn2-turn.
; This does not promise delivery, resource availability, or per-row fairness.
(in-package "ACL2")
(include-book "executor")

(local (defthm fn2-progress-principal-visits
  (equal (mv-nth 1 (fn2-exec-principal principal position budget fn2-core)) 1)
  :hints (("Goal" :in-theory
           (e/d (fn2-exec-principal)
                (fn2-exec-pop fn2-machine-run fn2-machine-take-wake
                 fn2-exec-wake fn2-exec-charge-run fn2-exec-record fn2-exec-queued))))))
(local (defthm fn2-progress-service-visits
  (equal (mv-nth 1 (fn2-exec-service service position budget fn2-core)) 1)
  :hints (("Goal" :in-theory
           (e/d (fn2-exec-service)
                (fn2-exec-run-services fn2-exec-grant-p fn2-machine-grant-one
                 fn2-exec-arm fn2-exec-wake fn2-exec-charge-run fn2-exec-record
                 fn2-exec-system-row fn2-exec-queued))))))

(defthm fn2-transition-calendar-visits
  (implies (and (not allow-observation) (fn2-exec-eligible-p fn2-core))
           (equal (mv-nth 1 (fn2-transition allow-observation budget fn2-core)) 1))
  :hints (("Goal" :in-theory
           (e/d (fn2-transition)
                (fn2-exec-eligible-p fn2-exec-visit fn2-exec-principal fn2-exec-service)))))

(defthm fn2-concrete-loop-visits-monotone
  (implies (natp visits)
           (<= visits (mv-nth 2 (fn2-concrete-loop fuel h k a obs visits actions fn2-core))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn2-concrete-loop fuel h k a obs visits actions fn2-core)
           :in-theory (e/d (fn2-concrete-loop)
                           (fn2-concrete-loop-stop-p fn2-transition fn2-exec-account-work
                            fn2-turn-status)))))

; A fresh iteration with observation admission closed and adequate remaining
; visit/action/work capacity must visit. The explicit real stop predicate
; also preserves future reservations: no permanently reserved credit premise.
(defthm fn2-concrete-loop-calendar-progress
  (implies (and (natp fuel) (< 0 fuel) (natp obs) (natp h)
                (natp visits) (>= obs h)
                (fn2-exec-eligible-p fn2-core)
                (not (fn2-concrete-loop-stop-p h k a obs visits actions fn2-core)))
           (< visits (mv-nth 2 (fn2-concrete-loop fuel h k a obs visits actions fn2-core))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-concrete-loop fuel h k a obs visits actions fn2-core))
           :in-theory (disable fn2-concrete-loop fn2-concrete-loop-stop-p
                               fn2-transition fn2-exec-account-work fn2-turn-status
                               fn2-exec-eligible-p))))
