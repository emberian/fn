; Bounds on the counters returned by the executor and the cost of a word of runs.
(in-package "ACL2")
(include-book "executor")
(include-book "owed-discharge")

; A transition counts at most one visit. Only an enabled observation can
; increment the observation counter.
(local
 (defthm fn2-transition-observation-and-visit-increments
   (let ((result (fn2-transition allow budget core)))
     (and (<= (nfix (mv-nth 0 result)) (if allow 1 0))
          (<= (nfix (mv-nth 1 result)) 1)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (union-theories
             '(fn2-transition fn2-exec-harvest fn2-exec-mailbox
               fn2-exec-principal fn2-exec-service mv-nth car-cons cdr-cons
               (:e zp) (:e binary-+) (:e nfix) (:e <))
             (theory 'minimal-theory))))))

(local
 (defthm fn2-concrete-loop-observation-and-visit-bounds
   (implies (and (natp h) (natp k) (natp nobs) (natp nvisits)
                 (<= nobs h) (<= nvisits k))
            (let ((result (fn2-concrete-loop fuel h k a nobs nvisits nactions core)))
              (and (<= (mv-nth 1 result) h)
                   (<= (mv-nth 2 result) k))))
   :hints (("Goal" :induct (fn2-concrete-loop fuel h k a nobs nvisits nactions core)
            :expand ((fn2-concrete-loop fuel h k a nobs nvisits nactions core))
            :in-theory (union-theories
                        '((:i fn2-concrete-loop) fn2-concrete-loop-stop-p
                          (:t nfix) natp mv-nth car-cons cdr-cons (:e zp) (:e binary-+))
                        (theory 'minimal-theory)))
           ("Subgoal *1/2" :use
            (:instance fn2-transition-observation-and-visit-increments
                       (allow (< nobs h)) (budget (- a nactions)))))))

(defthm fn2-turn-bounds-proved
  (fn2-turn-bounds$owed core)
  :rule-classes nil
  :hints (("Goal" :use (:instance fn2-turn-actions-within-limit (fn2-core core))
           :in-theory (e/d (fn2-turn-bounds$owed fn2-turn fn2-concrete-turn)
                           (fn2-concrete-loop fn2-corep fn2-core-wfp
                            fn2-exec-h fn2-exec-k fn2-exec-aturn)))))
(fn2-owed-discharge fn2-turn-bounds fn2-turn-bounds-proved)

; Add one certified run to the bound for the rest of the word.
(local
 (defthm fn2-certified-arm-work
   (implies (fn2-machine-arm-charge-ok-p kind phase bytes steps descriptors)
            (and (natp bytes) (natp steps)
                 (natp (fn2-machine-arm-bound kind phase))
                 (<= (+ bytes steps) (fn2-machine-arm-bound kind phase))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-machine-arm-charge-ok-p fn2-machine-arm-bound)
                                   (natp))))))

(defthm fn2-arm-cost-composition-proved
  (implies (fn2-arm-word-certified-p word)
           (<= (fn2-arm-word-charge word) (fn2-arm-word-bound word)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-arm-word-charge word)
           :in-theory (union-theories
                       '(fn2-arm-word-certified-p fn2-arm-word-charge fn2-arm-word-bound
                         atom natp nfix (:e nfix) (:e binary-+))
                       (theory 'minimal-theory)))
          ("Subgoal *1/2" :use
           (:instance fn2-certified-arm-work
                      (kind (nth 0 (car word))) (phase (nth 1 (car word)))
                      (bytes (nth 2 (car word))) (steps (nth 3 (car word)))
                      (descriptors (nth 4 (car word)))))))
(fn2-owed-discharge fn2-arm-cost-composition fn2-arm-cost-composition-proved)
