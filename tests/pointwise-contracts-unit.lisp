(in-package "ACL2")
(include-book "../books/pointwise-contracts")

; A changing ghost threshold and a single replaced cell. The point predicate
; is deliberately false for negative cells, so omitting repair has a witness.
(defun fn2-pw-test-point (key g c) (<= g (nth (nfix key) c)))
(defun fn2-pw-test-step (delta g a h b)
  (and (<= h g) (equal b (update-nth (nfix delta) (nth (nfix delta) b) a))))
(defun fn2-pw-test-affected (key delta g a h b)
  (declare (ignore g a h b))
  (equal (nfix key) (nfix delta)))
(defun fn2-pw-test-all (keys g c)
  (if (atom keys) t
    (and (fn2-pw-test-point (car keys) g c) (fn2-pw-test-all (cdr keys) g c))))
(defun fn2-pw-test-repaired (keys delta g a h b)
  (if (atom keys) t
    (and (or (not (fn2-pw-test-affected (car keys) delta g a h b))
             (fn2-pw-test-point (car keys) h b))
         (fn2-pw-test-repaired (cdr keys) delta g a h b))))
(defthm fn2-pw-test-locality
  (implies (and (fn2-pw-test-step delta g a h b)
                (not (fn2-pw-test-affected key delta g a h b))
                (fn2-pw-test-point key g a))
           (fn2-pw-test-point key h b))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth nth-update-nth)
           :use ((:instance nth-update-nth
                         (n (nfix delta)) (m (nfix key))
                         (val (nth (nfix delta) b)) (l a))))))
(defthm fn2-pw-test-instance
  (implies (and (fn2-pw-test-all keys g a)
                (fn2-pw-test-step delta g a h b)
                (fn2-pw-test-repaired keys delta g a h b))
           (fn2-pw-test-all keys h b))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance fn2-pw-transport
                         (fn2-pw-point fn2-pw-test-point)
                         (fn2-pw-step fn2-pw-test-step)
                         (fn2-pw-affected fn2-pw-test-affected)
                         (fn2-pw-all fn2-pw-test-all)
                         (fn2-pw-repaired fn2-pw-test-repaired)))
           :in-theory (disable fn2-pw-test-point fn2-pw-test-step fn2-pw-test-affected))
          ("Subgoal 2" :by fn2-pw-test-locality)))
(assert-event
 (and (fn2-pw-test-all '(0 1 1 2) 2 '(3 4 5))
      (fn2-pw-test-step 1 2 '(3 4 5) 1 '(3 1 5))
      (fn2-pw-test-repaired '(0 1 1 2) 1 2 '(3 4 5) 1 '(3 1 5))
      (fn2-pw-test-all '(0 1 1 2) 1 '(3 1 5))))
; Remove repair: the other hypotheses hold and the conclusion is false.
(assert-event
 (and (fn2-pw-test-all '(0 1 2) 2 '(3 4 5))
      (fn2-pw-test-step 1 2 '(3 4 5) 1 '(3 -1 5))
      (not (fn2-pw-test-repaired '(0 1 2) 1 2 '(3 4 5) 1 '(3 -1 5)))
      (not (fn2-pw-test-all '(0 1 2) 1 '(3 -1 5)))))
; Remove locality/step: the untouched cell invalidates the conjunction.
(assert-event
 (and (fn2-pw-test-all '(0 1 2) 2 '(3 4 5))
      (fn2-pw-test-repaired '(0 1 2) 1 2 '(3 4 5) 1 '(-1 4 5))
      (not (fn2-pw-test-step 1 2 '(3 4 5) 1 '(-1 4 5)))
      (not (fn2-pw-test-all '(0 1 2) 1 '(-1 4 5)))))
