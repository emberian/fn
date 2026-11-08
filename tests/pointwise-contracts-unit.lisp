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

; Sum replacement uses the same mask twice, even with repeated domain keys.
(defun fn2-fold-test-value (key g c)
  (declare (ignore g)) (nfix (nth (nfix key) c)))
(defun fn2-fold-test-all (keys g c)
  (if (atom keys) 0
    (+ (fn2-fold-test-value (car keys) g c) (fn2-fold-test-all (cdr keys) g c))))
(defun fn2-fold-test-touched (keys delta g a h b context core)
  (if (atom keys) 0
    (+ (if (fn2-pw-test-affected (car keys) delta g a h b)
           (fn2-fold-test-value (car keys) context core) 0)
       (fn2-fold-test-touched (cdr keys) delta g a h b context core))))
(defthm fn2-fold-test-locality
  (implies (and (fn2-pw-test-step delta g a h b)
                (not (fn2-pw-test-affected key delta g a h b)))
           (equal (fn2-fold-test-value key h b) (fn2-fold-test-value key g a)))
  :hints (("Goal" :in-theory (disable nth update-nth nth-update-nth)
           :use ((:instance nth-update-nth (n (nfix delta)) (m (nfix key))
                            (val (nth (nfix delta) b)) (l a))))))
(defthm fn2-fold-test-replacement
  (implies (fn2-pw-test-step delta g a h b)
           (equal (+ (fn2-fold-test-all keys h b)
                     (fn2-fold-test-touched keys delta g a h b g a))
                  (+ (fn2-fold-test-all keys g a)
                     (fn2-fold-test-touched keys delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance fn2-fold-replacement
                          (fn2-fold-value fn2-fold-test-value)
                          (fn2-fold-step fn2-pw-test-step)
                          (fn2-fold-affected fn2-pw-test-affected)
                          (fn2-fold-all fn2-fold-test-all)
                          (fn2-fold-touched fn2-fold-test-touched)))
           :in-theory (e/d (fn2-fold-test-value fn2-fold-test-all fn2-fold-test-touched
                            fn2-fold-test-locality)
                           (fn2-pw-test-step fn2-pw-test-affected))
           :do-not-induct t)
          ("Subgoal 2" :use fn2-fold-test-locality
           :in-theory (e/d (fn2-fold-test-value)
                            (fn2-fold-test-locality fn2-pw-test-step fn2-pw-test-affected nth)))))
(assert-event
 (let ((keys '(0 1 1 2)) (a '(3 4 5)) (b '(3 1 5)))
   (and (fn2-pw-test-step 1 2 a 1 b)
        (equal (+ (fn2-fold-test-all keys 1 b) (fn2-fold-test-touched keys 1 2 a 1 b 2 a))
               (+ (fn2-fold-test-all keys 2 a) (fn2-fold-test-touched keys 1 2 a 1 b 1 b))))))
(assert-event
 (let ((keys '(0 1 1 2)) (a '(3 4 5)) (b '(2 1 5)))
   (and (not (fn2-pw-test-step 1 2 a 1 b))
        (not (equal (+ (fn2-fold-test-all keys 1 b) (fn2-fold-test-touched keys 1 2 a 1 b 2 a))
                    (+ (fn2-fold-test-all keys 2 a) (fn2-fold-test-touched keys 1 2 a 1 b 1 b)))))))

; Bounded-range instances and concrete hypothesis-removal controls.
(defun fn2-pw-test-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (fn2-pw-test-point start g c)
         (fn2-pw-test-range (+ 1 start) (- count 1) g c))))
(defun fn2-pw-test-range-repaired (start count delta g a h b)
  (declare (xargs :measure (nfix count)))
  (if (zp count) t
    (and (or (not (fn2-pw-test-affected start delta g a h b))
             (fn2-pw-test-point start h b))
         (fn2-pw-test-range-repaired (+ 1 start) (- count 1) delta g a h b))))
(defthm fn2-pw-test-range-instance
  (implies (and (fn2-pw-test-range start count g a)
                (fn2-pw-test-step delta g a h b)
                (fn2-pw-test-range-repaired start count delta g a h b))
           (fn2-pw-test-range start count h b))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance fn2-pw-range-transport
                         (fn2-pw-point fn2-pw-test-point)
                         (fn2-pw-step fn2-pw-test-step)
                         (fn2-pw-affected fn2-pw-test-affected)
                         (fn2-pw-range fn2-pw-test-range)
                         (fn2-pw-range-repaired fn2-pw-test-range-repaired)))
           :in-theory '(fn2-pw-test-range fn2-pw-test-range-repaired) :do-not-induct t)))
(defun fn2-fold-test-range (start count g c)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (fn2-fold-test-value start g c)
       (fn2-fold-test-range (+ 1 start) (- count 1) g c))))
(defun fn2-fold-test-range-touched (start count delta g a h b context core)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (if (fn2-pw-test-affected start delta g a h b)
           (fn2-fold-test-value start context core) 0)
       (fn2-fold-test-range-touched (+ 1 start) (- count 1) delta g a h b context core))))
(defthm fn2-fold-test-range-replacement
  (implies (fn2-pw-test-step delta g a h b)
           (equal (+ (fn2-fold-test-range start count h b)
                     (fn2-fold-test-range-touched start count delta g a h b g a))
                  (+ (fn2-fold-test-range start count g a)
                     (fn2-fold-test-range-touched start count delta g a h b h b))))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance fn2-fold-range-replacement
                          (fn2-fold-value fn2-fold-test-value)
                          (fn2-fold-step fn2-pw-test-step)
                          (fn2-fold-affected fn2-pw-test-affected)
                          (fn2-fold-range fn2-fold-test-range)
                          (fn2-fold-range-touched fn2-fold-test-range-touched)))
           :in-theory '(fn2-fold-test-value fn2-fold-test-range fn2-fold-test-range-touched
                        (:type-prescription nfix)) :do-not-induct t)
          ("Subgoal 2" :use fn2-fold-test-locality)))
(assert-event
 (and (fn2-pw-test-range 1 2 2 '(3 4 5))
      (fn2-pw-test-step 1 2 '(3 4 5) 1 '(3 1 5))
      (fn2-pw-test-range-repaired 1 2 1 2 '(3 4 5) 1 '(3 1 5))
      (fn2-pw-test-range 1 2 1 '(3 1 5))))
(assert-event
 (and (fn2-pw-test-range 1 2 2 '(3 4 5))
      (fn2-pw-test-step 1 2 '(3 4 5) 1 '(3 -1 5))
      (not (fn2-pw-test-range-repaired 1 2 1 2 '(3 4 5) 1 '(3 -1 5)))
      (not (fn2-pw-test-range 1 2 1 '(3 -1 5)))))
(assert-event
 (let ((a '(3 4 5)) (b '(3 1 5)))
   (and (fn2-pw-test-step 1 2 a 1 b)
        (equal (+ (fn2-fold-test-range 1 2 1 b) (fn2-fold-test-range-touched 1 2 1 2 a 1 b 2 a))
               (+ (fn2-fold-test-range 1 2 2 a) (fn2-fold-test-range-touched 1 2 1 2 a 1 b 1 b))))))
(assert-event
 (let ((a '(3 4 5)) (b '(3 1 4)))
   (and (not (fn2-pw-test-step 1 2 a 1 b))
        (not (equal (+ (fn2-fold-test-range 1 2 1 b) (fn2-fold-test-range-touched 1 2 1 2 a 1 b 2 a))
                    (+ (fn2-fold-test-range 1 2 2 a) (fn2-fold-test-range-touched 1 2 1 2 a 1 b 1 b)))))))
