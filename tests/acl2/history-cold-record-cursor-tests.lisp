(in-package "ACL2")
(include-book "../../books/history-cold-record-cursor")
(include-book "history-cold-record-runtime-tests")

; Complete initial boundary, then one literal omission at a time.
(defthm fn-hrcur-cold-test-initial-positive
  (and
    (fn-hrcur-widthp '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) 2)
    (eq (car '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) :decoded)
    (fn-hrcur-cold-domainp (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) '(78 73 76))
    (fn-scc-octet-listp '(78 73 76))
    (and (fn-hrcur-cold-invariantp (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(78 73 76)) (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(78 73 76)) (fn-scc-encode (fn-hdc-abstract (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) '(78 73 76))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-invariantp fn-hrcur-cold-domainp fn-hrcur-dos-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
            fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract))))

; Argument/source mutation: omit width only.
(defthm fn-hrcur-cold-test-initial-remove-width
  (and
    (eq (car '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra)) :decoded)
    (fn-hrcur-cold-domainp (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra)) '(78 73 76))
    (fn-scc-octet-listp '(78 73 76))
    (not (fn-hrcur-widthp '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra) 2))
    (not (and (fn-hrcur-cold-invariantp (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra) :capture :lease) '(78 73 76)) (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra) :capture :lease) '(78 73 76)) (fn-scc-encode (fn-hdc-abstract (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)) :extra)) '(78 73 76)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-invariantp fn-hrcur-cold-domainp fn-hrcur-dos-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
            fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract))))

; Argument/source mutation: omit tag only.
(defthm fn-hrcur-cold-test-initial-remove-tag
  (and
    (fn-hrcur-widthp '(:resident (:pair (:atom 65) (:span 4 1 0 3))) 2)
    (fn-hrcur-cold-domainp (cadr '(:resident (:pair (:atom 65) (:span 4 1 0 3)))) '(78 73 76))
    (fn-scc-octet-listp '(78 73 76))
    (not (eq (car '(:resident (:pair (:atom 65) (:span 4 1 0 3)))) :decoded))
    (not (and (fn-hrcur-cold-invariantp (fn-hrcur-cold-begin '(:resident (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(78 73 76)) (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin '(:resident (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(78 73 76)) (fn-scc-encode (fn-hdc-abstract (cadr '(:resident (:pair (:atom 65) (:span 4 1 0 3)))) '(78 73 76)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-invariantp fn-hrcur-cold-domainp fn-hrcur-dos-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
            fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract))))

; Argument/source mutation: omit source-domain only.
(defthm fn-hrcur-cold-test-initial-remove-source-domain
  (and
    (fn-hrcur-widthp '(:decoded (:bogus nil)) 2)
    (eq (car '(:decoded (:bogus nil))) :decoded)
    (fn-scc-octet-listp '(78 73 76))
    (not (fn-hrcur-cold-domainp (cadr '(:decoded (:bogus nil))) '(78 73 76)))
    (not (and (fn-hrcur-cold-invariantp (fn-hrcur-cold-begin '(:decoded (:bogus nil)) :capture :lease) '(78 73 76)) (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin '(:decoded (:bogus nil)) :capture :lease) '(78 73 76)) (fn-scc-encode (fn-hdc-abstract (cadr '(:decoded (:bogus nil))) '(78 73 76)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-invariantp fn-hrcur-cold-domainp fn-hrcur-dos-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
            fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract))))

; Argument/source mutation: omit pool only.
(defthm fn-hrcur-cold-test-initial-remove-pool
  (and
    (fn-hrcur-widthp '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) 2)
    (eq (car '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) :decoded)
    (fn-hrcur-cold-domainp (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) '(999 73 76))
    (not (fn-scc-octet-listp '(999 73 76)))
    (not (and (fn-hrcur-cold-invariantp (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(999 73 76)) (equal (fn-hrcur-cold-rest (fn-hrcur-cold-begin '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease) '(999 73 76)) (fn-scc-encode (fn-hdc-abstract (cadr '(:decoded (:pair (:atom 65) (:span 4 1 0 3)))) '(999 73 76)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-invariantp fn-hrcur-cold-domainp fn-hrcur-dos-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-rest
            fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest fn-hdc-abstract))))

; Test-only literal trace: each iteration invokes one actual cold tick.
(defun fn-hrcur-cold-test-ticks (c n)
  (declare (xargs :guard (natp n)))
  (if (zp n) c
    (mv-let (v byte next) (fn-hrcur-cold-tick c)
      (declare (ignore v byte))
      (fn-hrcur-cold-test-ticks next (1- n)))))
(defun-nx fn-hrcur-cold-test-tick-conclusionp (c pool)
  (let ((v (mv-nth 0 (fn-hrcur-cold-tick c)))
        (b (mv-nth 1 (fn-hrcur-cold-tick c)))
        (next (mv-nth 2 (fn-hrcur-cold-tick c))))
    (and (fn-hrcur-cold-invariantp next pool)
         (equal (fn-hrcur-cold-rest c pool)
                (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                  (fn-hrcur-cold-rest next pool)))
         (implies (eq v :prepared) (equal (fn-hrcur-cold-rest c pool) nil)))))
(defun-nx fn-hrcur-cold-test-supply-conclusionp (c position byte pool)
  (let ((v (mv-nth 0 (fn-hrcur-cold-supply c position byte)))
        (b (mv-nth 1 (fn-hrcur-cold-supply c position byte)))
        (next (mv-nth 2 (fn-hrcur-cold-supply c position byte))))
    (and (member-eq v '(:continue :emit)) (fn-hrcur-cold-invariantp next pool)
         (equal (fn-hrcur-cold-rest c pool)
                (if (eq v :emit) (cons b (fn-hrcur-cold-rest next pool))
                  (fn-hrcur-cold-rest next pool))))))

; Reachable positive literal with complete antecedent/conclusion.
(defthm fn-hrcur-cold-test-tick-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (equal (mv-nth 0 (fn-hrcur-cold-tick c)) :emit)
         (equal (mv-nth 1 (fn-hrcur-cold-tick c)) 6)
         (fn-hrcur-cold-test-tick-conclusionp c '(17 23))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Corrupted-state/source/observation mutation; every retained hypothesis checked.
(defthm fn-hrcur-cold-test-tick-remove-invariant
  (let ((c '(:work ((:bad-task nil)) nil nil :capture :lease nil nil 0)))
    (and (not (fn-hrcur-cold-invariantp c '(17 23)))
         (not (fn-hrcur-cold-test-tick-conclusionp c '(17 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Reachable positive literal with complete antecedent/conclusion.
(defthm fn-hrcur-cold-test-supply-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
         (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
         (equal 17 (nth 0 '(17 23)))
         (equal (mv-nth 0 (fn-hrcur-cold-supply c 0 17)) :emit)
         (equal (mv-nth 1 (fn-hrcur-cold-supply c 0 17)) 17)
         (fn-hrcur-cold-test-supply-conclusionp c 0 17 '(17 23))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Corrupted-state/source/observation mutation; every retained hypothesis checked.
(defthm fn-hrcur-cold-test-supply-remove-invariant
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (not (fn-hrcur-cold-invariantp c '(999 23)))
         (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
         (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
         (equal 999 (nth 0 '(999 23)))
         (not (fn-hrcur-cold-test-supply-conclusionp c 0 999 '(999 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Corrupted-state/source/observation mutation; every retained hypothesis checked.
(defthm fn-hrcur-cold-test-supply-remove-demand
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
         (equal nil (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
         (equal 17 (nth nil '(17 23)))
         (not (fn-hrcur-cold-test-supply-conclusionp c nil 17 '(17 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Corrupted-state/source/observation mutation; every retained hypothesis checked.
(defthm fn-hrcur-cold-test-supply-remove-position
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
         (not (equal 1 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c)))))
         (equal 23 (nth 1 '(17 23)))
         (not (fn-hrcur-cold-test-supply-conclusionp c 1 23 '(17 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Corrupted-state/source/observation mutation; every retained hypothesis checked.
(defthm fn-hrcur-cold-test-supply-remove-source-byte
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
         (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
         (not (equal 18 (nth 0 '(17 23))))
         (not (fn-hrcur-cold-test-supply-conclusionp c 0 18 '(17 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-test-tick-conclusionp fn-hrcur-cold-test-supply-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-span-shapep))))

; Complete reachable output-type antecedent and conclusion.
(defthm fn-hrcur-cold-test-tick-octet-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :emit)
         (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-tick c)))))
  :rule-classes nil)
; Hypothesis removal, reachable prefix-to-body continuation emits no byte.
(defthm fn-hrcur-cold-test-tick-octet-remove-emit
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 4)))
    (and (not (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :emit))
         (not (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-tick c))))))
  :rule-classes nil)
(defthm fn-hrcur-cold-test-supply-octet-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (eq (mv-nth 0 (fn-hrcur-cold-supply c 0 17)) :emit)
         (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-supply c 0 17)))))
  :rule-classes nil)
; Observation mutation: wrong position refuses and returns no byte.
(defthm fn-hrcur-cold-test-supply-octet-remove-emit
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and (not (eq (mv-nth 0 (fn-hrcur-cold-supply c 1 17)) :emit))
         (not (fn-scc-octetp (mv-nth 1 (fn-hrcur-cold-supply c 1 17))))))
  :rule-classes nil)
(defthm fn-hrcur-cold-test-complete-tick-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and (fn-hrcur-cold-invariantp c '(17 23))
         (fn-hrcur-cold-tick-lawp c '(17 23))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-tick-lawp fn-hrcur-cold-test-tick-conclusionp
            fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest
            fn-hrcur-cold-task-rest fn-hrcur-dos-domainp fn-hdc-abstract
            fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-shapep))))
; Corrupted task state: sole invariant hypothesis and full conclusion fail.
(defthm fn-hrcur-cold-test-complete-tick-remove-invariant
  (let ((c '(:work ((:bad-task nil)) nil nil :capture :lease nil nil 0)))
    (and (not (fn-hrcur-cold-invariantp c '(17 23)))
         (not (fn-hrcur-cold-tick-lawp c '(17 23)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-tick-lawp fn-hrcur-cold-invariantp
            fn-hrcur-cold-tasksp fn-hrcur-cold-taskp))))
; The ordinal theorem has no antecedent. This state is actually reached.
(defthm fn-hrcur-cold-test-rank-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (o-p (fn-hrcur-cold-rank c)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hrcur-cold-rank-is-well-founded-ordinal
                            (c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))))))

; Productive progress: reachable positives and literal hypothesis removals.
; Invariant removals are corrupted-state/source mutations; other omissions
; are reachable terminal/demand states or scalar observation mutations.
(defthm fn-hrcur-cold-test-progress-tick-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (not (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared))
      (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
      (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-tick c)))
             (fn-hrcur-cold-rank c))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-tick-remove-invariant
  (let ((c '(:work ((:bad-task nil)) nil nil :capture :lease nil nil 0)))
    (and
      (not (fn-hrcur-cold-progress-invariantp c '(17 23)))
      (not (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared))
      (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-tick c)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-tick-remove-terminal
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:atom nil)) :capture :lease) 20)))
    (and
      (fn-hrcur-cold-progress-invariantp c nil)
      (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared)
      (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-tick c)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-tick-remove-demand
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (not (eq (mv-nth 0 (fn-hrcur-cold-tick c)) :prepared))
      (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-tick c)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-supply-positive
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
      (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
      (equal 17 (nth 0 '(17 23)))
      (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-supply c 0 17)))
             (fn-hrcur-cold-rank c))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-supply-remove-invariant
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and
      (not (fn-hrcur-cold-progress-invariantp c '(999 23)))
      (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
      (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
      (equal 999 (nth 0 '(999 23)))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-supply c 0 999)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-supply-remove-demand
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (not (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte))
      (equal nil (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
      (equal 17 (nth nil '(17 23)))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-supply c nil 17)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-supply-remove-position
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
      (not (equal 1 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c)))))
      (equal 23 (nth 1 '(17 23)))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-supply c 1 23)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defthm fn-hrcur-cold-test-progress-supply-remove-source-byte
  (let ((c (fn-hrcur-cold-test-ticks (fn-hrcur-cold-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
    (and
      (fn-hrcur-cold-progress-invariantp c '(17 23))
      (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-cold-tick c))) :need-byte)
      (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hrcur-cold-tick c))))
      (not (equal 999 (nth 0 '(17 23))))
      (not (o< (fn-hrcur-cold-rank (mv-nth 2 (fn-hrcur-cold-supply c 0 999)))
             (fn-hrcur-cold-rank c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (enable fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hrcur-span-invariantp fn-hrcur-span-shapep
            fn-hrcur-span-rest fn-hrcur-span-wire fn-hdc-abstract
            fn-hrcur-cold-rank fn-hrcur-cold-structural-credit fn-hrcur-cold-tasks-credit
            fn-hrcur-cold-task-credit fn-hrcur-cold-phase-credit fn-hrcur-cold-child-credit
            fn-hrcur-span-work o< make-ord))))

(defun-nx fn-hrcur-cold-test-source-run-conclusionp (source pool)
  (equal (fn-hrcur-cold-oracle-run (fn-hrcur-cold-begin source :capture :lease) pool)
         (fn-scc-encode (fn-hdc-abstract (cadr source) pool))))

; Supported-source full stream positive.
(defthm fn-hrcur-cold-test-source-run-positive
  (let ((source '(:decoded (:span 6 0 0 2))) (pool '(17 23)))
    (and
      (fn-hrcur-widthp source 2)
      (eq (car source) :decoded)
      (fn-hrcur-cold-domainp (cadr source) pool)
      (fn-scc-octet-listp pool)
      (fn-hrcur-cold-test-source-run-conclusionp source pool)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hrcur-cold-supported-source-run-is-current-codec
      (source '(:decoded (:span 6 0 0 2))) (pool '(17 23))
      (capture :capture) (lease :lease))) :in-theory
    (enable fn-hrcur-cold-test-source-run-conclusionp fn-hrcur-cold-oracle-run
            fn-hrcur-cold-oracle-step fn-hrcur-cold-begin
            fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp
            fn-hrcur-span-shapep fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
            fn-hrcur-cold-countp fn-hrcur-cold-demand))))

; Supported-source full stream argument/source mutation.
(defthm fn-hrcur-cold-test-source-run-remove-width
  (let ((source '(:decoded (:span 6 0 0 2) :extra)) (pool '(17 23)))
    (and
      (not (fn-hrcur-widthp source 2))
      (eq (car source) :decoded)
      (fn-hrcur-cold-domainp (cadr source) pool)
      (fn-scc-octet-listp pool)
      (not (fn-hrcur-cold-test-source-run-conclusionp source pool))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-hrcur-cold-oracle-run '(:refused nil nil nil :capture :lease nil nil 0) '(17 23))) :in-theory
    (enable fn-hrcur-cold-test-source-run-conclusionp fn-hrcur-cold-oracle-run
            fn-hrcur-cold-oracle-step fn-hrcur-cold-begin
            fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp
            fn-hrcur-span-shapep fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
            fn-hrcur-cold-countp fn-hrcur-cold-demand))))

; Supported-source full stream argument/source mutation.
(defthm fn-hrcur-cold-test-source-run-remove-tag
  (let ((source '(:resident (:span 6 0 0 2))) (pool '(17 23)))
    (and
      (fn-hrcur-widthp source 2)
      (not (eq (car source) :decoded))
      (fn-hrcur-cold-domainp (cadr source) pool)
      (fn-scc-octet-listp pool)
      (not (fn-hrcur-cold-test-source-run-conclusionp source pool))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-hrcur-cold-oracle-run '(:refused nil nil nil :capture :lease nil nil 0) '(17 23))) :in-theory
    (enable fn-hrcur-cold-test-source-run-conclusionp fn-hrcur-cold-oracle-run
            fn-hrcur-cold-oracle-step fn-hrcur-cold-begin
            fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp
            fn-hrcur-span-shapep fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
            fn-hrcur-cold-countp fn-hrcur-cold-demand))))

; Supported-source full stream argument/source mutation.
(defthm fn-hrcur-cold-test-source-run-remove-domain
  (let ((source '(:decoded (:bogus nil))) (pool '(17 23)))
    (and
      (fn-hrcur-widthp source 2)
      (eq (car source) :decoded)
      (not (fn-hrcur-cold-domainp (cadr source) pool))
      (fn-scc-octet-listp pool)
      (not (fn-hrcur-cold-test-source-run-conclusionp source pool))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-hrcur-cold-oracle-run '(:work ((:node (:bogus nil))) nil (:bogus nil) :capture :lease nil nil 0) '(17 23))) :in-theory
    (enable fn-hrcur-cold-test-source-run-conclusionp fn-hrcur-cold-oracle-run
            fn-hrcur-cold-oracle-step fn-hrcur-cold-begin
            fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp
            fn-hrcur-span-shapep fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
            fn-hrcur-cold-countp fn-hrcur-cold-demand))))

; Supported-source full stream argument/source mutation.
(defthm fn-hrcur-cold-test-source-run-remove-pool
  (let ((source '(:decoded (:span 6 0 0 2))) (pool '(999 23)))
    (and
      (fn-hrcur-widthp source 2)
      (eq (car source) :decoded)
      (fn-hrcur-cold-domainp (cadr source) pool)
      (not (fn-scc-octet-listp pool))
      (not (fn-hrcur-cold-test-source-run-conclusionp source pool))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-hrcur-cold-oracle-run '(:work ((:node (:span 6 0 0 2))) nil (:span 6 0 0 2) :capture :lease nil nil 0) '(999 23))) :in-theory
    (enable fn-hrcur-cold-test-source-run-conclusionp fn-hrcur-cold-oracle-run
            fn-hrcur-cold-oracle-step fn-hrcur-cold-begin
            fn-hrcur-cold-progress-invariantp fn-hrcur-cold-invariantp
            fn-hrcur-cold-domainp fn-hrcur-cold-tasksp fn-hrcur-cold-taskp
            fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp
            fn-hrcur-span-shapep fn-hrcur-span-rest fn-hrcur-span-wire
            fn-hrcur-cold-tick fn-hrcur-cold-supply fn-hrcur-cold-state
            fn-hrcur-cold-countp fn-hrcur-cold-demand))))
