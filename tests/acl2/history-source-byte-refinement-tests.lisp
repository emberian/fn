(in-package "ACL2")
(include-book "../../books/history-source-byte-refinement")

(defun fn-hsrct-ticks (c n)
 (declare (xargs :guard (natp n)))
 (if (zp n) c
   (mv-let (v b next) (fn-hsrcb-tick c)
     (declare (ignore v b)) (fn-hsrct-ticks next (1- n)))))
(defun fn-hsrct-census-ticks (c n)
 (declare (xargs :guard (natp n)))
 (if (zp n) c
   (mv-let (v b next) (fn-hsrcc-tick c)
     (declare (ignore v b)) (fn-hsrct-census-ticks next (1- n)))))
(defun-nx fn-hsrct-tick-law (c pool)
 (let ((v (mv-nth 0 (fn-hsrcb-tick c))) (b (mv-nth 1 (fn-hsrcb-tick c)))
       (next (mv-nth 2 (fn-hsrcb-tick c))))
  (and (fn-hsrcb-invariantp next pool) (implies (eq v :emit) (fn-scc-octetp b))
       (equal (fn-hsrcb-rest c pool) (if (eq v :emit) (cons b (fn-hsrcb-rest next pool)) (fn-hsrcb-rest next pool)))
       (implies (eq v :prepared) (equal (fn-hsrcb-rest c pool) nil)))))
(defun-nx fn-hsrct-supply-law (c pos byte pool)
 (let ((v (mv-nth 0 (fn-hsrcb-supply c pos byte))) (b (mv-nth 1 (fn-hsrcb-supply c pos byte)))
       (next (mv-nth 2 (fn-hsrcb-supply c pos byte))))
  (and (member-eq v '(:continue :emit)) (fn-hsrcb-invariantp next pool)
       (implies (eq v :emit) (fn-scc-octetp b))
       (equal (fn-hsrcb-rest c pool) (if (eq v :emit) (cons b (fn-hsrcb-rest next pool)) (fn-hsrcb-rest next pool))))))
(defun-nx fn-hsrct-census-tick-law (c pool)
 (let ((v (mv-nth 0 (fn-hsrcc-tick c))) (n (mv-nth 1 (fn-hsrcc-tick c)))
       (next (mv-nth 2 (fn-hsrcc-tick c))))
  (and (fn-hsrcc-invariantp next pool) (equal (fn-hsrcc-total next pool) (fn-hsrcc-total c pool))
       (implies (eq v :prepared) (equal n (fn-hsrcc-total c pool))))))
(defun-nx fn-hsrct-census-supply-law (c pos byte pool)
 (let ((v (mv-nth 0 (fn-hsrcc-supply c pos byte))) (next (mv-nth 1 (fn-hsrcc-supply c pos byte))))
  (and (equal v (if (eq (fn-hrcur-field 0 c) :active) :continue '(:refused :census-cursor)))
       (fn-hsrcc-invariantp next pool) (equal (fn-hsrcc-total next pool) (fn-hsrcc-total c pool)))))

; Reachable positive, complete antecedent and complete output law.
(defthm fn-hsrct-tick-positive
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
  (and (fn-hsrcb-invariantp c '(17 23)) (eq (mv-nth 0 (fn-hsrcb-tick c)) :emit) (fn-hsrct-tick-law c '(17 23))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-tick-remove-invariant
 (let ((c '(:cold (:work ((:bad-task nil)) nil nil :capture :lease nil nil 0))))
  (and (not (fn-hsrcb-invariantp c '(17 23))) (not (fn-hsrct-tick-law c '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Reachable positive, complete antecedent and complete output law.
(defthm fn-hsrct-supply-positive
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (fn-hsrcb-invariantp c '(17 23)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c)))) (equal 17 (nth 0 '(17 23))) (fn-hsrct-supply-law c 0 17 '(17 23))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-supply-remove-invariant
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (not (fn-hsrcb-invariantp c '(999 23))) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c)))) (equal 999 (nth 0 '(999 23))) (not (fn-hsrct-supply-law c 0 999 '(999 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-supply-remove-demand
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
  (and (fn-hsrcb-invariantp c '(17 23)) (not (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c)))) (equal nil (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c)))) (equal 17 (nth nil '(17 23))) (not (fn-hsrct-supply-law c nil 17 '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-supply-remove-position
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (fn-hsrcb-invariantp c '(17 23)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c))) (not (equal 1 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c))))) (equal 23 (nth 1 '(17 23))) (not (fn-hsrct-supply-law c 1 23 '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-supply-remove-byte
 (let ((c (fn-hsrct-ticks (fn-hsrcb-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (fn-hsrcb-invariantp c '(17 23)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick c))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick c)))) (not (equal 18 (nth 0 '(17 23)))) (not (fn-hsrct-supply-law c 0 18 '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Reachable positive, complete antecedent and complete output law.
(defthm fn-hsrct-census-tick-positive
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
  (and (fn-hsrcc-invariantp c '(17 23)) (eq (mv-nth 0 (fn-hsrcc-tick c)) :continue) (fn-hsrct-census-tick-law c '(17 23))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-census-tick-remove-invariant
 (let ((c '(:bogus (:cold (:work nil nil nil :capture :lease nil nil 0)) 0)))
  (and (not (fn-hsrcc-invariantp c '(17 23))) (not (fn-hsrct-census-tick-law c '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Reachable positive, complete antecedent and complete output law.
(defthm fn-hsrct-census-supply-positive
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (fn-hsrcc-invariantp c '(17 23)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal 17 (nth 0 '(17 23))) (fn-hsrct-census-supply-law c 0 17 '(17 23))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-census-supply-remove-invariant
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (not (fn-hsrcc-invariantp c '(999 23))) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal 999 (nth 0 '(999 23))) (not (fn-hsrct-census-supply-law c 0 999 '(999 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-census-supply-remove-demand
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 1)))
  (and (fn-hsrcc-invariantp c '(17 23)) (not (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal nil (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (equal 17 (nth nil '(17 23))) (not (fn-hsrct-census-supply-law c nil 17 '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-census-supply-remove-position
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 6 0 0 2)) :capture :lease) 5)))
  (and (fn-hsrcc-invariantp c '(17 23)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (not (equal 1 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))))) (equal 23 (nth 1 '(17 23))) (not (fn-hsrct-census-supply-law c 1 23 '(17 23)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Hypothesis-removal counterexample; corrupted source/state or observation as named.
(defthm fn-hsrct-census-supply-remove-byte
 (let ((c (fn-hsrct-census-ticks (fn-hsrcc-begin '(:decoded (:span 4 2 0 3)) :capture :lease) 1)))
  (and (fn-hsrcc-invariantp c '(78 73 76)) (fn-hsrcb-demandp (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c)))) (equal 0 (fn-hrcur-field 1 (mv-nth 0 (fn-hsrcb-tick (fn-hrcur-field 1 c))))) (not (equal 79 (nth 0 '(78 73 76)))) (not (fn-hsrct-census-supply-law c 0 79 '(78 73 76)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrcb-invariantp fn-hsrcb-rest fn-hsrcb-tick fn-hsrcb-supply fn-hsrcb-coldp fn-hsrcb-demandp
fn-hsrcb-begin fn-hsrcc-begin fn-hsrcc-tick fn-hsrcc-supply fn-hsrcc-invariantp fn-hsrcc-total
fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp fn-hrcur-cold-begin
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-symbol-budgetp fn-hrcur-cold-symbol-childp
fn-hdsn-coherent fn-hdsn-denote fn-hdsn-classify-name fn-hdsn-find fn-hrcur-cold-name
fn-hsrct-tick-law fn-hsrct-supply-law fn-hsrct-census-tick-law fn-hsrct-census-supply-law))))

; Literal actual census row gate: stop just before the tick that acknowledges
; the fully encoded row. The fixture, not the served path, reads this pool.
(defun fn-hsrct-row-await (fuel c pool)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) c
   (mv-let (v encoded next) (fn-hct-tick c)
    (declare (ignore encoded))
    (cond ((eq v :row-done) c)
          ((eq v :continue) (fn-hsrct-row-await (1- fuel) next pool))
          ((fn-hsrcb-demandp v)
           (mv-let (sv supplied) (fn-hct-supply c (fn-hrcur-field 1 v) (nth (fn-hrcur-field 1 v) pool))
             (if (eq sv :continue) (fn-hsrct-row-await (1- fuel) supplied pool) c)))
          (t c)))))
(defun fn-hsrct-ready-row ()
 (declare (xargs :verify-guards nil))
 (mv-let (word c) (fn-hct-offer (fn-hct-begin 1 :capture :lease) 0 '(:decoded (:span 3 0 1 3)))
  (declare (ignore word)) (fn-hsrct-row-await 100 c '(0 65 66 67))))
(defun-nx fn-hsrct-row-law (c h ev)
 (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c))) (len (append h (list ev))))
      (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c))) (fn-hp-pes-len (append h (list ev))))))

; Reachable full row antecedent/conclusion.
(defthm fn-hsrct-row-positive
 (let ((c (fn-hsrct-ready-row)) (ev "ABC")) (and (equal (fn-hrcur-field 2 c) (len nil)) (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil))
 (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67))
 (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev)))
 (eq (mv-nth 0 (fn-hct-tick c)) :row-done) (fn-hsrct-row-law c nil ev)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))

; Hypothesis-removal: corrupted carried census/codec or missing completion as named.
(defthm fn-hsrct-row-remove-count
 (let ((c (update-nth 2 1 (update-nth 1 2 (fn-hsrct-ready-row)))) (ev "ABC")) (and (not (equal (fn-hrcur-field 2 c) (len nil))) (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil))
 (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67))
 (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev)))
 (eq (mv-nth 0 (fn-hct-tick c)) :row-done) (not (fn-hsrct-row-law c nil ev))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))

; Hypothesis-removal: corrupted carried census/codec or missing completion as named.
(defthm fn-hsrct-row-remove-pool
 (let ((c (update-nth 3 1 (fn-hsrct-ready-row))) (ev "ABC")) (and (equal (fn-hrcur-field 2 c) (len nil)) (not (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil)))
 (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67))
 (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev)))
 (eq (mv-nth 0 (fn-hct-tick c)) :row-done) (not (fn-hsrct-row-law c nil ev))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))

; Hypothesis-removal: corrupted carried census/codec or missing completion as named.
(defthm fn-hsrct-row-remove-codec
 (let ((c (update-nth 4 (list :done (fn-hsrcb-begin '(:decoded (:span 3 0 1 3)) :capture :lease) 0) (fn-hsrct-ready-row))) (ev "ABC")) (and (equal (fn-hrcur-field 2 c) (len nil)) (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil))
 (not (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67)))
 (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev)))
 (eq (mv-nth 0 (fn-hct-tick c)) :row-done) (not (fn-hsrct-row-law c nil ev))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))

; Hypothesis-removal: corrupted carried census/codec or missing completion as named.
(defthm fn-hsrct-row-remove-total
 (let ((c (fn-hsrct-ready-row)) (ev "ABCDEFGHIJKLMNOPQRST")) (and (equal (fn-hrcur-field 2 c) (len nil)) (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil))
 (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67))
 (not (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev))))
 (eq (mv-nth 0 (fn-hct-tick c)) :row-done) (not (fn-hsrct-row-law c nil ev))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))

; Hypothesis-removal: corrupted carried census/codec or missing completion as named.
(defthm fn-hsrct-row-remove-completion
 (let ((c (mv-nth 1 (fn-hct-offer (fn-hct-begin 1 :capture :lease) 0 '(:decoded (:span 3 0 1 3))))) (ev "ABC")) (and (equal (fn-hrcur-field 2 c) (len nil)) (equal (fn-hrcur-field 3 c) (fn-hp-pes-len nil))
 (fn-hsrcc-invariantp (fn-hrcur-field 4 c) '(0 65 66 67))
 (equal (fn-hsrcc-total (fn-hrcur-field 4 c) '(0 65 66 67)) (len (fn-scc-encode ev)))
 (not (eq (mv-nth 0 (fn-hct-tick c)) :row-done)) (not (fn-hsrct-row-law c nil ev))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hsrct-row-law fn-hsrcc-invariantp fn-hsrcc-total fn-hsrcb-invariantp fn-hsrcb-rest
fn-hsrcb-coldp fn-hrcur-cold-invariantp fn-hrcur-cold-rest fn-hrcur-cold-domainp
fn-hrcur-cold-tasksp fn-hrcur-cold-taskp fn-hrcur-cold-tasks-rest fn-hrcur-cold-task-rest
fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-span-invariantp fn-hrcur-span-rest fn-hrcur-span-wire
fn-hrcur-span-shapep fn-hrcur-cold-begin fn-hct-tick fn-hsrcc-tick))))
