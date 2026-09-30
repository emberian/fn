; PRF-1132 / SCN-1039 continuation: literal source trace teeth.

(in-package "ACL2")

(include-book "../../books/payload-profile-source-trace")

(defthm pzt-zin-bomb-limit-literal-positive
 (and
  (equal (car (fn-pzt-zin-bomb-limit (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st))))) (fn-zin-bomb-limit (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))
  (equal (fn-pzt-count :add (cdr (fn-pzt-zin-bomb-limit (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))) 1)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-zin-bomb-limit (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))) 1)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-zin-bomb-limit (fn-zin-set 7 18446744073709551614 (fn-zin-reset (create-fn-zin-st)))))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-zin-stored-allowance-literal-positive
 (and
  (equal (car (fn-pzt-zin-stored-allowance 9223372036854775807)) (fn-zin-stored-allowance 9223372036854775807))
  (equal (fn-pzt-count :add (cdr (fn-pzt-zin-stored-allowance 9223372036854775807))) 1)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-zin-stored-allowance 9223372036854775807))) 1)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-zin-stored-allowance 9223372036854775807))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzd-budget-literal-positive
 (and
  (equal (car (fn-pzt-pzd-budget 9223372036854775807 9223372036854775807)) (fn-pzd-budget 9223372036854775807 9223372036854775807))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzd-budget 9223372036854775807 9223372036854775807))) 2)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzd-budget 9223372036854775807 9223372036854775807))) 2)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzd-budget 9223372036854775807 9223372036854775807))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-quantum-literal-positive
 (and
  (equal (car (fn-pzt-pzw-quantum 1025 1025)) (fn-pzw-quantum 1025 1025))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-quantum 1025 1025))) 0)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-quantum 1025 1025))) 0)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-quantum 1025 1025))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-room-literal-positive
 (and
  (equal (car (fn-pzt-pzw-room 9223372036854775807 9223372036854775800)) (fn-pzw-room 9223372036854775807 9223372036854775800))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-room 9223372036854775807 9223372036854775800))) 2)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-room 9223372036854775807 9223372036854775800))) 0)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-room 9223372036854775807 9223372036854775800))) 1))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-budget-left-literal-positive
 (and
  (equal (car (fn-pzt-pzw-budget-left 1024 18446744073709551615 512)) (fn-pzw-budget-left 1024 18446744073709551615 512))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-budget-left 1024 18446744073709551615 512))) 2)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-budget-left 1024 18446744073709551615 512))) 0)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-budget-left 1024 18446744073709551615 512))) 2))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-select-literal-positive
 (and
  (equal (car (fn-pzt-pzw-select 9223372036854775800 64 9223372036854775799 16384)) (fn-pzw-select 9223372036854775800 64 9223372036854775799 16384))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-select 9223372036854775800 64 9223372036854775799 16384))) 5)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-select 9223372036854775800 64 9223372036854775799 16384))) 0)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-select 9223372036854775800 64 9223372036854775799 16384))) 3))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-stored-allowance-literal-positive
 (and
  (equal (car (fn-pzt-pzw-stored-allowance 9223372036854775807)) (fn-pzw-stored-allowance 9223372036854775807))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-stored-allowance 9223372036854775807))) 1)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-stored-allowance 9223372036854775807))) 1)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-stored-allowance 9223372036854775807))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-pzw-stored-admissiblep-literal-positive
 (and
  (equal (car (fn-pzt-pzw-stored-admissiblep 9223372036854775807 9223372036854775807)) (fn-pzw-stored-admissiblep 9223372036854775807 9223372036854775807))
  (equal (fn-pzt-count :add (cdr (fn-pzt-pzw-stored-admissiblep 9223372036854775807 9223372036854775807))) 1)
  (equal (fn-pzt-count :multiply (cdr (fn-pzt-pzw-stored-admissiblep 9223372036854775807 9223372036854775807))) 1)
  (equal (fn-pzt-count :negate (cdr (fn-pzt-pzw-stored-admissiblep 9223372036854775807 9223372036854775807))) 0))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

; Mutation: pricing subtraction as only its addition misses an actual event.
(defthm pzt-budget-left-omitted-negation-mutant
 (let ((trace (cdr (fn-pzt-pzw-budget-left 1024 65536 512))))
  (and (equal (fn-pzt-count :add trace) 2)
       (equal (fn-pzt-count :negate trace) 2)
       (not (equal (+ (fn-pzt-count :add trace) (fn-pzt-count :negate trace))
                   (fn-pzt-count :add trace)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-selector-disjoint-positive
 (let ((result (fn-pzt-pzw-select 10 1 100 1)))
  (and (equal (car result) (fn-pzw-select 10 1 100 1))
       (equal (car result) '(0 0 0))
       (equal (fn-pzt-count :add (cdr result)) 2)
       (equal (fn-pzt-count :multiply (cdr result)) 0)
       (equal (fn-pzt-count :negate (cdr result)) 0)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))

(defthm pzt-admissibility-refusal-positive
 (let ((result (fn-pzt-pzw-stored-admissiblep -1 0)))
  (and (equal (car result) (fn-pzw-stored-admissiblep -1 0))
       (equal (car result) nil)
       (equal (fn-pzt-count :add (cdr result)) 0)
       (equal (fn-pzt-count :multiply (cdr result)) 0)
       (equal (fn-pzt-count :negate (cdr result)) 0)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-zin-bomb-limit fn-pzt-zin-stored-allowance fn-pzt-pzd-budget fn-pzt-pzw-quantum fn-pzt-pzw-room fn-pzt-pzw-budget-left fn-pzt-pzw-select fn-pzt-pzw-stored-allowance fn-pzt-pzw-stored-admissiblep))))
