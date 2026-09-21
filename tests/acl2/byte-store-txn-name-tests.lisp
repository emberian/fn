; Executable witnesses and hypothesis teeth for the attached transaction name.
(in-package "ACL2")
(include-book "../../books/byte-store-txn-name")
(include-book "std/testing/must-fail" :dir :system)

; Minimum width is padding, not a bound.  The realization covers every
; natural, including a 21-digit value outside the allocator's bounded domain.
(assert-event
 (equal (fn-bs-txn-name-impl 0) "00000000000000000000.txn"))
(assert-event
 (equal (fn-bs-txn-name-impl 17) "00000000000000000017.txn"))
(assert-event
 (equal (fn-bs-txn-name 17) "00000000000000000017.txn"))
(assert-event
 (equal (fn-bs-txn-name-impl 100000000000000000000)
        "100000000000000000000.txn"))
(assert-event
 (not (equal (fn-bs-txn-name-impl 17) (fn-bs-txn-name-impl 18))))

; Each hypothesis of fn-bs-txn-name-impl-injective has teeth.  NFIX makes a
; non-natural share zero's name, while dropping the name equality would claim
; every two naturals are equal.
(assert-event
 (equal (fn-bs-txn-name-impl -1) (fn-bs-txn-name-impl 0)))
(local
 (must-fail
  (defthm fn-bs-txn-name-injective-without-left-natp
    (implies (and (natp j)
                  (equal (fn-bs-txn-name-impl i)
                         (fn-bs-txn-name-impl j)))
             (equal i j))
    :rule-classes nil)))
(local
 (must-fail
  (defthm fn-bs-txn-name-injective-without-right-natp
    (implies (and (natp i)
                  (equal (fn-bs-txn-name-impl i)
                         (fn-bs-txn-name-impl j)))
             (equal i j))
    :rule-classes nil)))
(local
 (must-fail
  (defthm fn-bs-txn-name-injective-without-name-equality
    (implies (and (natp i) (natp j))
             (equal i j))
    :rule-classes nil)))
