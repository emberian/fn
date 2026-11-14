; Actual ACL2 numeric controls for the integer EXPT fragment used by the bridge.
; These do not establish that a served root discharges every reached domain.
(in-package "ACL2")

(defthm fn2-expt-natural-exponent-integer-result
 (implies (and (integerp base) (natp exponent))
          (integerp (expt base exponent)))
 :rule-classes nil)

; Positive whole antecedent and complete result, including the zero exponent.
(assert-event
 (and (integerp 3) (natp 4) (equal (expt 3 4) 81)
      (integerp 0) (natp 0) (equal (expt 0 0) 1)))

; Removing the exponent-domain condition admits a noninteger ACL2 result.
; The integer Val adapter's zero completion cannot represent this value.
(defthm fn2-expt-negative-domain-counterexample
 (and (integerp 2) (integerp -1) (not (natp -1))
      (equal (expt 2 -1) 1/2)
      (not (integerp (expt 2 -1)))
      (not (equal (expt 2 -1) 0)))
 :rule-classes nil)

; Changing exponentiation to addition preserves integer shape but not meaning.
(assert-event
 (and (integerp 3) (natp 4) (integerp (+ 3 4))
      (not (equal (+ 3 4) (expt 3 4)))))
