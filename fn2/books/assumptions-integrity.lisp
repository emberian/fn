(in-package "ACL2")

; A-INTEGRITY-EVIDENCE: a passing checksum is integrity evidence only under
; the named assumption that the accidental faults in this run do not produce
; a checksum collision. No claim is made against chosen/adversarial faults.
; The constrained predicate makes the assumption available to future claims;
; classification itself reports evidence, never asserts this predicate.
(encapsulate
 (((fn2-a-integrity-evidence * *) => *))
 (local (defun fn2-a-integrity-evidence (expected observed)
          (equal expected observed)))
 (defthm fn2-a-integrity-evidence-sound
   (implies (fn2-a-integrity-evidence expected observed)
            (equal expected observed))
   :rule-classes nil))

