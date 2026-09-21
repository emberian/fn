(in-package "ACL2")
(include-book "../../books/hybrid-signature")
(include-book "std/testing/must-fail" :dir :system)

(local (in-theory (enable fn-hybrid-signature-vocabulary)))

(defconst *hs-ed-key* (make-list 32 :initial-element 17))
(defconst *hs-ml-key* (make-list 1952 :initial-element 34))
(defconst *hs-ed-sig* (make-list 64 :initial-element 51))
(defconst *hs-ml-sig* (make-list 3309 :initial-element 68))
(defconst *hs-principal* (make-list 32 :initial-element 85))
(defconst *hs-source* '(70 114 111 109 58 32 97 13 10 13 10 120 13 10))
(defconst *hs-keys* (list (cons :ed25519 *hs-ed-key*)
                          (cons :ml-dsa-65 *hs-ml-key*)))
(defconst *hs-signatures* (list (cons :ed25519 *hs-ed-sig*)
                                (cons :ml-dsa-65 *hs-ml-sig*)))

; Reachable, non-degenerate witness for the host-called decision.
(assert-event (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                 *hs-signatures* *hs-ml-key*
                                 :verified :verified))

; One bad component, absence, unknown observation and classical-only fallback.
(assert-event (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                      *hs-signatures* *hs-ml-key* :refused :verified)))
(assert-event (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                      *hs-signatures* *hs-ml-key* :verified :refused)))
(assert-event (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                      *hs-signatures* *hs-ml-key* :verified :unsupported)))
(assert-event (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                      (list (cons :ed25519 *hs-ed-sig*))
                                      *hs-ml-key* :verified :verified)))
(assert-event (not (fn-hsig-authorize
                    *hs-principal* *hs-keys* *hs-source* *hs-signatures*
                    (make-list 1952 :initial-element 35) :verified :verified)))

; Stripping, swapping and profile confusion fail before primitive verdicts.
(assert-event (not (fn-hsig-authorize *hs-principal*
                                      (list (cons :ml-dsa-65 *hs-ml-key*)
                                            (cons :ed25519 *hs-ed-key*))
                                      *hs-source* *hs-signatures*
                                      *hs-ml-key* :verified :verified)))
(assert-event (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-source*
                                      (list (cons :ml-dsa-65 *hs-ml-sig*)
                                            (cons :ed25519 *hs-ed-sig*))
                                      *hs-ml-key* :verified :verified)))

; Exact authored bytes and enrolled keyset are visible in the signed subject.
(assert-event
 (not (equal (fn-hsig-signed-preimage *hs-principal* *hs-keys* *hs-source*)
             (fn-hsig-signed-preimage *hs-principal* *hs-keys*
                                      (append *hs-source* '(32))))))
(assert-event
 (not (equal (fn-hsig-signed-preimage *hs-principal* *hs-keys* *hs-source*)
             (fn-hsig-signed-preimage
              *hs-principal*
              (list (cons :ed25519 (make-list 32 :initial-element 18))
                    (cons :ml-dsa-65 *hs-ml-key*))
              *hs-source*))))

; Teeth: neither theorem follows after deleting one of its essential premises.
(must-fail
 (defthm hybrid-without-ml-observation
   (implies (and (fn-hsig-subject-p principal keys source)
                 (fn-hsig-signatures-p signatures)
                 (equal ed :verified))
            (fn-hsig-authorize principal keys source signatures observed ed ml))))
(must-fail
 (defthm hybrid-without-signature-shape
   (implies (and (fn-hsig-subject-p principal keys source)
                 (equal ed :verified) (equal ml :verified))
            (fn-hsig-authorize principal keys source signatures observed ed ml))))
