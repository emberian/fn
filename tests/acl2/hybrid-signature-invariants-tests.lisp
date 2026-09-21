(in-package "ACL2")
(include-book "../../books/hybrid-signature-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *hsigi-principal-a* (make-list 32 :initial-element 17))
(defconst *hsigi-principal-b* (make-list 32 :initial-element 18))
(defconst *hsigi-ed-a* (make-list 32 :initial-element 33))
(defconst *hsigi-ed-b* (make-list 32 :initial-element 34))
(defconst *hsigi-ml-a* (make-list 1952 :initial-element 65))
(defconst *hsigi-ml-b* (make-list 1952 :initial-element 66))
(defconst *hsigi-keys-a*
  (list (cons :ed25519 *hsigi-ed-a*) (cons :ml-dsa-65 *hsigi-ml-a*)))
(defconst *hsigi-keys-b*
  (list (cons :ed25519 *hsigi-ed-b*) (cons :ml-dsa-65 *hsigi-ml-b*)))
(defconst *hsigi-source-a* '(70 114 111 109 58 32 97 13 10 13 10 120 13 10))
(defconst *hsigi-source-b* '(70 114 111 109 58 32 98 13 10 13 10 121 13 10))

; Reachable non-degenerate subject: both algorithm keys, a nonzero principal,
; and exact source bytes all project back out of the real subject body.
(assert-event
 (and (fn-hsig-subject-p *hsigi-principal-a* *hsigi-keys-a* *hsigi-source-a*)
      (equal (fn-hsigi-principal
              (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
             *hsigi-principal-a*)
      (equal (fn-hsigi-ed-key
              (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
             *hsigi-ed-a*)
      (equal (fn-hsigi-ml-key
              (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
             *hsigi-ml-a*)
      (equal (fn-hsigi-source
              (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
             *hsigi-source-a*)))

; The witness separates every bound component at both byte-subject layers.
(assert-event
 (and (not (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                        *hsigi-source-a*)
                  (fn-hsig-subject-body *hsigi-principal-b* *hsigi-keys-a*
                                        *hsigi-source-a*)))
      (not (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                        *hsigi-source-a*)
                  (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-b*
                                        *hsigi-source-a*)))
      (not (equal (fn-hsig-signed-preimage *hsigi-principal-a* *hsigi-keys-a*
                                           *hsigi-source-a*)
                  (fn-hsig-signed-preimage *hsigi-principal-a* *hsigi-keys-a*
                                           *hsigi-source-b*)))))

; Every hypothesis of both keystones is load-bearing.
(must-fail
 (defthm hsigi-body-without-left-subject
   (implies (and (fn-hsig-subject-p pb kb sb)
                 (equal (fn-hsig-subject-body pa ka sa)
                        (fn-hsig-subject-body pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-body-without-right-subject
   (implies (and (fn-hsig-subject-p pa ka sa)
                 (equal (fn-hsig-subject-body pa ka sa)
                        (fn-hsig-subject-body pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-body-without-byte-equality
   (implies (and (fn-hsig-subject-p pa ka sa)
                 (fn-hsig-subject-p pb kb sb))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-preimage-without-left-subject
   (implies (and (fn-hsig-subject-p pb kb sb)
                 (equal (fn-hsig-signed-preimage pa ka sa)
                        (fn-hsig-signed-preimage pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-preimage-without-right-subject
   (implies (and (fn-hsig-subject-p pa ka sa)
                 (equal (fn-hsig-signed-preimage pa ka sa)
                        (fn-hsig-signed-preimage pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-preimage-without-byte-equality
   (implies (and (fn-hsig-subject-p pa ka sa)
                 (fn-hsig-subject-p pb kb sb))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))

