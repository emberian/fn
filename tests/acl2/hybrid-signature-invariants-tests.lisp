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
(defconst *hsigi-keys-ed-only*
  (list (cons :ed25519 *hsigi-ed-b*) (cons :ml-dsa-65 *hsigi-ml-a*)))
(defconst *hsigi-keys-ml-only*
  (list (cons :ed25519 *hsigi-ed-a*) (cons :ml-dsa-65 *hsigi-ml-b*)))
(defconst *hsigi-keys-bad-tag*
  (list (cons :not-ed25519 *hsigi-ed-a*) (cons :ml-dsa-65 *hsigi-ml-a*)))
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
      (not (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                        *hsigi-source-a*)
                  (fn-hsig-subject-body *hsigi-principal-a*
                                        *hsigi-keys-ed-only*
                                        *hsigi-source-a*)))
      (not (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                        *hsigi-source-a*)
                  (fn-hsig-subject-body *hsigi-principal-a*
                                        *hsigi-keys-ml-only*
                                        *hsigi-source-a*)))
      (not (equal (fn-hsig-signed-preimage *hsigi-principal-a* *hsigi-keys-a*
                                           *hsigi-source-a*)
                  (fn-hsig-signed-preimage *hsigi-principal-a* *hsigi-keys-a*
                                           *hsigi-source-b*)))))

; Concrete counterexamples for the theorem hypotheses.  The body writes fixed
; algorithm identifiers and selects key bytes from the pairs, so a malformed
; input tag can share bytes with the valid tuple.  Subject recognition is what
; excludes that alias on either side.
(assert-event
 (with-guard-checking
  :none
  (and (not (fn-hsig-subject-p *hsigi-principal-a* *hsigi-keys-bad-tag*
                               *hsigi-source-a*))
       (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-bad-tag*
                                    *hsigi-source-a*)
              (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
       (not (equal *hsigi-keys-bad-tag* *hsigi-keys-a*)))))
(assert-event
 (and (fn-hsig-subject-p *hsigi-principal-a* *hsigi-keys-a* *hsigi-source-a*)
      (not (equal (fn-hsig-subject-body *hsigi-principal-a* *hsigi-keys-a*
                                        *hsigi-source-a*)
                  (fn-hsig-subject-body *hsigi-principal-b* *hsigi-keys-b*
                                        *hsigi-source-b*)))
      (not (and (equal *hsigi-principal-a* *hsigi-principal-b*)
                (equal *hsigi-keys-a* *hsigi-keys-b*)
                (equal *hsigi-source-a* *hsigi-source-b*)))))

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

;; ---------------------------------------------------------------- carrier v2
(defconst *hsigi-big-a* (make-list 65536 :initial-element 120))
(defconst *hsigi-big-b* (make-list 65537 :initial-element 120))

; Reachable v2 subjects project back out of the v2 body.
(assert-event
 (and (fn-hsig-subject-v2-p *hsigi-principal-a* *hsigi-keys-a* *hsigi-big-a*)
      (fn-hsig-subject-v2-p *hsigi-principal-b* *hsigi-keys-b* *hsigi-big-b*)
      (equal (fn-hsigi-source-v2
              (fn-hsig-subject-body-v2 *hsigi-principal-a* *hsigi-keys-a*
                                       *hsigi-big-a*))
             *hsigi-big-a*)
      (equal (fn-hsigi-ml-key
              (fn-hsig-subject-body-v2 *hsigi-principal-a* *hsigi-keys-a*
                                       *hsigi-big-a*))
             *hsigi-ml-a*)))

; Separating witnesses: sources differing only in length, and subjects
; differing only in the ML-DSA key, give different v2 preimages.
(assert-event
 (and (not (equal (fn-hsig-signed-preimage-v2 *hsigi-principal-a* *hsigi-keys-a*
                                              *hsigi-big-a*)
                  (fn-hsig-signed-preimage-v2 *hsigi-principal-a* *hsigi-keys-a*
                                              *hsigi-big-b*)))
      (not (equal (fn-hsig-signed-preimage-v2 *hsigi-principal-a* *hsigi-keys-a*
                                              *hsigi-big-a*)
                  (fn-hsig-signed-preimage-v2 *hsigi-principal-a*
                                              *hsigi-keys-ml-only*
                                              *hsigi-big-a*)))))

; Disjointness on the same principal, keys and source octets framed as v1
; and as v2 (the logical v2 framing, outside its guard): they differ, and
; first at octet 29, the tag.
(assert-event
 (with-guard-checking
  :none
  (let ((v1 (fn-hsig-signed-preimage *hsigi-principal-a* *hsigi-keys-a*
                                    *hsigi-source-a*))
       (v2 (fn-hsig-signed-preimage-v2 *hsigi-principal-a* *hsigi-keys-a*
                                       *hsigi-source-a*)))
   (and (not (equal v1 v2))
        (equal (take 29 v1) (take 29 v2))
        (not (equal (nth 29 v1) (nth 29 v2)))))))

; Teeth: v2 injectivity needs each subject premise and the byte equality.
(must-fail
 (defthm hsigi-v2-body-without-left-subject
   (implies (and (fn-hsig-subject-v2-p pb kb sb)
                 (equal (fn-hsig-subject-body-v2 pa ka sa)
                        (fn-hsig-subject-body-v2 pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-v2-body-without-right-subject
   (implies (and (fn-hsig-subject-v2-p pa ka sa)
                 (equal (fn-hsig-subject-body-v2 pa ka sa)
                        (fn-hsig-subject-body-v2 pb kb sb)))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-v2-preimage-without-byte-equality
   (implies (and (fn-hsig-subject-v2-p pa ka sa)
                 (fn-hsig-subject-v2-p pb kb sb))
            (and (equal pa pb) (equal ka kb) (equal sa sb)))))

; Teeth: disjointness rests on the two different tags.  The same claim
; between two preimages under one tag is false (equal subjects frame to
; equal preimages).
(must-fail
 (defthm hsigi-v1-v1-preimages-disjoint
   (not (equal (fn-hsig-signed-preimage pa ka sa)
               (fn-hsig-signed-preimage pb kb sb)))))

; Teeth for the cross-version keystone: without either subject premise,
; or without the preimage equality, versions and subjects need not agree.
(must-fail
 (defthm hsigi-at-without-left-subject
   (implies (and (fn-hsig-subject-at-p vb pb kb sb)
                 (equal (fn-hsig-signed-preimage-at va pa ka sa)
                        (fn-hsig-signed-preimage-at vb pb kb sb)))
            (and (equal va vb) (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-at-without-right-subject
   (implies (and (fn-hsig-subject-at-p va pa ka sa)
                 (equal (fn-hsig-signed-preimage-at va pa ka sa)
                        (fn-hsig-signed-preimage-at vb pb kb sb)))
            (and (equal va vb) (equal pa pb) (equal ka kb) (equal sa sb)))))
(must-fail
 (defthm hsigi-at-without-byte-equality
   (implies (and (fn-hsig-subject-at-p va pa ka sa)
                 (fn-hsig-subject-at-p vb pb kb sb))
            (and (equal va vb) (equal pa pb) (equal ka kb) (equal sa sb)))))

; Teeth for version determinism: an unadmitted subject names any version.
(must-fail
 (defthm hsigi-version-without-subject
   (equal version (fn-hsig-source-version source))))
(assert-event
 (and (fn-hsig-subject-at-p 1 *hsigi-principal-a* *hsigi-keys-a* *hsigi-source-a*)
      (fn-hsig-subject-at-p 2 *hsigi-principal-a* *hsigi-keys-a* *hsigi-big-a*)
      (not (fn-hsig-subject-at-p 2 *hsigi-principal-a* *hsigi-keys-a*
                                 *hsigi-source-a*))))
