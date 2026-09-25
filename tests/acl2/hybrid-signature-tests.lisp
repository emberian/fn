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

; The exact maximum-source preimage is the native bound exercised by the
; component interoperability test; it is derived here by the actual ACL2
; framing function rather than duplicated in host arithmetic.
(assert-event
 (equal (len (fn-hsig-signed-preimage
              *hs-principal* *hs-keys* (make-list 32768 :initial-element 42)))
        34820))

;; Carrier v2 (bounds P4).  The v1 bound is the u16's 65535: the old
;; 32768 bound no longer refuses, 65535 is v1, 65536 is not.
(assert-event
 (and (fn-hsig-subject-p *hs-principal* *hs-keys*
                         (make-list 32769 :initial-element 42))
      (fn-hsig-subject-p *hs-principal* *hs-keys*
                         (make-list 65535 :initial-element 42))
      (not (fn-hsig-subject-p *hs-principal* *hs-keys*
                              (make-list 65536 :initial-element 42)))
      (equal (len (fn-hsig-signed-preimage
                   *hs-principal* *hs-keys*
                   (make-list 65535 :initial-element 42)))
             67587)))

;; A 70,000-octet source is v2 and not v1: the signer's version is 2, the v2
;; subject admits it, the v1 subject refuses it, and its preimage carries the
;; v2 tag, version octet 2 and the u32 length 00 01 11 70.
(defconst *hs-big-source* (make-list 70000 :initial-element 42))
(assert-event
 (and (equal (fn-hsig-source-version *hs-big-source*) 2)
      (equal (fn-hsig-source-version *hs-source*) 1)
      (fn-hsig-subject-v2-p *hs-principal* *hs-keys* *hs-big-source*)
      (not (fn-hsig-subject-p *hs-principal* *hs-keys* *hs-big-source*))
      (not (fn-hsig-subject-v2-p *hs-principal* *hs-keys* *hs-source*))
      (fn-hsig-subject-at-p 2 *hs-principal* *hs-keys* *hs-big-source*)
      (not (fn-hsig-subject-at-p 1 *hs-principal* *hs-keys* *hs-big-source*))
      (not (fn-hsig-subject-at-p 3 *hs-principal* *hs-keys* *hs-big-source*))
      (let ((pre (fn-hsig-signed-preimage-at 2 *hs-principal* *hs-keys*
                                             *hs-big-source*)))
        (and (equal (len pre) (+ 2 28 2024 70000))
             (equal (take 30 pre)
                    (append '(88 28) *fn-hsig-v2-domain-tag*))
             (equal (nth 30 pre) 2)
             (equal (take 4 (nthcdr (+ 30 2020) pre)) '(0 1 17 112))))
      (fn-hsig-authorize-at 2 *hs-principal* *hs-keys* *hs-big-source*
                            *hs-signatures* *hs-ml-key* :verified :verified)
      (not (fn-hsig-authorize *hs-principal* *hs-keys* *hs-big-source*
                              *hs-signatures* *hs-ml-key* :verified :verified))))

;; The v1 path is the v1 function on a v1 source, byte for byte.
(assert-event
 (equal (fn-hsig-signed-preimage-at (fn-hsig-source-version *hs-source*)
                                    *hs-principal* *hs-keys* *hs-source*)
        (fn-hsig-signed-preimage *hs-principal* *hs-keys* *hs-source*)))

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
(assert-event
 (not (equal (fn-hsig-signed-preimage *hs-principal* *hs-keys* *hs-source*)
             (fn-hsig-signed-preimage
              (make-list 32 :initial-element 86) *hs-keys* *hs-source*))))
(assert-event
 (not (equal (fn-hsig-signed-preimage *hs-principal* *hs-keys* *hs-source*)
             (fn-hsig-signed-preimage
              *hs-principal*
              (list (cons :ed25519 *hs-ed-key*)
                    (cons :ml-dsa-65 (make-list 1952 :initial-element 35)))
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

;; Teeth for the -by-definition v1 equalities: without the v1 length they fail.
(must-fail
 (defthm hs-preimage-at-v1-without-length
   (equal (fn-hsig-signed-preimage-at (fn-hsig-source-version source)
                                      principal keys source)
          (fn-hsig-signed-preimage principal keys source))
   :hints (("Goal" :in-theory (enable fn-hsig-signed-preimage-at
                                      fn-hsig-source-version)))))
(must-fail
 (defthm hs-authorize-at-v1-without-length
   (equal (fn-hsig-authorize-at (fn-hsig-source-version source)
                                principal keys source signatures observed ed ml)
          (fn-hsig-authorize principal keys source signatures observed ed ml))
   :hints (("Goal" :in-theory (enable fn-hsig-authorize-at fn-hsig-authorize
                                      fn-hsig-subject-at-p
                                      fn-hsig-source-version)))))
