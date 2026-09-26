; Teeth for books/store-profile-namespace (D27, PRF-102).
(in-package "ACL2")
(include-book "../../books/store-profile-namespace")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; D27, PRF-102: the namespace accessors read the profile a store runs under.
; The default profile and the development preset give 2^20 for each; an
; operator's value above the pre-D27 caps (credentials
; 128, configuration generations 8192) is read back as written.
(assert-event (equal (fn-bs-profile-max-credentials *fn-bs-profile-defaults*) 1048576))
(assert-event (equal (fn-bs-profile-max-config-generations *fn-bs-profile-defaults*)
                     1048576))
(assert-event (equal (fn-bs-profile-max-consumers *fn-bs-profile-development*)
                     1048576))
(defconst *spnt-raised*
  (fn-bs-profile-put 12 129 (fn-bs-profile-put 11 8193 *fn-bs-profile-defaults*)))
(assert-event (fn-bs-profile-validp *spnt-raised*))
(assert-event (equal (fn-bs-profile-max-credentials *spnt-raised*) 129))
(assert-event (equal (fn-bs-profile-max-config-generations *spnt-raised*) 8193))
(assert-event (equal (fn-bs-profile-max-policy-members *spnt-raised*) 1048576))
; A zero count is refused by name, so no store runs with an empty namespace.
(assert-event (equal (fn-bs-profile-invalid-reason
                      (fn-bs-profile-put 12 0 *fn-bs-profile-defaults*))
                     :namespace-count-outside-width))
; `fn-bs-profile-namespace-counts-within-width' needs its hypothesis: a value
; that is no profile reads 0 for every count.
(must-fail
 (defthm spnt-namespace-counts-without-admission
   (fn-bs-profile-countp (fn-bs-profile-max-credentials nil))
   :rule-classes nil))

; The width keystone's reachable witness: the default profile, admitted, has
; every count within the width.
(assert-event (fn-bs-profile-admittedp *fn-bs-profile-defaults*))
(assert-event (fn-bs-profile-countp (fn-bs-profile-max-bp-rows *fn-bs-profile-defaults*)))
