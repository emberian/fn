; Teeth for books/store-profile-namespace (D27, PRF-102).
(in-package "ACL2")
(include-book "../../books/store-profile-namespace")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; D27, PRF-102: the namespace accessors read the profile a store runs under.
; The default profile gives 2^20 for each; a format-7 store reads its
; translation's 2^20; an operator's value above the pre-D27 caps (credentials
; 128, configuration generations 8192) is read back as written.
(assert-event (equal (fn-bs-profile-max-credentials *fn-bs-profile-defaults*) 1048576))
(assert-event (equal (fn-bs-profile-max-config-generations *fn-bs-profile-defaults*)
                     1048576))
(assert-event (equal (fn-bs-profile-max-consumers
                      *fn-bs-meta-format-7-development-values*)
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

; D27, PRF-102: teeth for `fn-profile-upgrade-keeps-namespace-counts'.  The
; witness raises credentials to 129 and configuration generations to 8193,
; both above the pre-D27 caps, and is an upgrade of the defaults' lowered
; copy; the shrink back is refused by the field's name.
(defconst *spnt-ns-low*
  (fn-bs-profile-put 12 128 (fn-bs-profile-put 11 8192 *fn-bs-profile-defaults*)))
(defconst *spnt-ns-high*
  (fn-bs-profile-put 12 129 (fn-bs-profile-put 11 8193 *fn-bs-profile-defaults*)))
(assert-event (fn-profile-upgradep *spnt-ns-low* *spnt-ns-high*))
(assert-event (not (fn-profile-upgradep *spnt-ns-high* *spnt-ns-low*)))
(assert-event (equal (fn-profile-shrunk-field *spnt-ns-high* *spnt-ns-low*
                                              *fn-bs-profile-field-names*)
                     "max-config-generations"))
; Without the upgrade hypothesis the counts may fall.
(must-fail
 (defthm spnt-namespace-counts-without-upgrade
   (<= (fn-bs-profile-max-credentials *spnt-ns-high*)
       (fn-bs-profile-max-credentials *spnt-ns-low*))
   :rule-classes nil))
; The width keystone's reachable witness: the default profile, admitted, has
; every count within the width.
(assert-event (fn-bs-profile-admittedp *fn-bs-profile-defaults*))
(assert-event (fn-bs-profile-countp (fn-bs-profile-max-bp-rows *fn-bs-profile-defaults*)))
