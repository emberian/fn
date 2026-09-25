; fn: the operator's namespace counts (D27, PRF-102).
;
; Format 8's fields 9 to 13 (books/byte-store-frame.lisp) bound collections
; the store holds: consumers, BP rows, configuration generations, AUTHINFO
; credentials and group-policy members.  A constant that bounded any of them
; was a defect (D27, "bound work, never data"); each is now the operator's,
; read here through the profile the store runs under (`fn-bs-profile-field',
; so a format-7 store reads its translation's 2^20).  The books that refuse
; at a count take it as a natural argument; the host reads it once from the
; profile it opened (host/store-host.lisp, host/store-node-host.lisp).
;
; This book adds no field and does not change the layout: the fields and
; their validity relation (`fn-bs-profile-countp', 1 <= n <= 2^32 - 1) are
; byte-store-frame's, and the upgrade relation already lists them
; (`fn-profile-upgradep').
(in-package "ACL2")
(include-book "store-profile-upgrade")

(defun fn-bs-profile-max-consumers (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field *fn-bs-pf-max-consumers* values))
(defun fn-bs-profile-max-bp-rows (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field *fn-bs-pf-max-bp-rows* values))
(defun fn-bs-profile-max-config-generations (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field *fn-bs-pf-max-config-generations* values))
(defun fn-bs-profile-max-credentials (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field *fn-bs-pf-max-credentials* values))
(defun fn-bs-profile-max-policy-members (values)
  (declare (xargs :guard t))
  (fn-bs-profile-field *fn-bs-pf-max-policy-members* values))

; The five counts of the profile a store runs under are each at least 1 and
; within the u32 count width, so a consumer that refuses at `(< n (len xs))'
; never refuses an empty namespace, and no codec that carries a count caps
; below the operator's bound.
(defthm fn-bs-profile-namespace-counts-within-width
  (implies (fn-bs-profile-admittedp values)
           (and (fn-bs-profile-countp (fn-bs-profile-max-consumers values))
                (fn-bs-profile-countp (fn-bs-profile-max-bp-rows values))
                (fn-bs-profile-countp
                 (fn-bs-profile-max-config-generations values))
                (fn-bs-profile-countp (fn-bs-profile-max-credentials values))
                (fn-bs-profile-countp
                 (fn-bs-profile-max-policy-members values))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-of-profile-of))
           :in-theory (e/d (fn-bs-profile-validp
                            fn-bs-profile-invalid-reason
                            fn-bs-profile-field)
                           (fn-bs-profile-of fn-bs-pf fn-bs-profile-admittedp
                            fn-bs-profile-validp-of-profile-of
                            fn-frame-values-okp
                            fn-record-encoded-octets-ceiling)))))

; KEYSTONE (the upgrade never lowers a count).  A namespace the node wrote
; within the old profile's bound (configuration generations,
; `fn-native-admin-publication-within-the-operator-bound'; credentials,
; `fn-native-auth-load-within-the-operator-bound') is within the new
; profile's, so the listing and the loader keep admitting it after
; `store upgrade-profile' (host/native/io.lisp `fnn-command-upgrade-profile',
; whose verdict `fn-profile-upgrade-verdict' writes only an upgrade:
; `fn-profile-upgrade-verdict-writes-only-upgrades').
(defthm fn-profile-upgrade-keeps-namespace-counts
  (implies (fn-profile-upgradep old new)
           (and (<= (fn-bs-profile-max-consumers old)
                    (fn-bs-profile-max-consumers new))
                (<= (fn-bs-profile-max-bp-rows old)
                    (fn-bs-profile-max-bp-rows new))
                (<= (fn-bs-profile-max-config-generations old)
                    (fn-bs-profile-max-config-generations new))
                (<= (fn-bs-profile-max-credentials old)
                    (fn-bs-profile-max-credentials new))
                (<= (fn-bs-profile-max-policy-members old)
                    (fn-bs-profile-max-policy-members new))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-profile-upgradep fn-profile-bound)
                                  (fn-bs-profile-field fn-bs-profile-admittedp
                                   fn-bs-profile-validp)))))
