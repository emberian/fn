(in-package "ACL2")
(include-book "../../books/admission-preparation-source-capture")
; Actual retained-source mutation MODEL, no issuer or constructor permission.
(defthm fn-owner-admission-capture-complete-model
 (let* ((next (fn-owner-admission-retain-prepare-source
                '(token) 7 2 3 '(same-base-store) '(same-canonical) '(same-current)
                '(same-parent) '(same-config) '(same-obligations)
                '(same-reader) '(same-posting) state))
        (intent (f-get-global 'fn-owner-canonical-admission-executor next)))
  (and (equal intent '(:admission-prepare-intent (token) 7 2 (2 . 2)
                        (same-base-store) (same-canonical) (same-current)))
       (equal (f-get-global 'fn-owner-history-semantic-source next)
              '(:history-semantic-source (token) (same-parent) (same-config)))
       (equal (f-get-global 'fn-owner-history-semantic-obligation-base next)
              '(:history-obligation-base (token) (same-obligations)))
       (equal (f-get-global 'fn-owner-history-semantic-reader-base next)
              '(:history-reader-base (token) (same-reader) (same-posting)))))
 :hints (("Goal" :in-theory (enable fn-owner-admission-retain-prepare-source))))
