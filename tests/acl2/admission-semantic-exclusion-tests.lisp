; Fixed exclusion MODELs; tags do not grant issuer or semantic authority.
(in-package "ACL2")
(include-book "../../books/admission-semantic-exclusion")
(defthm fn-owner-admission-config-acquiring-model-busy
 (fn-owner-admission-semantic-busy-p
  (f-put-global 'fn-owner-history-semantic-source
                '(:history-config-acquiring 7 9) state)))
(defthm fn-owner-admission-config-source-model-busy
 (fn-owner-admission-semantic-busy-p
  (f-put-global 'fn-owner-history-semantic-source
                '(:history-config-source 1 2 3 4 5 6 7 8 9) state)))
(defthm fn-owner-admission-unretained-model-not-busy
 (not (fn-owner-admission-semantic-busy-p
       (f-put-global 'fn-owner-history-semantic-source nil state))))
