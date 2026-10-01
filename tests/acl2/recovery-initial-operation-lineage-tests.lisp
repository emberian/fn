(in-package "ACL2")
(include-book "../../books/recovery-initial-operation-lineage")
(include-book "../../books/recovery-source-authority")
; Synthetic custody lineage, not runtime INITIAL issuance or canonical carry.
(assert-event
 (let* ((old (list :recovering 4 1 :borrowed-origin 0 0 '(:ok 0 nil nil nil :source) 0 3))
        (token (fn-rsa-token old)))
  (mv-let (observed next)
    (fn-rsa-observe old token 1 3 '(:ok 1 nil nil nil :source) 1)
    (and (eq observed :counted)
         (not (fn-rsa-currentp next token 1 3))
         (fn-rsa-initial-operation-lineagep next token 1 3 1 1 nil)
         (mv-let (word source sealed)
           (fn-rsa-seal next (fn-rsa-token next) 1 3 1 1)
           (let ((canonical (list :ready 1 1 nil nil nil nil 0 0 source)))
            (and (eq word :sealed)
                 (not (fn-rsa-currentp sealed token 1 3))
                 (fn-rsa-initial-operation-lineagep sealed token 1 3 1 1 canonical)
                 (not (fn-rsa-initial-operation-lineagep sealed token 2 3 1 1 canonical))
                 (not (fn-rsa-initial-operation-lineagep sealed token 1 4 1 1 canonical))
                 (not (fn-rsa-initial-operation-lineagep sealed token 1 3 2 1 canonical))
                 (not (fn-rsa-initial-operation-lineagep sealed token 1 3 1 2 canonical))
                 (not (fn-rsa-initial-operation-lineagep sealed token 1 3 1 1 nil))
                 (not (fn-rsa-initial-operation-lineagep
                       sealed '(:recovery-source 5 1 0) 1 3 1 1 canonical))
                 (not (fn-rsa-initial-operation-lineagep
                       sealed '(:recovery-source 4 1 2) 1 3 1 1 canonical))
                 (not (fn-rsa-initial-operation-lineagep
                       sealed token 1 3 1 1
                       '(:ready 1 1 nil nil nil nil 0 0 (1 (4 2) 0 0))))
                 (not (fn-rsa-initial-operation-lineagep next token 1 3 1 1 canonical)))))))))
; Hypothesis removal: wrong already-issued token lineage, exact frontier kept.
(assert-event
 (let* ((issuer '(:recovering 4 1 :origin 1 1 (:ok 1 nil nil nil :source) 1 3))
        (token '(:recovery-source 5 1 0)))
  (and (equal 1 (fn-omk-at 5 issuer))
       (not (fn-rsa-initial-operation-lineagep issuer token 1 3 1 1 nil))
       (mv-let (word source sealed)
         (fn-rsa-seal issuer (fn-rsa-token issuer) 1 3 1 1)
         (not (and (eq word :sealed)
                   (fn-rsa-initial-operation-lineagep
                    sealed token 1 3 1 1
                    (list :ready 1 1 nil nil nil nil 0 0 source))))))))
; Hypothesis removal: actual frontier exceeds the issuer's retained frontier.
(assert-event
 (let* ((issuer '(:recovering 4 1 :origin 1 1 (:ok 1 nil nil nil :source) 1 3))
        (token '(:recovery-source 4 1 0)))
  (and (fn-rsa-initial-operation-lineagep issuer token 1 3 1 2 nil)
       (not (equal 2 (fn-omk-at 5 issuer)))
       (mv-let (word source sealed)
         (fn-rsa-seal issuer (fn-rsa-token issuer) 1 3 1 2)
         (not (and (eq word :sealed)
                   (fn-rsa-initial-operation-lineagep
                    sealed token 1 3 1 2
                    (list :ready 1 1 nil nil nil nil 0 0 source))))))))
