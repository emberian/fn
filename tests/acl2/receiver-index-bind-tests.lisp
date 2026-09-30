(in-package "ACL2")
(include-book "../../books/receiver-index-custody")
; Internal helper model teeth, not a fabricated committed producer receipt.
(defconst *fn-ric-bind-row*
 '(:receiver-custody :source (:index-query 2 1 1 1)
   (:receiver-copy 0 20 80) 7 20 :retained
   (:index-query 2 1 1 1) nil nil nil nil))
(defthm fn-ric-bind-generation-change-positive-literal
 (and (fn-omk-widthp *fn-ric-bind-row* 12)
      (fn-ibp-query-tokenp '(:index-query 2 1 1 1))
      (fn-ibp-query-tokenp '(:index-query 2 1 1 3))
      (equal (fn-ric-custody-bind-query *fn-ric-bind-row*
               '(:index-query 2 1 1 1) '(:index-query 2 1 1 3))
       (mv :query-bound
        '(:receiver-custody :source (:index-query 2 1 1 1)
          (:receiver-copy 0 20 80) 7 20 :query-owned
          (:index-query 2 1 1 3) nil nil nil nil))))
 :rule-classes nil)
(defthm fn-ric-bind-foreign-nonce-refusal-literal
 (and (fn-omk-widthp *fn-ric-bind-row* 12)
      (fn-ibp-query-tokenp '(:index-query 2 1 1 1))
      (fn-ibp-query-tokenp '(:index-query 4 1 1 3))
      (not (equal 2 4))
      (equal (fn-ric-custody-bind-query *fn-ric-bind-row*
               '(:index-query 2 1 1 1) '(:index-query 4 1 1 3))
             (mv :unavailable-custody *fn-ric-bind-row*)))
 :rule-classes nil)
(defthm fn-ric-bind-repeat-preserves-row-literal
 (let ((row '(:receiver-custody :source (:index-query 2 1 1 1)
              (:receiver-copy 0 20 80) 7 20 :query-owned
              (:index-query 2 1 1 3) nil nil nil nil)))
  (and (fn-omk-widthp row 12)
       (fn-ibp-query-tokenp '(:index-query 2 1 1 1))
       (fn-ibp-query-tokenp '(:index-query 2 1 1 3))
       (equal (fn-ric-custody-bind-query row
                '(:index-query 2 1 1 1) '(:index-query 2 1 1 3))
              (mv :already-bound row))))
 :rule-classes nil)
