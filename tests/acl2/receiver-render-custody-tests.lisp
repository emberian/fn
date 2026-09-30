(in-package "ACL2")
(include-book "../../books/receiver-render-custody")
; Internal acquisition model teeth. Actual RH projection/installation and
; physical/alias terminal receipts are not supplied by these models.
(defconst *fn-ric-render-row*
 '(:receiver-custody :source (:index-query 2 1 1 1)
   (:receiver-copy 0 20 80) 7 20 :query-owned
   (:index-query 2 1 1 3) nil nil nil nil))
(defconst *fn-ric-render-owned*
 '(:receiver-custody :source (:index-query 2 1 1 1)
   (:receiver-copy 0 20 80) 7 20 :render-owned
   (:index-query 2 1 1 3)
   (:receiver-render-root t :plan :pin (:index-query 2 1 1 3) :resource :origin)
   nil nil nil))
(defthm fn-ric-render-acquire-positive-literal
 (and (fn-omk-widthp *fn-ric-render-row* 12)
      (fn-ibp-query-tokenp '(:index-query 2 1 1 3))
      (equal (fn-ric-custody-render-acquire *fn-ric-render-row*
               t :plan :pin '(:index-query 2 1 1 3) :resource :origin)
             (mv :render-acquired *fn-ric-render-owned*)))
 :rule-classes nil)
(defthm fn-ric-render-repeat-preserves-original-roots-literal
 (and (fn-omk-widthp *fn-ric-render-owned* 12)
      (fn-ibp-query-tokenp '(:index-query 2 1 1 3))
      (equal (fn-ric-custody-render-acquire *fn-ric-render-owned*
               t :other-plan :other-pin '(:index-query 2 1 1 3) :other-resource :other-origin)
             (mv :already-render-owned *fn-ric-render-owned*)))
 :rule-classes nil)
(defthm fn-ric-render-terminal-phase-cannot-rearm-literal
 (let ((row (update-nth 6 :render-returned *fn-ric-render-owned*)))
  (and (fn-omk-widthp row 12)
       (fn-ibp-query-tokenp '(:index-query 2 1 1 3))
       (equal (fn-ric-custody-render-acquire row
                t :plan :pin '(:index-query 2 1 1 3) :resource :origin)
              (mv :unavailable-custody row))))
 :rule-classes nil)
