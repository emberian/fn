(in-package "ACL2")
(include-book "../../books/receiver-custody-row")
(defconst *fn-rcr-provider* '(nil ((:rx-capacity 0 0 4096) 0 nil)))
(defconst *fn-rcr-turn*
 '((:receiver-turn 1)
   (:receiver-source (:receiver-turn 1) (:rx-capacity 0 0 4096) 0)
   :transferred (256 0 0 0 1)
   (:receiver-recipient (:index-query 2 1 1 1) (:receiver-copy 0 20 80) 7 20)
   (:receiver-install (:rx-capacity 0 0 4096) 0)))
(defconst *fn-rcr-pool*
 (list (list (fn-prl-build '(8192 0 0 0 8) '(256 0 0 0 2) 2 nil '(4608 0 0 0 0))
             nil nil nil nil) :served nil))
(defthm fn-rcr-retained-suffix-positive-literal
 (and (fn-rx-providerp *fn-rcr-provider*)
      (fn-receiver-turnp *fn-rcr-turn*) (fn-page-read-poolp *fn-rcr-pool*)
      (fn-rxt-owned-claim-p '(:receiver-turn 1) *fn-rcr-provider* *fn-rcr-turn* *fn-rcr-pool*)
      (eq (fn-rxt-phase *fn-rcr-turn*) :transferred)
      (null (fn-rxp-capacity *fn-rcr-provider*))
      (fn-rxt-recipient-jobp (fn-rxt-job *fn-rcr-turn*))
      (equal (fn-owner-rx-turn-custody-row '(:receiver-turn 1) *fn-rcr-provider* *fn-rcr-turn* *fn-rcr-pool*)
       (mv :retained-custody
        '(:receiver-custody
          (:receiver-source (:receiver-turn 1) (:rx-capacity 0 0 4096) 0)
          (:index-query 2 1 1 1) (:receiver-copy 0 20 80) 7 20 :retained
          (:index-query 2 1 1 1) nil nil nil nil))))
 :rule-classes nil)
(defthm fn-rcr-stale-ticket-refusal-literal
 (and (not (fn-rxt-owned-claim-p '(:receiver-turn 0) *fn-rcr-provider* *fn-rcr-turn* *fn-rcr-pool*))
      (equal (fn-owner-rx-turn-custody-row '(:receiver-turn 0) *fn-rcr-provider* *fn-rcr-turn* *fn-rcr-pool*)
             (mv :unavailable-custody nil)))
 :rule-classes nil)
(defthm fn-rcr-corrupted-overconsumption-literal
 (let ((turn (update-nth 4 '(:receiver-recipient (:index-query 2 1 1 1)
                            (:receiver-copy 0 20 80) 21 20) *fn-rcr-turn*)))
  (and (fn-receiver-turnp turn)
       (fn-rxt-owned-claim-p '(:receiver-turn 1) *fn-rcr-provider* turn *fn-rcr-pool*)
       (not (fn-rxt-recipient-jobp (fn-rxt-job turn)))
       (equal (fn-owner-rx-turn-custody-row '(:receiver-turn 1) *fn-rcr-provider* turn *fn-rcr-pool*)
              (mv :unavailable-custody nil))))
 :rule-classes nil)
