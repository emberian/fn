(in-package "ACL2")
(include-book "../../books/checkpoint-account-gate")
(defconst *cpag-pending* '(:adoption 1 2 3 4 5 6 7 8))
(defconst *cpag-new* (list :consumer-state nil nil 0 0 nil
                         (list :authority 0 1 nil nil *cpag-pending*)))
(defconst *cpag-old* (list :consumer-state nil nil 0 0 nil
                         (list :authority 4 5 'old-policy 'old-root *cpag-pending*)))
(assert-event (equal (fn-cpa-checkpoint-word (list :ok *cpag-new* nil nil)) :defer))
(assert-event (equal (fn-cpa-checkpoint-word (list :ok *cpag-old* 'old-root 7)) :defer))
(assert-event (equal (fn-cpa-checkpoint-word
 (list :ok (update-nth 6 '(:authority 4 5 old-policy old-root nil) *cpag-old*) 'old-root 7)) :checkpoint))
(assert-event (equal (fn-cpa-checkpoint-word '(:unavailable :source)) :unavailable))
(assert-event (equal (fn-cpa-checkpoint-word '(:ok (:consumer-state) root 7)) :unavailable))
