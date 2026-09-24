(in-package "ACL2")
(include-book "../../books/topic-history-store-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sti-initial-store* (fn-sn-initial nil 4))
(assert-event (fn-sti-livep *sti-initial-store*))
(assert-event
 (fn-sf-recovery-crash-imagep (fn-sn-files *sti-initial-store*) 0 nil))
(assert-event (fn-sn-observed-topic-okp nil))

; Corrupting the carried topic cursor is observable to the relation even
; though the empty record directory still satisfies the consumer relation.
(defconst *sti-wrong-cursor*
  (fn-sn-with-topic *sti-initial-store*
                    (fn-th-prefix-state :ok 1 nil nil nil nil nil)))
(assert-event (fn-csi-livep *sti-wrong-cursor*))
(must-fail (assert-event (fn-sti-livep *sti-wrong-cursor*)))
