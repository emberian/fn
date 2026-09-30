; Corrupted checkpoint-state regression: the public finish accepts arbitrary
; decoded values and must fault without entering a guarded fold on a bad node.
(in-package "ACL2")
(include-book "../../books/store-checkpoint-open")

(assert-event
 (let ((r (fn-sco-paused 'broken-node 'bad-config-sequence 'bad-event-sequence)))
   (and (fn-sco-pausedp r)
        (not (fn-cnode-statep (fn-sco-at 1 r)))
        (not (integerp (fn-sco-at 2 r)))
        (not (integerp (fn-sco-at 3 r)))
        (equal (fn-sco-cpr-finish r '(unconsumed-config))
               (fn-replay-fault 'broken-node 0 :invalid-node)))))

(assert-event
 (and (equal (fn-sco-cpr-finish '(:paused broken-node 3 -1) '(a b c d))
             (fn-replay-fault 'broken-node 3 :invalid-node))
      (equal (fn-sco-cpr-finish '(:paused . broken-tail) '(a))
             (fn-replay-fault nil 0 :invalid-node))
      (equal (fn-sco-cpr-finish '(:fault preserved) '(a))
             '(:fault preserved))))
