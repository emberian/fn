; Public algebra teeth. Nonempty semantic producer/refinement is distinct.
(in-package "ACL2")
(include-book "replay-enrollment-public-refinement")
; Reachable genuine initial context has no enrollment snapshots/evidence.
(assert-event
 (and (fn-rse-public-ledger-correspondsp nil nil)
      (equal (fn-rse-enrolled-model nil '((:ed25519) (:ml-dsa-65)) nil)
             (fn-hsig-enrolled-keys-of-principalp nil '((:ed25519) (:ml-dsa-65)) nil))))
; Hypothesis-removal/corrupted metadata witness: all remaining hypotheses
; (none) hold, the missing SAME public semantic/order relation is false,
; and the conclusion affirmatively fails. This is not restored evidence.
(assert-event
 (let* ((principal '(11 12 13))
        (keys '((:ed25519 21 22) (:ml-dsa-65 31 32 33)))
        (entry '(unissued-snapshot :enrolled
                 ((:bytes 7 3 (11 12 13 99)) (:bytes 20 2 (21 22 88))
                  (:bytes 30 3 (31 32 33 77))) unissued-source))
        (evidence (list entry)))
  (and (not (fn-rse-public-ledger-correspondsp nil evidence))
       (fn-rse-enrolled-model principal keys evidence)
       (not (fn-hsig-enrolled-keys-of-principalp principal keys nil))
       (not (equal (fn-rse-enrolled-model principal keys evidence)
                   (fn-hsig-enrolled-keys-of-principalp principal keys nil))))))
