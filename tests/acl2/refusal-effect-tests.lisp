; Teeth for books/refusal-effect.lisp: the full-store POST refusal consumes
; exactly one transaction id and nothing else (a positive witness with the
; complete antecedent and each conclusion), and the id it consumes is the
; reservation's (a hypothesis-removal witness: with another txid the refusal
; is disabled and the files stay reserved).  The fixture is the resolution
; tests' (tests/acl2/store-node-resolution-tests.lisp): a fresh store of two
; groups, capacity 10, reserved through the host's route.
(in-package "ACL2")

(include-book "../../books/refusal-effect")
(include-book "../../books/codec-attach")

(defconst *rfx-groups* '("fn.letters" "fn.test"))
(defconst *rfx-s* (fn-sn-initial *rfx-groups* 10))
(defconst *rfx-after* (fn-sn-refuse-reservation (fn-olr-sn-reserve *rfx-s*) 0))

; POSITIVE WITNESS (fn-rfx-refused-post-keeps-records,
; -keeps-configuration, -consumes-one-txid): the complete antecedent ...
(assert-event (and (fn-sn-statep *rfx-s*)
                   (equal (fn-sf-phase (fn-sn-files *rfx-s*)) :ready)
                   (< (fn-sf-frontier (fn-sn-files *rfx-s*)) *fn-sf-max-uint*)
                   (equal 0 (fn-sf-frontier (fn-sn-files *rfx-s*)))
                   (fn-replay-advance-okp (fn-sn-node *rfx-s*) 1)))
; ... and each conclusion.
(assert-event (equal (fn-sf-records (fn-sn-files *rfx-after*))
                     (fn-sf-records (fn-sn-files *rfx-s*))))
(assert-event (and (equal (fn-sn-groups *rfx-after*) (fn-sn-groups *rfx-s*))
                   (equal (fn-sn-capacity *rfx-after*) (fn-sn-capacity *rfx-s*))))
(assert-event (and (equal (fn-sf-phase (fn-sn-files *rfx-after*)) :ready)
                   (equal (fn-sf-frontier (fn-sn-files *rfx-after*)) 1)
                   (equal (fn-state-next-txid
                           (fn-node-acceptance (fn-sn-node *rfx-after*)))
                          1)))
; The consumed id left no record and no success.
(assert-event (null (fn-sf-records (fn-sn-files *rfx-after*))))
(assert-event (not (fn-sf-successes (fn-sn-files *rfx-after*))))

; HYPOTHESIS-REMOVAL WITNESS (fn-rfx-refused-post-consumes-one-txid without
; `(equal txid (fn-sf-frontier (fn-sn-files s)))'): every retained hypothesis
; holds of the fixture ...
(defconst *rfx-wrong* (fn-sn-refuse-reservation (fn-olr-sn-reserve *rfx-s*) 5))
(assert-event (and (fn-sn-statep *rfx-s*)
                   (equal (fn-sf-phase (fn-sn-files *rfx-s*)) :ready)
                   (< (fn-sf-frontier (fn-sn-files *rfx-s*)) *fn-sf-max-uint*)
                   (fn-replay-advance-okp (fn-sn-node *rfx-s*) 1)))
; ... the omitted one fails ...
(assert-event (not (equal 5 (fn-sf-frontier (fn-sn-files *rfx-s*)))))
; ... and so does the conclusion: the refusal is disabled, the files stay
; :reserved at frontier 1 and the node has consumed nothing.
(assert-event (not (equal (fn-sf-phase (fn-sn-files *rfx-wrong*)) :ready)))
(assert-event (equal (fn-sf-phase (fn-sn-files *rfx-wrong*)) :reserved))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-sn-node *rfx-wrong*)))
                     0))

; The by-definition refusals: a request the served test refuses leaves the
; configured owner it was given (fn-rfx-unserved-prepare-is-unchanged-by-
; definition), witnessed on the served prepare's own fixture in
; tests/acl2/owner-prepare-served-tests.lisp; the reconfigure's refused
; branch on owner-config's (fn-ocfg-reconfigure of a request
; fn-ocfg-reconfig-okp refuses answers the same owner).
