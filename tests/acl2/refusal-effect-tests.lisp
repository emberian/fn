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

; -----------------------------------------------------------------------------
; THE BY-DEFINITION REFUSALS, each on its subject's own fixture (lane
; closure-theorems-3, 2026-09-29).  A positive witness asserts the theorem's
; antecedent and its conclusion; a hypothesis-removal witness (each theorem
; has one hypothesis, so nothing is retained) asserts that the hypothesis
; fails and that the conclusion fails with it: the request is NOT the
; identity, it stages.

(include-book "owner-prepare-served-tests")
(include-book "owner-config-tests")

; fn-rfx-unserved-prepare-is-unchanged-by-definition.  The served prepare's
; retired-group fixture (*lgt-r-reserved*: fn.letters retired by a live
; completion, the article filed in it).  POSITIVE WITNESS: the antecedent ...
(assert-event (not (fn-psrv-event-servedp (fn-ocfg-config *lgt-r-reserved*)
                                          *acar-t-record*)))
; ... and the conclusion, at the host's budget and carry.
(assert-event (equal (fn-psrv-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                      (pst-carry *lgt-r-reserved*))
                     *lgt-r-reserved*))
; HYPOTHESIS-REMOVAL WITNESS: at :reserved the group is served (the
; hypothesis fails) ...
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *lgt-reserved*) *acar-t-record*))
; ... and the prepare is not the identity: the article is staged.
(assert-event (not (equal (fn-psrv-prepare *lgt-reserved* *acar-t-record* 1000000
                                           (pst-carry *lgt-reserved*))
                          *lgt-reserved*)))
(assert-event (equal (lgt-phase (fn-psrv-prepare *lgt-reserved* *acar-t-record* 1000000
                                                 (pst-carry *lgt-reserved*)))
                     :record-staged))

; fn-rfx-unaffordable-prepare-is-unchanged-by-definition.  The same served
; owner under a budget of no transactions.  POSITIVE WITNESS: the antecedent
; (a budget of 0 admits nothing) ...
(assert-event (not (fn-sbud-admitp 0 (fn-sbud-count (fn-sbud-oc-store *lgt-reserved*)))))
; ... the conclusion ...
(assert-event (equal (fn-prc-sbud-prepare *lgt-reserved* *acar-t-record* 0
                                          (pst-carry *lgt-reserved*))
                     *lgt-reserved*))
; ... and the word the host reports for it through the served prepare.
(assert-event (equal (fn-psrv-prepare *lgt-reserved* *acar-t-record* 0
                                      (pst-carry *lgt-reserved*))
                     *lgt-reserved*))
(assert-event (equal (fn-psrv-refusal-kind *lgt-reserved* *acar-t-record* 0)
                     :unaffordable))
; HYPOTHESIS-REMOVAL WITNESS: the host's budget admits (the hypothesis
; fails) ...
(assert-event (fn-sbud-admitp 1000000 (fn-sbud-count (fn-sbud-oc-store *lgt-reserved*))))
; ... and the prepare stages: not the identity.
(assert-event (not (equal (fn-prc-sbud-prepare *lgt-reserved* *acar-t-record* 1000000
                                               (pst-carry *lgt-reserved*))
                          *lgt-reserved*)))

; fn-rfx-refused-reconfigure-is-unchanged-by-definition.  owner-config-tests'
; recovered owner with one reader open (*ocfg-l-reader*: connection 0 at
; generation 1, a clock observed, nothing staged).  POSITIVE WITNESS: a
; request from a connection the owner does not hold is not admitted, by
; name ...
(assert-event (not (fn-ocfg-reconfig-okp *ocfg-l-reader* 7 *ocfg-l-deltas1*)))
(assert-event (equal (fn-ocfg-reconfig-refusal *ocfg-l-reader* 7 *ocfg-l-deltas1*)
                     :no-such-connection))
; ... and the reconfigure answers the same owner.
(assert-event (equal (fn-ocfg-reconfigure *ocfg-l-reader* 7 *ocfg-l-deltas1*)
                     *ocfg-l-reader*))
; HYPOTHESIS-REMOVAL WITNESS: the same deltas from the open connection are
; admitted (the hypothesis fails) ...
(assert-event (fn-ocfg-reconfig-okp *ocfg-l-reader* 0 *ocfg-l-deltas1*))
; ... and the reconfigure stages the configuration record: not the identity.
(defconst *rfx-staged* (fn-ocfg-reconfigure *ocfg-l-reader* 0 *ocfg-l-deltas1*))
(assert-event (not (equal *rfx-staged* *ocfg-l-reader*)))
(assert-event (and (null (fn-ocfg-staged *ocfg-l-reader*))
                   (fn-cfg-recordp (fn-ocfg-staged *rfx-staged*))))

; fn-rfx-config-record-txid-is-the-node-next-by-definition (no hypothesis).
; POSITIVE WITNESS on the recovered owner: the staged record's txid is the
; node's next txid ...
(assert-event (equal (fn-cfg-record-txid (fn-ocfg-staged *rfx-staged*))
                     (fn-state-next-txid
                      (fn-node-acceptance
                       (fn-sn-node (fn-own-store (fn-ocfg-owner *ocfg-l-reader*)))))))
; ... and on an owner over the store the full-store refusal burned an id in
; (*rfx-after* above, frontier 1, no record): the record's id is 1, above
; the burned 0 -- the id the open's frontier must account for.
(defconst *rfx-burned-oc*
  (fn-ocfg-make (fn-own-start *rfx-after* 3) *ocfg-t-g1* nil nil))
(assert-event (fn-cfgp (fn-ocfg-config *rfx-burned-oc*)))
(assert-event (equal (fn-cfg-record-txid
                      (fn-ocfg-reconfig-record *rfx-burned-oc* *ocfg-l-deltas1*))
                     (fn-state-next-txid
                      (fn-node-acceptance
                       (fn-sn-node (fn-own-store (fn-ocfg-owner *rfx-burned-oc*)))))))
(assert-event (equal (fn-cfg-record-txid
                      (fn-ocfg-reconfig-record *rfx-burned-oc* *ocfg-l-deltas1*))
                     1))
(assert-event (null (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *rfx-burned-oc*))))))
