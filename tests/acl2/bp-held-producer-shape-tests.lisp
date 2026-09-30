; Literal actual producer positives and complete hypothesis removals.
(in-package "ACL2")
(include-book "../../books/bp-held-producer-shape")
(include-book "bp-handoff-producer-shape-tests")
(defconst *bphgp-id* (fn-bpp-primary-identity (fn-bpb-bundle-primary *fn-bphsp-bundle*)))
(defconst *bphgp-dispatched* (fn-bpnp-dispatched-held *fn-bphsp-held* *fn-bphsp-local*))
(defconst *bphgp-attempt* (fn-bpnp-forward-attempt-record 1 1 0 *bphgp-id* *fn-bphsp-local* (cons 1 1) nil))
(defconst *bphgp-attempted* (fn-bpnp-attempted-held *bphgp-dispatched* *bphgp-attempt*))
(defconst *bphgp-result* (fn-bpnp-forward-result-record 1 2 0 *bphgp-id* 1 1 (cons 1 1) :uncertain))
(defconst *bphgp-delete* (fn-bpn-report-delete-record 1 3 0 *bphgp-id* :lifetime-expired))
; Corrupted slot is outside the producer domain; it survives each update.
(defconst *bphgp-corrupt* (update-nth 5 :unknown-source *fn-bphsp-held*))

; dispatch: complete positive.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (fn-bpp-eidp *fn-bphsp-local*) (fn-bphg-held-auxp (fn-bpnp-dispatched-held *fn-bphsp-held* *fn-bphsp-local*))))
; Remove record/peer hypothesis, affirm retained auxiliary premise.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (not (fn-bpp-eidp :unknown-peer)) (not (fn-bphg-held-auxp (fn-bpnp-dispatched-held *fn-bphsp-held* :unknown-peer)))))
; Corrupted-state removal of auxiliary premise; retain valid record/peer.
(assert-event (and (not (fn-bphg-held-auxp *bphgp-corrupt*)) (fn-bpp-eidp *fn-bphsp-local*) (not (fn-bphg-held-auxp (fn-bpnp-dispatched-held *bphgp-corrupt* *fn-bphsp-local*)))))

; delivery: complete positive.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (fn-bpah-delivery-recordp *fn-bphsp-record*) (fn-bphg-held-auxp (fn-bpah-delivered-held *fn-bphsp-held* *fn-bphsp-record*))))
; Remove record/peer hypothesis, affirm retained auxiliary premise.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (not (fn-bpah-delivery-recordp (update-nth 5 :unknown-disposition *fn-bphsp-record*))) (not (fn-bphg-held-auxp (fn-bpah-delivered-held *fn-bphsp-held* (update-nth 5 :unknown-disposition *fn-bphsp-record*))))))
; Corrupted-state removal of auxiliary premise; retain valid record/peer.
(assert-event (and (not (fn-bphg-held-auxp *bphgp-corrupt*)) (fn-bpah-delivery-recordp *fn-bphsp-record*) (not (fn-bphg-held-auxp (fn-bpah-delivered-held *bphgp-corrupt* *fn-bphsp-record*)))))

; attempt: complete positive.
(assert-event (and (fn-bphg-held-auxp *bphgp-dispatched*) (fn-bpnp-forward-attempt-recordp *bphgp-attempt*) (fn-bphg-held-auxp (fn-bpnp-attempted-held *bphgp-dispatched* *bphgp-attempt*))))
; Remove record/peer hypothesis, affirm retained auxiliary premise.
(assert-event (and (fn-bphg-held-auxp *bphgp-dispatched*) (not (fn-bpnp-forward-attempt-recordp (update-nth 5 :unknown-peer *bphgp-attempt*))) (not (fn-bphg-held-auxp (fn-bpnp-attempted-held *bphgp-dispatched* (update-nth 5 :unknown-peer *bphgp-attempt*))))))
; Corrupted-state removal of auxiliary premise; retain valid record/peer.
(assert-event (and (not (fn-bphg-held-auxp *bphgp-corrupt*)) (fn-bpnp-forward-attempt-recordp *bphgp-attempt*) (not (fn-bphg-held-auxp (fn-bpnp-attempted-held *bphgp-corrupt* *bphgp-attempt*)))))

; deletion: complete positive.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (fn-bpn-report-delete-recordp *bphgp-delete*) (fn-bphg-held-auxp (fn-bpn-report-tombstone-held *fn-bphsp-held* *bphgp-delete*))))
; Remove record/peer hypothesis, affirm retained auxiliary premise.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (not (fn-bpn-report-delete-recordp (update-nth 5 :unknown-reason *bphgp-delete*))) (not (fn-bphg-held-auxp (fn-bpn-report-tombstone-held *fn-bphsp-held* (update-nth 5 :unknown-reason *bphgp-delete*))))))
; Corrupted-state removal of auxiliary premise; retain valid record/peer.
(assert-event (and (not (fn-bphg-held-auxp *bphgp-corrupt*)) (fn-bpn-report-delete-recordp *bphgp-delete*) (not (fn-bphg-held-auxp (fn-bpn-report-tombstone-held *bphgp-corrupt* *bphgp-delete*)))))

; Deferral has exactly one premise.
(assert-event (and (fn-bphg-held-auxp *fn-bphsp-held*) (fn-bphg-held-auxp (fn-bpnp-deferred-held *fn-bphsp-held* 1))))
(assert-event (and (not (fn-bphg-held-auxp *bphgp-corrupt*)) (not (fn-bphg-held-auxp (fn-bpnp-deferred-held *bphgp-corrupt* 1)))))
; Actual uncertain result must match the retained forwarding attempt.
(assert-event (and (fn-bphg-held-auxp *bphgp-attempted*) (fn-bpnp-forward-result-matches-heldp *bphgp-result* *bphgp-attempted*) (fn-bphg-held-auxp (fn-bpnp-forward-result-held *bphgp-attempted* (fn-bpn-nth 8 *bphgp-result*)))))
(assert-event (let ((h (update-nth 5 :unknown-source *bphgp-attempted*))) (and (not (fn-bphg-held-auxp h)) (fn-bpnp-forward-result-matches-heldp *bphgp-result* h) (not (fn-bphg-held-auxp (fn-bpnp-forward-result-held h (fn-bpn-nth 8 *bphgp-result*)))))))
; Removing the actual match gate permits an uncertain result over a busy slot.
(assert-event (let ((h (fn-bpnp-deferred-held *bphgp-dispatched* 1))) (and (fn-bphg-held-auxp h) (fn-bpnp-forward-result-recordp *bphgp-result*) (not (fn-bpnp-forward-result-matches-heldp *bphgp-result* h)) (not (fn-bphg-held-auxp (fn-bpnp-forward-result-held h (fn-bpn-nth 8 *bphgp-result*)))))))
; Frame constructor: actual bundle/ingress inputs, complete anchor premise.
(assert-event (and (fn-bpb-bundlep *fn-bphsp-bundle*) (fn-bphg-anchorp '(:wall)) (fn-bphg-held-auxp (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* 0 *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*) '(:wall)))))
(assert-event (and (fn-bpb-bundlep *fn-bphsp-bundle*) (not (fn-bphg-anchorp :unknown-anchor)) (not (fn-bphg-held-auxp (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* 0 *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*) :unknown-anchor)))))
