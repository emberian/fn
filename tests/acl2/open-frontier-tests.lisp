; Teeth for books/open-frontier.lisp (row B10, lane limits-live-2).
; The operability review's walk F3 in miniature: two retention events
; consume txids 0 and 1, then txids 2..6 are consumed with no record (the
; refused POSTs of a full budget), and a configuration record is accepted
; naming txid 7, above every event.

(in-package "ACL2")
(include-book "../../books/open-frontier")
(include-book "held-rows-tests")

(defconst *ofr-t-stamp* *fn-cfg-default-stamp*)
(defconst *ofr-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-ofr" "subject" "evidence" 10))
(defconst *ofr-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-ofr" "subject" "evidence" 0))
(defconst *ofr-t-late-config*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 20)) *ofr-t-stamp*))
(defconst *ofr-t-configs* (list *fn-cfg-default-record* *ofr-t-late-config*))
(defconst *ofr-t-events* (fn-hrt-rows (list *ofr-t-undertake* *ofr-t-release*) nil 0))
(defconst *ofr-t-replay* (fn-cpr-replay *ofr-t-configs* *ofr-t-events*))
(defconst *ofr-t-node* (fn-cnode-node (fn-replay-result-node *ofr-t-replay*)))

; REACHABLE (fn-ofr-replay-ok-frontier-admits, floor 0): the antecedent --
; the replay accepts the history, the floor is a natural -- and the
; conclusion: the node is idle at or below the frontier, which is the
; configuration record's 7, not the events' 2.
(assert-event (equal (fn-replay-result-kind *ofr-t-replay*) :ok))
(assert-event (natp 0))
(assert-event (equal (fn-ofr-events-next *ofr-t-events* 0) 2))
(assert-event (equal (fn-ofr-configs-next *ofr-t-configs* 0) 7))
(assert-event (equal (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* 0) 7))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance *ofr-t-node*)) 7))
(assert-event (fn-replay-advance-okp *ofr-t-node*
                                     (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* 0)))

; The bug (B10): the frontier from the events alone refuses this history.
(assert-event (not (fn-replay-advance-okp *ofr-t-node* (fn-ofr-events-next *ofr-t-events* 0))))

; A checkpoint floor above both folds is kept (fn-ofr-loop-ok-within-frontier,
; ACC the floor): the frontier is the floor.
(assert-event (equal (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* 12) 12))
(assert-event (fn-replay-advance-okp *ofr-t-node* 12))

; HYPOTHESIS REMOVAL (natp floor): a floor that is no natural is read as 0
; by both folds, so the frontier is the one at floor 0 and still admits the
; node; the conclusion does not depend on the hypothesis at this history.
(assert-event (equal (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* :none)
                     (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* 0)))
; CONCLUSION FAILURE: below the configuration record's txid the replayed
; node is not admitted (the frontier the open computed before B10's fix).
(assert-event (not (fn-replay-advance-okp *ofr-t-node* 6)))
; The :ok hypothesis: a history whose configuration sequence does not start
; at 0 is refused (:config-sequence), not accepted.
(defconst *ofr-t-improper*
  (fn-cpr-replay (list *ofr-t-late-config*) *ofr-t-events*))
(assert-event (not (equal (fn-replay-result-kind *ofr-t-improper*) :ok)))
