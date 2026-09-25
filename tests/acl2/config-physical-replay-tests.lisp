; The physical directories have independent sequences. Config txid marks the
; next Store event, so a config at that id precedes the event. The histories
; here include a burned transaction-id gap and a released high reservation.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/config-physical-replay")

(defconst *cpr-t-stamp* *fn-cfg-default-stamp*)
(defconst *cpr-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-cpr" "subject" "evidence" 10))
(defconst *cpr-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-cpr" "subject" "evidence" 0))
(defconst *cpr-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *cpr-t-stamp*))
(defconst *cpr-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *cpr-t-stamp*))
(defconst *cpr-t-article*
  (fn-record-make 2 7 7 "<cpr@example.invalid>" '(65) '("fn.test")
                  "archive-cpr" "subject" "evidence" 2 841000000))
(defconst *cpr-t-configs*
  (list *fn-cfg-default-record* *cpr-t-decrease* *cpr-t-increase*))
(defconst *cpr-t-events*
  (list *cpr-t-undertake* *cpr-t-release* *cpr-t-article*))
(defconst *cpr-t-open* (fn-cpr-replay *cpr-t-configs* *cpr-t-events*))

; The high charge was valid at its historical capacity, then was released.
; The decrease to the current reservation (one history unit) is valid, the
; increase at the same txid is valid, and the immediately following article
; is admitted at the increased capacity after a burned gap from txid 2 to 7.
(assert-event (equal (fn-replay-result-kind *cpr-t-open*) :ok))
(assert-event (fn-cnode-statep (fn-replay-result-node *cpr-t-open*)))
(assert-event
 (equal (fn-cfg-generation
         (fn-cnode-config (fn-replay-result-node *cpr-t-open*)))
        (len *cpr-t-configs*)))
(assert-event
 (equal (fn-cfg-capacity
         (fn-cfg-value (fn-cnode-config (fn-replay-result-node *cpr-t-open*))))
        20))
(assert-event
 (consp (fn-find-article
         "<cpr@example.invalid>"
         (fn-state-articles
          (fn-node-acceptance
           (fn-cnode-node (fn-replay-result-node *cpr-t-open*)))))))

; Replaying every Store record at the FINAL capacity 1 refuses the earlier
; undertaking of 10. The physically ordered replay over the same two files
; accepts the decrease because the release precedes it. This separates
; historical admission from current-budget replay.
(defconst *cpr-t-lower-open*
  (fn-cpr-replay (list *fn-cfg-default-record* *cpr-t-decrease*)
                 (list *cpr-t-undertake* *cpr-t-release*)))
(assert-event (equal (fn-replay-result-kind *cpr-t-lower-open*) :ok))
(assert-event
 (equal (fn-replay-result-kind
         (fn-replay '("fn.letters" "fn.test") 1
                    (list *cpr-t-undertake* *cpr-t-release*)))
        :fault))

; A post immediately after the valid decrease observes the reduced, still
; sufficient budget. The same history cannot replay at that final budget if
; the historical undertaking is judged against it instead of the old budget.
(defconst *cpr-t-decrease-to-five*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 5)) *cpr-t-stamp*))
(defconst *cpr-t-post-after-decrease*
  (fn-cpr-replay
   (list *fn-cfg-default-record* *cpr-t-decrease-to-five*)
   (list *cpr-t-undertake* *cpr-t-release* *cpr-t-article*)))
(assert-event
 (equal (fn-replay-result-kind *cpr-t-post-after-decrease*) :ok))
(assert-event
 (equal (fn-cfg-capacity
         (fn-cfg-value
          (fn-cnode-config
           (fn-replay-result-node *cpr-t-post-after-decrease*))))
        5))
(assert-event
 (consp (fn-find-article
         "<cpr@example.invalid>"
         (fn-state-articles
          (fn-node-acceptance
           (fn-cnode-node
            (fn-replay-result-node *cpr-t-post-after-decrease*)))))))

; A forged decrease *before* the release sees the high reservation and is
; refused even though config-only replay sees an empty node and accepts it.
(defconst *cpr-t-premature-decrease*
  (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 1)) *cpr-t-stamp*))
(defconst *cpr-t-premature-open*
  (fn-cpr-replay (list *fn-cfg-default-record* *cpr-t-premature-decrease*)
                 (list *cpr-t-undertake* *cpr-t-release*)))
(assert-event (equal (fn-replay-result-kind *cpr-t-premature-open*) :fault))
(assert-event (equal (fn-replay-result-reason *cpr-t-premature-open*)
                     :config-refusal))
; Removing the successful-result hypothesis exposes a fault before the
; second configuration has been applied, so the generation need not count
; every record in the input file.
(assert-event
 (not (equal (fn-cfg-generation
              (fn-cnode-config (fn-replay-result-node *cpr-t-premature-open*)))
             2)))
(assert-event
 (equal (fn-replay-result-kind
         (fn-cnode-config-replay
          (list *fn-cfg-default-record* *cpr-t-premature-decrease*)))
        :ok))

; Each file's own dense sequence and the txid tie are checked, rather than
; manufacturing a new on-disk global sequence number.
(assert-event
 (equal (fn-replay-result-reason
         (fn-cpr-replay (list *fn-cfg-default-record*
                              (fn-cfg-record-make 2 7 2
                                                  (list (fn-cfg-set-capacity 1))
                                                  *cpr-t-stamp*))
                        (list *cpr-t-undertake* *cpr-t-release*)))
        :config-sequence))
(assert-event
 (equal (fn-replay-result-reason
         (fn-cpr-replay (list *fn-cfg-default-record* *cpr-t-decrease*)
                        (list *cpr-t-undertake* *cpr-t-undertake*)))
        :event-sequence))

; Successful recovery is deterministic on the same exact records.
(assert-event (equal (fn-cpr-replay *cpr-t-configs* *cpr-t-events*)
                     *cpr-t-open*))

; -----------------------------------------------------------------------------
; The carried invariant (fn-cpr-apply-event-preserves-cnode-statep,
; fn-cpr-loop-preserves-cnode-statep): a reachable, non-degenerate witness and
; one must-fail per hypothesis.

(defconst *cpr-t-configured*
  (fn-replay-result-node (fn-cpr-replay (list *fn-cfg-default-record*) nil)))
(defconst *cpr-t-step*
  (fn-cpr-apply-event *cpr-t-configured* *cpr-t-undertake*))
; Witness: the undertaking replays from the configured default node, and the
; result is a configured node carrying the pin.
(assert-event (fn-cnode-statep *cpr-t-configured*))
(assert-event (consp *cpr-t-step*))
(assert-event (fn-cnode-statep *cpr-t-step*))
(assert-event (not (equal *cpr-t-step* *cpr-t-configured*)))
; The one hypothesis: a refused event (here, an article in a group the
; configuration does not serve) leaves NIL, which is not a configured node.
(defconst *cpr-t-unserved*
  (fn-record-make 1 1 1 "<cpr-unserved@example.invalid>" '(65) '("no.such.group")
                  "archive-cpr-2" "subject" "evidence" 2 841000000))
(assert-event (null (fn-cpr-apply-event *cpr-t-step* *cpr-t-unserved*)))
(must-fail
 (defthm cpr-t-apply-event-statep-without-non-refusal
   (fn-cnode-statep (fn-cpr-apply-event *cpr-t-step* *cpr-t-unserved*))))
; The loop: from a configured node every result's node is configured, the
; faults included (a sequence fault keeps the last good node).
(assert-event (equal (fn-replay-result-kind
                      (fn-cpr-loop *cpr-t-step* nil (list *cpr-t-undertake*) 1 0))
                     :fault))
(assert-event (fn-cnode-statep
               (fn-replay-result-node
                (fn-cpr-loop *cpr-t-step* nil (list *cpr-t-undertake*) 1 0))))
; Its hypothesis: from a node that is not configured the fault carries that
; node, and the conclusion fails.
(must-fail
 (defthm cpr-t-loop-statep-without-configured-start
   (fn-cnode-statep
    (fn-replay-result-node (fn-cpr-loop nil nil nil 0 0)))))
