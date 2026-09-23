; Observed-image opening vectors.  Records have already passed exact codec
; decoding before this ACL2 entry point receives them.  The process-root
; relation witnesses (D6), the reopen retention witnesses (D5) and their
; teeth are in store-observed-traces-tests.
(in-package "ACL2")
(include-book "../../books/store-observed")
(include-book "../../books/codec-attach")

(defconst *fn-so-groups* '("fn.letters"))
(defconst *fn-so-empty*
  (fn-sn-open-observed *fn-so-groups* 10 0 nil))
(assert-event (fn-sn-open-okp *fn-so-empty*))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state *fn-so-empty*)))
                     :recovering))
(assert-event (equal (fn-sf-successes (fn-sn-files (fn-sn-open-state *fn-so-empty*)))
                     nil))

(defconst *fn-so-record0*
  (fn-record-make 0 0 0 "<observed@example>" '(65) *fn-so-groups*
                  "observed-pin" "observed-content" "observed-release" 1 841000000))
(defconst *fn-so-replayed*
  (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-record0*)))
(assert-event (fn-sn-open-okp *fn-so-replayed*))
(assert-event (equal (fn-sn-node (fn-sn-open-state *fn-so-replayed*))
                     (fn-sf-replay-node *fn-so-groups* 10
                                        (list *fn-so-record0*) 1)))

; A known-aborted allocation gap is replayable: record txid 1 and frontier 2.
(defconst *fn-so-gap-record*
  (fn-record-make 0 1 1 "<gap@example>" '(66) *fn-so-groups*
                  "gap-pin" "gap-content" "gap-release" 1 841000000))
(assert-event
 (fn-sn-open-okp (fn-sn-open-observed *fn-so-groups* 10 2
                                      (list *fn-so-gap-record*))))

; Every refusal code is reachable: configuration, frontier, history, replay.
(assert-event (equal (fn-sn-open-observed 7 10 0 nil) '(:error :configuration)))
(assert-event (equal (fn-sn-open-observed *fn-so-groups* 10 -1 nil) '(:error :frontier)))
(assert-event
 (equal (fn-sn-open-observed *fn-so-groups* 10 1
                             (list *fn-so-record0* 'not-a-record))
        '(:error :history)))
(assert-event
 (equal (fn-sn-open-observed *fn-so-groups* 10 0 (list *fn-so-record0*))
        '(:error :history)))
; Structurally valid but unreplayable: a record in a group this store does
; not configure is refused with the distinct :replay code.  The teeth built on
; this witness live in store-observed-traces-tests.
(defconst *fn-so-alien*
  (fn-record-make 0 0 0 "<alien@example>" '(65) '("fn.other")
                  "alien-pin" "alien-content" "alien-release" 1 841000000))
(assert-event (fn-sn-observed-historyp 1 (list *fn-so-alien*)))
(assert-event (not (fn-sf-history-recoverablep *fn-so-groups* 10 (list *fn-so-alien*) 1)))
(assert-event (equal (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-alien*))
                     '(:error :replay)))

(defconst *fn-so-four*
  (fn-sn-observed-rebarrier (fn-sn-open-state *fn-so-replayed*) 4))
(defconst *fn-so-five*
  (fn-sn-observed-rebarrier (fn-sn-open-state *fn-so-replayed*) 5))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-four*)) :recovering))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-five*)) :ready))
