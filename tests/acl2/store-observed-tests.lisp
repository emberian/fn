; Observed-image opening vectors.  Records have already passed exact codec
; decoding before this ACL2 entry point receives them.
(in-package "ACL2")
(include-book "../../books/store-observed")

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
                  "observed-pin" "observed-content" "observed-release" 1))
(defconst *fn-so-replayed*
  (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-record0*)))
(assert-event (fn-sn-open-okp *fn-so-replayed*))
(assert-event (equal (fn-sn-node (fn-sn-open-state *fn-so-replayed*))
                     (fn-sf-replay-node *fn-so-groups* 10
                                        (list *fn-so-record0*) 1)))

; A known-aborted allocation gap is replayable: record txid 1 and frontier 2.
(defconst *fn-so-gap-record*
  (fn-record-make 0 1 1 "<gap@example>" '(66) *fn-so-groups*
                  "gap-pin" "gap-content" "gap-release" 1))
(assert-event
 (fn-sn-open-okp (fn-sn-open-observed *fn-so-groups* 10 2
                                      (list *fn-so-gap-record*))))

; Invalid trailing data and a frontier behind a committed txid refuse opening.
(assert-event
 (equal (fn-sn-open-observed *fn-so-groups* 10 1
                             (list *fn-so-record0* 'not-a-record))
        '(:error :history)))
(assert-event
 (equal (fn-sn-open-observed *fn-so-groups* 10 0 (list *fn-so-record0*))
        '(:error :history)))

(defconst *fn-so-four*
  (fn-sn-observed-rebarrier (fn-sn-open-state *fn-so-replayed*) 4))
(defconst *fn-so-five*
  (fn-sn-observed-rebarrier (fn-sn-open-state *fn-so-replayed*) 5))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-four*)) :recovering))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-five*)) :ready))
