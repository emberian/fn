; Invariants for pure fail-closed committed-record replay.
;
; These claims concern the executable logical replay interpreter.  They neither
; establish a durable journal format nor prove that a supplied record was
; authenticated, complete on disk, or selected by a physical recovery process.

(in-package "ACL2")
(include-book "replay")
(include-book "node-invariants")

; Raising an idle acceptance txid models a known-aborted transaction gap.  It
; cannot create a partial article or pin and preserves the full node invariant.
(defthm fn-replay-advance-preserves-node-statep
  (implies (fn-node-statep node)
           (fn-node-statep (fn-replay-advance-txid node recorded-txid)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid
                                      fn-node-statep fn-statep))))

; A non-NIL one-record result is the existing node transaction machine's
; durable branch, hence remains a valid node.  NIL is intentionally a refusal,
; not a partially reconstructed state.
(defthm fn-replay-apply-record-non-nil-is-node-state
  (implies (and (fn-node-statep node)
                (fn-record-p record)
                (consp (fn-replay-apply-record node record)))
           (fn-node-statep (fn-replay-apply-record node record)))
  :hints (("Goal"
           :use ((:instance fn-replay-advance-preserves-node-statep
                            (recorded-txid (fn-record-txid record))))
           :in-theory (e/d (fn-replay-apply-record)
                            (fn-node-prepare fn-node-complete)))))

(defthm fn-replay-ok-constructor-is-typed
  (implies (and (fn-node-statep node) (natp sequence))
           (fn-replay-okp (fn-replay-ok node sequence)))
  :hints (("Goal" :in-theory (disable fn-node-statep))))

(defthm fn-replay-fault-constructor-is-typed
  (implies (and (fn-node-statep node) (natp sequence))
           (fn-replay-faultp (fn-replay-fault node sequence reason)))
  :hints (("Goal" :in-theory (disable fn-node-statep))))

(defthm fn-replay-natural-successor
  (implies (natp sequence) (natp (+ 1 sequence))))

; From a valid node and natural expected sequence, replay always returns a
; typed success or a typed fault containing a valid diagnostic prefix node.
(defthm fn-replay-loop-result-is-typed
  (implies (and (fn-node-statep node)
                (natp expected-sequence))
           (or (fn-replay-okp
                (fn-replay-loop node records expected-sequence))
               (fn-replay-faultp
                (fn-replay-loop node records expected-sequence))))
  :hints (("Goal" :induct (fn-replay-loop node records expected-sequence)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-replay-loop fn-replay-ok-constructor-is-typed
              fn-replay-fault-constructor-is-typed fn-replay-natural-successor)))))

; Valid configured initial inputs inherit the typed replay-result boundary.
(defthm fn-replay-result-is-typed-from-valid-configuration
  (implies (and (fn-string-listp groups)
                (fn-no-duplicatesp groups)
                (natp capacity))
           (or (fn-replay-okp (fn-replay groups capacity records))
               (fn-replay-faultp (fn-replay groups capacity records))))
  :hints (("Goal"
           :use ((:instance fn-replay-loop-result-is-typed
                            (node (fn-node-initial-state groups capacity))
                            (expected-sequence 0)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn-replay fn-node-initial-state-is-state
                         (:executable-counterpart natp))))))
