; Teeth for the sender-workflow node-preservation keystone.
;
; The 2026-09-18 review §5 names `fn-bp-trace-preserves-node' as one of the
; real trace inductions: "an unconditional equality".  Unconditional means
; there is no hypothesis to remove, so the teeth take the other form the review
; asks for.  Two things can make an unconditional equality worthless: the trace
; could do nothing, or the projection could be constant.  The witness rules out
; the first and the must-fail rules out reading the theorem as the second.

(in-package "ACL2")
(include-book "../../books/bp-workflow-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: a committed node, a durable enqueue and
; a durable attempt, run as an actual finite trace rather than a single step.

(defconst *bpw-teeth-groups* '("fn.letters"))
(defconst *bpw-teeth-payload* '(72 105 13 10))
(defconst *bpw-teeth-node*
  (fn-node-complete
   (fn-node-prepare (fn-node-initial-state *bpw-teeth-groups* 16)
                    9 "<bp@example.invalid>" *bpw-teeth-payload*
                    *bpw-teeth-groups* "archive-bp" "subject-bp" "release-bp" 4 841000000)
   0 9 :durable))
(defconst *bpw-teeth-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))
(defconst *bpw-teeth-state*
  (fn-bp-initial-state *bpw-teeth-node* *bpw-teeth-config*))

(assert-event (fn-node-statep *bpw-teeth-node*))
(assert-event (fn-bp-statep *bpw-teeth-state*))
(assert-event (equal (fn-bp-state-node *bpw-teeth-state*) *bpw-teeth-node*))

(defconst *bpw-teeth-events*
  (list (fn-bp-enqueue-prepare-event 10 0 "work-1" "<bp@example.invalid>"
                                     "forward-1" "policy-1" "terms-1")
        (fn-bp-storage-complete-event 10 0 :durable)
        (fn-bp-attempt-prepare-event 11 0 "work-1" "attempt-1")
        (fn-bp-storage-complete-event 11 0 :durable)))

(defconst *bpw-teeth-after* (fn-bp-trace *bpw-teeth-state* *bpw-teeth-events*))

; The trace is not a no-op: work exists afterwards that did not exist before,
; and the transaction identities have been consumed.
(assert-event (fn-bp-statep *bpw-teeth-after*))
(assert-event (null (fn-bp-state-works *bpw-teeth-state*)))
(assert-event (consp (fn-bp-state-works *bpw-teeth-after*)))
(assert-event
 (fn-bp-work-outstandingp
  (fn-bp-find-work "work-1" (fn-bp-state-works *bpw-teeth-after*))))
(assert-event
 (not (equal (fn-bp-state-used-txs *bpw-teeth-after*)
             (fn-bp-state-used-txs *bpw-teeth-state*))))

; And the keystone holds across it: the local node component is untouched by
; four sender transactions.
(assert-event
 (equal (fn-bp-state-node *bpw-teeth-after*) (fn-bp-state-node *bpw-teeth-state*)))

; -----------------------------------------------------------------------------
; Teeth for `fn-bp-trace-preserves-node'
;   (equal (fn-bp-state-node (fn-bp-trace s events)) (fn-bp-state-node s))
;
; No hypothesis, so no hypothesis can be dropped.  What is worth ruling out is
; the reading under which the theorem is free: that `fn-bp-trace' preserves the
; whole state and the node is carried along.  It does not, and the case below
; is the proof -- the same trace, the same witness, the claim one notch
; stronger, and ACL2 refuses it.

(local
 (must-fail
  (defthm bpw-teeth-trace-does-not-preserve-the-state
    (equal (fn-bp-trace *bpw-teeth-state* *bpw-teeth-events*)
           *bpw-teeth-state*))))

; The other way the theorem could be free is if the projection were constant.
; It is not: two states of the same shape with different nodes project
; differently, so `fn-bp-state-node' distinguishes what it is asked to preserve.
(defconst *bpw-teeth-other-node*
  (fn-node-initial-state *bpw-teeth-groups* 16))
(assert-event
 (not (equal (fn-bp-state-node
              (fn-bp-initial-state *bpw-teeth-other-node* *bpw-teeth-config*))
             (fn-bp-state-node *bpw-teeth-state*))))
