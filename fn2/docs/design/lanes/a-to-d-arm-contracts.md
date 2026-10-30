# Arm contracts: what layer D writes (R7; from the A/D DSL seat; present state)

`defmachine` declares every continuation and observation handler with a contract, and
`defmachine-callback` checks each body against it in a restricted arm language. Violations are
macro refusals with a named message. Source: `fn2/books/arms.lisp` (the language, defcost, the
resource checks, the frame predicate) and `fn2/books/machines.lisp` (the registry, the generated
certificates, the run-time asserts, the owed rows). Worked declarations: `fn2/books/machines-a.lisp`
(listener, echo, scribe); outside-call costs: `fn2/books/machines-a-costs.lisp`.

## defmachine

```lisp
(defmachine K
 :states (PHASE ...)
 :fields ((FIELD KIND) ...)                    ; as before; the common fields are added
 :holds ((PHASE RESOURCE-KIND ...) ...)        ; D0's kinds, in rank order; unlisted phases hold ()
 :budget (:bytes B :steps S :descriptors D)    ; the per-run caps
 :capacity FORM :initial (...)
 :continuations
 ((PHASE FN :cost (:bytes F :steps F :descriptors F)   ; omitted dimensions are 0
            :writes (FIELD ...)          ; own-row fields this arm may write (not phase)
            :tables (CHILD ...)          ; core children it may change (fn2-core-pool, fn2-core-ops,
                                         ; fn2-core-machines, K2-table, ...; fn2-core-machine-tables =
                                         ; every kind's table); fn2-core-control is implicit
            :next (PHASE ...)            ; phases the row may be in after the run
            :uses (OP ...)               ; every outside call and forwarded callback the body makes
            [:on-refusal (POSTURE :to PHASE :releases (KIND ...))]
            [:language :unchecked])      ; the declared escape: body not checked, recorded
  ...)
 :observes
 ((EVENT FN :cost (...) :writes (...) :tables (...) :next (PHASE ...) :uses (...)
            [:from (PHASE ...)])         ; phases it observes in; default all but :free/:retired
  ...))
```

Cost forms: `F ::= nat | *CONSTANT* | (+ F ...) | (max F ...) | (* nat F) | (:cost OP DIM)`, where
`OP` is in the arm's `:uses` and has a defcost or is a contracted callback. A bare `(PHASE FN)`
entry is refused: "arm ~ needs its contract (:cost :writes :next :uses ...); the bare (TAG FN) form
is retired".

Checked at declaration: contract shape, writes are own fields, next/from are declared phases,
holds use D0's kinds in rank order. Checked when the kind's run is generated (the `:callbacks`
section, every callback defined): the evaluated cost is within the caps; **an arm whose cost
reaches a cap must list its own phase in :next** (its continuation is the row's fields); every use
resolves; the resource moves below; D0's `fn2-resource-effects-p` over the arm's effect rows; the
refusal posture.

## defcost (outside calls)

```lisp
(defcost OP :bytes N|*C* :steps N|*C* :descriptors N|*C*
            :tables (CHILD ...) :own-writes (FIELD ...)
            :effects (EFFECT ...) | :per-use
            :target (KIND FROM TO)
            :doc "one line")
```
EFFECT is D0's form: `(:acquire KINDS)`, `(:acquire KINDS :for KIND)`, `(:release KINDS)`,
`(:transfer KINDS :to KIND)`. `:per-use` means the kind is the caller's: the arm then writes
`(OP :effects (EFFECT ...))` in its `:uses` (the pool range operations: `:rx-range` for a
connection, `:storage-window` for the scribe). `:target` says the call moves a row of another kind
between two of its phases (admission: `(fn2-echo :free :command)`). `:operation` (an op
reservation) is transient: held only across an issue, never a hold. D's parser and renderer
continuations, the bundle operations of D3-D8, B's commit reference and C's lookups each get one
defcost from their own layer (`:bytes` bounded by the run quantum).

## The restricted arm language (decision 2)

Accepted in a checked body: variables and constants; `quote`; `let`, `let*`, `b*` (symbol and
`(mv ...)` binders), `mv-let`; `if cond and or case mv prog2$ progn`; the scalar primitives
(`+ - * < <= > >= = /= equal eq eql min max nfix ifix zp zip natp posp integerp unsigned-byte-p
1+ 1- floor mod logand logior ash not null`); `(fn2-call CALLEE ...)` of a contracted callback of
the same kind in `:uses` (its writes, next and tables within the caller's); `K-PUT-CORE` on the
row `id` for declared fields, `phase` only to constants in `:next`; `fn2-machine-result`,
`fn2-machine-with-work`; calls of `:uses` operations that have a defcost (their `:own-writes` and
`:tables` within the arm's). Refused, each with a message: a write outside `:writes`; a move
outside `:next`; any other call (a helper hiding a foreign-table write is refused whether or not it
is listed, unless it has a defcost); a stale row read (`ROW-f` after `f` was written on the same
path: read the row first); a cost citing an undeclared call. A callback only forwarded to takes
`:contract (...)` after its position argument:

```lisp
(defmachine-callback K-HELPER K (id budget) 4
  :contract (:cost (...) :writes (...) :tables (...) :next (...) :uses (...))
  BODY)
```

## Resources (`:holds`, HIGHER-STRUCTURES entry 2)

A row's holds are a function of its phase. For every source phase S of an arm and successor S'
in `:next`, the arm's operations (transitively through forwarded callbacks) must acquire
`holds(S') - holds(S)` and release or transfer `holds(S) - holds(S')`; every own-row effect they
declare must be one of those moves ("an undeclared resource effect" otherwise); an effect on
behalf of a `:target` row must give it exactly `holds(TO) - holds(FROM)` of its kind. The check is
per arm, not per path: an arm whose paths reach S' along different branches is accepted when some
operation it uses makes each move. When a phase cannot say what the row holds (L1's listener held
a reserved row only while an Accept was in flight), split the phase (the listener's
:accepting / :admitting).

## Postures (`:on-refusal`)

`(POSTURE :to PHASE :releases (KIND ...))`, POSTURE one of `:close-and-release`,
`:discard-to-terminator`, `:refuse-by-word`, `:stop`; PHASE in the arm's `:next`; the releases
equal `holds(source) - holds(PHASE)`. The listener's :admitting arm declares
`(:close-and-release :to :closing :releases (:connection-row))`. D declares its own kinds'.

## What is generated per kind and arm

- `K-ARM-CHARGE-OK-P (phase bytes steps descriptors)`, `K-ARM-NEXT-OK-P (phase next)`,
  `K-OBSERVE-NEXT-OK-P (event from next)` (unchanged phase allowed), `K-ARM-BOUND (phase)`;
  across kinds `fn2-machine-arm-charge-ok-p` and `fn2-machine-arm-bound`.
- The run entry and the observation handler assert them: a run charging beyond its arm's bound
  or moving to an undeclared phase stops the core with `:machine-contract` (assert, never absorb).
- Owed rows in fn2-squares, `:from (:machine K)`: per continuation arm `K-PHASE-BOUND`
  (`:bound`: the charge within the certificate) and `K-PHASE-FRAME` (`:invariant`: only declared
  fields of the row and declared children change, and the row moves only to a declared phase);
  per handler `K-OBSERVE-EVENT-FRAME`; per kind `K-PHASE-TOTALITY`. Teeth: the certificates
  accept every declared bound and successor and refuse one step beyond, an undeclared successor
  and an out-of-range phase; the frame predicate `fn2-arm-framep` is evaluated on witnesses that
  satisfy and falsify it.
- `fn2-arm-cost-composition` (a word of certified runs costs at most the sum of its arms' bounds)
  and `fn2-arm-residual-budget` (a run handed the residual descriptor budget spends at most it):
  the turn bound's composition and its internal-hom law, owed with executable teeth.

## What R7 did not build (D owns or later)

- The line-scanner and buffer-compaction worked example on a connection-shaped kind: D3 builds
  the connection machine on D2a's grammar continuation; it takes this syntax, and every gap
  comes back through main.
- Per-path resource checking (the check is per arm), and per-row resource accounting (A6).
- `*fn2-turn-transition-max*` still takes the kinds' caps, not the arms' bounds (changing it
  changes the turn's work room and every A4 summary; a separate measured change).

## Admission (D's section 4.5; landed with the A/D seam commit)

A kind the listener admits declares
`:admission (:phase P :ranges (RANGE ...) [:copy (FIELD ...)] [:clear (FIELD ...)])`. RANGE is
`:rx-range` / `:tx-range` (row fields `rx-slot rx-gen` / `tx-slot tx-gen`, pool class 0) or
`(KIND :slot F :gen F :class N)`; the row needs `cap-index`, `cap-nonce` and a `:link` `next-free`
(initial `fn2-machine-initial-next-free`), and a `:free` phase. Admitted kinds get ordinals in
declaration order (`*K-ADMISSION-ORDINAL*`; echo is 0); the directory's partition (capacity, free
head, credits, active count, admission FIFO) is an array indexed by ordinal (at most 16 kinds).
Generated per kind (`fn2-machine-admission-events`, at the top of the callbacks section):
`fn2-machine-admit-K (index nonce COPIES... fn2-core)` -> `(mv code fn2-core)` (`:ok`, `:no-row`,
`:pool`; all ranges or none), defcost `:target (K :free P)`, effects
`((:transfer (:connection-row) :to K) (:acquire RANGES :for K))`, checked against K's `:holds`;
`fn2-machine-reclaim-K (id retire fn2-core)`, effects `((:release (:connection-row)))`; and the
listener's dispatcher `fn2-machine-admit (target index nonce COPIES... fn2-core)`. Listeners carry a
`target` field (the ordinal), set for every listener at init from the profile key
`:listener-targets` (a kind name; absent: the first admitted kind, so every existing profile is
unchanged). A drain arm releases its ranges with `fn2-core-release` (`:effects` per range) and calls
`fn2-machine-reclaim-K`.
Not yet: the peer-address words in the Accept result (an ABI change to the result cell, which
carries two aux words today: cap-index and cap-nonce); it goes with the adapter work (A5r).
