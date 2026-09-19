# Proof style

These are the conventions every book in `books/` and `tests/acl2/` follows.
They were set on the core cluster (acceptance, retention, node, replay,
exchange) in the 2026-09-19 realignment; each worked example below is real
code from that cluster, cited by file. The assurance rules in
[`AGENTS.md`](../AGENTS.md) say what a claim must be; this document says how
a book is written so that green stays green when lanes merge.

The problem these solve, measured on the tree before the realignment: no
typed structures (806 raw-list accessors), 642 `-is-`/`-of-` equalities of
which 68 were `:rule-classes nil` and the rest were global rewrite rules on
include, whole-state recognizers recomputed on every served operation
(`fn-statep` is Θ(n²) and ran at `acceptance.lisp:662/695/720`), general
negated `must-fail` teeth, and 116 reaches for `minimal-theory`. Each of
those is a symptom of the same thing: books exported their internals.

## 1. Records are opaque

A record is a shape recognizer, a constructor and accessors. The accessors
are total (`:guard t`) with an `mbe` whose `:logic` is the raw selector and
whose `:exec` is the total `fn-ag-` helper. Immediately after the
constructor, prove the shape lemma and one accessor-of-constructor lemma per
field, then withdraw the `:definition` runes of the shape, the accessors and
the constructor. Nothing below that point opens a record: rules are stated
in accessor vocabulary and goals stay in it.

```lisp
(defun fn-article-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))
(defun fn-article-msgid (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-article-msgid)
...
(defun fn-make-article (msgid payload groups memberships pin)
  (declare (xargs :guard t))
  (list msgid payload groups memberships pin))

(defthm fn-article-shapep-of-fn-make-article
  (fn-article-shapep (fn-make-article msgid payload groups memberships pin)))
(defthm fn-article-msgid-of-fn-make-article
  (equal (fn-article-msgid (fn-make-article msgid payload groups memberships pin))
         msgid))
...
(in-theory (disable (:d fn-article-shapep) (:d fn-article-msgid) ...
                    (:d fn-make-article)))
```
(`books/acceptance.lisp`, article; the same pattern for pending, state,
obligation, release, stage, binding, fact, policy, result.)

Withdraw only the `:definition` rune (`(:d name)`). The constructor's
type-prescription (it is a cons) and every executable counterpart stay, so
`(null (fn-make-pending ...))` still decides and ground evaluation still
works.

The recognizer of a record is then written over the shape predicate and the
accessors, never over `car`/`len`:

```lisp
(defun fn-articlep (configured x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-article-shapep x)
       (stringp (fn-article-msgid x))
       ...))
```

Why this and not `(len x)` in the recognizer: a `len` conjunct is a
`len`-backchaining invitation every time the recognizer opens. The shape
predicate opens to it only if you enable it, and you never need to.

## 2. Export theory at book end

Every book ends with an explicit theory event. It withdraws the recognizers
of records and states, the initial state, the transitions and every lemma
that is proof vocabulary rather than a keystone. What remains enabled on
include is: keystones, record lemmas, list-recursive vocabulary (the
functions proofs induct on) and small glue predicates written in accessor
vocabulary. A book that withdraws nothing says so:

```lisp
(in-theory (current-theory :here))          ; books/acceptance-alloc.lisp
```

```lisp
(in-theory (disable fn-articlep fn-pendingp fn-statep fn-initial-state
                    fn-install-pending fn-clear-pending
                    fn-accept-prepare fn-accept-complete fn-accept-recover))
                                            ; books/acceptance.lisp
```

Lemmas that are proof vocabulary (allocator, watermark, set and length
lemmas) are withdrawn under a name, so a book above can re-enable exactly
that vocabulary in one line without knowing the list:

```lisp
(deftheory fn-acceptance-invariants-vocabulary
  '(fn-bump-preserves-nexts fn-next-positive ... fn-watermark-pair-not-below-member))
(in-theory (disable fn-acceptance-invariants-vocabulary))
                                            ; books/acceptance-invariants.lisp
(local (in-theory (enable fn-acceptance-invariants-vocabulary ...)))
                                            ; books/node-invariants.lisp
```

A book above that must open one of these does so locally and says which:

```lisp
(local (in-theory (enable fn-articlep fn-pendingp fn-statep fn-initial-state
                          fn-install-pending fn-clear-pending
                          fn-accept-prepare fn-accept-complete
                          fn-accept-recover)))   ; books/acceptance-invariants.lisp
```

The theorems in the book are proved before the export event, in the theory
the book built, so a book's own proofs never depend on what an includer
happens to have enabled, and an includer never inherits a rule it did not
ask for. This is what makes two green lanes merge green.

## 3. Guard-proof equalities are `:rule-classes nil`

An equality that exists to discharge a guard or an `mbe` obligation is not a
rewrite rule. It is stated once, `:rule-classes nil`, and used by `:use`:

```lisp
(defthm fn-replay-apply-record-statep-iff-consp
  (implies (and (fn-node-statep node) (fn-record-p record))
           (iff (fn-node-statep (fn-replay-apply-record node record))
                (consp (fn-replay-apply-record node record))))
  :rule-classes nil ...)

(verify-guards fn-replay-loop
  :hints (("Goal" :use ((:instance fn-replay-apply-record-statep-iff-consp
                                   (record (car records)))) ...)))
```
(`books/replay.lisp`.) A guard fact needed only inside one book is `local`
(`fn-retain-guard-find-is-obligation`, `books/retention.lisp`).

The `fn-ag-car-is-car` family is the cautionary example: five `-is-`
equalities exported enabled to every book in the tree. The helpers are now
their logical primitives by `mbe` (`fn-ag-car` is `(mbe :logic (car x) :exec
...)`), so opening the definition is the equality and the twins survive only
as `:rule-classes nil` names for the one includer that cites them by `:use`.

## 4. Recognizers are carried invariants

A whole-state recognizer guards the executable path; it is never recomputed
per operation. The `:logic` body keeps the original total definition, so
every theorem keeps its statement and non-states are still returned
unchanged in the logic; the `:exec` path relies on the guard:

```lisp
(defun fn-accept-prepare (s generation msgid payload groups)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    ...))                                   ; books/acceptance.lisp
```

For a predicate whose first conjunct is the recognizer:

```lisp
(defun fn-retain-admissiblep (s id subject kind evidence charge)
  (declare (xargs :guard (fn-retain-statep s)))
  (and (mbe :logic (fn-retain-statep s) :exec t) ...))   ; books/retention.lisp
```

A caller discharges the callee's guard from a preservation keystone, which is
why `books/replay.lisp` includes `node-invariants`: `fn-replay-apply-record`
calls `fn-node-prepare` on an advanced node and `fn-node-complete` on a
prepared one, and `fn-replay-advance-preserves-node-statep` and
`fn-node-prepare-preserves-state` are the guard proof. The loop tests
one-record refusal by `NIL` in the `:exec` path, justified by the
`:rule-classes nil` iff above. An entry point checks the recognizer once
(`fn-replay` on the initial node) and the loop carries it.

The measured reason: `fn-statep` is Θ(n²) in Message-ID comparisons and
Θ(n·P) in octet checks, and it ran on every served operation and four times
per replayed record (`planning/lanes/HANDOFF-w3-scale-profile.md`). After
this change the per-operation cost is the operation's own work.

## 5. Teeth are concrete witnesses

A keystone ships with a reachable non-degenerate witness and one concrete
violating value per hypothesis, each an `assert-event` on the negated
conclusion. A value outside a guard is evaluated under
`with-guard-checking :none`, which is the point: the `:logic` body is total,
the `:exec` path is not.

```lisp
(assert-event (not (fn-statep *acc-teeth-forged*)))
(assert-event (consp (fn-state-pending *acc-teeth-forged*)))
(assert-event (not (fn-statep (fn-install-pending *acc-teeth-forged*))))
                                            ; tests/acl2/acceptance-tests.lisp
(assert-event
 (with-guard-checking :none
  (not (equal (car (fn-retain-releases
                    (fn-retain-release *ret-teeth-forged* ...)))
              (fn-retain-make-release ...)))))   ; tests/acl2/retention-tests.lisp
```

Never a general negated `must-fail`: it proves that the prover could not
find a proof, which is not a counterexample, and it loops when the negation
is unprovable rather than false. Never a trivially true assertion. If no
violating value exists for a hypothesis, the hypothesis is unnecessary:
delete it from the theorem and say so (`fn-retain-known-obligation-id-is-
not-reused` lost its `fn-retain-statep` hypothesis this way), or record it
open with the reason (`fn-allocate-at-watermark`, whose first two hypotheses
need a watermark lemma without the membership-list hypothesis before they
can be dropped).

## 6. Book layering

One cluster is: primitives, definitions, properties, one test book.

- `<x>-alloc.lisp` or the like: total helpers and list vocabulary, exports
  everything (`acceptance-alloc`).
- `<x>.lisp`: records, recognizers, transitions, the first theorems, export
  theory (`acceptance`, `retention`, `node`, `exchange`, `replay`).
- `<x>-invariants.lisp`: the preservation keystones, opening the definitions
  locally (`acceptance-invariants`, `node-invariants`).
- `<x>-traces.lisp` only when there is a dispatcher and a fold over it
  (`node-traces`).
- `tests/acl2/<x>-tests.lisp`: guard-world audit, malformed-input
  regressions, scenarios and teeth, in that order, one book per cluster.

Split a book over 800 lines at its seam and keep the old name as the top
(`acceptance` includes `acceptance-alloc`). Fold a property book into the
definition book when its theorems discharge the definitions' guards
(`replay-invariants` into `replay`); leave a two-line include shim behind
for includers outside the cluster and say who should delete it.

## 7. Naming

- `fn-<field>-of-fn-make-<rec>`: accessor of constructor. `fn-<rec>-shapep`:
  shape.
- `-preserves-<inv>`: a preservation keystone. `-is-typed`, `-iff-consp`:
  what they say.
- A fact that restates a branch of a definition with the branch test as its
  hypothesis (`-is-no-op`, `-refusal-is-no-op`) is `:rule-classes nil`,
  carries a `-by-definition` comment, and is never a registry event. A
  theorem whose proof is `:in-theory '(A B)` is a corollary: `:rule-classes
  nil`, cite A and B instead.
- `-unfolds`: a definitional restatement kept for an includer's `:use`.

## 8. What may leave a book enabled

May: keystones; record lemmas; list-recursive definitions (they are the
induction vocabulary: `fn-article-listp`, `fn-node-binding-msgids`,
`fn-exchange-merge`); glue predicates in accessor vocabulary
(`fn-pending-matchesp`, `fn-retain-matching-releasep`); the total `fn-ag-`
helpers.

May not: record accessors, constructors and shapes; recognizers of records
and states; initial states; transitions; `len`-, `consp`- or
`true-listp`-backchaining rules; `-is-`/`-of-` equalities other than record
lemmas; proof-vocabulary lemmas (allocator, watermark, set and length
lemmas); corollaries; anything an includer would have to `disable` to keep
its own proofs stable. A hint that reaches for `minimal-theory` is a book
that exported too much; say which rules you mean with `e/d`.

## 9. The FTY question

Should records migrate to `fty::defprod`/`deftagsum` instead of the raw-list
discipline above? `centaur/fty/top` is certified in the laptop install
(ACL2 8.7, 18 of 21 books in `centaur/fty` certified, `std` 818 of 822). A
scratch trial on 2026-09-19 included `centaur/fty/top` and admitted a
three-field `defprod` with `:layout :list` in 0.9 s wall (ACL2 8.7, SBCL,
this laptop), so the cost is not include time or certification but what it
buys and what it drags in.

What it would buy: fixing functions and `-equiv` congruences for free, a
generated `-p` recognizer with the shape baked in, `b*` binders, and the
accessor-of-constructor and constructor-of-accessors lemmas generated rather
than written. What it costs: `defprod` records are keyed by fixing
functions, so every field type needs a fixer and every theorem inherits
`-fix` normal forms; `include-book "centaur/fty/top"` pulls `std/lists`,
`std/util` and their enabled rules into every book above, which is exactly
the enabled-rule pollution this document exists to stop; the host encodes
records as positional lists today (`books/records.lisp`, the CBOR record
codec) and `defprod` layouts are `:layout :list`-compatible only when asked
and only for the tagless form; and the ledger's guard reader would need to
learn `fty` events.

Recommendation: keep raw-list records under the opaque discipline. It
gives the same interface (shape, constructor, accessors, one lemma per
field, disabled definitions) with no new theory on include, no fixing-
function normal forms in keystone statements, and no change to the host
encoding. Revisit only if a cluster needs congruence reasoning over record
equivalences, and then trial `defprod :layout :list` on that cluster's one
record behind its own `-fty.lisp` book so the include stays local. The
scratch trial recorded in `planning/deputies/core.md` says what one
`defprod` costs to include on this laptop.
