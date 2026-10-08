# Catch-up carried transit: implementation and checked statements

Codex, lane `s-catchup-k`, 2026-10-08. Base: `f2629613ed5fed8084ab7e9b2d79c10dfb7c0dd9`.
Phase 1's proposed statements and cost obstructions are preserved in this file
at `f4df2bc3389b39750c0923a42485f78b3f8fdbbc`. Deputy S authorized Phase 2,
accepted K1, allowed premise transfer for K1-carry, and replaced the proposed
connection-only def-cost bound with K2a executed reachability and K2b's trace.

Both durable transit arms now call the existing `fn-oop-advance`. There is no
new advance implementation. K1 holds under exactly `fn-ocl-relation oc`, which
the host already carries. These are certified equalities, not a measured W6
speedup or a connection-only time bound. Configuration-sized group comparisons
remain; the W6 measurement belongs to Deputy S and L.

## K1: owner and effects at both subjects

The following are the admitted theorem statements, verbatim apart from proof
hints. The counted return is `((effects . oc) . pending)`; its whole owner,
including the feed table, equals the reference owner for every `pending`.
No aggregate or feed-table hypothesis has been added to K1.

Subject: `fn-oop-transit-outcome`.

```lisp
(defthm fn-oop-transit-outcome-is-own-transit-outcome
  (implies (fn-ocl-relation oc)
   (and (equal (car (fn-oop-transit-outcome oc id kind reason word))
              (car (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word)))
       (equal (fn-ocfg-owner (cdr (fn-oop-transit-outcome oc id kind reason word)))
              (cdr (fn-own-transit-outcome (fn-ocfg-owner oc) id kind reason word))))))
```

Subject: `fn-oct-transit`.

```lisp
(defthm fn-oct-transit-is-own-transit-outcome-under-ocl-relation
  (implies
   (fn-ocl-relation oc)
   (and
    (equal (car (car (fn-oct-transit oc id kind reason word pending)))
           (car (fn-own-transit-outcome
                 (fn-ocfg-owner oc) id kind reason word)))
    (equal (fn-ocfg-owner
            (cdr (car (fn-oct-transit oc id kind reason word pending))))
           (cdr (fn-own-transit-outcome
                 (fn-ocfg-owner oc) id kind reason word))))))
```

Why this does not weaken the host contract: the logical statements are
conditional, but their only premise is supplied at the existing call site.
`fn-lgoc-invariantp` includes `fn-ocl-relation` in
`books/owner-log-ocl.lisp:233`; `fn-ohr-carried-implies-ocl-relation` at
`books/owner-host-relation.lisp:474` exposes it. The host's transit preservation
theorem retains its existing premises. The shape-only keeps-store theorem
still proves structurally without invoking conditional K1. No caller required
a new premise. The old pinned theorem name remains; `host/interfaces.lisp`
cites both subjects, and the two obsolete reference-advance comments are fixed.

## K1-carry: premise transfer, not full relation preservation

These unconditional equalities transfer the two actual carried-advance
premises. Transit-next preserves the view and connection list. Composing these
with `fn-acar-ocl-relation-carries-conn-sessionp` and
`fn-acar-ocl-relation-carries-view-statep` at the incoming configured owner
supplies the advance's premises after transit-next. No new host hypothesis.

Subject: `fn-oop-transit-next`.

```lisp
(defthm fn-oop-transit-next-keeps-acar-premises
  (let ((next (fn-oop-transit-next o id conn sub completion kind reason)))
    (and (equal (fn-acar-conn-sessionp next target)
                (fn-acar-conn-sessionp o target))
         (equal (fn-acar-view-statep next) (fn-acar-view-statep o)))))
```

Subject: `fn-oct-transit-next`.

```lisp
(defthm fn-oct-transit-next-keeps-acar-premises
  (let ((next (fn-oct-transit-next o id conn sub completion kind reason feeds)))
    (and (equal (fn-acar-conn-sessionp next target)
                (fn-acar-conn-sessionp o target))
         (equal (fn-acar-view-statep next) (fn-acar-view-statep o)))))
```

Subject: `fn-acar-own-advance-result composed with fn-oop-transit-next`.

```lisp
(defthm fn-oop-transit-next-advance-is-reference
  (implies (fn-ocl-relation oc)
           (equal
            (fn-acar-own-advance-result
             (fn-oop-transit-next (fn-ocfg-owner oc)
                                  id conn sub completion kind reason) id)
            (fn-own-advance-result
             (fn-oop-transit-next (fn-ocfg-owner oc)
                                  id conn sub completion kind reason) id))))
```

## K2a: checked executed closure, derived from the final ACL2 world

Statement (a gate, not an ACL2 theorem): the conservative, path-sensitive
executed closures derived from `fn-oop-advance` and the whole `fn-oct-transit`
contain none of `fn-statep`, `fn-node-statep`, `fn-nntp-projectionp`,
`fn-peer-sessionp`, `fn-own-conn-boundedp`, `fn-articles-freshp`, or
`fn-article-listp`. Checking the whole counted function includes its durable
arm. The same check on `fn-ocfg-advance` fails: it reaches `fn-node-statep`
and `fn-statep`.

The existing `tools/extract/frontend.lisp` reads the ACL2 world's executable
bodies and resolves MBE/attachment routes. The new
`tools/extract/executed_closure.py` consumes that exported IR, not source text
or a declared closure list. It symbolically reduces immutable constructors,
selectors and decidable tests. Unknown IFs inspect both arms. Recursive SCCs
are inspected with unconstrained arguments and return opaque results; bounded
unrolling of small, decreasing natural arguments resolves record selectors.
Anything not resolved that way falls back to the conservative SCC treatment.
Missing definitions, mutable/stobj routes, non-guard-verified definitions,
frontend blockers and exhausted analysis budgets fail the gate.

This is deliberately path-sensitive: the static graph still has
`fn-scar-node-statep -> fn-node-statep`. Its first disjunct is true in this
composition, so the validator arm cannot execute. Reporting a static closure
without that edge would be false. No new hypothesis is used to prune it.

Reproduce with a fresh remote world (cached certification dependencies only):

```sh
timeout 300 python3 tests/acl2/catchup-carried-transit-closure.py --host persvati --lane s-catchup-k
```

The runner creates and stops its own proof-REPL session and exports fresh IR;
it does not accept an old world file. The complete derived sets, reference
paths, world digest and source commit are saved in `build/catchup-closure-*/`.
The checked world at `3c443d564017f62916041a44f1020cc8337d0c3d` had SHA-256
`4013fb038a9872bad281ab917d71a2bf35bb58cf2757c46344a0855e68d63ec2`:

```text
K2a ACL2::FN-OOP-ADVANCE: 238 reachable functions; 0 forbidden
K2a ACL2::FN-OCT-TRANSIT: 637 reachable functions; 0 forbidden
K2a reference tooth: ACL2::FN-NODE-STATEP, ACL2::FN-STATEP
```

The six narrow Python controls include a changed-node mutation exposing the
forbidden fallback, unknown branches, direct and mutual recursion, concrete
initial arguments that cannot hide later recursive cases, and fail-closed
checks. The reference tooth is independently derived from the same real world.
This gate makes no claim about total runtime, allocation, or article-independent
work in predicates outside the specified forbidden set.

## K2b: held-node comparison on the executed path

Statement (source trace, not a theorem or a timing result): the arguments to
`(equal node live)` at `books/served-carried.lisp:39` are EQ on the carried
advance's host path; this comparison does not traverse the held node.

`fn-acar-own-advance-result` at `books/owner-advance-carried.lisp:266` obtains
`old` from the selected connection and `pold` from its auth-session base.
`fn-peer-with-base` at `books/peer-inbound.lisp:949` puts
`(fn-peer-session-node pold)` straight into `fn-peer-make-session`; the list
constructor borrows the node object. `fn-auth-with-base` at
`books/nntp-auth.lisp:572` and the connection constructor preserve that rebuilt
peer session. `fn-scar-conn-boundedp` consequently reads the identical old node
object from `next`. Its `live` argument is `(fn-acar-session-node conn)`
(`books/owner-advance-carried.lisp:49`), which selects the same node from the
old connection. No node copy or re-decoding lies between these selectors.
The source trace establishes raw pointer identity here; ACL2 logical EQUAL
alone would not establish it. The def-cost tariff based on `acl2-count` cannot
express this raw EQ fact, so it is not presented as a cost theorem.

## Teeth and validation

`tests/acl2/catchup-carried-transit-tests.lisp` composes the existing configured
recovery fixture with a real peer open, IHAVE, article read, take, journal
completion and durable outcome. The input satisfies `fn-ocl-relation`, has
view version 3 and connection version 2, and actually triggers durable
transit. The result replies `235`, advances that connection to version 3 and
preserves the relation. Both K1 `defteeth` entries check the full antecedent
and conclusion. Each removes the sole `ocl` premise with a corrupt view;
each also exercises a corrupt held node. Both corruptions make the equality
false. They are corrupted-state removals, not reachable host states. A
no-advance conclusion mutation fails on the positive fixture. The
unconditional K1-carry equalities have no premise to remove.

Proofs were admitted incrementally on persvati before certification. One
affected certification batch then covered both outcome books, host relation,
`host/owner-host`, and the new fixture, at the unchanged Lisp closure from
`3c443d564`. No second certification was used for proof iteration.

```sh
timeout 900 python3 tools/boxq.py submit --kind certify-lane --box persvati --lane s-catchup-k --slots 2 --wait -- --lane --affected-by books/owner-outcome-pinned.lisp --affected-by books/owner-outcome-counted.lisp
```

Run `run-20261008T103534Z-8ec4` passed: 8 certified, 0 failed, 918 installed
from cache. D26 remains red for `host/owner-host` (99.5 s) and
`books/owner-host-relation` (46.3 s), measured at two jobs. These times are
reported, not waived or re-baselined.

`interface_emit --check`, `keystone_emit --check`, and `host_check --load`
reported 0 findings. The host load was the bare-ACL2 fallback: 58/58 raw files,
73 undefined certified-world names, 27 certified-world load-time calls,
46 other compiler warnings. The affected `host/owner-host` certified book was
also covered by the batch above. Interface checking retained one unresolved
pre-existing output-tariff citation and 13 source-undecidable kind rows;
these are not a claim of complete resolution. The existing toothless ceiling
was unchanged. Exact gate tails accompany the phase's final message.
