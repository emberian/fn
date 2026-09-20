# Handoff: w10/dtn-3 — the record eliminator every codec needed, and the fold it unblocked

Branch `w10/dtn-3`, worktree `build/lanes/w10-dtn-3`, from `dev` at `34288c4`
and merged forward. Boxes, measured before every run: hbox
(`/tank/fn/lanes/w10-dtn-3`, ACL2 `/tank/fn/acl2-8.7/saved_acl2`, cache
`/tank/fn/certcache`, always under `swarm-build`) and persvati
(`/home/ember/fn-lanes/w10-dtn-3`, ACL2 `$HOME/fn-tools/acl2-8.7/saved_acl2`,
cache `/home/ember/fn-certcache`). Two ACL2 runs on the laptop, both under a
second.

## 1. Packet 0 — `fn-defrecord` generates constructor-of-accessors (LANDED ALONE)

`books/defrecord.lisp` generated accessor-of-constructor and not its dual,
so every decode-of-encode round trip in this tree had a hand-written
eliminator under it: `fn-record-reconstruct`, `fn-snt-node-reconstruct`,
`fn-snt-acceptance-reconstruct`, `fn-bpa-request-fields-reconstruct`,
`fn-bpb-block-is-its-own-accessors`, each with its own name, its own
`:expand` list and its own rule class. The macro now generates it:

```lisp
(defthm <ctor>-of-accessors
  (implies (<shape> x)
           (equal (<ctor> (acc1 x) ... (accn x)) x)))
```

**Under the shape predicate, not the recognizer**, for two reasons a
recognizer-hypothesis form could not meet: a record declared `:recognizer
nil` (`fn-sched-result`) has no recognizer and still needs the lemma, and a
recognizer with `:recognizer-formals` (`fn-articlep`, `fn-pendingp`,
`fn-node-stagep`) would put a free variable in the rule's hypothesis. **It
still fires with the recognizer CLOSED** --- the only way a transition proof
may use it --- because `<recognizer>-forward-shape` now forward-chains
`(<shape> x)` beside `consp` and `true-listp`; the shape predicate stays
withdrawn, and the forward-chained literal relieves the hypothesis without
opening anything.

**There is no field shape it cannot do.** Tagged and untagged, every width:
the constructor writes the tag itself and the shape predicate pins
`(equal (car x) tag)`, so a tagged record rebuilds from its fields alone.
The `:expand` list of `(len (cdr^k x))` the proof needs is generated from
the record's width.

Teeth (`tests/acl2/defrecord-tests.lisp`): three rebuilds proved with the
recognizer disabled AT THE FORM (untagged, tagged, and the context-formal
record), and four concrete values on which the rebuild is not the original
--- wrong length, right length but not a true list, not a cons, a foreign
tag --- with the admitted witness beside them so none is vacuous.
`tools/ledger.py` mirrors both changes; `tests/test_ledger.py` pins the
statement and the new forward-chaining conjunct.

**The hazard it introduces, and the cure, because it cost this lane a
run.** The hand-written eliminators were `:rule-classes nil` and cited by
`:use`. The generated one is an ENABLED rewrite, so a `:use` of it adds a
hypothesis whose left-hand side is the rule's own left-hand side: the
rewriter collapses it to `(equal b b)` and the `:use` is gone before the
goal can use it. `fn-bpb-decode-block-of-encode-block` failed exactly this
way at `Subgoal 17.3'` (`build/acl2/certify-*`, the first profile run).
**Every `:use` of a `<ctor>-of-accessors` needs that rule in the `e/d`
disable list of the same hint.**

Certified, ACL2 8.7 / SBCL 2.6.8, all `passed`:

| where | run | evidence | books | note |
| --- | --- | --- | --- | --- |
| laptop | --- | `build/acl2/certify-20260920T213002Z-19121` | `books/defrecord` 0.13 s, `tests/acl2/defrecord-tests` 0.22 s | the macro and its teeth |
| persvati | `run-20260920T213144Z-7728` | `build/acl2/certify-20260920T213153Z-3503617` | 16 books, 63.92 s wall at `--jobs 4` | the named heavy users: `books/records` 8.04 s, `books/records-invariants` 51.01 s, `books/anchor` 1.91 s, `books/peer-config` 2.90 s |
| hbox | `run-20260920T213132Z-f558` | `build/acl2/certify-20260920T213139Z-1210785` | 7 books | `books/bp-primary-invariants` 632.25 s, `books/bp-primary-cbor` 54.03 s, `books/bp-bundle` 10.32 s |
| persvati | `run-20260920T214122Z-02f2` | `build/acl2/certify-20260920T214126Z-3601692` | **54 books**, 203.94 s wall at `--jobs 6` | the whole DTN image substrate: `books/tcpcl-octets` 133.92 s, `books/store-node-invariants` 71.35 s, `books/frame` 69.25 s, `books/tcpcl-session` 66.81 s |

That is 77 distinct books re-certified against the changed macro with no
statement edited anywhere and no regression. Ledger lint total unchanged at
236; `defthm` count +38 (one per record), `assert-event` +5, SUSPECT 45 to
44.

Landed alone on `dev` as `ab8816e` (+ board `6dd10da`), merged `fed697f`,
before any of the work below.

## 2. Packet 1 — the fold's round trip

PLACEHOLDER-P1

## 3. Packet 2 — what the round trip unblocked

PLACEHOLDER-P2

## 4. Packet 3 — the §1.5 machine, named and not started

PLACEHOLDER-P3

## 5. Per-root table

PLACEHOLDER-TABLE

## 6. What the next lane should take

PLACEHOLDER-NEXT
