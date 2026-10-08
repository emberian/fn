# Catch-up carried transit: statements for Deputy S

Codex, lane `s-catchup-k`, 2026-10-08. Base: `f2629613ed5fed8084ab7e9b2d79c10dfb7c0dd9`.
Phase 1 only: these are proposed statements, not admitted events or certification.

The two durable transit calls can use `fn-oop-advance` with the same owner and
effects on the host's carried domain. K1 and K1-carry below state that contract.
**K2 is blocked as specified:** the existing advance has other size-dependent
work, and the cost generator cannot certify pointer identity at its node
comparison. A two-call-site replacement does not establish a total bound in
connection count alone. No implementation, proof, or new caller premise is
included in this change. Deputy S must resolve the K2 scope before Phase 2.

## K1: the host's owner and effects

Subject: `fn-oop-transit-outcome`, the configured projection of the host's
`fn-owner-transit-outcome`. Replace the existing theorem under the same name:

```lisp
(defthm fn-oop-transit-outcome-is-own-transit-outcome
  (implies
   (fn-ocl-relation oc)
   (and
    (equal (car (fn-oop-transit-outcome oc id kind reason word))
           (car (fn-own-transit-outcome
                 (fn-ocfg-owner oc) id kind reason word)))
    (equal (fn-ocfg-owner
            (cdr (fn-oop-transit-outcome oc id kind reason word)))
           (cdr (fn-own-transit-outcome
                 (fn-ocfg-owner oc) id kind reason word))))))
```

Subject: `fn-oct-transit`, the function actually called at
`host/owner-host.lisp:3483`. Its result is `((effects . oc) . pending)`, not
`(effects . oc)`. The feed table is inside that configured owner; the outer
cdr is the counted aggregate. This equality includes the whole owner,
including its feed table, for every `pending`, with no aggregate premise:

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

The conclusion is unchanged on every host state covered today by the carried
invariant. The new statement is logically conditional where today's theorem
is unconditional; it is not a claim of unconditional equality on corrupt
owners. It does not weaken the served contract because the caller already
carries the sole premise. The removal witness must demonstrate why equality
on arbitrary corrupt owners is deliberately not claimed.

Keep `fn-oct-transit-has-the-original-result` unconditional: changing both
advance calls together leaves its full configured-result equality intact.
Keep `fn-oct-transit-preserves-aggregate` with its existing premise and
conclusion; K1 does not replace the aggregate contract. The host's
`fn-oct-result` projection remains tied to that same result.

Caller audit at the base revision:

- `books/owner-host-relation.lisp:1028` already assumes `fn-ocl-relation`.
- `books/owner-host-relation.lisp:1087` assumes `fn-lgoc-invariantp`;
  `books/owner-log-ocl.lisp:233` includes `fn-ocl-relation`, and
  `fn-ohr-carried-implies-ocl-relation` at `owner-host-relation.lisp:474`
  states the discharge. No added premise is needed.
- `books/owner-host-relation.lisp:1070` (keeps-store) only assumes owner
  shape. Its hint at line 1078 DISABLES the old K1, rather than using it.
  Preserve this theorem by the structural store-frame argument; do not
  introduce a relation premise to this theorem.
- `host/interfaces.lisp:2092` currently has only `:class ::program`, no
  keystone citation. The brief's assertion that it already cites K1 is
  stale at this revision. Add the audited citations in Phase 2; do not
  invent an interface guard evaluating the relation.
- `host/owner-host.lisp:3473-3480` describes the uncounted projection.
  Update it to name `fn-oct-transit` and scope equivalence to the carried
  relation. This is an invariant carried through host transitions, not a
  runtime whole-state check or a theorem about arbitrary ACL2 global state.

No inspected consumer requires adding a hypothesis. The keeps-store theorem
must continue to work without using K1.

## K1-carry: the actual intermediate configured owners

Subjects: `fn-oop-transit-next` and `fn-oct-transit-next`, wrapped by the
actual `fn-ocfg-with-owner` used to construct `oc2`. State the full relation,
so the existing relation-to-acar lemmas and configured advance equivalence
apply directly. No well-formedness premise on `feeds`, `conn`, or `sub` is
needed: these transitions keep the fields read by the relation.

```lisp
(defthm fn-oop-transit-next-preserves-ocl-relation
  (implies
   (fn-ocl-relation oc)
   (fn-ocl-relation
    (fn-ocfg-with-owner
     oc (fn-oop-transit-next (fn-ocfg-owner oc)
                             id conn sub completion kind reason)))))

(defthm fn-oct-transit-next-preserves-ocl-relation
  (implies
   (fn-ocl-relation oc)
   (fn-ocl-relation
    (fn-ocfg-with-owner
     oc (fn-oct-transit-next (fn-ocfg-owner oc)
                             id conn sub completion kind reason feeds)))))
```

These preserve a substantive historical relation across real mutations:
pending/inflight, feeds, and refusal state change. They are not P implies P.
The store, view, connections, ledger field, clock, facts, configuration,
pins, and staged configuration remain the relation's same inputs. Existing
`fn-acar-ocl-relation-carries-conn-sessionp` and
`fn-acar-ocl-relation-carries-view-statep` then give both premises at `oc2`.
Use the existing `fn-ocmt-post-commit-preserves-ocl-relation` for the commit
preceding the host outcome, not an extra premise on the host keystone.

## K2: blocked bound and the required cost form

Intended subject: `fn-oop-advance`; this is the narrower choice allowed by
the brief. It covers the advance within both transit functions, not feed
enqueue, reply rendering, or all import work.

Three distinct obstructions prevent an honest concrete K2 statement today:

1. `books/owner-advance-carried.lisp:168-182` still calls
   `fn-nntp-nexts-boundedp`. Its recursive definition at
   `books/nntp-session.lisp:374` walks all group watermarks. Group count is
   independent of connection count; the relation does not bound one by the
   other. `books/owner-served-carried.lisp:21-34` also searches the store's
   group list for a selected group. These are real work even if a visit
   tariff happens not to charge every recursive cell operation.
2. `books/served-carried.lisp:37-39` uses `(equal node live)` before its
   fallback `fn-node-statep`. At this advance the rebuilt peer session holds
   the same node as `fn-acar-session-node conn`, so raw pointer identity
   avoids the fallback. But `books/def-cost.lisp:130` charges `equal` as
   `1 + acl2-count` of its first argument. Exposing this call in the derived
   cost therefore charges the node's archive even on the equal branch.
   The current generator has no contextual pointer-identity tariff.
3. `def-cost` uses the subject's guard for its bound, not an arbitrary
   invariant (`books/def-cost.lisp:660-666`). `fn-oop-advance` has guard t;
   arbitrary pin tables and identifiers are not bounded by its connection
   count. The pin-set loop is at `books/owner-config.lisp:138`. A conditional
   cost theorem needs the `defkeystone :visits` route described below.

Do not hide those costs in an opaque parent such as
`fn-acar-own-advance-result` or `fn-scar-auth-sessionp`. At
`books/def-cost.lisp:380-385`, an inlined wrapper with unknown descendants
collapses to the wrapper as an unaccounted leaf. Merely excluding the six
forbidden names from that top-level set can therefore conceal them.
Furthermore, `fn-cost-events-dimension` adds unaccounted terms to the emitted
bound at lines 642-644: a small declared `:visits` term alone is not a total
cost bound. Audit the expanded bound and descendant rows, not just the input
declaration. No derived set has been evaluated in this statements-only phase.

Proposed fallback schema (NOT an admissible event yet; uppercase constants
are unresolved design parameters, not established tariffs):

```lisp
(def-cost fn-oop-advance :unaccounted ())

;; On a defkeystone whose :subject is fn-oop-advance and whose sole
;; hypothesis is (fn-ocl-relation oc), attach:
:visits
((advance
  (fn-oop-advance-route-visits oc id)
  (+ *SCK-FIXED-VISITS*
     (* *SCK-PER-CONNECTION-VISITS*
        (len (fn-own-conns (fn-ocfg-owner oc)))))
  :not-attained "A conservative envelope; supply an attainment if tight."
  :derived-by fn-oop-advance))
```

The enclosing substantive equality would be the existing
`fn-oop-advance-is-ocfg-advance-under-ocl-relation`, registered with teeth.
`defkeystone` checks that the cost record is the subject's and that the
visit term calls its route twin (`books/defkeystone.lisp:118-134`). The
empty unaccounted set above is a required future closed derivation, not a
report of the current derived set. Its exact equality must be checked by
`def-cost`; neither whole-store recognizers nor opaque wrappers concealing
them may remain. No values for the constants are asserted in Phase 1.

This form solves only the missing invariant context. It cannot make the
watermark/group walks disappear or change the structural-equality tariff.
Recommendation to S: preserve K1's scope and resolve K2 by authorizing the
necessary carried summaries/representation and cost-generator work, or
explicitly revise the requested bound to name the independent profile
dimensions. A profile-dependent bound must not be reported as the requested
connection-only K2. Do not add undischargeable caller hypotheses, hard-code
group limits, register zero-cost wrappers, or weaken a cost ratchet.

## Teeth plan

Register K1 with `defkeystone` (or the identical theorem plus `defteeth`),
`:subject fn-oop-transit-outcome` / `fn-oct-transit`, and one hypothesis
label `ocl`. Each witness must check the complete antecedent AND both
equalities; checking an implication alone is insufficient.

Positive fixture: build a small configured owner by composing the historical
configured-owner setup in `tests/acl2/owner-host-relation-tests.lisp:118-150`
with the real peer open / IHAVE / article / take sequence in
`tests/acl2/transit-same-decision-tests.lisp:91-120`. Use the former's store
event and commit recipe for the transit submission. Check the relation at
the input, non-nil named connection, matching inflight id, transit-subp,
kind `:want`, completion `:durable`, the advanced connection/version and pin,
and both K1 equalities. Supply a numeric pending aggregate and check the
counted entry's feed-table guards under ordinary guard checking.

The existing `*ohrt-b9*` transit assertion is explicitly an absent-branch
witness (`owner-host-relation-tests.lisp:176-183`), not this positive tooth.
The proposed composed fixture must be executed after GO; it is not yet a
demonstrated reachable durable transit. Do not simply relabel its POST
submission and call that a reachable transit.

Removal tooth for the sole K1 premise `ocl`: keep that durable transit's
trigger and store intact, but insert a non-article into its view archive,
following `tests/acl2/owner-advance-carried-tests.lisp:100-147`. Explicitly
assert `(not (fn-ocl-relation oc))` AND failure of the conjunction of K1's
two equalities. The expected divergence is the rebuilt session's projected
flag and therefore the owner; effects can still agree. Also exercise the
independent bad-session construction from that file's lines 169-192:
reference advance refuses, carried advance accepts. These are labelled
corrupted-state removals; use `:logical` only if an actual guard prevents
evaluation, with the specific reason recorded. Run both removals for the
counted and uncounted subjects, preserving the counted feed-table guards.

K1-carry teeth: reuse the positive input and the actual intermediate values.
For each single `ocl` premise, the corrupted view remains corrupted after
the corresponding `transit-next`, so both the omitted premise and the
conclusion are false. Mutate the output pin behavior (old pins retained
after advance) using the existing generation-2 to generation-3 scenario;
the output relation must fail. Do not count proof-search failure as a tooth.

Cost tooth: derive a reference row for `fn-own-advance-result`, expanding
descendant rows far enough to expose `fn-own-conn-boundedp` /
`fn-auth-sessionp` / `fn-peer-sessionp` / `fn-node-statep` and
`fn-nntp-open-session` / `fn-nntp-projectionp` / `fn-statep`. Assert from the
world's actual cost rows that the reference's derived unaccounted/visit
dependencies contain `fn-node-statep` or `fn-statep`. Pair it with the
carried subject's exact derived set excluding all of `fn-statep`,
`fn-node-statep`, `fn-nntp-projectionp`, `fn-peer-sessionp`,
`fn-own-conn-boundedp`, and `fn-articles-freshp`, checking opaque descendants
as well. A source grep or a hand-written dependency list is not this tooth.

## Phase boundary and gates

Stop for Deputy S's audit after committing this named note. Phase 2 remains
unauthorized until GO. K2 and the executable durable fixture are outstanding;
no caller-premise blocker was found. No ACL2 session, certification, host
load, interface generation, or keystone generation was run for this note.
The only applicable Phase 1 gates are the named-file secrets check and
`git diff --check`; their exact outputs are reported with the commit.
