# X3 — diagnosis complete; STOP, no book repair

At lane HEAD 5fe2f59430c6a1d37bd6b020360177d0120e9546, the catalog-paged refusal
is caused by **shared codec runes stripped by history-columns' structural
export, then left disabled by redundant dependency includes**. It is not the
CREATE-FN-HIST executable counterpart and not a changed generated theorem.

Three runes used by dev's certificate differ at the failing event:

| Rune | Dev at FN-CROW$C-TW-TREE-IS-CPUTS | Lane | Lane status-setting event | Original declaration |
| --- | --- | --- | --- | --- |
| (:EXECUTABLE-COUNTERPART FN-SCC-OCTETS-VALUEP) | enabled | disabled | books/history-columns.lisp:182, final structural IN-THEORY | books/store-tree-codec.lisp:331 |
| (:EXECUTABLE-COUNTERPART FN-SCC-LE-DIGITS) | enabled | disabled | books/history-columns.lisp:182, same event | books/store-tree-codec.lisp:113 |
| (:TYPE-PRESCRIPTION FN-SCC-OCTETS-VALUEP) | enabled | disabled | books/history-columns.lisp:182, same event | books/store-tree-codec.lisp:331 |

A session-only LOCAL control restoring these three, with the unchanged
original generated theorem/hints and original local scopes, passes and uses
**exactly dev's 28-rule Rules set**. No repair was made in any project book.
The proof is a diagnostic control, not certification or a proposal to ship
that LOCAL scope. The seat brings the source decision to main.

## Dev comparison and precise measurement

The seat's record #4, run-20261013T232640Z-6076, logs
build/acl2/certify-20261013T232739Z-4123336, reports 1336 books, one REAL
catalog-paged refusal and 307 cascades. All six direct-history-columns books
and the owner test certified. This supersedes the prior cache-frontier STOP.
Triage: triage-6076.txt; reported checkpoint is Subgoal *1/3.18'' with
ADT-PG-CPUT 0 versus ADT-PG-CPUTS of FN-SCC-PROGRAM NIL.

Dev's exact certificate Rules list was read by the fetch-dev method from:
`/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T093213Z-3279561/books--catalog-paged.certify.log`.
The event's dev certificate proof takes 30,970 steps. Rules, Hint-events and
source theorem are saved in x3-dev-rules.log / x3-dev-target-source.log.
Its functional-instance hint is ADT-H-TW-TREE-IS-PUTS, emitted by
books/def-representation.lisp:1825–1832.

Fresh x3-catalog-lane loaded the current certified closure and the original
catalog-paged prefix. The attempt reproduced the failing generated scope
(top-level form #15), rolled it back, and left 14 original source forms loaded.
x3-catalog-dev started at #1 with zero source forms, then admitted the exact
dev prefix through #14 against certified dependencies.

The generator's full def-representation expansion was evaluated in both
worlds and is **byte-identical** (x3-generator-identity.txt). A diagnostic
prefix retained the exact original outer LOCAL scaffolding at catalog-paged:94–100,
all original generated events/scopes up to the target, and captured the theory
immediately before the target rather than asserting a repaired theorem.
Both prefixes pass; their raw enabled/universal sets are in
x3-lane-at-event.log / x3-dev-at-event.log. This measurement includes generated
LOCAL theory effects, not just the theory before the macro.

At the event there are **22,036 common runes, 688 enabled only in dev and
10 enabled only in the lane**. The complete difference is retained in
x3-at-event-diff.json / .txt, not reduced to three runes. Among the 28 runes
actually used by dev's proof, **exactly the three in the table differ**.
All 28 statuses are in x3-dev-rules-statuses.json.
Related FN-SCC-PROGRAM and FN-SCC-REPEAT executable counterparts are also
lane-disabled/dev-enabled, but the three-rune control suffices for this event;
no claim that all 688 differences are harmless is made.

The lane-only enabled common set contains the eight octet/buffer runes restored
by X plus the CREATE-FN-ARENA / CREATE-FN-HIST executable counterparts. None
of those ten is used by dev's target proof. The diagnostic control leaves
that set untouched, so the creator residual is not the obstruction.

## The source event and include mechanism

For every causal rune, the measured lane enabled-membership sequence is:

```text
fn-hist-theory-before-paged baseline: NIL (not introduced in that baseline)
current theory after history-paged: T
current theory at fn-hist-msgid-records-serve-cei, before final export: T
catalog-paged world after the includes: NIL
```

x3-export-transition.log records all three, plus the related PROGRAM/REPEAT
counterparts and the creator. The setter is the NON-LOCAL final IN-THEORY at
history-columns:182: it unions the enabled baseline with the own-event delta
obtained by subtracting fn-hist-theory-after-paged's universal snapshot.
The codec runes are absent from the baseline and belong to the subtracted
implementation dependency set. They are therefore disabled at this event.
Expanded source event evidence: x3-lane-first-include-pcb.log.

First introduction in the lane, confirmed by :pe:

`catalog-paged:54 → catalog-logic:64 → msgid-linear-exec:67 → msgid-linear:67 →
msgid-pages:46 → history-columns:8 → history-paged:6 → history-pages-resident:6 →
history-pages-placed:13 → history-pages-write-keys:17 → history-pages-write-exec:7 →
history-pages-write:14 → history-pages-read:16 → history-pages-row:6 →
history-pages-exec:4 → history-pages:40 → store-checkpoint-buffer:46 →
store-checkpoint-codec:31 → store-tree-codec`.
(All unprefixed names here are books/<name>.lisp.)

In dev the codec is first introduced later:
`catalog-paged:61 → def-representation-tree:24 →
def-representation-tree-walk:35 → store-checkpoint-buffer:46 →
store-checkpoint-codec:31 → store-tree-codec`.
Normal codec admission enables its counterparts/type-prescriptions. In the
lane, that later store-checkpoint-buffer include is redundant: its book has
already been introduced through history-columns and its shared runes stripped.
A redundant include does not recreate their former enabled status.
The explicit catalog-paged store-checkpoint-buffer include at lane :69 is
already redundant in dev too, because the tree dependency introduced it first.
Deleting that later include alone cannot repair this status difference.

:pe/disabledp introduction and status evidence:
x3-lane-status-before-generator.log, x3-dev-status-before-generator.log,
x3-lane-program-before-generator.log. The same source LOCAL disables in
catalog-paged:98 and def-representation-tree-walk:49 are present in both
worlds; the at-event capture measures their actual effects. They do not
account for the lane/dev difference in the three counterparts/type rules.

The catalog-paged diff against origin/dev changes comments and removes
`:attachable t` from its final defabsstobj, AFTER the failing event. Its include
order is unchanged. Catalog-logic differs only in two one-world comments.
The inspected def-representation-* files have no include or executable-code
difference; only def-representation's one-world comment changed. Complete
source comparisons: x3-catalog-source.diff / x3-generators-source.diff.
The identical generated expansion independently checks this candidate.

## Why the exporter diff did not predict this

All three causal runes are in **lane_only_world**, not the common set, in
x2-columns-lane-PUBLIC-diff.json. Dev's history-columns world did not contain
the tree codec; one-world's history-paged include introduces it early.
The public-export comparison correctly found zero unexpected differences
on its common runes, but it did not establish equivalence of subsequent
include behavior for newly present, disabled shared runes.

Later def-representation-tree joins the codec into dev's world, making these
runes common in the consumer world. They enter enabled in dev and remain
disabled in the lane. That is why a larger consumer-world common set reveals
the gap that the exporter-world intersection did not test. X is dropping
shared dependency theory that dev introduces LATER, not theory that dev's
history-columns itself formerly exported through history-paged.

The raw pre-filter eight-rune columns diagnostic discussed in ROUNDX.md is a
different direction of effect: those common octet rules were restored by X.
It did not measure the newly introduced codec runes' later redundant includes.

## Faithful diagnostic control and proposed structural fix

Fresh x3-catalog-control loaded exactly 14 original source forms. Its control
replayed the exact original local scaffolding and generated prefix, then
inside those scopes enabled only the three tabled runes LOCALly and attempted
the unchanged original target. It passed in 23,783 steps / 0.06 ACL2 seconds;
its Rules set is exactly the dev certificate's 28-rule set. Source/hints and
guards were not edited. This is a sufficient diagnostic set, not a claim
that all three are individually necessary (no hypothesis/removal claim).

Artifacts: x3-faithful-control.lisp / .log, x3-control-rules-comparison.json.
An earlier exploratory control ran after leaving the prefix scopes; the
faithful control supersedes that control as the causality evidence.
This proves no property of the whole currently refused book or its certificate.

**Proposed source fix, not made:** treat the shared codec dependency separately
from implementation-private dependencies at the history-columns exporter.
Preinclude `store-checkpoint-buffer` (the normal shared codec dependency used
by def-representation-tree-walk) before fn-hist-theory-before-paged's enabled
snapshot, analogous to f7760ab8c's shared-book staging in store-records-field.
Its ordinary exported theory, including the codec counterparts and type rules,
then belongs to the preserved baseline; the later history-paged universal
snapshot still hides the implementation-private rules. Do not append a list
of the three runes to the exporter. Verify public common-rune equality and,
critically, the full theory after the later generator dependency includes.
This proposal is not a certified source fix and may need a broader shared
book partition if the remaining 688/10 consumer-world differences matter.

The history-paged include itself is required before attach-stobj by OW1;
deleting it is not the proposed fix. Deleting catalog-paged:69 alone leaves
the offending earlier import/disable unchanged. A LOCAL generated-event repair
is the measured last-resort alternative for the seat to take to main, not a
change made here.

The stronger future exporter check is composition with subsequently included
shared dependencies, alongside the raw world-only rune inventory. Common-rune
intersection equality at the exporter alone cannot establish that contract.

## Shutdown and scope

All three sessions are stopped by name: x3-catalog-lane, x3-catalog-dev,
x3-catalog-control. All end queries/assertions return NIL / PASSED for
illegal-to-certify; these are diagnostic worlds, not whole-book certification.
The lane's initial load reproduced the unmodified failure; both at-event
prefix captures and the final diagnostic control have zero refused events.
No source fix, new book repair, commit, push, box certify or full suite was run.
Git status remains clean at 5fe2f5943; only allowed report/evidence files were
written under build/vertical-runs/one-world/. Diagnosis complete; STOP.
