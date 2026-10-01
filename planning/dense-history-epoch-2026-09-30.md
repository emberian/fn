# Dense all-event history: execution contract

Status: architectural handoff ratified by the active coordinator on 2026-09-30.
This document describes new interfaces to implement, not already installed
authority, certification, a qualified image, or a deployment. Source inspected:
`a7d460d04` in `build/lanes/batch-be`. The coordinator assigned Sol execution
after this architectural synthesis. No new requirement or proof ID is claimed
by this design document; implementers claim IDs before registry changes.

## Selected representation and semantic boundary

Use an independent append-only **history epoch**, containing fixed pages of
256 event references and a persistent binary forest of page descriptors.
Every committed Store event appears at its dense ordinal, including policy,
withdrawal, retention, identity, topic, consumer and configuration events.
Preserve the exact event value, including NIL where the logical history allows
it. The success word distinguishes a NIL record from an unavailable record.

The abstraction is the existing oldest-first history list:

```
alpha(source, backing) = the first source.F events of its forest's pages
alpha(current-source, backing) = fn-sf-records(fn-sn-files(actual-store))
```

Thus count is `fn-hist$a-count`, ordinal lookup is `fn-hist$a-at`, and one
committed append is `fn-hist$a-append` in `books/history-columns.lisp`.
Catalog count C is unrelated to this dense index F. Catalog rows, local
article numbers, Store allocator frontier and event ordinal are different
coordinates. In particular, never derive F from Pub19 count or from its
largest article sequence. The Store event count is the authoritative F.

`fn-hist$c-grow`, hash-table insertion/rehash, and clear/resize in the old
FnHIST implementation are outside this bounded representation. Adding a
bounded scanner while continuing to call those operations does not implement
bounded publication.

## Exact source and owner association

Introduce `fn-history-backing`, with fields for an installed source,
registered physical provider/epoch records, and a private builder. These
fields are internal; there is no host setter for a source or page root.
Existing custody work owns the single serialized capture in actual STATE.

Source9, retained as an actual object inside the owner:

```
(:history-source source-id epoch root-id forest max-height page-count F
                 owner-publication-id)
```

`source-id`, concrete `epoch`, `root-id` and `owner-publication-id` are fixed
identity fields. The concrete epoch is a positive source-owned allocation
identity. It is bound in the registered epoch row to the canonical Store
history/incarnation; those semantic IDs are not confused with its physical
nonce. Epoch zero means an uninitialized physical page, never a live epoch.
`forest` is the actual immutable directory pointer, not a reconstructed copy.
For a committed nonempty source, page-count is `ceiling(F/256)`; empty is
F=0, page-count=0, forest=NIL. Max-height is carried by the builder, never
recomputed by a served tree walk. Shape recognition does not validate content.

The new STATE global `fn-owner-history-publication` is exactly:

```
(:history-installed source-id epoch root-id owner-publication-id canonical-owner-epoch)
```

The final field is read from `fn-owner-canonical-epoch` at the actual
installation and checked against that current owner value by the getter.
This prevents an old backing plus matching old association from surviving an
independent canonical reset. Source9 remains unchanged. It is installed with
the actual Store/CP/config/publication transition. A
C-only publication can change source-id and owner-publication-id with the
same F, forest and root-id. A within-page append changes F and source-id but
can retain root-id. A new page obtains a newly issued root identity.

Proposed exact APIs (not currently sanctioned exports):

```
(fn-hep-current fn-history-backing) -> Source9
(fn-owner-history-source fn-history-backing state) -> (mv word Source9)
(fn-owner-history-read-begin token ordinal fn-history-backing state)
  -> (mv word state)
(fn-owner-history-read-step fuel fn-history-backing state)
  -> (mv word row fuel-left state)
```

`fn-hep-current` reads the installed object. The owner getter compares its
four source association fields and actual canonical owner epoch with STATE and returns `:source` and
that exact object, `:unavailable` when uninstalled, or `:recovery-required`
on disagreement. It never derives an installed source from a caller tuple,
FnHIST count, Pub19, a ready flag, or a shaped runtime token.

The custody lane's public descriptor is fixed6:

```
(:history-prefix typed-PRS-token canonical-epoch F source-id root-id)
```

Its registered STATE slot separately retains the actual Source9 pointer and
its shared-pool grant. Begin takes only a token and ordinal, gets Source9
from that slot, and requires ordinal<F. The read continuation lives in a
separate `fn-owner-history-read` STATE slot. Each step checks the active
custody identity and registered epoch before its bounded action. Append in
the same epoch does not stale an earlier captured source merely because the
current source/root/publication changed. Account, READ and semantic-view
revalidation remain the remote scanner's separate obligations.

## Fixed event page: handed to history_event_page

New `fn-history-event-page` fields: event references array `t(256)`, positive
epoch or virgin zero, positive page-id or virgin zero, natural incarnation,
natural base ordinal, and committed count in 0..256. No array resizes.

```
(fn-hec-initialize epoch page-id incarnation base page)
  -> (mv :initialized/:stale page)
(fn-hec-append epoch page-id incarnation expected event page)
  -> (mv :appended/:stale/:full page)
(fn-hec-read epoch page-id incarnation slot captured-count page)
  -> (mv :row/:stale/:range row)
```

Initialize is internal, only on a virgin page (epoch=0 and committed=0),
with positive epoch/page-id issued by actual allocation. Append requires
matching stamps, expected=committed<256, writes precisely one reference and
increments committed. No event traversal, hash, held-article conversion, or
event equality occurs. Read requires matching positive stamps and
slot<captured-count<=committed<=256; `:row NIL` is a successful NIL event.
The owner derives captured-count as `min(256,F-base)` for the selected page.
Old slots never change. A page's committed count may increase while an old
capture reads its smaller prefix.

The leaf arguments are internal operands derived from registered source and
page ownership. Leaf shape/stamp checks are not construction or publication
authority. Reuse after retirement requires the separate joined physical
restamp operation; initialize cannot rebind an empty live page.

## Persistent forest: no directory resize or per-publication retain walk

Do not wrap `fn-ibp-directory-step`'s existing least-significant-bit tree in
a new root: that changes the address interpretation. Reuse fixed-page and
allocation mechanisms only where their domain and ownership agree. The new
directory is deliberately a different immutable family.

A forest is a newest-first list of blocks with strictly increasing widths:

```
(:history-block width height tree)
(:history-leaf physical-slot page-id incarnation epoch base)
(:history-branch older-tree newer-tree)
```

Width=2^height is a carried invariant, not a served exponentiation check.
Each tree's leaves are chronological. For example, seven pages have blocks
of widths 1,2,4 holding respectively pages 6; 4..5; 0..3. All pointers are
immutable. Published page *prefixes* are immutable even while their tail
page's committed count grows.

New-page directory APIs, internal to the funded builder:

```
(fn-hed-grow-begin forest page-count max-height leaf) -> cursor
(fn-hed-grow-step cursor) -> cursor
(fn-hed-read-begin forest page-count ordinal) -> cursor
(fn-hed-read-step cursor) -> (mv word cursor descriptor)
```

Grow starts with carry=(width1,height0,newleaf), the old forest, and a
carried max-height. One step does exactly one of these:

1. If the forest head has the carry width, allocate one fixed branch with
   head.tree older and carry.tree newer, double width, increment height,
   pop that forest cell, and yield with this carry.
2. If the head width is larger, or the forest is empty, allocate one block
   and one forest cons with the carry and finish. Preserve the old tail by
   reference. A smaller head is a corrupted carried state, not a restart.

Every allocating step first consumes the actual registered operation's
adequate allowance. An allocation failure retains its receipt and cursor;
it does not issue another identity or install a partial root. Root-id is
issued by the real allocator, not by taking max-height or page-count.
All carries/frames are fixed tuples; there is no recursive merge to closure.

For N appended pages there are N leaves, fewer than N merge branches, and
N final block/forest cells. Even retaining all historical forest metadata
until epoch retirement is O(N) space. A single append may take O(log N)
steps, each fixed allocation/work; normal within-page append needs no
directory change. This is stronger than amortized resize: no individual
step copies the old directory. It does not assert a measured throughput.

Read uses page-index=floor(ordinal/256) and
from-end=page-count-1-page-index. One forest step either subtracts one
block width and moves to its tail, or selects the block. Convert to its
chronological offset `width-1-from-end`; one branch step halves the carried
width and chooses older/newer, subtracting the half in the newer branch.
The cursor retains its exact subtree pointer and offsets across yields.
At a leaf, require the expected epoch and base=256*page-index, then perform
the separately funded physical lookup and `fn-hec-read`. The descriptor is
returned only internally. Neither NIL content nor NIL forest is a gap signal.

Directory height greater than one scheduling quantum is therefore resumable.
The physical nested-stobj provider is a separate concern: its existing
full-depth routines preflight `depth+1` and cannot pretend to retain a child
cursor. Its installed profile must admit that atomic traversal envelope
within the selected scheduler quantum, or it needs a separately proved
resumable physical-address representation. A directory continuation alone
does not discharge this. Supported profile validation must cover address and
counter codecs, runtime representation and that envelope; 256 is a page
format, never the maximum stored event count.

## Same-row private candidate and atomic publication

The snapshot lane's current producer is `fn-ssrp-intern-row`, returning the
SAME interned row in MV8, and `fn-crp-produced-event`, retaining the SAME
produced6 packet across callbacks in MV7. Preserve those objects and
ORIGINAL context/fields; never synthesize an event from a catalog row.
The exact event is the separate MV6 position of `fn-ssrp-intern-row`'s MV8.
Produced6 contains checked ORIGINAL context, next fields, status, effect,
child and sizes; it does **not** contain the event. A `:none` child can be
NIL, and a `:verdict` child is a verdict rather than the composite event.

The builder holds the exact candidate event reference plus its old installed
source and producer/completion identity. Its private candidate-prefix reader
answers ordinal=oldF from that reference, and lower ordinals from the old
source. Its logical prefix is `append(alpha(old),list(event))`. This makes
the current E available to historical control decisions while the external
source remains at oldF. It does not prepublish an event-page slot or increment
committed count. Reject another builder/candidate while this one is live.

The exact new internal builder ABI is:

```
(fn-hep-offer-produced row produced6 original-context original-fields
                      producer-token fn-history-backing)
  -> (mv word fn-history-backing)
(fn-hep-builder-step fuel fn-history-backing fn-page-read-pool)
  -> (mv word fuel-left fn-history-backing fn-page-read-pool)
(fn-hep-builder-readout fn-history-backing)
  -> (mv word row produced6 original-context original-fields)
(fn-hep-candidate-read-begin ordinal fn-history-backing)
  -> (mv word fn-history-backing)
(fn-hep-candidate-read-step fuel fn-history-backing)
  -> (mv word row fuel-left fn-history-backing)
```

Offer consumes only the actual producer's registered current operation and
empty builder; its inputs are lexical results of the actual owner producer,
not host-supplied packets. It returns `:offered`, or `:busy` without replacing
a live candidate. Step returns `:yield`, `:prepared`, `:unavailable` or
`:recovery-required`, retaining its current issued receipts across yields.
Readout returns the SAME row/packet/context/fields; `:prepared` requires the
actual page, directory and reservation phases, not a caller boolean.
Candidate reads use the registered builder's event and old source, with
`:row` including NIL. These helpers add no public allocation authority.
The snapshot/backing owners agree on the existing producer-token accessor;
an absent current producer registration remains unavailable.

Prepare all needed page construction, forest growth, controller/frame
allowance and root/page custody before durable acceptance. On the actual
successful transition, one serialized owner completion performs the exact
leaf append, installs the prepared directory/source F+1, and installs the
corresponding full Store/CP7/root4/fence/config state. No observer runs
between these updates. The full result/effect theorem covers their combined
operation; a theorem about the leaf alone cannot authorize this boundary.
Only actual owner completion is allowed to call the internal
`fn-hep-publish-current`; it accepts no host-supplied root/count/ready flag.

Repeated callback after a yield resumes the same private packet and builder.
Once published, the completion identity prevents a second append. Definite
precommit refusal leaves installed source unchanged and enters joined
candidate cleanup. An ambiguous durable completion is a recovery event,
never a refused append followed by further mutation. The pages are an
in-memory representation; process death recovers them from the authoritative
committed Store, not from the fact that a page write happened.

## Epoch custody, reset and bounded retirement

An epoch owns each page and every directory allocation exactly once. New
source publication transfers the current epoch reference, not references to
every older page. A capture adds one registered epoch reference plus its
source/cursor allocation debt. An active candidate has a writer reference.
The epoch row binds canonical history/incarnation, concrete allocation ID,
phase, current/readers/writers, actual page allocation inventory and charges.

The initial custody lane supports one serialized active capture and refuses
reset/recovery/import with `:history-source-held` while it exists. It does
not hold that capture through indefinite WAIT: clear scanner/cursor/borrow,
then retire, then reacquire a current source for the next poll. This is a
complete initial reset fence, not an assumption that no old reader exists.

`fn-hep-reset-begin/step` build a separately funded new epoch. Installation
joins the actual reset/Store transition after its custody gate. Old epoch
becomes retiring; never clear its global array, map or tree. Once its current,
reader, writer, callback and raw-borrow references have all been relinquished,
retirement consumes a concrete allocation inventory one fixed object/page
action at a time. The inventory itself must be an incrementally grown fixed
record family, not a resizable vector or a final list of all reachable pages.
It can record one fixed handle cons per allocation under the same allowance.
It releases each allocation once; shared trees are never recursively freed
once per historical source. If the runtime requires clearing reference slots,
clear a bounded span before dropping the page. Parent inventory references,
cursor frames and temporary roots remain charged until their own final use.

PRS `fn-prs-issue` and `fn-iqr-promoted-ledger` are accounting primitives,
not a qualified constructor issuer. Existing index page reservation13 and
page-owner records demonstrate once-only current custody but accept only
their existing families. An event family requires explicit operation demand,
selected-unit constructor/lifetime receipt and source-owned registration;
do not just add `:events` to a tag recognizer. No genuine installed constructor
grant was present at inspection, so public startup remains unavailable until
that actual proof/runtime boundary exists.

## Served migration and remaining lookup semantics

The bounded owner mode replaces the actual `fn-crp-append` path used by
`fn-crp-produced-event`. It does not update both new backing and legacy
FnHIST. `fn-hist-append`, `fn-hist-sync`, `fn-hist-load`, hash rehash and
whole-array clear cannot run anywhere in that bounded publication call graph.
Recovery populates the new builder incrementally from the decoded all-event
producer and installs a source only at the successful Store-open boundary.

Existing synchronous `fn-hist-msgid-records` callers also need conversion.
Use a private yielding oldest-first history fold, exposing at most one exact
matching record per result, with matching itself resumable by field/string
fragment. Carry the accepted event domain rather than rerunning arbitrary
whole-record recognizers. The logical result is
`fn-cei-article-records-for(msgid,alpha(source))`; callers that need a
predicate/fold consume that stream instead of allocating a complete list.
This initial rare-control operation costs Theta(F) records, explicitly.
It is bounded per step, not a high-throughput indexed-lookup claim.

Pub19 remains the independent fast current-article lookup. Mapping its
candidate to historical events would need a named correspondence about exact
retained event ordinals and original event values, including withdrawal and
reclamation; no such equality follows from a catalog ordinal or count.
An unmigrated history/control entry is unavailable in bounded mode before
mutation. Legacy mode may remain for separate existing evidence but is not
silently selected as a fallback and carries no new boundedness claim.

## Proof and execution handoff

The leaf execution lane owns guards and literal witnesses for actual
initialize/append/read: exact appended value, all prior slots unchanged,
positive NIL/nonarticle/withdrawal cases, stamp replay and full-page refusal.
The directory executor owns chronological flatten/grow equality, exact
ordinal selection, cursor progress and a literal multi-step carry at page
counts 1,3,7 plus old-root reads after growth. Tests of a toy twin do not
establish the real selector; the theorems name these actual kernels.

The combined host-boundary keystones to implement are:

- `fn-owner-history-read-step-is-hist-at`: under established source/content
  and retained-custody invariants, `:row` returns exactly `fn-hist$a-at` at
  the captured ordinal, including NIL, and preserves the complete owner
  state/effect abstraction except the named read continuation.
- `fn-owner-history-publish-refines-hist-append`: the actual same-row
  owner completion refines append and its full Store/CP/config/source
  result/effects; other outcomes retain the old committed prefix.
- `fn-owner-history-append-preserves-captured-prefix`: later same-epoch
  appends preserve every event below captured F, with the actual forest,
  pages and source/epoch custody, not a supplied prefix assumption alone.
- `fn-owner-history-reset-keeps-retained-custody`: reset refuses while the
  initial active capture exists; joined retirement releases no reachable
  page or unresolved allocation debt.

All are proposed names/statements, not admitted theorems. Provide complete
antecedent/conclusion witnesses and hypothesis-removal witnesses for each
literal keystone; distinguish corruption/mutation tests. The combined
abstraction and lifetime invariant is carried from actual recovery/creation
through every producer, not checked by a whole-state walk per request.

Ownership: `history_event_page` executes the fixed page; `history_record_cursor`
owns STATE custody/source getter/reset/read dispatch; `sol_snapshot_open`
owns candidate/read and actual producer/publication replacement;
`sol_remote_endpoint` consumes exact `:row` values through its bounded scan;
physical/allocator owners supply genuine construction and settlement. The
coordinator assigned `allocation_turn_receipts` to the forest cursor and its
actual physical source/lifetime adapter in new
`books/history-event-directory.lisp` and `books/history-event-backing.lisp`.
That lane owns the single canonical `fn-history-backing` definition, its
`fn-hep-installed-source` field and `fn-hep-current` accessor; the custody lane
includes it rather than defining another stobj. The coordinator's runner
alone integrates.

Validation for this artifact: source/API inspection and `git diff --check`.
No ACL2 invocation, source certification, native image, throughput measurement
or deployment was performed by this architecture lane.
