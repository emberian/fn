# X4 measurements; X5 candidate awaiting certify of record #5
Current disposition: the X5 enabled-snapshot union is implemented and its five
static gates pass. See **X5 candidate** below. The following X4 measurements
cover the earlier bytes and are retained as diagnosis, not X5 evidence.

The seat certified books/history-columns and books/store-records-field at the
X4 bytes in run-20261014T002841Z-3c6c, manifest
build/acl2/certify-20261014T002940Z-260113 (142 cached books, two roots passed).
The fresh certified history-columns comparison **does not meet condition (a)**:
13,317 common runes, **8 dev-only enabled / 1 lane-only enabled**. The latter
is the accepted CREATE-FN-HIST executable counterpart; the eight are unexpected.
No repair was made after this measurement.

Condition (b) cannot yet be captured from certified lane dependencies:
proof_repl's cached-only start refused seven missing current-closure certificates
before creating a live session. The exact names are below. No X4 consumer-world
counts or target proof result are claimed. The old 688 / 10 result is X3 only.
All five static gates pass. No commits; every started session is stopped.

## (a) Certified public export and mechanism

Sessions **x4m-columns-lane** and **x4m-columns-dev** each loaded zero source
forms and included the certified foundation, then certified history-columns.
The lane target was installed from a current cache artifact set
7330c2e45881fe007b587d1a1667688f92adeef3dfd25b433fcd25a62e23f6d7;
its include passed without an uncertified-book warning. Dev uses the existing
dev-reference tree and its certified cache artifacts. No source replay or
certify fallback was used. Both captures have zero refused events and finish
with (@ illegal-to-certify-message) = NIL plus its successful assert-event.
Both exact-name stop logs confirm shutdown.

The full raw sets and difference are retained in x4m-columns-{lane,dev}-runes.log
and x4m-columns-lane-PUBLIC-diff.json / .txt. All common runes are compared:
no rune list or proof-used-only filter selects the measurement. Dev-only world
count is zero; lane-only world count is 4,774 (not common-rune status differences).

| Unexpected dev-only enabled common rune | NON-LOCAL disable in books/pagestore-words.lisp |
| --- | ---: |
| `(:DEFINITION FN-CBOR-OCTET-LISTP)` | 379 |
| `(:DEFINITION FN-OCTETS$C-BUFP)` | 243 |
| `(:INDUCTION FN-CBOR-OCTET-LISTP)` | 379 |
| `(:INDUCTION FN-OCTETS$C-BUFP)` | 243 |
| `(:REWRITE FN-OCT-BUFP-CELL-IS-OCTET . 2)` | 243 |
| `(:REWRITE FN-OCT-BUFP-CELL-IS-OCTET . 3)` | 243 |
| `(:REWRITE FN-OCT-BUFP-OF-RESIZE-LIST)` | 243 |
| `(:REWRITE FN-OCT-BUFP-OF-UPDATE-NTH)` | 243 |

The accepted lane-only common residual is
`(:EXECUTABLE-COUNTERPART CREATE-FN-HIST)`.

Measured membership of **each of the eight**, from the same certified include:
foundation enabled = T; saved fn-hist-theory-before-paged enabled = NIL;
pre-export enabled = NIL; public enabled = NIL; dev public enabled = T.
The complete per-rune table is x4m-export-statuses.json. Thus the disables
already enter the saved baseline at books/history-columns.lisp:10, following
the new shared include at :8; the final structural IN-THEORY at :185 preserves
them. This is not a private-rune subtraction failure.

The literal ordered include graph gives the first introduction path:
history-columns:8 → history-records:49 → history-pages-import:15 →
history-pages-step:31 → history-pages-grow-then-append:15 →
history-pages-relocate:4 → history-pages-grow:12 → history-pages-placed-write:13 →
history-pages-nest:5 → history-pages-placed:13 → history-pages-write-keys:17 →
history-pages-write-exec:7 → history-pages-write:14 → history-pages-read:16 →
history-pages-row:6 → history-pages-exec:4 → history-pages:42 →
pagestore-words-blake3:31 → pagestore-words.
All unprefixed names are books/<name>.lisp. The path is graph-derived, not an
ACL2 event trace; the certified saved-snapshot membership establishes its effect.
Exact path edges and counts are in x4m-measurement-summary.json.

pagestore-words:243 disables the buffer recognizer and concrete-array rules;
:379 disables the CBOR octet-list recognizer. Both are NON-LOCAL. Preincluding
a SHARED closure preserves its ordinary theory, but that ordinary theory can
turn off runes inherited from the original foundation. The graph partition
alone does not preserve the old enabled baseline. These eight were previously
lane-only enabled at the X3 consumer event; they are now dev-only enabled in
the exporter comparison. None is in the dev certificate's 28 Rules for
FN-CROW$C-TW-TREE-IS-CPUTS (x3-dev-rules.log / statuses.json). That observation
does not substitute for the new consumer-world comparison or proof.

A structural next candidate, **not implemented**, is to snapshot the enabled
foundation before the SHARED frontier, then build the preserved baseline as
the union of that enabled snapshot and the post-SHARED enabled snapshot. Both
inputs would be enabled theories; the existing universal boundary would still
serve subtraction only. This addresses the measured eight by general snapshot
structure, without rune-name lists. Its full exporter and consumer composition
would still need certification and measurement; no green is predicted here.
Deleting history-records would also undo the required shared partition, so
that include is not a redundant-include deletion candidate.

## (b) Consumer-world composition: certificate STOP

Attempt: x4m-catalog-lane, books/catalog-paged, cached-only, --upto '#15'.
The intended method is unchanged: load the original prefix through #14 from
certified dependencies, then replay x3-at-event-prefix.lisp with the exact
original LOCAL scopes/generated prefix and capture inside the target event's
world. No repair or target change is involved.

The start exited 1 before loading forms or creating a live session. It names:

- books/msgid-pages (first missing closure key, source SHA prefix 9188b58bbed301cd)
- books/msgid-pages-exec
- books/msgid-linear
- books/msgid-linear-exec
- books/msgid-tag-exec
- books/catalog-logic
- books/catalog-live-links

The seat must certify these seven at the X4 closure to permit the requested
cached-only consumer capture. **No certify job was launched.** The explicit
stop-by-name attempt reports no live session 'x4m-catalog-lane'. Its start and
stop logs are retained. No new dev at-event session was started once the lane
capture was blocked. Dev's earlier certified-prefix capture is historical
reference only; no 0-ish count or comparison to it is invented.

## The general partition and evidence


x4_partition.py uses the non-LOCAL literal edge-reading policy of r5_paths.py:
read source forms, ignore LOCAL events, follow literal project include-book
edges in encapsulates, and exclude system-directory includes from the project
book graph. It reads all 1986 origin/dev production book sources without a
parser error. Dev reference revision:
`c671cc26394324310c114cc19078651d2558928f`.

Derivation:
1. Compute the lane's non-LOCAL history-paged closure.
2. Preserve the existing history-columns-foundation closure separately.
3. Find all origin/dev production-book consumers (transitive ancestors) of
   history-columns. Cut the generic history-columns boundary and the
   history-paged implementation root while following independent dev paths.
4. A newly introduced implementation-closure book is SHARED if some dev
   consumer reaches it independently; remaining newly introduced books are
   PRIVATE. Existing foundation books are already in the preserved baseline.
5. Generate a private-free include frontier covering every SHARED book. Use
   maximal shared books to avoid redundant direct includes of their children.

No rune names enter this computation. Full sets, consumers and path witnesses
are in x4-partition.json. The text inventory is x4-partition.txt; generated
source input is x4-shared-includes.lisp. These are saved evidence for the
seat's later commit; the explicit no-commits instruction was followed here.

| Partition | Count | Disposition |
| --- | ---: | --- |
| Existing foundation baseline | 88 | already included before the enabled snapshot |
| Additional SHARED | 47 | generated history-records frontier included before the enabled snapshot |
| PRIVATE | 2 | history-paged and history-pages-resident introduced after the enabled snapshot |
| Total implementation closure | 137 | disjoint baseline/shared/private partition |

The initial literal graph, before separating the existing baseline, marked
132 of 137 closure books shared; its five non-shared books include three
already present in the foundation baseline. Thus exactly two additional
books are private. In particular **most history-pages books are SHARED by the
actual graph**, rather than being assigned private because of their filename.

An independent witness for history-records and its page-chain dependencies:
`history-root-figure:28 → history-root-credit:5 → history-image-row-step:5 →
history-image-build-rows:7 → history-records`.
This path never traverses the generic or the history-paged root.

The shared codec has an independent dev witness too:
`acceptance-payload-ref:33 → store-files-traces:20 → store-files-invariants:8 →
store-files:32 → store-records-field:36 → store-checkpoint-buffer:46 →
store-checkpoint-codec:31 → store-tree-codec`.
All unprefixed path names mean books/<name>.lisp. Per-book path edges and
source lines for all 47 shared books are recorded in the JSON evidence.

The script also cross-checks an ordered book-level projection of the detected
structural export boundaries (dev store-records-field:175, before/after-disk),
retaining first-load/redundant-include behavior. Its partition is **identical**
to the literal independent-path partition. Consequently the optional question
about counting exporter-hidden paths does not affect this edit: the independent
history-root-figure path establishes sharing even with that boundary excluded.
This projection is a graph/ownership cross-check, not a calculation of ACL2's
actual enabled rune sets. Certified measurements remain the acceptance test.

Fixtures pass for a masked dependency, a redundant include after a mask,
a dependency introduced before the mask, and LOCAL-edge exclusion. The
emitter verifies every shared book is covered and no private book is pulled
in by the generated frontier. It regenerates its own include block, replacing
an earlier generated layout if the partition changes. The final rerun is
idempotent at these source inputs. Logs: x4-partition-run.log,
x4-partition-apply.log, x4-partition-final.log.

## Source preservation

Only the prior generated SHARED history-records include is present as the X4
source change. This measurement turn changes no book. The previously recorded
23 non-theory/non-include event byte strings and locality remain unchanged.
No consumer repairs were reintroduced; store-records-field source is unchanged.
The redundant include concern at store-records-field:28–31 was not edited in
this measurement turn; no new rune evidence attributes the eight to it.

## Static gates and shutdown

All gates were rerun after the certified measurements, with exit 0:

| Command | Result | Log |
| --- | --- | --- |
| python3 tools/one_world_check.py | 29 / 29 sites; 0 findings | x4m-one-world-gate.log |
| python3 tools/book_roots_check.py | 1928 / 1983 covered, 55 excluded; 0 unlisted orphans / unanalyzable includes | x4m-book-roots-gate.log |
| python3 tools/host_check.py --attach-order | 3 pairs, 56 files; 0 findings | x4m-attach-order-gate.log |
| python3 tools/extract/world.py --check | exit 0, no output | x4m-world-gate.log |
| python3 tools/interface_emit.py --check | 1915 declared, 1862 / 1862 dispatched; 0 findings | x4m-interface-gate.log |

Existing interface indeterminate/unresolved source categories are non-failing.
The gates do not override the certified export RED or certify the consumer world.
x4m-columns-lane and x4m-columns-dev are stopped by name; the failed catalog
start left no live session. No commit, push, book repair, source-dependency
fallback, box certify job or full suite. Evidence writes remain under
build/vertical-runs/one-world/.

Certified/current source SHA-256:
- history-columns: 69e6f9e03a6fdd72e078c8a8fe6d2fa10f4f88f8f464610e01bb29d7752618cf
- store-records-field: a6ed0e2e226cd746f84e1f7e81aaf56819ae0074ec77bb8ef3a8db0c621ef8e2

## X5 candidate

Implemented at the seat's direction after the X4 certified export measurement.
This is a **candidate awaiting certify of record #5**, not a certified X5 result.
The X4 counts and mechanism above remain historical evidence.

books/history-columns.lisp:6 now snapshots the enabled foundation:
`(deftheory fn-hist-theory-foundation (current-theory :here))`.
The generated SHARED frontier is included at :10. The existing
fn-hist-theory-before-paged at :12 snapshots the enabled post-SHARED theory.
The final export at :187 forms the preserved baseline by unioning these two
**enabled** snapshots, then unions that baseline with the generic's own enabled
runes, obtained by subtracting fn-hist-theory-after-paged from the current theory.
That after-paged snapshot at :14 is universal and is used **only for subtraction**.
No universal snapshot is unioned into the enabled export, and no rune-name list
is used in source construction.

This preserves the foundation's enabled runes even when a SHARED dependency's
NON-LOCAL theory event disables them, while retaining the SHARED dependencies'
enabled contribution. The measured X4 eight-rune loss occurred between these
two stages, so the new foundation snapshot supplies exactly the missing stage
of evidence. The two enabled snapshots already cover both preserved regions;
the existing universal snapshot separates imported runes from the generic's
own additions. The final current theory supplies the generic's enabled delta.
Consequently no third enabled snapshot, post-export snapshot, new universal
snapshot, or per-rune correction is needed for this construction. Whether its
full public export and consumer composition satisfy the requested equality
remains a certification/measurement question; no X5 counts are asserted.

x4_partition.py --apply was rerun (timeout 300) and regenerated its evidence.
The frontier is unchanged: history-records, covering 47 SHARED books;
88 original baseline books and two PRIVATE books remain the same partition.
Its generator marker and post-SHARED snapshot remain compatible, so no script
change was needed. Log: x5-partition-regenerate.log. No redundant include was
deleted. No consumer repair was introduced and store-records-field was unchanged.

x5-byte-audit.log confirms all **26 non-theory event byte strings, including
includes and locality**, identical to the pre-X5 candidate. Exactly one
DEFTHEORY was added; the final IN-THEORY expression was changed. Theorem
statements, definitions, guards, hypotheses and rule classes were not changed.
git diff --check passes.

The five requested static gates were rerun after the edit and regeneration:

| Command | Result | Log |
| --- | --- | --- |
| python3 tools/one_world_check.py | 29 / 29 sites; 0 findings; exit 0 | x5-one-world-gate.log |
| python3 tools/book_roots_check.py | 1928 / 1983 covered, 55 excluded; 0 unlisted orphans / unanalyzable includes; exit 0 | x5-book-roots-gate.log |
| python3 tools/host_check.py --attach-order | 3 pairs, 56 files; 0 findings; exit 0 | x5-attach-order-gate.log |
| python3 tools/extract/world.py --check | exit 0, no output | x5-world-gate.log |
| python3 tools/interface_emit.py --check | 1915 declared, 1862 / 1862 dispatched; 0 findings; exit 0 | x5-interface-gate.log |

The existing source-indeterminate interface categories are non-failing.
No proof_repl session was started this turn. No certify job, commit or push.
The seat runs certify of record #5 next, covering both exporters and the
consumer dependencies needed for fresh measurements (a) and (b).

Current candidate SHA-256 (x5-candidate-hashes.json):
- books/history-columns.lisp: `ae91efa79ff4d7dffb6860166b5e611cc6f234d02914008bf58e08773f3a2482`
- books/store-records-field.lisp: `a6ed0e2e226cd746f84e1f7e81aaf56819ae0074ec77bb8ef3a8db0c621ef8e2`
