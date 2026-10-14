# Round 4 — STOP: exporter snapshot changed by include order

TASK 2 found the specified source leak. The NON-LOCAL restoration at
`books/store-records-field.lisp:45` removes the history-page theory introduced
early at line 42. The later `fn-sfr-theory-after-disk` snapshot at line 52 thus
omits nine executable counterparts that dev's snapshot contains. The existing
consumer restore at `tests/acl2/history-pages-owner-tests.lisp:31` no longer
restores dev's theory. No source correction was made; proof edits stopped.

TASK 1 remains partial at #404 `fn-ctg-commit-live-cover-row`. No statement was
found false and no counterexample is claimed. This is a theory/source STOP,
not a successful catalog whole-book check. No commits.

## Present per-book dispositions

These are REPL event-admission checks, not certificates of record. The four
A27 records and two completed predecessor round-4 records below are retained
evidence for unchanged book bytes; their exporter/cached-dependency scopes
remain as recorded in REPAIRS.md and EXPORTER-FIX.md. The completed
`export-membership.txt` certified-lane capture was not repeated.

| Book | Disposition and colliding pair | Include path | Final whole-book session; refusal / illegal-message |
| --- | --- | --- | --- |
| books/msgid-pages | Retained: ADT-CDR-NTHCDR versus FN-MPX-NTHCDR-CDR | pages:46 → C | a27-mpx-kept; 0 / NIL |
| books/msgid-pages-exec | Retained: ADT-NTH-0 / ADT-NTH-1+ versus FN-MPXT-RECOGNIZER-FACTS / FN-MPXT-NTHCDR-UNFOLD at FN-MPXT-KEY-FROM-IS-NTHCDR | pages-exec:79 → pages:46 → C | a27b-msgid-pages-exec-1; 0 / NIL |
| books/msgid-linear-exec | Retained: ADT-NTH-0 / ADT-NTH-1+ versus FN-MLH-RECOGNIZER-FACTS / FN-MLH-NTHCDR-UNFOLD and set-key list vocabulary | linear-exec:67 → linear:67 → pages:46 → C | a27-linear-new2; 0 / NIL |
| books/msgid-probe-layout | Retained: ADT-NTH-1+ recursively opens FN-MPXT-WI's NTH 1024; ADT-NTH-0 loses FN-MPL-CURSOR-FIELD-BOUNDS vocabulary | probe-layout:4 → probe-cursor:6 → pages-exec:79 → pages:46 → C | a27-probe-layout-pair; 0 / NIL |
| books/catalog-logic | Partial: sixteen LOCAL theory repairs; individual pairs below | catalog-logic:64 → linear-exec:67 → linear:67 → pages:46 → C | No final whole-book session. r5-catalog stops at #404; last range 1 refused, end NIL |
| books/msgid-query-chunk | Retained: ADT-NTH-0 / ADT-NTH-1+ versus chunk tag/sequence bridge lemmas and NTH guard vocabulary | query-chunk:5 → query-page:4 → probe-layout:4 → probe-cursor:6 → pages-exec:79 → pages:46 → C | r4-chunk-final; 0 / NIL |
| tests/acl2/history-pages-owner-tests | Source STOP: early-theory removal versus dev's executable evaluation at the seven repaired witness events | test:25 → history-pages-owner → S; test:31 restores the named snapshot | r4-hpo-whole; 0 / NIL, but consumer repair is not approved for retention |

All shorthand book names in paths mean `books/<name>.lisp`, except the test.

**C**, the actual direct history-columns import path:
`history-columns:5 → history-paged:6 → history-pages-resident:6 →
history-pages-placed:13 → history-pages-write-keys:17 →
history-pages-write-exec:7 → history-pages-write:14 → history-pages-read:16 →
history-pages-row:6 → history-pages-exec:4 → history-pages:39 →
proto/adt-bytes:53 → proto/adt-key-lib`.
The rule definitions are `proto/adt-key-lib.lisp:557` (ADT-NTH-0),
`:553` (ADT-NTH-1+), and `:70` (ADT-CDR-NTHCDR).

**S**, the source import path in the owner-test closure:
`history-pages-owner:35 → owner-checkpoint-open:30 → owner-recover-ocl:15 →
owner-served-carried:17 → owner-tls-prefix:9 → owner-config:43 → owner-fault:46 →
owner:96 → store-observed:23 → store-node-resolution:3 → store-node-traces:3 →
store-node-traces-prepare:6 → store-node-invariants:3 →
store-node-invariants-base:7 → store-node:8 → store-files-invariants:8 →
store-files:32 → store-records-field:42 → history-paged`.
The resident definitions then follow C's suffix starting at history-paged;
`history-paged:7 → history-records:49/50 → history-pages-import/view`
introduces the import and view functions.

`r5_paths.py`, `r5-include-paths.json`, and `r5-paths.log` give literal-source
edge measurements. ACL2 confirms the catalog and chunk introduction paths in
`r5-catalog-adt-path.log` and `r5-chunk-adt-path.log`; the owner definition paths
are in `r5-hpo-pe-all.log`. Source-path measurement does not itself assert
enabled-theory membership.

## TASK 1: catalog pairs and partial progress

Every repair is LOCAL at its colliding event; statements, definitions, guards,
hypotheses, rule classes and non-theory hints are unchanged. `round4_theory_wrap.py`
preserves the event's original bytes when introducing a proof scope. All imported
rules in this table follow the catalog path through C above.

| Colliding event | Imported rule(s) | Displaced dev rule or lemma |
| --- | --- | --- |
| fn-ctg-numbers-okp-old-keys | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-PLAN-NUMBERS-IS-ASSIGN, FN-CTG-NPUTS-LOOKUP |
| fn-mpxt-spec-from-is-cat-seqs-for | ADT-CDR-NTHCDR | FN-CTG-NTHCDR-CDR, FN-CTG-CAR-NTHCDR, FN-CTG-CONSP-NTHCDR |
| fn-ctg-scan-is-seqs-for | ADT-CDR-NTHCDR | FN-CTG-NTHCDR-CDR and FN-CTG-ROWS-CORR-NTH slice vocabulary |
| fn-ctg-commit-numbers-cover-row-any | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-PLAN-NUMBERS-IS-ASSIGN, FN-CTG-NPUTS-LOOKUP |
| fn-ctg-commit-groups-cover-row | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-GPUTS-LOOKUP, FN-CTG-GROUPS-COVER-ROWP-MONOTONE |
| fn-ctg-commit-groups-okp-keys | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-GPUTS-LOOKUP, FN-CTG-GROUPS-ENTRY-BOUND, FN-CTG-HIGH-APPEND / ROWS-APPEND |
| fn-ctg-index-add-fields | ADT-NTH-0 / ADT-NTH-1+ | NTH-UPDATE-NTH field vocabulary |
| fn-ctg-commit-fields | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-APPLY-PLAN-FIELDS / FIELDS-910, FN-CTG-INDEX-ADD-FIELDS, NTH-UPDATE-NTH |
| fn-ctg-key-of-index-add | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-CP-INDEX-FIELDS, NTH-UPDATE-NTH |
| #344 fn-ctg-key-of-commit-base | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-CP-COUNT-NTH; the :use of FN-CTG-KEY-OF-INDEX-ADD needs this NATP fact |
| #345 fn-ctg-commit-base-corr | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-PLAN-NUMBERS-IS-ASSIGN and FN-CTG-COMMIT-GROUPS-COVER-ROW |
| #369 fn-ctg-clear-fields | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-INDEX-CLEAR-FIELDS-U / INDEX-CLEAR-FRAME and NTH-UPDATE-NTH |
| #380 fn-ctg-base-fields-67 | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-APPLY-PLAN-FIELDS field vocabulary |
| #393 fn-ctg-lplan-lookup | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-LIVE-READERS, FN-CTG-GROUPS-ENTRY-BOUND / ENTRY-UNBOUND |
| #396 fn-ctg-commit-live-okp-old | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-LPLAN-LOOKUP / LIVE-LOOKUP |
| #399 fn-ctg-commit-lookup-member | ADT-NTH-0 / ADT-NTH-1+ | FN-CTG-LPLAN-LOOKUP / LIVE-ENTRY-APPEND-MEMBER |

The predecessor's first nine repairs remain on disk. Seven additional scopes
were added here, at #344, #345, #369, #380, #393, #396, #399. Each passed in
`r5-catalog`; dev comparisons are the corresponding `r5-catalog-*-dev-rules.txt`
and earlier `r4-*-dev-rules.txt`. In particular #344 returned exactly 289
prover steps, as in dev's Rules record. Iteration is recorded in
`r5-catalog-tail.log` through `r5-catalog-tail7.log`.

The next refusal, #404, is unrepaired. Its checkpoint has CADR/CDDDDR field
expressions where dev's `FN-CTG-LPLAN-LOOKUP` expects NTH vocabulary;
`r5-catalog-livecover-dev-rules.txt` records the dev comparison. That diagnosis
is not a tested repair. `r5-catalog-end.log` returns NIL for
`(@ illegal-to-certify-message)` on the partial world. The requested fresh
whole-book 0-refused check was not reached because TASK 2 required STOP.

## TASK 2: source mechanism, both worlds

The lane measurement session `r5-hpo-source` stopped before top-level form
#22, the first repaired witness scope. It loaded 21 source forms. The dev
measurement session `r5-hpo-dev` included certified history-pages-owner in the
read-only dev-reference setup used by dev-repl.py, then sent the unchanged dev
test theory/constant/macro/first-two-theorem prefix. The following must-fail
control introduces no enabled theory. Dev-prefix source was read from
`/tank/fn/scratch/integrate-20261013f/native-cd6c683386f1/tree/`.
Both sessions' illegal-message end queries returned NIL.

The exact `(disabledp '<fn>')` outputs are in `r5-hpo-source-disabled.log`
and `r5-hpo-dev-prefix-disabled.log`. `:pe` output for every function is in
`r5-hpo-pe-all.log` / `r5-hpo-dev-pe-all.log`; expanded `:pcb! 1` source
events are in `r5-hpo-pcb-include.log` / `r5-hpo-dev-pcb.log`.

| Function | Definition book:line | Lane at first witness | Dev after existing test restore | Lane disabling event |
| --- | --- | --- | --- | --- |
| adt-placement-ok | books/proto/adt-bytes.lisp:356 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-lens | books/history-pages-exec.lisp:160 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-okp | books/history-pages-exec.lisp:154 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-piw | books/history-pages-placed.lisp:163 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-records-at | books/history-pages-view.lisp:54 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-starts-okp | books/history-pages-read.lisp:33 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-vhold-x | books/history-pages-read.lisp:382 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-x-append-all | books/history-pages-import.lisp:180 | EC disabled | EC enabled | store-records-field:45 |
| fn-hp-x-init | books/history-pages-import.lisp:36 | EC disabled | EC enabled | store-records-field:45 |
| pgs-v-length | generated accessor of pgs-mem, books/pagestore-words.lisp:37 | EC enabled; definition disabled | EC enabled; definition disabled | definition disable in pagestore-words:222; no EC disable at the witness |

For each of the first nine, enabled membership at the lane's four landmarks
before-paged / before-columns / before-disk / after-disk is **NIL / T / NIL /
NIL**. For PGS-V-LENGTH it is T / T / T / T. This pins the nine-counterpart
disable to the intervening NON-LOCAL event at line 45, rather than inferring
it from a function's definition. Dev before-disk / after-disk membership is
**NIL / T** for each of the nine; PGS-V-LENGTH is T / T. See
`r5-hpo-snapshots-all.log` / `r5-hpo-dev-snapshots-all.log`.

Dev's final exporter event at store-records-field:175 temporarily disables
the nine (both certified include worlds show this). Dev's pre-export snapshot
still contains them, so the unchanged test:31 restores them. In the lane,
history-paged introduces these books before the disk include; line 45 removes
their theory, and disk finds them already loaded. Its includes are redundant
and do not reenable them. The lane final exporter event at line 188 leaves
them disabled, and test:31 has no snapshot members to restore.

The imported-source/consumer pair is therefore the early-history-paged
restoration versus the executable evaluation used by HPO-RECORDS-AT-INSTALLED-W
and the other six repaired witness events, not ADT-NTH versus a rewrite lemma.
The ten-counterpart consumer enable includes an already-enabled PGS-V-LENGTH.

**Proposed source fix, not made:** separate the public exported theory from
the named pre-export restore snapshot in store-records-field. Preserve dev's
enabled after-disk snapshot despite the early implementation include, using
an enabled import snapshot before line 45 (or delaying the filtering until
after that snapshot is formed), while retaining the exact dev public export.
Measure the full common-rune snapshot delta; do not substitute a nine-name
reenable list. Do not union a universal snapshot into an enabled theory, since
that would also enable previously disabled rules. Then remove the seven
consumer scopes and recheck the whole test. The current seven scopes remain
untouched on disk as provisional evidence; they are not approved retained fixes.

## TASK 3: chunk pair

The three retained scopes are at FN-MIQ-CHUNK-NEXT-IS-PAGE-LAYOUT-STEP,
VERIFY-GUARDS FN-MIW-CHUNK-PLACE, and FN-MIW-CHUNK-PLACE-IS-PAGE-LAYOUT-STEP.
ADT-NTH-0 / ADT-NTH-1+ open the cursor/page fields before
FN-MIQ-CHUNK-TAG-IS-PAGE-TAG / FN-MIQ-CHUNK-SEQ-IS-PAGE-SEQ can bridge to the
layout model. FN-MPL-CURSOR-FIELD-BOUNDS depends on the same cursor vocabulary.
The guard proof's dev rules instead use NTH-0-CONS, NTH-ADD1, NTH-UPDATE-NTH.
Evidence: round4-dev-rules.txt, r4-secondary-dev-rules.txt, the repaired event
logs, r4-chunk-final-start.log (19 source forms loaded) and end.log (NIL).
ACL2's fresh r5-chunk-path :pe query confirms the full path above.

## TASK 4: structural-restore measurement

| Book | Displacing theory's route | Through history-columns direct implementation include? | Exact dev history-columns export would remove which repair? |
| --- | --- | --- | --- |
| msgid-pages | pages:46 → C | Yes | ADT-CDR-NTHCDR disable |
| msgid-pages-exec | pages-exec:79 → pages:46 → C | Yes | ADT-NTH pair disable |
| msgid-linear-exec | linear-exec:67 → linear:67 → pages:46 → C | Yes | ADT-NTH pair disable |
| msgid-probe-layout | probe-layout:4 → probe-cursor:6 → pages-exec:79 → pages:46 → C | Yes | ADT-NTH pair disable |
| catalog-logic | catalog:64 → linear-exec:67 → linear:67 → pages:46 → C | Yes | All sixteen current ADT-NTH / ADT-CDR scopes or theory-hint repairs |
| msgid-query-chunk | query-chunk:5 → query-page:4 → probe-layout:4 → probe-cursor:6 → pages-exec:79 → pages:46 → C | Yes | All three ADT-NTH pair scopes |
| history-pages-owner-tests | test:25 → S; source restore at store-records-field:45 → test:31 | No: first import is the separate store-records-field:42 include | None by columns restoration alone; correct the source snapshot |

The first six have **no literal non-LOCAL include path to adt-key-lib avoiding
history-columns**. Their disabling repairs would become unnecessary if
history-columns exported exactly dev's theory, using the structural approach
of f7760ab8c in store-records-field. This is a conditional theory-necessity
conclusion; no such source change or unrepaired whole-book recertification
was performed here. It does not establish that the unresolved catalog tail
has no other problem.

The redundant-include hazard at `books/store-records-field.lisp:28-31` matters:
once an implementation book has been included, a later direct include will
not reenable rules stripped by the exporter. The owner-test snapshots exhibit
that hazard directly. Restoring columns' theory alone also does not undo
store-records-field's separate early implementation include.

## Gates and shutdown

All required commands exited 0:

```text
python3 tools/one_world_check.py
one_world_check: 29 source sites, 29 expected sites; 0 findings
python3 tools/book_roots_check.py
book_roots_check: 1928 of 1983 books/**/*.lisp are covered; 55 excluded;
0 unlisted orphan(s); 0 unanalyzable include(s)
python3 tools/host_check.py --attach-order
host_check --attach-order: 3 attach pair(s) (fn-cat, fn-hist, fn-arena),
56 host file(s) in scope, 0 finding(s)
python3 build/vertical-runs/one-world/round4_audit.py
catalog-logic: 638; msgid-query-chunk: 16; history-pages-owner-tests: 38
non-theory events and non-theory hints unchanged, including locality
```

Logs: r5-one-world-gate.log, r5-book-roots-gate.log,
r5-attach-order-gate.log, r5-audit-gate.log. The supplemental
`r5-byte-audit.log` also compares raw event bytes outside theory-hint
expressions and the one added theory comment; all 638 / 16 / 38 match,
with locality identical.

Stopped by the wrapper, by name: r5-catalog, r5-hpo-mechanism,
r5-hpo-source, r5-hpo-dev, r5-chunk-path. Each stop log says stopped.
No predecessor session was touched; the brief says none remained running.

Tooling caveat: dev-repl send-range rejected an external-prefix input because
its staging path was outside its dev-reference root. It staged that input
under build/proof-repl-files before raising ValueError; no ACL2 send occurred.
The retry used stdin send with an input in this allowed report directory.
No source file outside the allow-list was edited; the staged operational
artifact was not deleted. All subsequent measurements and reports stayed
inside the allowed scope.
