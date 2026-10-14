# X — consumer repairs removed; STOP for msgid-pages certificate

Both certified public exporters and their corresponding named pre-export
snapshots match dev on every common rune except the accepted
`(:executable-counterpart create-fn-hist)` residual. All seven consumer repair
sets are deleted. Unrepaired msgid-pages passes its WHOLE book in a fresh hbox
session: 68 forms, 0 refused, illegal-to-certify NIL.

The next fresh check, msgid-pages-exec, cannot start because the current
unrepaired msgid-pages dependency has no certificate in the cache. Per the
later-certification rule, STOP; the seat must certify **books/msgid-pages** at
the restored exporter closure. No box certify job or source replay was
substituted. The remaining six WHOLE checks are outstanding, not green.
No proof RED was encountered and no new consumer repair was added. No commits.

## Certified exporter evidence — Step 4

The seat certified the exact exporter candidates in
run-20261013T230927Z-247c, manifest
build/acl2/certify-20261013T231129Z-4059941: two exporters passed, 142 closure
books cached, pairs published to /tank/fn/certcache, two relabelled.

Fresh sessions x2-columns-lane, x2-columns-dev, x2-sfr-lane, x2-sfr-dev each
started --cached-only --upto #1 with **0 source forms loaded and 0 sends**.
Each capture then used a certified include, with no source-loading flags.
Both dev-reference exporter source files are byte-identical to origin/dev
`c671cc26394324310c114cc19078651d2558928f`.
Dev certificates came from the dev-repl reference/cache method authorized by
the brief, principally /tank/fn/scratch/spans-view-walks/native-c19-vw/tree.
Both sides' raw enabled/universal rune sets are saved without filtering.

| Required comparison | Common runes | Dev-only enabled common | Lane-only enabled common |
| --- | ---: | ---: | --- |
| history-columns public export | 13,317 | 0 | CREATE-FN-HIST executable counterpart |
| history-columns saved foundation baseline versus dev's certified foundation | 13,278 | 0 | 0 |
| store-records-field public export | 18,148 | 0 | CREATE-FN-HIST executable counterpart |
| store-records-field fn-sfr-theory-before-disk | 15,202 | 0 | CREATE-FN-HIST executable counterpart |
| store-records-field fn-sfr-theory-after-disk | 18,106 | 0 | CREATE-FN-HIST executable counterpart |

**Unexpected common-rune differences: zero in all five comparisons.**
The restored after-disk snapshot now supplies the dev enabled import theory
that the owner test's existing restore reads. No nine-name workaround is used.
The columns saved foundation snapshot also matches a fresh lane foundation
control and dev's certified foundation include exactly on common runes.

“Pre-export snapshot” is interpreted as the corresponding **named structural
snapshots**: columns' enabled fn-hist-theory-before-paged baseline, and SFR's
before/after-disk snapshots. Columns has no named enabled snapshot immediately
before its final filtering event; fn-hist-theory-after-paged is its UNIVERSAL
subtraction boundary. The optional clarification offered this interpretation;
no answer arrived, and work continued on this stated interpretation.

An additional diagnostic captured columns' RAW proof theory at
FN-HIST-MSGID-RECORDS-SERVE-CEI before final filtering. It has eight common
runes disabled relative to dev, plus the creator residual. The eight are:

```text
(:DEFINITION FN-CBOR-OCTET-LISTP)
(:DEFINITION FN-OCTETS$C-BUFP)
(:INDUCTION FN-CBOR-OCTET-LISTP)
(:INDUCTION FN-OCTETS$C-BUFP)
(:REWRITE FN-OCT-BUFP-CELL-IS-OCTET . 2)
(:REWRITE FN-OCT-BUFP-CELL-IS-OCTET . 3)
(:REWRITE FN-OCT-BUFP-OF-RESIZE-LIST)
(:REWRITE FN-OCT-BUFP-OF-UPDATE-NTH)
```

These come from NON-LOCAL implementation proof-theory disables in
books/pagestore-words.lisp:243 and :379, reached through the direct
history-paged implementation include. The final snapshot-based columns export
restores them; they do not differ in its public export or saved foundation
baseline. This diagnostic is retained separately and is not silently filtered
into a passing comparison. If main instead requires equality of that raw
pre-filter proof state, this diagnostic is a STOP with those exact source
events; no such equality is claimed here.

Capture/diff artifacts:
- x_certified_capture.py: reproducible certified-include capture and full-set comparison.
- x2-columns-{lane,dev}-{start,include,runes,end,stop}.log and .exit.
- x2-columns-{lane,dev}-foundation-control.log; lane's saved baseline is also in runes.log.
- x2-sfr-{lane,dev}-{start,include,runes,end,stop}.log and .exit.
- x2-columns-lane-{PUBLIC,FOUNDATION-SAVED,RAW-PRE-EXPORT}-diff.{json,txt}.
- x2-sfr-lane-{PUBLIC,BEFORE-DISK,AFTER-DISK}-diff.{json,txt}.
- x2-columns-comparison.json, x2-sfr-comparison.json, x2-evidence-validation.json.

All four capture end queries/assertions pass: 0 refused, illegal-message NIL.
All four capture stop commands exit 0 and say stopped. Original
export-membership.txt is untouched and remains evidence for its prior bytes.

Certified public-include artifact sets:

| Include | Artifact set |
| --- | --- |
| lane history-columns | 45b1d0fadfddeabef1bc3b3701b312b1ad95631d722e72a0a934d045a08a2980 |
| dev history-columns | 91552582b6358008a321cb6aaa5e52f2fc76483a5960d112bdea3ed3663bab88 |
| lane store-records-field | 7deec4848729eec053aaf9909f2a2f418f19a34077ee000235b734649c2776c5 |
| dev store-records-field | b8244c4e919b4eb0f135718a3428295cd1e410170aa3bfd21ba649c76a981a9d |

## Exporter structures and redundant-include rule

history-columns:7 snapshots the enabled foundation; :9 snapshots the
implementation universal theory; :182 exports foundation plus the book's
own enabled-event delta. store-records-field:45 saves the enabled import
snapshot before public filtering; :53 preserves the public before-disk
baseline; :56 restores the import snapshot before disk and the after-disk
snapshot at :62. Its final public-export expression at :198 is unchanged.
No universal snapshot is unioned into an enabled theory and no new rune-name
exception list is introduced. Exporter non-theory bytes/locality remain
unchanged as previously audited (25 / 34 events).

No redundant include was deleted: the full required rune comparisons show
no unexpected difference attributable to one. Lines 28–31 of
store-records-field describe the redundant-include hazard; the early
history-paged include at :42 remains. There is no workaround for a measured
public or named-snapshot difference, since those comparisons have none.
No exporter source was changed after the seat's certify.

## Consumers — Step 5, deletion complete / checks partial

x_remove_consumer_repairs.py validates non-theory events/hints and locality
for all seven before writing, then restores exact dev bytes, retaining only
the two catalog one-world comment hunks. Backups of the prior repair bytes
are in x2-before-delete-*. No statement, definition, guard, hypothesis or
rule-class change was made. Six `git diff origin/dev -- FILE` results are empty.

| Book | Final source disposition | Fresh whole-book result at restored exporter closure |
| --- | --- | --- |
| books/msgid-pages | no consumer repair; byte-identical to origin/dev | x2-whole-msgid-pages: 68 forms, 0 refused, end NIL; stopped |
| books/msgid-pages-exec | no consumer repair; byte-identical to origin/dev | start blocked by missing msgid-pages certificate; no resident session |
| books/msgid-linear-exec | no consumer repair; byte-identical to origin/dev | pending after certificate STOP |
| books/msgid-probe-layout | no consumer repair; byte-identical to origin/dev | pending after certificate STOP |
| books/catalog-logic | no consumer repair; only two one-world comment hunks differ | pending after certificate STOP |
| books/msgid-query-chunk | no consumer repair; byte-identical to origin/dev | pending after certificate STOP |
| tests/acl2/history-pages-owner-tests | no consumer repair; byte-identical to origin/dev | pending after certificate STOP |

Retained non-repair catalog changes at :56 and :5947 explain that catalog.lisp
selects/attaches fn-cat-paged before introducing fn-cat, and remove the obsolete
catalog-paged-attach reference. x2-consumers-final.diff contains only these two
comment hunks; x2-consumer-byte-identity.json records all source hashes.

The passed msgid-pages session installed certified dependencies from artifact
set 45b1d0fadfddeabef1bc3b3701b312b1ad95631d722e72a0a934d045a08a2980 and
ran the entire current unrepaired book. This is a fresh admission check, not
certification of msgid-pages.

The exact later STOP is in x2-whole-msgid-pages-exec-start.log:

```text
proof-repl: REFUSED -- no certificate at these bytes for books/msgid-pages.lisp
books/msgid-pages.lisp sha256 9188b58bbed301cd:
no certificate for these bytes was ever published to this cache
```

Its prescribed job is `swarm-build python3 tools/certify_books.py --incremental
--jobs 4 books/msgid-pages`. It was not launched. No ACL2 theorem was refused.
The start exits 1; a by-name stop returns “no live session”, confirming no
resident process started. Other books' later cache frontiers were not probed
past this STOP. The precise known certify need is books/msgid-pages, including
its current restored-exporter dependencies; further needs must be reported
when encountered.

## Gates — Step 6

All requested commands were rerun after consumer deletion and exited 0:

| Command | Result | Log |
| --- | --- | --- |
| python3 tools/one_world_check.py | 29 / 29 sites, 0 findings | x2-one-world-gate.log |
| python3 tools/book_roots_check.py | 1928 / 1983 covered, 55 excluded; 0 unlisted orphans, 0 unanalyzable includes | x2-book-roots-gate.log |
| python3 tools/host_check.py --attach-order | 3 pairs, 56 files, 0 findings | x2-attach-order-gate.log |
| python3 tools/extract/world.py --check | exit 0; no output | x2-extract-world-gate.log |
| python3 tools/interface_emit.py --check | 1915 declared, 1862 / 1862 dispatched; 0 findings | x2-interface-gate.log |

Interface's one listed unresolved keystone remains a non-failing category.
round4_audit.py also passes: 638 / 16 / 38 non-theory events and non-theory
hints unchanged, including locality. git diff --check passes.

All five resident sessions started in this continuation are stopped: the four
captures and x2-whole-msgid-pages. The msgid-pages-exec start never became live.
No commits, pushes, deployment, source replay or box certify job was run.
