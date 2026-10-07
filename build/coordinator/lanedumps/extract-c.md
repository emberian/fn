# LANEDUMP extract-c (2026-10-07; successor of extract-b; Deputy E, X3)

Base origin/lane/extract-b df0db93bc merged with origin/dev 1e190ff19 (d76fd37ac; image-world*/tools/extract/world*.lisp conflicts resolved by taking dev and regenerating with tools/extract/world.py).

## (i) Attribution: the bridge (1e99adbf0) caused the 8 reds
- run-20261007T031553Z-cde8: tests/acl2/newnews-cursor-tests GREEN at base 319aee828 (hbox).
- Fix e80f4fc14: fn-dt-lambda declares kept-but-unused lambda formals IGNORABLE (class of shapes); pins in tests/acl2/defkeystone-tests.lisp (fixed 'mv-list 2' count in a later commit).
- run-20261007T031943Z-5f1e (--lane --affected-by books/defkeystone, 112 books certified): 110 passed incl. the 8; 2 failed: defkeystone-tests (my pins; fixed, then green in run-20261007T034446Z-d5b6) and tests/acl2/page-read-startup-tests (DEV-WIDE RED, not the bridge: green at base run-20261007T033446Z-a036; dev's teeth-21 merge added defteeth calling fn-prstartup-plan with 9 args, the book's takes 10 (reserve)). Not touched; file to dev teeth debt.

## (ii) X3 load side (a66e5d486 + follow-ups)
- books/raw-dispatch-verdict.lisp: fn-rdv-table-digests / -table-problem / -carried-problem; keystone fn-rdv-table-verified-only-if-it-is-the-digested-table (+ own-digests premise theorem, defteeth 3 mutations). run-20261007T035233Z-6312 GREEN (book + tests).
- tools/extract/core-export.lisp: scans closure bodies for (table-alist 'X ..), carries those tables + fn-interfaces + fn-raw-dispatch-verdicts, plus manifest symbol FN-CORE-TABLE-DIGESTS (table-alist = ((table . row-digests)..)).
- host/native/raw-trap.lisp fnn-check-carried-tables, called first in fnn-install-raw-dispatch (image: empty manifest; core: missing manifest/table/row refused BY NAME).
- tests/test_native_raw_dispatch_trap.py: row edit, dropped FN-CARRIED, no manifest, edited fn-interfaces row (red with the call removed, green with it).
- host_check --load 4 findings -> 0: host/interfaces.lisp :direct rows for fn-rdv-*; 4 stale fn-di-* rows deleted; interface_emit --write, world.py regenerated.

## (iii) core.sh: xt-core-verdicts already runs inside xt-core-export (core.sh runs it); core.sh now also detects "HARD ACL2 ERROR" in export.log.

## NEXT
1. Gated core.sh run on hbox when Deputy E relays the dev-world image slot GO; report export log tail and whether fn-core identity passes load.
2. Non-gating smoke against hbox:/tank/fn/scratch/extract-measure (scratch core.sh copy only), one mutated verdict row refusal output.
