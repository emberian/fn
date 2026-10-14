# FAM5 — four reds and D2

Current disposition: the complete project-owned recognizer-bridge family is treated; K-U64 matches dev exactly and all six final gates pass. See [A: recognizer bridges, complete](#a-recognizer-bridges-complete). Earlier STOPs and one-pair findings below are historical.

**The index-provider and pool call-depth failures have one size/serialization cause, repaired by default-disabling ADT-LEN-REGION-BELOW-BODY. Served-columns and served-catalog-view are STOPs for main’s fifth family. All six static gates pass.** No commits or certification jobs.

Controls and D2 use cached certificates for dependency closures at `b32eced13c14a43cdf0f8ae9ec14653fd62e553e`; exact dev D2 source is `e0981366718013c5d96c9780e81a3fe1cb75e2bd`, archived from this worktree’s git objects into `fam5-dev-reference/`. D2 measures the committed HEAD before the repair, not its uncertified working-tree closure. Hbox toolchain: `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`. Historical certificates below establish their own event Rules lists, not current certification.

## Task 1 — causes and session-only controls

Each target statement is the unchanged source form. The failed attempts’ Rules lists omit unfinished rule applications; the BRR/cw-gstack captures supply those applications. No rewrite-depth ceiling was increased. Timing is single-session ACL2 time, not a two-job certification measurement.

| Red / event | Responsible rune(s) | Baseline | Session-only control | Disposition |
| --- | --- | --- | --- | --- |
| index-backing-provider / FN-IBP-QUERY-SLOT-BORROW-START guard | `(:LINEAR ADT-LEN-REGION-BELOW-BODY)` | depth refusal; 9,698 steps, 1.78 s | disable only that linear rune: admits, 81,776 steps, 1.96 s | FIX applied |
| catalog-pool / FN-CPG-GROUP-NUMBER-FILLS | same linear rune | depth refusal; 2,830 steps, 1.88 s | disable only that linear rune: admits, 11,961 steps, 0.24 s | FIX applied |
| served-columns / FN-SCOL-HEADER-CONTENT-OCTETS | `(:REWRITE FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP)` | refuses; 1,463 steps, 0.04 s | disable only that rune: admits, 29 steps, 0.02 s | STOP: recognizer normalization, neither NTH openers nor size/serialization |
| served-catalog-view / FN-SCV-FIRST-IS-FIRST-P | `(:REWRITE FN-CPL-LAST-SKIPS)`; `FN-CPL-FIRST-SKIPS` adds work | 60 s limit; 252 credited steps | LAST-SKIPS off: admits, 539,073 steps, 13.68 s; both off: admits, 96,658 steps, 2.33 s | STOP: live-link backchaining, neither authorized family |

### Index provider and pool: the pair rule selects the introducing linear theorem

`books/proto/adt-bytes.lisp:663` bounds `(len (nth r regs))` by `(len (adt-body regs))`. The bound inserts the serialized body into the linear pot. `(:DEFINITION ADT-BODY)` opens region padding, and `(:DEFINITION BINARY-APPEND)` recursively consumes the resulting quoted zero list. This is finite expansion, not an opposing rewrite cycle. The index guard’s 64-cell region pads to a 16,384-cell page: 16,320 zeros. The pool stack applies the same bound to `(LEN (NTH 2 (CONS ...)))` and then reaches the quoted padding tail of the `:INDEX-MISMATCH` result. The rule introducing the expensive term is the linear theorem; neither ADT-BODY nor an append associativity rule is edited.

Evidence: [index baseline](fam5-ibp-baseline.log), [index stack](fam5-ibp-stack.log), [index linear-off control](fam5-ibp-linear-off-control.log); [pool baseline](fam5-pool-baseline.log), [pool stack](fam5-pool-stack.log), [pool linear-off control](fam5-pool-linear-off-control.log). The earlier complete index trajectory and padding-value query remain in [P1F.md](P1F.md).

Applied exactly `(defthm adt-len-region-below-body ...)` → `(defthmd adt-len-region-below-body ...)`; its formula, hypotheses, rule class and hint are byte-identical. This keeps the opaque-field/length normal form instead of enabling the NTH openers to mask the match.

### Served-columns: STOP on an octet-recognizer bridge

`books/catalog-paged.lisp:254` exports the equality `(equal (fn-cbor-octet-listp x) (adt-octetsp x))`. It rewrites the goal and subsumes the local scrub lemma when that lemma is admitted. The target needs the FN-CBOR-OCTET-LISTP vocabulary of FN-SCOL-SCRUB-OCTETS. Turning the bridge off preserves that vocabulary and reproduces dev’s exact six-rule proof and 29 steps. This is an equality between recognizers, not ADT serialization or a size bound. No bridge or consumer edit is applied. [Baseline](fam5-scol-baseline.log), [control](fam5-scol-rune-off-control.log).

### Served-catalog-view: STOP on live-link search backchaining

`books/catalog-live-links.lisp:530` supplies FN-CPL-LAST-SKIPS: a negative FN-CAT-LIVE-NUMBERP conclusion requires a condition on FN-CAT-LIVE-LAST. The rewriter expands that recursive search while relieving the rule’s hypothesis. `:511` supplies FN-CPL-FIRST-SKIPS with the analogous FN-CAT-LIVE-FIRST condition. [The target stack](fam5-scv-target-stack.log) shows LAST-SKIPS, the live-last definition, and FIRST-SKIPS while proving the latter’s search-bound hypothesis. They are absent from dev’s target Rules list and absent from dev catalog’s enabled and universal theories; both are present at HEAD. [Membership](fam5-suspect-membership.json).

The initial 20 s cached-prefix load stopped at the earlier local FN-SCV-XDIFF-LOOP-IS-SUM, rather than reaching the r9 target. A 65 s unchanged retry also limited at 452 credited steps; [its stack](fam5-scv-stack65.log) exposes LAST-SKIPS. With both skips disabled, all 65 unchanged forms from that local event through FN-SCV-SUMMARY-OFF-NATURALS admitted: 16.10 s, 1,122,811 steps. The following COUNT theorem admitted in 14,069 steps. The target baseline then **restored both skips**, without changing any admitted statement, and limited at 60 s. This prefix preparation is explicit; it is not a whole-book replay with the original theory.

Independent target controls restored `fam5-target-base`: FIRST-SKIPS off alone still limits at 20 s / 252 steps; LAST-SKIPS off alone admits in 13.68 s / 539,073 steps. Both off admits in 2.33 s / 96,658 steps. LAST-SKIPS is sufficient to cause the observed limit in the FIRST-off world; FIRST-SKIPS adds proof work after LAST is disabled. No live-links or consumer source changes. [Prefix control](fam5-scv-skips-off-prefix.log), [target baseline](fam5-scv-target-baseline.log), [FIRST-only off](fam5-scv-first-off-control.log), [LAST-only off](fam5-scv-last-off-control.log), [both off](fam5-scv-target-off-control.log).

### Dev certificate Rules-list comparisons

Complete reference Rules lists, baseline lists and deltas are in [fam5-rule-comparisons.json](fam5-rule-comparisons.json); the successful-log inventories are [local](fam5-dev-event-history.json) and [hbox](fam5-dev-remote-history.json).

| Event | Dev successful certificate reference | Dev rules / steps | Passing control vs dev Rules |
| --- | --- | --- | --- |
| index-backing-provider | `hbox:/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T093213Z-3279561/books--index-backing-provider.certify.log:4641` | 44 / 81,841 | adds `(:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)`, `(:REWRITE PGS-X-NFIX-WHEN-NATP)`; omits `(:DEFINITION NFIX)` |
| catalog-pool | `/Users/ember/dev/fn/build/integrate-20261006n/build/acl2/certify-20261009T112025Z-1188876/books--catalog-pool.certify.log:2014` | 44 / 11,975 | adds `(:REWRITE PGS-X-NFIX-WHEN-NATP)`; omits `(:DEFINITION NFIX)` |
| served-columns | `hbox:/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T093213Z-3279561/books--served-columns.certify.log:937` | 6 / 29 | identical |
| served-catalog-view | `hbox:/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T093213Z-3279561/books--served-catalog-view.certify.log:10603` | 22 / 70,608 | adds `(:REWRITE PGS-X-NFIX-WHEN-NATP)`; omits `(:DEFINITION NFIX)` |

All completed dev event lists omit the responsible rune(s). For the two depth failures and catalog-view’s limit, the offending backchain/linear attempts are not credited in the aborted summaries either. A Rules-list omission is not evidence of disabledness; the controls and stacks establish causation. Served-columns’ failed summary does credit the new recognizer bridge.

### Census and byte identity

`p1_enables.py` now accepts ADT-LEN-REGION-BELOW-BODY alongside the two openers, matches its **LINEAR** class exactly, retains DEFTHM/DEFUN/VERIFY-GUARDS summary evidence, and supports deterministic defining-book changes plus combined consumer lines from immutable HEAD. Fixtures distinguish LINEAR from a wrong-class or suffix decoy, source echoes from Rules evidence, and implicit-guard summaries. PCRE2 is used for the same class-sensitive pattern in the batched rg prefilter. The existing ancestry classification, successful-log predicate, seven exclusions and separate authorized proto guard provenance are unchanged.

Fresh October/all-event and September/guard-only scans of the named local and read-only hbox trees found **zero** successful ADT-LEN-REGION-BELOW-BODY Rules uses in dev, other lanes or this lane. Therefore it gets **no derived LOCAL enables**, including no defining-book enable. Existing opener subjects remain 62 ADT-NTH-0 and 53 ADT-NTH-1+ (65-book union). Apply was repeated idempotently. All seven exclusions are byte-identical; the entire tracked diff is the one DEFTHMD token. [Independent audit](fam5-byte-audit.json).

Exact generation: `timeout 900 python3 build/vertical-runs/one-world/p1_enables.py --scan`; `timeout 180 python3 build/vertical-runs/one-world/p1_enables.py --apply` (twice); `timeout 30 python3 build/vertical-runs/one-world/p1_enables.py --report`. Regenerated: [p1-census.json](p1-census.json), [p1-enables.json](p1-enables.json), [p1-enables.txt](p1-enables.txt), [P1.md](P1.md). The command’s default rune list is the three named runes.

## Task 2 — D2, measurement only

### Method and exported generic theories

Each measurement starts from the same ACL2 initial world, performs a **certified INCLUDE-BOOK**, dumps CURRENT-THEORY and UNIVERSAL-THEORY with full rune identities, then undoes to the pre-include label. It does not count the generic’s source-load LOCAL proofs. The common initial world has 5,446 enabled / 5,621 universal runes. “Exported” below removes this initial universal set; whole-world totals are supplied separately. This counts the entire exported include closure, including included system libraries, and retains disabled rules in the universal count. The implementation-closure intersection excludes the same initial universal set; shared foundation rules count in both closures and are not unique implementation authorship.

ALLOWED_SITES’ actual attachments are fn-hist → fn-hist-paged, fn-cat → fn-cat-paged, fn-arena → fn-arena-extent. The arena implementation book is **payload-arena-extent**, not a presumed payload-arena-paged.

| Generic book | Dev exported enabled / universal | HEAD exported enabled / universal | HEAD exported from implementation closure, enabled / universal | Dev whole-world enabled / universal | HEAD whole-world enabled / universal |
| --- | ---: | ---: | ---: | ---: | ---: |
| history-columns | 6,285 / 7,696 | 10,418 / 12,470 | 10,388 / 12,431 | 11,729 / 13,317 | 15,862 / 18,091 |
| catalog | 11,682 / 13,947 | 18,311 / 21,393 | 18,228 / 21,285 | 17,126 / 19,568 | 23,755 / 27,014 |
| payload-arena | 2,315 / 2,718 | 3,161 / 3,655 | 3,003 / 3,479 | 7,761 / 8,339 | 8,607 / 9,276 |

| Generic | HEAD-only enabled / universal | Of those, in implementation closure |
| --- | ---: | ---: |
| history-columns | 4,133 / 4,774 | 4,132 / 4,774 |
| catalog | 6,629 / 7,446 | 6,628 / 7,446 |
| payload-arena | 846 / 937 | 845 / 937 |

The one enabled addition outside each implementation closure is the generic creator executable counterpart; universal additions are all within the implementation closure. Start/cache metadata and full rune dumps: `fam5-d2-{head,dev}-start.log`, `fam5-d2-{head,dev}-restart.log`, `fam5-d2-{head,dev}-{book}.log`. Dev and HEAD use separate owned remote trees. [Counts and intersections](fam5-d2-counts.json), [reproducible measurement driver](fam5_measure.py), [counter](fam5_counts.py). The first measurement attempt stopped its own sessions after SET-EVISC-TUPLE prompted interactively; the reported dumps come from the subsequent successful sessions and use CW’s explicit full-output tuple.

### Typical consumer, fixed early include event

The anchors are immediately after the last top-level include and **before** the first LOCAL theory event/function: catalog-logic’s `(include-book "def-loop")`, served-columns’ `(include-book "nntp-xref")`, and owner-served-carried’s `(include-book "config-store-traces")`. Their exact ordered source include prefixes are used at dev and HEAD. No consumer theorem, implementation source replay or proposed repair is loaded. All dependencies come from compatible cached certificates; owner’s set has 286 dev / 292 HEAD books.

| Consumer prefix | Dev enabled | HEAD enabled | HEAD-only | History implementation fraction | Catalog implementation fraction | Arena implementation fraction |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| catalog-logic | 16,333 | 20,611 | 4,278 | 3,431/10,514 (32.63%) | 4,278/18,235 (23.46%) | 845/3,003 (28.14%) |
| served-columns | 18,163 | 24,792 | 6,629 | 3,431/10,514 (32.63%) | 6,628/18,235 (36.35%) | 845/3,003 (28.14%) |
| owner-served-carried | 25,197 | 26,044 | 847 | 0/10,514 (0.00%) | 847/18,235 (4.64%) | 845/3,003 (28.14%) |

The fractions’ numerator is **HEAD-only enabled runes intersected with the implementation’s exported enabled theory**, and the denominator is that implementation closure’s exported enabled runes. They overlap, so columns must not be summed. Dev-only enabled runes: zero at all three anchors. Served-columns’ single HEAD-only rune outside the implementation union is `(:EXECUTABLE-COUNTERPART CREATE-FN-CAT)`.

| Implementation closure | Exported enabled | Exported universal |
| --- | ---: | ---: |
| history-paged | 10,514 | 12,431 |
| catalog-paged | 18,235 | 21,285 |
| payload-arena-extent | 3,003 | 3,479 |

For an all-exported-runes denominator, the corresponding fractions are:

| Consumer | History universal fraction | Catalog universal fraction | Arena universal fraction |
| --- | ---: | ---: | ---: |
| catalog-logic | 3,431/12,431 (27.60%) | 4,278/21,285 (20.10%) | 845/3,479 (24.29%) |
| served-columns | 3,431/12,431 (27.60%) | 6,628/21,285 (31.14%) | 845/3,479 (24.29%) |
| owner-served-carried | 0/12,431 (0.00%) | 847/21,285 (3.98%) | 845/3,479 (24.29%) |

### Attach hazard and the proposed image-only header

**An image-only attachment header plus OW4’s certified attach-table assertion does not by itself cover the compiled-creator hazard.** OW4 checks the admitted image world’s attachment table and current creator tuples; it does not establish which creator already-compiled WITH-LOCAL-STOBJ sites call.

The exact tooth is `tests/acl2/one-world-hole-tests.lisp`. FN-OWH-INTERN uses `(with-local-stobj fn-arena (mv-let (held fn-arena) (fn-cat-intern-list w nil 0 fn-arena) held))`; `(defconst *owh-held* (fn-owh-intern *owh-w*))` is computed, not a literal. Its FASL re-evaluates the initializer using the creator selected when that book compiled. At dev that is the unattached generic’s list foundation. The composing `tests/acl2/one-world-hole-attached-tests.lisp` first includes `../../host/page-read-host` (the attached arena path), then includes `one-world-hole-tests`. The stale list-created arena reaches attached concrete exports; protected export execution can exit non-locally and poison the session’s abstract-stobj invariant state.

Historical hbox run `run-20261013T051009Z-5a3e`, [local certificate log](../../acl2/certify-20261013T051039Z-2486027/tests--acl2--one-world-hole-attached-tests.certify.log): INCLUDE-BOOK at line 62 reports a raw-Lisp error loading the computed book’s FASL. The later `(assert-event (fn-held-p *owh-held*))` **passes**, then line 100 reports `ACL2 Error in CHK-ABSSTOBJ-INVARIANTS: Possible invariance violation`. CERTIFY-BOOK refuses the now-illegal session and names `(@ illegal-to-certify-message)`. The failing certification is the composing book, not the standalone computed book. A passing data assertion is therefore not sufficient evidence of a legal composed world.

[STATEMENT.md](STATEMENT.md) gives OW1/OW3’s compilation mechanism and OW4’s table/creator checks. [foundation-analysis.md](foundation-analysis.md) explains why the list/column foundations remain correspondence references and cannot simply be deleted. [REPAIRS-before-exporter.md](REPAIRS-before-exporter.md) records proof collisions separately and end-of-book illegal-to-certify NIL checks; those theory repairs do not change the initializer or selected compiled creator. The historical *hrt-rows* shape was converted to a literal, but that avoids one initializer rather than covering all compiled callers.

With implementation-free generics compiled in the plain world and attachment only in image worlds, this mismatched-creator possibility returns. An OW4 test that actually includes the hazardous compiled initializer may itself be refused by ACL2’s invariant check; the attach-table assertion alone can observe the correct pairs/tuples and still cannot repair or prove consistent those compiled sites. Covering it would need an additional enforced condition about all reachable compiled creator sites/eager initializers, or a compilation/dispatch design that selects the implementation consistently. No such design or edit is claimed here.

## Six gates and shutdown

| Command | Exit | Evidence |
| --- | ---: | --- |
| `timeout 180 python3 tools/one_world_check.py` | 0 | [log](fam5-gate-one-world.log) |
| `timeout 180 python3 tools/book_roots_check.py` | 0 | [log](fam5-gate-book-roots.log) |
| `timeout 180 python3 tools/host_check.py --attach-order` | 0 | [log](fam5-gate-host-attach-order.log) |
| `timeout 180 python3 tools/host_check.py --world` | 0 | [log](fam5-gate-host-world.log) |
| `timeout 180 python3 tools/extract/world.py --check` | 0 | [log](fam5-gate-extract-world.log) |
| `timeout 180 python3 tools/interface_emit.py --check` | 0 | [log](fam5-gate-interface.log) |

All gates report zero findings/refusals; existing book-root exclusions and source-undecidable cases retain their existing scope. These are static gates, not certification of the modified ADT closure. `secrets_check.py` checked the rule book and census tool: zero findings.

Owned sessions stopped by name through proof_repl: `fam5-ibp`, `fam5-pool`, `fam5-scol`, `fam5-scv`, `fam5-d2-head`, `fam5-d2-dev`, `fam5-d2-owner-head`, `fam5-d2-owner-dev`; every corresponding `fam5-*-stop.log` says stopped. Only these owned sessions were stopped. The wrapper imports tools/proof_repl.py and disables SSH multiplexing because its default control socket is outside writable roots; slot ownership and cached-only policy are unchanged. All long commands used timeout. No laptop ACL2, non-REPL box job, source-loading dependency fallback, certification job, commit, push, deployment or other seat’s file edit.

## A: fifth-family pair fixes

**A28/main’s A ruling is applied: the exported octet bridge and both skip rules are DEFTHMD, with historical-census LOCAL enables. The earlier STOP dispositions in this report are superseded. STOP here for the seat’s recertify.** No commit or certification job.

### Wrong-way sides, measured by PAIRS’ method

`fam5_a_shapes.py` uses PAIRS’ literal DEFTHM/DEFTHMD rewrite-schema parser, splitting conjunctive conclusions, retaining disabled schemas, and excluding non-rewrite and NIL rule classes. It scans books/ only: 1,989 books, 46,526 literal theorem forms, 38,722 rewrite-capable forms. These are source shapes, not enabled-world or macro-generated rune counts. [Complete members and statements](fam5-a-shapes.json).

| Vocabulary / shape | Conclusion branches | Source rules | Books |
| --- | ---: | ---: | ---: |
| positive conclusion fn-cbor-octet-listp | 577 | 561 | 165 |
| positive conclusion adt-octetsp | 41 | 38 | 17 |
| conclusion contains fn-cbor-octet-listp | 676 | 655 | 184 |
| conclusion contains adt-octetsp | 50 | 47 | 18 |
| fn-cbor-octet-listp -> adt-octetsp | 3 | 3 | 3 |
| adt-octetsp -> fn-cbor-octet-listp | 0 | 0 | 0 |
| negative live-numberp conclusion | 4 | 4 | 2 |
| negative live-numberp with fn-cat-live-first hypothesis | 1 | 1 | 1 |
| negative live-numberp with fn-cat-live-last hypothesis | 1 | 1 | 1 |

**Octet pair: FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP is the wrong-way exported side.** The house consumer vocabulary is FN-CBOR-OCTET-LISTP: 561 positive-conclusion rules in 165 books versus 38 ADT-OCTETSP rules in 17 books. The exact bridge direction appears three times, never in reverse; the other two occurrences, FN-ARN-OCTET-LISTP-IS-ADT-OCTETSP and FN-ARP-OCTET-LISTP-IS-ADT-OCTETSP, are already LOCAL serializer/generator proof bridges. That direction has a legitimate private use at the ADT boundary, but global import displaces the much larger consumer vocabulary. FN-SCOL-SCRUB-OCTETS stays in that house vocabulary; no consumer lemma is restated.

**Skip pair: FN-CPL-FIRST-SKIPS and FN-CPL-LAST-SKIPS are expensive backchaining rules and belong opt-in.** Only these two of the four negative live-number schemas put a recursive live-first/live-last search in a hypothesis. FIRST-SKIPS introduces A and TOP, which are absent from its FN-CAT-LIVE-NUMBERP matching term; LAST-SKIPS introduces B. Relieving the hypotheses generates new searches rather than consuming a bound already in the goal. The original FAM5 target and prefix stacks show the recursive expansions. The other two negative schemas are the zero-number facts FN-CPL-LIVE-NUMBERP-0 and FN-CTG-LIVE-NUMBERP-0. The skip rules’ statements and all consumer statements remain unchanged.

### Exact repair and census-derived enables

Changed to DEFTHMD: `books/catalog-paged.lisp`’s FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP, and `books/catalog-live-links.lisp`’s FN-CPL-FIRST-SKIPS and FN-CPL-LAST-SKIPS. ADT-LEN-REGION-BELOW-BODY’s existing DEFTHMD is retained. All four formulas, hypotheses, hints and rule classes are byte-identical.

| Rune | Dev historical books | Qualifying other-lane books | Consumer U after seven exclusions | Derived enable sites |
| --- | ---: | ---: | ---: | --- |
| FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP | 3 | 3 | 2 | books/catalog-pages.lisp (consumer include anchor); host/owner-host.lisp (consumer include anchor); books/catalog-paged.lisp (immediate defining-event LOCAL) |
| FN-CPL-FIRST-SKIPS | 1 | 1 | 1 | books/catalog-live-links.lisp (immediate defining-event LOCAL) |
| FN-CPL-LAST-SKIPS | 0 | 0 | 0 | none; explicit zero-user evidence |
| ADT-LEN-REGION-BELOW-BODY | 0 | 0 | 0 | none; explicit zero-user evidence |

The bridge’s two consumer enables are a new line after catalog-pages’ last top-level include and a replacement of owner-host’s existing combined opener line. The bridge also gets an immediate LOCAL enable after its defining DEFTHMD, based on qualifying dev/other-lane Rules summaries for that book. FIRST-SKIPS gets its immediate defining-book LOCAL enable; it has no downstream consumer user. LAST-SKIPS and the linear bound get none. The source diff is five files: catalog-live-links, catalog-paged, catalog-pages, proto/adt-bytes, host/owner-host.

**Seven consumer exclusions remain intact:** U is still (dev union qualifying other lanes) minus exactly the original seven; none receives a consumer line at its include anchor or an opener enable. Catalog-paged has the selected defining-event exception only: its bridge DEFTHMD token plus adjacent private enable from its own historical evidence. The other six excluded books are entirely byte-identical. The defining-book exception is separately recorded as `defining_needed_runes` / `defining_runes`, not added to consumer U or treated as replay provenance. [Independent exact-token/enable audit](fam5-a-byte-audit.json).

`p1_enables.py` now scans all six selected runes with exact REWRITE/LINEAR class matching. Provenance, successful FN_CERTIFY_SUCCESS/Form/Rules filtering, DEFTHM and implicit/explicit guard summaries, ancestry exclusion and seven consumer exclusions are unchanged. Its definition-book metadata `defined_runes` in [p1-enables.json](p1-enables.json) explicitly records **ADT-LEN-REGION-BELOW-BODY: zero_historical_users=true, empty evidence, empty U**; it likewise records LAST-SKIPS’ zero users. Zero evidence never invents an enable. Existing opener selection remains unchanged.

Commands: `timeout 900 python3 build/vertical-runs/one-world/p1_enables.py --scan`; `timeout 180 python3 build/vertical-runs/one-world/p1_enables.py --apply`; `timeout 30 python3 build/vertical-runs/one-world/p1_enables.py --report`. Outputs regenerated and apply repeated idempotently. The first apply timed out while its recursive export-path search revisited include diamonds; the tool now visits each book once and caches each book/rune result. No provenance or reachability criterion changed. The completed and repeated applies are `fam5-a-census-apply2.log` and `fam5-a-census-apply-repeat.log`.

### Fresh cached-only controls reproduce dev’s proof shape

Two fresh hbox proof_repl sessions use an isolated exact HEAD reference at b32eced13, with compatible cached dependency certificates and no fallback. Session-only theory disables the four proposed default-disabled rules; this models their exported setting without claiming a certificate for the modified libraries. The defining-book LOCAL enables do not export. The unchanged target source forms are used.

| Target | Fresh control | Dev reference | Rules comparison |
| --- | --- | --- | --- |
| FN-SCOL-HEADER-CONTENT-OCTETS | 29 steps, 0.03 s | 29 steps, six Rules; hbox Oct 12 served-columns certificate :937 | Exact same six Rules |
| FN-SCV-FIRST-IS-FIRST-P | 96,658 steps, 0.45 s | 70,608 steps, 22 Rules; hbox Oct 12 served-catalog-view certificate :10603 | Adds PGS-X-NFIX-WHEN-NATP; omits NFIX definition; the same difference as the original FAM5 passing control |

The fresh view session loads through FN-SCV-XDIFF, then admits all 67 unchanged forms through the target under the proposed exported setting: 0 refused, 1,233,538 steps, 7.59 s ACL2 time. That includes the previously expensive off-naturals lemmas. These are single-session times, not two-job certification measurements. [Columns control](fam5-a-scol-control.log), [view control](fam5-a-scv-control.log), [complete dev Rules deltas](fam5-a-rule-comparisons.json). The original failing baseline stacks and independent off/on controls remain above.

### A gates and stop

| Command | Exit | Log |
| --- | ---: | --- |
| `timeout 180 python3 tools/one_world_check.py` | 0 | [log](fam5-a-gate-one-world.log) |
| `timeout 180 python3 tools/book_roots_check.py` | 0 | [log](fam5-a-gate-book-roots.log) |
| `timeout 180 python3 tools/host_check.py --attach-order` | 0 | [log](fam5-a-gate-host-attach-order.log) |
| `timeout 180 python3 tools/host_check.py --world` | 0 | [log](fam5-a-gate-host-world.log) |
| `timeout 180 python3 tools/extract/world.py --check` | 0 | [log](fam5-a-gate-extract-world.log) |
| `timeout 180 python3 tools/interface_emit.py --check` | 0 | [log](fam5-a-gate-interface.log) |

All six static gates pass after the five-file source repair. The source token/enable byte audit, census fixtures and diff whitespace check pass. Owned sessions `fam5-a-scol` and `fam5-a-scv` were stopped by name; [columns stop](fam5-a-scol-stop.log), [view stop](fam5-a-scv-stop.log). No commits or certification jobs. The unrelated untracked ONE-WORLD-B-LOCAL-VOCABULARY tracker item was not opened or changed. **Work stops for the seat’s recertify; certification of this modified closure is not claimed.**

## A: recognizer bridges, complete

**The complete project-owned family in the three requested implementation closures is treated: 52 exported recognizer bridges, comprising 36 literal theorem events and 16 generated rules. K-U64-OCTETS admits with only the SCC bridge disabled in exactly dev’s two Rules and five steps. All six final gates pass. STOP for the seat’s recertify; no commits or certification jobs.**

Parent/source control: `83563270a3ae0b88eecc4f2b6af56ace22de5b4a`. This supersedes the earlier one-bridge-at-a-time scope; the original FAM5 and A measurements above remain historical. The r10 refusal is `build/acl2/certify-20261014T061941Z-2596546/books--charged-totals-header.certify.log`, from `run-20261014T061731Z-57c9` in submit-r10.log.

### Complete discovery, including generated and normalized rules

The script first walks non-LOCAL project include edges from history-paged, catalog-paged and payload-arena-extent: respectively 137, 177 and 23 project books, 177 distinct books in their union at the parent. It records every exported literal call-to-call EQUAL/IFF candidate, with LOCAL/non-rewrite exclusions retained separately. It then measures all three **certified include** worlds in cached-only hbox sessions, enumerating the exported universal theory rather than only enabled runes. Disabled-by-default family members are retained in the inventory. [Source inventory](fam5-bridges-source-inventory.json), [admitted theorem inventory](fam5-bridges-complete.json).

The final check reads ACL2’s actual normalized REWRITE-RULE records (`:rune`, `:equiv`, `:lhs`, `:rhs`, hypotheses count), checks membership in each exported universal theory, and discards DEFINITION records and logical operators. This covers conditional/conjunctive surface statements and generated events. Predicate identification uses admitted automatic Boolean result types and equivalences to such predicates, with IFF predicates retained; names do not select the project family. It distinguishes the byte/extent/tree recognizers from list/stobj-returning functions such as LOOKUP, STAMP and ZERO-LOOP despite their trailing P. The normalized check finds **the same 52 project names, no additional project member and no surface-only member**. [Normalized record audit](fam5-bridges-normalized-audit.json), [query helpers](fam5-bridges-record-helpers-v3.lisp), [checker](fam5_bridges_record_audit.py).

All query worlds use one compatible cached dependency set for the exact parent. The normalized-query session uses an isolated parent archive so the modified working tree cannot be mistaken for a certified dependency closure. The control/inventory tools install cached sets only; no source-loading fallback or certification occurs.

Project ownership is explicit: the initial ACL2 world’s rules are subtracted. Five system-library rules are inventoried separately and unchanged under the worktree-only edit boundary: `LIST-EQUIV-WHEN-ATOM-RIGHT`, `LIST-EQUIV-WHEN-ATOM-LEFT`, `ELEMENT-LIST-NONEMPTY-P-OF-SINGLETON-NON-TRUE-LIST`, `ELEMENT-LIST-NONEMPTY-P-OF-SINGLETON-TRUE-LIST`, `ELEMENT-LIST-NONEMPTY-P-OF-CONS`. They have no defining event in project books/. Neither LOCAL helpers such as ADT-TREE-OCTET-LISTP-IS-ADT-OCTETSP nor non-rewrite declarations are silently counted as exported project rules.

### Every project member and its census

All listed literal events are now DEFTHMD (including already-opt-in members); all generated members are emitted DEFTHMD by their generator. No formula, hypothesis, hint or rule class changes. U is still the successful dev/qualifying-other-lane union minus the same seven consumer exclusions. Counts below are book counts; complete event/guard provenance is in p1-enables.json.

| Rune | Defining book | Treatment | Dev / other / consumer U |
| --- | --- | --- | ---: |
| ADT-G-COLP-IS-ALL-ELT-P | books/proto/adt-lib.lisp | literal | 0 / 0 / 0 |
| ADT-KCORR-MEM | books/proto/adt-key-lib.lisp | literal | 2 / 0 / 2 |
| ADT-KGOOD-OF-CORR | books/proto/adt-key-lib.lisp | literal | 0 / 0 / 0 |
| ADT-REC-P-OF-LIST1 | books/def-representation-lib.lisp | literal | 6 / 8 / 7 |
| ADT-TREE-OKP-IS-SCCB-TREEP | books/def-representation-tree-walk.lisp | literal | 3 / 3 / 2 |
| FN-ACCEPTED-IFF-ID-MEMBER | books/acceptance-invariants.lisp | literal | 20 / 20 / 20 |
| FN-ARENA-BYTES$C-GET-PAYLOAD-OKP-BRIDGE | books/payload-arena-bytes.lisp | generator | 1 / 1 / 1 |
| FN-ARENA-BYTES$C-PAYLOAD-LENP-IS | books/payload-arena-bytes.lisp | generator | 1 / 1 / 1 |
| FN-ARENA-BYTES$C-PAYLOAD-OFFP-IS | books/payload-arena-bytes.lisp | generator | 1 / 1 / 1 |
| FN-ARENA-BYTES$C-POOLP-IS | books/payload-arena-bytes.lisp | generator | 1 / 1 / 1 |
| FN-ARENA-BYTESP-IS-SCALAR-SEQ-P | books/payload-arena-bytes.lisp | generator | 1 / 1 / 1 |
| FN-ARENA-P-IS-PAYLOAD-LISTP | books/payload-arena.lisp | literal | 16 / 15 / 16 |
| FN-ARENA-PAGEDP-IS-SCALAR-SEQ-P | books/payload-arena-paged.lisp | generator | 0 / 0 / 0 |
| FN-ARN-EXTENTP-OF-LIST | books/payload-arena-extent-logic.lisp | literal | 3 / 3 / 3 |
| FN-ARN-LZ-EXTENTP-OF-LIST | books/payload-arena-extent-logic.lisp | literal | 1 / 1 / 1 |
| FN-ARTICLE-FIELD-CLOSEDP-OF-CLOSE-FIELD | books/article.lisp | literal | 2 / 2 / 2 |
| FN-ARTICLE-OPEN-FIELD-CLOSEDP-IS-FIELD-CLOSEDP | books/article.lisp | literal | 2 / 2 / 2 |
| FN-ARTICLES-FRESHP-IS-ONE-PASS | books/acceptance.lisp | literal | 1 / 1 / 1 |
| FN-ARX-FILESP-IS-TRUE-LISTP | books/payload-arena-extent.lisp | literal | 1 / 1 / 1 |
| FN-ARX-PAGE-BYTESP-IS-OCTETS-BUFP | books/payload-arena-extent.lisp | literal | 1 / 1 / 1 |
| FN-CAT$P-LIVEP-IS-LIVE | books/catalog-paged.lisp | literal | 1 / 1 / 0 |
| FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP | books/catalog-paged.lisp | literal | 3 / 3 / 2 |
| FN-CPL-LIVE-AT-P-IS-LIVE | books/catalog-live-links.lisp | literal | 1 / 1 / 1 |
| FN-CPL-OKP-IS-ALL-GOODP | books/catalog-live-links.lisp | literal | 0 / 0 / 0 |
| FN-CROWP-IS-SEQ-P | books/catalog-paged.lisp | generator | 1 / 1 / 0 |
| FN-DLZ$C-GET-OCTET-OKP-BRIDGE | books/decoded-payload-buffer.lisp | generator | 1 / 1 / 1 |
| FN-DLZ$C-OCTETP-IS | books/decoded-payload-buffer.lisp | generator | 1 / 1 / 1 |
| FN-DLZ$C-POOLP-IS | books/decoded-payload-buffer.lisp | generator | 1 / 1 / 1 |
| FN-DLZP-IS-SCALAR-SEQ-P | books/decoded-payload-buffer.lisp | generator | 0 / 0 / 0 |
| FN-HIST$CP-IS-IX-CP | books/history-columns-foundation.lisp | generator | 0 / 0 / 0 |
| FN-HIST-P-IS-TRUE-LISTP | books/history-columns.lisp | literal | 10 / 11 / 11 |
| FN-HP-IN-BLOCK-RBLOCK-C-IS-IN-REGION | books/history-pages-grow-cap.lisp | literal | 1 / 1 / 1 |
| FN-HP-IN-BLOCK-RBLOCK-IS-IN-REGION | books/history-pages-grow.lisp | literal | 1 / 1 / 1 |
| FN-HP-VHOLD-IS-X | books/history-pages-read.lisp | literal | 4 / 2 / 4 |
| FN-HRC-SFXP-IS-TRUE-LISTP | books/history-records.lisp | literal | 9 / 8 / 9 |
| FN-KS-ALL-BOUNDP-IS-SUBSET | books/acceptance-alloc.lisp | literal | 1 / 1 / 1 |
| FN-KS-DISTINCTP-IS-NODUPP | books/acceptance-alloc.lisp | literal | 1 / 1 / 1 |
| FN-KS-SUBSETP-IS-SUBSET-LOGIC | books/acceptance-alloc.lisp | literal | 1 / 1 / 1 |
| FN-MPXT2P-IS-FN-MPXTP | books/msgid-pages-exec.lisp | literal | 1 / 1 / 0 |
| FN-NO-DUPLICATESP-IS-KS-NODUPP | books/acceptance-alloc.lisp | literal | 1 / 1 / 1 |
| FN-NODE-ARTICLES-HAVE-ARCHIVE-BINDINGSP-IS-INDEXED | books/node.lisp | literal | 1 / 1 / 1 |
| FN-OCT-OCTETS-P-IS-OCTET-LISTP | books/octets-stobj.lisp | literal | 15 / 16 / 17 |
| FN-OCT-PREFIX-EQUALP-IS-LIST-PREFIXP | books/octets-stobj.lisp | literal | 1 / 1 / 1 |
| FN-OCTETS-PG-P-IS-OCTET-LISTP | books/pagestore-words.lisp | generator | 13 / 12 / 13 |
| FN-RETAIN-KNOWN-ID-SCANP-IS-KNOWN-IDP | books/retention.lisp | literal | 1 / 1 / 1 |
| FN-RETAIN-KS-DISJOINTP-KS-IS-LOGIC | books/retention.lisp | generator | 0 / 0 / 0 |
| FN-RETAIN-KS-DISJOINTP-SCAN-AFTER-FILL | books/retention.lisp | generator | 1 / 1 / 1 |
| FN-RETAIN-KS-DISJOINTP-WALK-IS-LOGIC | books/retention.lisp | generator | 0 / 0 / 0 |
| FN-RETAIN-NO-DUPLICATESP-IS-NO-DUPLICATESP | books/retention.lisp | literal | 0 / 0 / 0 |
| FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP | books/catalog-paged.lisp | literal | 3 / 3 / 2 |
| FN-SCCB-SCC-OCTETP-IS-CBOR-OCTETP | books/store-checkpoint-buffer.lisp | literal | 7 / 8 / 8 |
| FN-SUBSETP-IS-KS-SUBSET-LOGIC | books/acceptance-alloc.lisp | literal | 1 / 1 / 1 |

### Generators, private proofs, and fan-out

Ten template sites in five existing generators are transformed by one script with fixtures: proto/adt (column, pool and get-OKP bridges); def-representation (scalar/record recognizers); def-representation-index (foundation recognizer); def-buffer (octet-list recognizer); def-keyset-check (three predicate refinements). This changes the design of record rather than adding instance twins. Scalar recognizers with an invariant still conclude AND and remain outside this direct-call family; the template chooses DEFTHMD only for its direct recognizer form. [Transformation](fam5_bridges_templates.py), [template/byte audit](fam5-bridges-byte-audit.json).

Those shared templates also emit the same bridge classes outside the original three closures. The census therefore covers **all 61 existing generated rule names across 33 current declaration sites**, not just the 16 observed in the closures. The registry includes their successful definition-summary provenance, verifies the current declaring instance, and excludes scalar invariant forms. With the existing opener/linear/skip entries and literal members, the complete census list has **102 rules**. [Full registry and fan-out](fam5-bridges-registry.json).

Generated bridges keep the generator’s uniform **internal** proof environment through `fn-proof-bridge-private-enable` in the small new `books/proof-bridge-policy.lisp`: immediately after emitting its own DEFTHMD, a generator emits a LOCAL enable for its internal proofs. This is uniform for future instances and uses no frozen name allow-list. These private events do not authorize consumer opens. Where a representation ENCAPSULATE ends that private scope, the producer book receives an additional LOCAL enable after the declaration **only when its own successful historical Rules require it**. Ordinary consumer enables likewise follow U. The two roles are separate in p1-enables.json (`generated_internal_private_events` versus `generated_defining_enable_events`).

The new event builder admits with its guard verified in a fresh cached-only hbox session (two source forms, zero prover steps). Controls check both a current generated name and a fresh name produce exactly the private LOCAL event; a new instance does not require historical-name bootstrapping. This is event/guard admission, not certification. [Start](fam5-bridges-policy-uniform-start.log), [controls](fam5-bridges-policy-uniform-controls.log).

### Provenance, exclusions and byte identity

The regenerated census processes 175 current subjects and changes 120 files relative to the parent (119 tracked files plus the new proof-only event builder). Most changes are derived combined enable-line insertions/replacements. The independent audit checks every literal theorem’s entire name/formula/hints/rule-class tail byte-for-byte, the ten permitted template transformations, preservation of unrelated events, scalar invariant handling, template idempotence, and exact non-enable bytes in all other consumers. [Audit](fam5-bridges-byte-audit.json).

The seven consumer exclusions remain exactly the original set; no excluded book receives an imported-family line at its include anchor. Five are byte-identical. Catalog-paged and msgid-pages-exec have only selected defining-event/private-proof exceptions; ordinary excluded imports are not relabeled as defining uses. The catalog-paged historical imported uses of ADT-REC-P-OF-LIST1 and ADT-TREE-OKP-IS-SCCB-TREEP remain excluded from automatic consumer enables. Existing explicit hints remain unchanged; whole-book proof acceptance belongs to the seat’s recertify.

Four qualifying historical subjects no longer exist at HEAD: `books/catalog-columns-guards.lisp`, `books/checkpoint-payloads-exec.lisp`, `books/extent-cache.lisp`, `books/over-render-lease.lisp`. Their evidence and empty enable placement are retained in p1-enables.json; no D68-retired file or layout is recreated. U itself is not reduced to hide them.

ADT-LEN-REGION-BELOW-BODY’s DEFTHMD is retained. Its p1-enables.json defining entry explicitly has zero_historical_users=true, empty evidence and empty U, with no enable; LAST-SKIPS’ zero-user entry is retained too. The regular census keeps the same October/all-event and September/guard-only scopes, FN_CERTIFY_SUCCESS requirement, DEFTHM/DEFUN/VERIFY-GUARDS summaries, own/ancestry exclusions, and separate four proto-guard authorizations. Dotted REWRITE subrunes are matched exactly by event name, and `$` names are shell-quoted for the read-only remote scan.

Generation: `timeout 900 python3 build/vertical-runs/one-world/p1_enables.py --scan`; `timeout 180 python3 build/vertical-runs/one-world/p1_enables.py --apply`; `timeout 30 python3 build/vertical-runs/one-world/p1_enables.py --report`. Apply is repeated idempotently. [P1.md](P1.md), [p1-census.json](p1-census.json), [p1-enables.json](p1-enables.json), [p1-enables.txt](p1-enables.txt) are regenerated. Intermediate-plan acceptance code was removed; current files must equal immutable HEAD or the exact generated result, and are checked again before writing.

### K-U64-OCTETS: exact dev proof

| World/control | Result | Rules | Steps | ACL2 seconds |
| --- | --- | --- | ---: | ---: |
| Parent/r10 baseline | same refusal | includes FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP and ADT-OCTETSP expansion | 12,280 | 0.18 |
| Only FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP disabled in session | admits unchanged local theorem | `(:REWRITE FN-SCC-U64-SHAPE)`, `(:TYPE-PRESCRIPTION FN-SCC-OCTET-LISTP)` | 5 | 0.02 |
| Dev successful certificate | admits | exactly the same two Rules | 5 | historical |

The dev reference is `hbox:/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-20261012T091354Z-3204821/books--charged-totals-header.certify.log:838`. Three local successful dev summaries and the hbox reference agree on the two Rules and five steps. The SCC→ADT bridge displaced the goal’s native SCC recognizer so the existing U64 shape theorem could not match; disabling only the bridge restores that match and avoids induction. No consumer statement, induction hint or arithmetic bound is changed. [Baseline](fam5-bridges-u64-baseline.log), [control](fam5-bridges-u64-control.log), [comparison](fam5-bridges-u64-comparison.json), [local history](fam5-bridges-dev-history.json), [hbox history](fam5-bridges-dev-remote-history.json).

### Final gates and shutdown

| Command | Exit | Evidence |
| --- | ---: | --- |
| `timeout 180 python3 tools/one_world_check.py` | 0 | [log](fam5-bridges-gate-one-world.log) |
| `timeout 180 python3 tools/book_roots_check.py` | 0 | [log](fam5-bridges-gate-book-roots.log) |
| `timeout 180 python3 tools/host_check.py --attach-order` | 0 | [log](fam5-bridges-gate-host-attach-order.log) |
| `timeout 180 python3 tools/host_check.py --world` | 0 | [log](fam5-bridges-gate-host-world.log) |
| `timeout 180 python3 tools/extract/world.py --check` | 0 | [log](fam5-bridges-gate-extract-world.log) |
| `timeout 180 python3 tools/interface_emit.py --check` | 0 | [log](fam5-bridges-gate-interface.log) |

All six gates pass at the final source state; the existing exclusion/undecidable-case scopes remain unchanged. The source/fixture audit and diff whitespace check pass. These are static gates and narrow cached-world controls, not certification of the modified 120-file closure.

Owned sessions stopped by name: fam5-bridges-u64, fam5-bridges-world, fam5-bridges-records and fam5-bridges-policy-uniform; the earlier policy prototype had already expired and its named stop confirms no live session. Corresponding `fam5-bridges-*-stop.log` files record the results. Only owned sessions were addressed. No laptop ACL2, non-REPL box job, certification, commit, push, deployment, external model, or other seat’s file edit. **STOP for the seat’s recertify.**
