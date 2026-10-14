# Recorded rewrite pairs: measurement and proposed direction

The two recorded slice pairs have the **local successor-to-CDR rule on the wrong side**: `FN-MPX-NTHCDR-CDR` and `FN-CTG-NTHCDR-CDR`. The house slice form is successor `NTHCDR`, not outer `CDR(NTHCDR)`. The positive-field displacements point to **ADT-NTH-1+** as the wrong-way universal opener. **ADT-NTH-0 must be considered separately**: index zero normally becomes `CAR`, so a zero-only displacement calls for an equivalent local normal-form statement, not disabling that imported rule indiscriminately.

No book changed, no commit, no certification or proof attempt. Proposals below have not been admission-tested. Recorded dev/lane comparisons establish theory sensitivity; they do not by themselves prove every named dev rule is an overlapping pair.

## Imported rules (exact ACL2 rule records)

| ID | Definition | Hypothesis | Exact LHS → RHS | Observed Rules-list blast radius |
| --- | --- | --- | --- | --- |
| A0: ADT-NTH-0 | books/proto/adt-key-lib.lisp:557 | `T` | `(nth 0 x)` → `(car x)` | **1453** distinct event summaries in **213** books; 2235 recorded uses |
| A1: ADT-NTH-1+ | books/proto/adt-key-lib.lisp:553 | `(natp j)` | `(nth (+ 1 j) x)` → `(nth j (cdr x))` | **1274** distinct event summaries in **198** books; 1803 recorded uses |
| AC: ADT-CDR-NTHCDR | books/proto/adt-key-lib.lisp:70 | `(natp j)` | `(cdr (nthcdr j r))` → `(nthcdr (+ 1 j) r)` | **35** distinct event summaries in **22** books; 51 recorded uses |

These are enabled in the measured certified-history-columns world. `:pr` reports no loop stopper for A1 or AC; A0 is an abbreviation. Evidence: [pairs-pr2.log](pairs-pr2.log). Source spells AC’s RHS `(nthcdr (1+ j) r)`; ACL2 translates `1+` to `(+ 1 j)` as printed above.

## House normal forms and rule-shape counts

Counts are literal `defthm` / `defthmd` **source rewrite schemas**, splitting conjunctive conclusions and excluding explicit non-rewrite rule classes and `:rule-classes nil`. Disabled-by-default schemas remain in the count. They are not enabled-world counts or a census of macro-generated ACL2 runes. Each rule occurrence is keyed by book, source line and name; book counts are distinct paths. Conditional/predicate rules retain their full hypotheses in the statement appendix.

The script scanned **1989 books**, **46526** literal theorem forms, of which **38722** permit rewrite rules. No reference-tree or build copies were included. [pairs_measure.py](pairs_measure.py), [pairs_families.py](pairs_families.py), [pairs-shapes.json](pairs-shapes.json), and [pairs-families.json](pairs-families.json) contain the selectors, complete members, and counts.

| Shape / direction | Conclusion branches | Source rules | Books |
| --- | ---: | ---: | ---: |
| cdr(nthcdr) -> successor nthcdr: exact inverse | 29 | 29 | 28 |
| successor nthcdr -> cdr(nthcdr): exact inverse | 7 | 7 | 7 |
| cdr(nthcdr) -> nthcdr: any root | 35 | 35 | 34 |
| RHS positive fixed-index nth | 234 | 105 | 40 |
| RHS positive fixed-index CAR-CDR selector | 50 | 41 | 35 |
| RHS nth 0 | 44 | 36 | 15 |
| nth 0 -> car: exact inverse | 8 | 8 | 6 |
| car -> nth 0: exact inverse | 0 | 0 | 0 |
| successor nth -> nth of cdr: peel | 5 | 5 | 4 |
| nth of cdr -> indexed nth: raise | 0 | 0 | 0 |

For the exact successor/CDR inverse pair, **29 rules in 28 books point toward successor NTHCDR**, versus **7 rules in 7 books away**. Four additional successor rules use `nfix`; two other forward rules push CDR into the list argument. Counting all RHS roots gives 194 rules in 108 books ending in NTHCDR versus 7 in 7 ending in CDR(NTHCDR). These larger counts include unrelated slice equations; the exact-inverse subset is the decisive comparison.

For positive fixed fields on opaque state, **105 rules in 40 books have a positive fixed-index NTH RHS**, versus **41 rules in 35 books a CAR/CDR selector RHS**. The full root census is 616 NTH-RHS rules in 245 books versus 256 selector-RHS rules in 153 books (see JSON; unrelated list heads are included). This supports the repository’s indexed-field vocabulary; it does not claim every list context uses NTH. Five universal successor-peeling schemas in four books run the other way. There is no literal inverse raising schema in books/, but the certified lists-light library provides it.

Zero has different evidence: **8 source rule occurrences in 6 books explicitly rewrite NTH-0 to CAR**, and **none explicitly rewrite CAR back to NTH-0**. The 36 NTH-0-RHS schemas in 15 books show that some local facts retain unnormalized zero fields, not that the zero opener is contrary to ACL2’s normal form.

Certified-world statements, read through hbox proof_repl (ACL2 8.7):

```lisp
; ACL2 builtins (-645 / -644): consume an explicit CONS.
(nth 0 (cons a l)) -> a
; integerp n, n >= 0:
(nth (+ 1 n) (cons a l)) -> (nth n l)
; kestrel/lists-light/nth, disabled by default in the measured world:
(nth n (cons x y)) -> (if (zp n) x (nth (+ -1 n) y)) ; NTH-OF-CONS
; same certified library, indexed form over the original opaque list:
(nth n (cdr x)) -> (nth (+ 1 (nfix n)) x)           ; NTH-OF-CDR
; std/lists/nth, enabled:
; zp n:
(nth n x) -> (car x)                             ; NTH-WHEN-ZP
; std/lists/nthcdr, enabled:
(nthcdr i (cdr x)) -> (cdr (nthcdr i x))           ; NTHCDR-OF-CDR
```

`NTHCDR-OF-CDR` produces an intermediate outer CDR; AC then gives successor NTHCDR for natural i. It is not a rule from successor NTHCDR back to CDR. `NTH-OF-CONS` is in **kestrel/lists-light**, not std/lists/nth in this toolchain. It was absent from the initial std world; the certified lists-light include supplied its exact statement. Positive explicit-cons reduction is compatible with preserving NTH on an opaque field/array. A1 has no explicit-cons restriction and reverses `NTH-OF-CDR`: for natp j, `(nth (+ 1 j) x) → (nth j (cdr x)) → (nth (+ 1 (nfix j)) x) = (nth (+ 1 j) x)`. This additional library inverse is supporting direction evidence, not a newly recorded rounds-1–5 collision.

Evidence: [pairs-pr2.log](pairs-pr2.log), [pairs-std-pr.log](pairs-std-pr.log), [pairs-std-pr2.log](pairs-std-pr2.log), [pairs-std-pr3.log](pairs-std-pr3.log), [pairs-nth-light-pr.log](pairs-nth-light-pr.log). Failed name queries are preserved, not silently replaced by assumed statements.

## Fix policy for the wrong-way side only

- **F-L — disable by default:** retain the exact local theorem and hypotheses, but make `FN-MPX-NTHCDR-CDR` / `FN-CTG-NTHCDR-CDR` disabled rewrite rules (e.g. local `defthmd`). Keep AC enabled. Do not flip/disable AC. Align the induction proof’s slice terms to successor NTHCDR; this report does not claim the old proof succeeds merely by toggling the local rule. Blast radius: 1 pages event / 2 catalog events observed using those local rules, rather than AC’s 35 events in 22 books.

- **F-P — disable by default:** make `ADT-NTH-1+` an opt-in opener in its defining library. Keep its theorem and NATP hypothesis unchanged; explicit-cons builtin reductions remain available. This removes the universal opaque-list peeling direction and the 1024-step expansion. Its observed blast radius is **1274 events in 198 books**; affected proofs that intentionally open opaque lists need a deliberate local enable. This is a larger, measured source-policy change, not a one-event include-order workaround. A generic loop-stopper does not address eager constant-index descent; a `syntaxp` explicit-cons guard would change applicability and create overlap with the builtins, so default-disable is the simpler proposal.

- **F-Z — restate to the normal form:** on a zero-only local overlap, replace every literal `(nth 0 x)` occurrence in the local theorem’s hypotheses and conclusion by `(car x)`; retain all conjuncts, bounds and rule classes. Keep A0. For a universal natural-index field/frame theorem whose zero instance is needed, retain the universal equality and supply its equivalent CAR zero specialization (or restate the indexed expression as `if (zp i) then (car x) else (nth i x)` under NATP i). No imported A0 disable is proposed. These are theorem-preserving changes; the evidence below distinguishes a necessary new match from a merely equivalent cleanup.

Let Z be recursive substitution of CAR for literal NTH-0. Certified A0 proves each replaced term equal for **all ACL2 objects**, so congruence gives `iff(S, Z(S))` for the **whole original formula**, including hypotheses. For NATP i, `(if (zp i) (car x) (nth i x)) = (nth i x)` by the zero theorem and the positive branch. This is an equivalence argument, not a newly certified equivalence theorem. Examples:

```lisp
; Keep exactly the same FN-CAT$C-APPLY-PLAN-FIELDS zero-frame meaning:
(equal (nth 0 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 0 fn-cat$c))
; equivalent normal-form clause:
(equal (car (fn-cat$c-apply-plan plan seq fn-cat$c)) (car fn-cat$c))

; Whole tag-bridge conclusion (hypotheses unchanged):
(equal (fn-ibp-table-word slot fn-ibp-table-page)
       (fn-mpl-tag-at 0 slot (nth 0 fn-ibp-table-page)))
; equivalent normal-form conclusion:
(equal (fn-ibp-table-word slot fn-ibp-table-page)
       (fn-mpl-tag-at 0 slot (car fn-ibp-table-page)))

; NATP i, i < LEN l: equivalent entire cons-fold equality
(equal (cons (if (zp i) (car l) (nth i l)) (nthcdr (+ 1 i) l))
       (nthcdr i l))
```

A displacement is a proof matching defect only when it removes a needed canonical redex/fact. A true opener and a true local lemma can coexist semantically. A lemma stated on an unnormalized zero term is not evidence that A0 is defective. Conversely, retaining positive opaque-field NTH vocabulary is not an unnormalized-zero mistake.

## Pair list covering the recorded events

A0/A1/AC refer to their exact maps above; every named local statement and its exact LHS → RHS branches are in the appendix. A **supporting dependency** is a rule named by the earlier dev comparison whose LHS has no overlap with the imported opener. It remains listed for complete coverage, but is not promoted to an invented direct pair. D-P = positive field displacement; D-Z = zero normal-form mismatch; D-E = eager finite expansion. The table separates those from genuine inverse cycles L1/L2.

| Recorded collision/event | Imported map | Local rule(s), source location, observed uses | Kind | Term / applicability affected | House normal form | Wrong-way side and proposed fix |
| --- | --- | --- | --- | --- | --- | --- |
| R1 pages; recertify #5 repeats it | AC | [FN-MPX-NTHCDR-CDR](#fn-mpx-nthcdr-cdr) (books/msgid-pages.lisp:85; **1** events) | LOOP, L1 | `(nthcdr (+ 1 i) l) → (cdr (nthcdr i l)) → (nthcdr (+ 1 i) l)`; `natp i`. | Successor NTHCDR (L1/L2) | **FN-MPX-NTHCDR-CDR**, F-L; 1 event. It introduces the noncanonical outer CDR. |
| R2 pages-exec: FN-MPXT-KEY-FROM-IS-NTHCDR | A1; A0 at zero specialization | [FN-MPXT-RECOGNIZER-FACTS](#fn-mpxt-recognizer-facts) (books/msgid-pages-exec.lisp:2594; **4** events)<br>[FN-MPXT-NTHCDR-UNFOLD](#fn-mpxt-nthcdr-unfold) (books/msgid-pages-exec.lisp:2626; **2** events) | DISPLACEMENT, D-P / D-Z | `(nth 3 x) → (nth 2 (cdr x)) → … → (car (cdddr x))`; cons-pattern `(cons (nth i l) (nthcdr (+ 1 i) l))` when `i` is a successor or 0. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274 events). Zero cons-pattern: **FN-MPXT-NTHCDR-UNFOLD**, F-Z (2). Recognizer facts have no NTH-0 subterm. |
| R3/A27 linear-exec: key-from and set-key list vocabulary | A1; A0 for exposed zero fields | [FN-MLH-RECOGNIZER-FACTS](#fn-mlh-recognizer-facts) (books/msgid-linear-exec.lisp:2694; **3** events)<br>[FN-MLH-NTHCDR-UNFOLD](#fn-mlh-nthcdr-unfold) (books/msgid-linear-exec.lisp:2730; **2** events)<br>[FN-MLH-SET-KEY-FROM-OVER-A-LIST](#fn-mlh-set-key-from-over-a-list) (books/msgid-linear-exec.lisp:2773; **0** events)<br>[FN-MLH-SET-KEY-IS-A-LIST](#fn-mlh-set-key-is-a-list) (books/msgid-linear-exec.lisp:2783; **6** events) | DISPLACEMENT, D-P / D-Z; list lemmas are supporting dependencies | `(nth 5 x) → (nth 4 (cdr x)) → … → (car (cdddddr x))`; unfold has the same cons-pattern as pages-exec. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P. Zero specialization: **FN-MLH-NTHCDR-UNFOLD**, F-Z (2). Neither set-key list lemma has NTH in its LHS; do not restate/disable it on this evidence. |
| R3/A27 probe-layout: operational next/layout step | A1 | FN-MPXT-WI (see builtin/generated rule below; **6** events) | DISPLACEMENT / eager expansion, D-E; not a two-rule LOOP | Generated definition exposes `(nth 1024 (nth 0 fn-mpxt))`; A0 makes the inner field CAR, then A1 gives `nth 1023 (cdr (car fn-mpxt))`, …, 1024 decreasing steps. | Positive opaque field/array: NTH; index zero: CAR | **ADT-NTH-1+**, F-P. FN-MPXT-WI is a definition in the imported pages-exec book, not a probe-local rewrite inverse; retain it. |
| R3/A27 probe-layout: placed-entry reachability | A0 / A1 | [FN-MPL-CURSOR-FIELD-BOUNDS](#fn-mpl-cursor-field-bounds) (books/msgid-probe-layout.lisp:162; **7** events) | DISPLACEMENT claim, D-Z / D-P; forward-chaining, not an opposing rewrite | `(nth 0 cursor) → (car cursor)`; `(nth 1 cursor) → (car (cdr cursor))`, `(nth 2 cursor) → (car (cddr cursor))`. The theorem already includes CAR bounds as well as NTH-0 bounds. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P. Zero: no demonstrated defect—CAR facts already exist; F-Z on **FN-MPL-CURSOR-FIELD-BOUNDS** (7) is an equivalent cleanup, not a proved repair necessity. |
| R4 chunk: NEXT refinement, PLACE guards, PLACE refinement | A0 / A1 | [FN-MIQ-CHUNK-TAG-IS-PAGE-TAG](#fn-miq-chunk-tag-is-page-tag) (books/msgid-query-chunk.lisp:45; **2** events)<br>[FN-MIQ-CHUNK-SEQ-IS-PAGE-SEQ](#fn-miq-chunk-seq-is-page-seq) (books/msgid-query-chunk.lisp:53; **1** events)<br>[FN-MPL-CURSOR-FIELD-BOUNDS](#fn-mpl-cursor-field-bounds) (books/msgid-probe-layout.lisp:162; **7** events)<br>NTH-UPDATE-NTH (see builtin/generated rule below; **587** events) | Reported DISPLACEMENT; D-P and supporting dependencies; zero bridge is not direct LHS overlap | Cursor NTH-1/2 fields normalize before bounds are used. Bridge **RHS** `(nth 0 fn-ibp-table-page) → (car fn-ibp-table-page)`; bridge LHS is FN-IBP-TABLE-WORD with a variable slot. | Positive opaque field/array: NTH; index zero: CAR | **ADT-NTH-1+**, F-P, for positive cursor fields. A0 does not erase either bridge LHS. F-Z on the two **FN-MIQ-CHUNK-…** statements (2 / 1 events) preserves their meaning; no independent zero bridge defect is established. |
| R4 catalog: fn-mpxt-spec-from-is-cat-seqs-for | AC | [FN-CTG-NTHCDR-CDR](#fn-ctg-nthcdr-cdr) (books/catalog-logic.lisp:2428; **2** events)<br>[FN-CTG-CAR-NTHCDR](#fn-ctg-car-nthcdr) (books/catalog-logic.lisp:2431; **2** events)<br>[FN-CTG-CONSP-NTHCDR](#fn-ctg-consp-nthcdr) (books/catalog-logic.lisp:2434; **2** events) | LOOP, L2; CAR/CONSP facts are supporting dependencies | Same L1 cycle, with FN-CTG-NTHCDR-CDR. AC has no LHS overlap with CAR-NTHCDR or CONSP-NTHCDR. | Successor NTHCDR (L1/L2) | **FN-CTG-NTHCDR-CDR**, F-L; 2 events. The CAR and CONSP rules already preserve house slice vocabulary. |
| R4 catalog: fn-ctg-scan-is-seqs-for | AC | [FN-CTG-NTHCDR-CDR](#fn-ctg-nthcdr-cdr) (books/catalog-logic.lisp:2428; **2** events)<br>[FN-CTG-ROWS-CORR-NTH](#fn-ctg-rows-corr-nth) (books/catalog-logic.lisp:2130; **15** events) | LOOP, L2; ROWS-CORR-NTH is a supporting dependency | Same cycle. ROWS-CORR-NTH is `(nth i rows) → (nth i c)`; AC cannot directly overlap its LHS. | Successor NTHCDR (L1/L2) | **FN-CTG-NTHCDR-CDR**, F-L; 2 events. Do not disable/restate ROWS-CORR-NTH. |
| R4 catalog: fn-ctg-numbers-okp-old-keys | A0 / A1 (reported) | [FN-CTG-PLAN-NUMBERS-IS-ASSIGN](#fn-ctg-plan-numbers-is-assign) (books/catalog-logic.lisp:2257; **4** events)<br>[FN-CTG-NPUTS-LOOKUP](#fn-ctg-nputs-lookup) (books/catalog-logic.lisp:2227; **3** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 4 fn-cat$c)` in plan applicability hypotheses; NPUTS has no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: fn-ctg-commit-numbers-cover-row-any | A0 / A1 (reported) | [FN-CTG-PLAN-NUMBERS-IS-ASSIGN](#fn-ctg-plan-numbers-is-assign) (books/catalog-logic.lisp:2257; **4** events)<br>[FN-CTG-NPUTS-LOOKUP](#fn-ctg-nputs-lookup) (books/catalog-logic.lisp:2227; **3** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | Same positive group-table field `(nth 4 fn-cat$c)`. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: fn-ctg-commit-groups-cover-row | A0 / A1 (reported) | [FN-CTG-GPUTS-LOOKUP](#fn-ctg-gputs-lookup) (books/catalog-logic.lisp:2279; **3** events)<br>[FN-CTG-GROUPS-COVER-ROWP-MONOTONE](#fn-ctg-groups-cover-rowp-monotone) (books/catalog-logic.lisp:2680; **2** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 4 fn-cat$c)` in GPUTS hypotheses; MONOTONE has no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: fn-ctg-commit-groups-okp-keys | A0 / A1 (reported) | [FN-CTG-GPUTS-LOOKUP](#fn-ctg-gputs-lookup) (books/catalog-logic.lisp:2279; **3** events)<br>[FN-CTG-GROUPS-ENTRY-BOUND](#fn-ctg-groups-entry-bound) (books/catalog-logic.lisp:2236; **13** events)<br>[FN-CTG-HIGH-APPEND](#fn-ctg-high-append) (books/catalog-logic.lisp:1533; **6** events)<br>[FN-CTG-ROWS-APPEND](#fn-ctg-rows-append) (books/catalog-logic.lisp:1538; **2** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 4 fn-cat$c)`; ENTRY-BOUND, HIGH-APPEND and ROWS-APPEND have no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: fn-ctg-index-add-fields | A0 / A1 (reported) | NTH-UPDATE-NTH (see builtin/generated rule below; **587** events) | DISPLACEMENT, D-P / D-Z; supporting rules explicitly marked in term column | `(nth k (update-nth n val l))` is opened before the builtin update rule, especially fixed indices 2 and 9. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). Zero only: F-Z on a CAR/update specialization in this consumer (the builtin itself stays unchanged). This is the equivalent local normal-form statement, not an A0 disable. |
| R4 catalog: fn-ctg-commit-fields | A0 / A1 (reported) | [FN-CTG-APPLY-PLAN-FIELDS](#fn-ctg-apply-plan-fields) (books/catalog-logic.lisp:2214; **2** events)<br>[FN-CTG-APPLY-PLAN-FIELDS-910](#fn-ctg-apply-plan-fields-910) (books/catalog-logic.lisp:2810; **1** events)<br>[FN-CTG-INDEX-ADD-FIELDS](#fn-ctg-index-add-fields) (books/catalog-logic.lisp:2752; **2** events)<br>NTH-UPDATE-NTH (see builtin/generated rule below; **587** events) | DISPLACEMENT, D-P / D-Z; supporting rules explicitly marked in term column | `(nth k (fn-cat$c-apply-plan plan seq fn-cat$c))`, k=0..5,9, and indexed-add fields 2/9. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). Zero only: F-Z on **FN-CTG-APPLY-PLAN-FIELDS** (2 events) and the zero instance of **FN-CTG-INDEX-ADD-FIELDS** (2). This is the equivalent local normal-form statement, not an A0 disable. |
| R4 catalog: fn-ctg-key-of-index-add | A0 / A1 (reported) | [FN-CTG-CP-INDEX-FIELDS](#fn-ctg-cp-index-fields) (books/catalog-logic.lisp:601; **7** events)<br>NTH-UPDATE-NTH (see builtin/generated rule below; **587** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth *fn-cat$c-mpx* fn-cat$c)` / `*fn-cat$c-unplaced*` (generated slots 2/9). Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #344 fn-ctg-key-of-commit-base | A0 / A1 (reported) | [FN-CTG-CP-COUNT-NTH](#fn-ctg-cp-count-nth) (books/catalog-logic.lisp:2951; **4** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(natp (nth *fn-cat$c-count* fn-cat$c))`, generated count slot 1. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #345 fn-ctg-commit-base-corr | A0 / A1 (reported) | [FN-CTG-PLAN-NUMBERS-IS-ASSIGN](#fn-ctg-plan-numbers-is-assign) (books/catalog-logic.lisp:2257; **4** events)<br>[FN-CTG-COMMIT-GROUPS-COVER-ROW](#fn-ctg-commit-groups-cover-row) (books/catalog-logic.lisp:2700; **2** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 4 fn-cat$c)` in both rules’ hypotheses. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #369 fn-ctg-clear-fields | A0 / A1 (reported) | [FN-CTG-INDEX-CLEAR-FIELDS-U](#fn-ctg-index-clear-fields-u) (books/catalog-logic.lisp:3165; **1** events)<br>[FN-CTG-INDEX-CLEAR-FRAME](#fn-ctg-index-clear-frame) (books/catalog-logic.lisp:3156; **1** events)<br>NTH-UPDATE-NTH (see builtin/generated rule below; **587** events) | DISPLACEMENT, D-P / D-Z; supporting rules explicitly marked in term column | `(nth 2 (fn-cat$c-index-clear fn-cat$c))`, index 9 and arbitrary preserved k (including 0). Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). Zero only: F-Z on the zero instance of **FN-CTG-INDEX-CLEAR-FRAME** (1 event). This is the equivalent local normal-form statement, not an A0 disable. |
| R4 catalog: #380 fn-ctg-base-fields-67 | A0 / A1 (reported) | [FN-CTG-APPLY-PLAN-FIELDS](#fn-ctg-apply-plan-fields) (books/catalog-logic.lisp:2214; **2** events)<br>[FN-CTG-APPLY-PLAN-FIELDS-67](#fn-ctg-apply-plan-fields-67) (books/catalog-logic.lisp:3277; **1** events) | DISPLACEMENT, D-P / D-Z; supporting rules explicitly marked in term column | `(nth 6 (fn-cat$c-apply-plan plan seq fn-cat$c))`, index 7 and other fields. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). Zero only: F-Z on **FN-CTG-APPLY-PLAN-FIELDS** (2 events). This is the equivalent local normal-form statement, not an A0 disable. |
| R4 catalog: #393 fn-ctg-lplan-lookup | A0 / A1 (reported) | [FN-CTG-LIVE-READERS](#fn-ctg-live-readers) (books/catalog-logic.lisp:3369; **5** events)<br>[FN-CTG-GROUPS-ENTRY-BOUND](#fn-ctg-groups-entry-bound) (books/catalog-logic.lisp:2236; **13** events)<br>[FN-CTG-GROUPS-ENTRY-UNBOUND](#fn-ctg-groups-entry-unbound) (books/catalog-logic.lisp:2245; **12** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 6 x)` in LIVE-READERS hypotheses; ENTRY rules have no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #396 fn-ctg-commit-live-okp-old | A0 / A1 (reported) | [FN-CTG-LPLAN-LOOKUP](#fn-ctg-lplan-lookup) (books/catalog-logic.lisp:3410; **3** events)<br>[FN-CTG-LIVE-LOOKUP](#fn-ctg-live-lookup) (books/catalog-logic.lisp:3352; **4** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | `(nth 4 fn-cat$c)` and `(nth 6 fn-cat$c)` in LPLAN hypotheses; LIVE-LOOKUP has no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #399 fn-ctg-commit-lookup-member | A0 / A1 (reported) | [FN-CTG-LPLAN-LOOKUP](#fn-ctg-lplan-lookup) (books/catalog-logic.lisp:3410; **3** events)<br>[FN-CTG-LIVE-ENTRY-APPEND-MEMBER](#fn-ctg-live-entry-append-member) (books/catalog-logic.lisp:3427; **3** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | Same fields 4/6; LIVE-ENTRY-APPEND-MEMBER has no NTH subterm. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |
| R4 catalog: #404 fn-ctg-commit-live-cover-row (unrepaired diagnosis) | A0 / A1 (reported) | [FN-CTG-LPLAN-LOOKUP](#fn-ctg-lplan-lookup) (books/catalog-logic.lisp:3410; **3** events) | DISPLACEMENT, D-P; supporting rules explicitly marked in term column | Same fields 4/6; ROUND4 records CADR/CDDDDR checkpoint vocabulary and dev LPLAN use, not a tested repair. Positive field k becomes `nth (k-1) (cdr state)` before the canonical field pattern can match. | Positive opaque field/array: NTH; index zero: CAR | Positive: **ADT-NTH-1+**, F-P (1274). No independent defect is established for a supporting rule without an overlapping field term. |

The ROUND4 catalog table has sixteen repaired scopes: fourteen NTH scopes and two AC scopes. All sixteen appear above, plus its unrepaired #404 diagnosis. The initial pages case, R2 pages-exec case, R3/A27 linear and probe cases, and all three chunk scopes are included. Recertify #5 is the recurrence of L1, not a third distinct inverse pair. R1–R5 labels describe the recorded investigations; no additional successful certification is implied.

## Exact local statement / rule appendix

Source notation is preserved (`1+`, constants, conjunctions, and all hypotheses). For each equality/iff branch below, the displayed LHS → RHS is under its statement’s hypotheses. Predicate conclusions represent conditional facts `predicate → T`; they are not fabricated field equations. A forward-chaining event has a trigger/consequence, not a rewrite orientation. Local rule records cannot be recovered from an include of a certified book after LOCAL removal, so these are **literal source statements**, not a claim of new admission or a :pr measurement of those local runes.

### FN-CTG-APPLY-PLAN-FIELDS

`books/catalog-logic.lisp:2214`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(and (equal (nth 0 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 0 fn-cat$c)) (equal (nth 1 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 1 fn-cat$c)) (equal (nth 2 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 2 fn-cat$c)) (equal (nth 3 (fn-cat$c-apply-plan plan seq fn-cat$c)) (fn-cat-nputs plan seq (nth 3 fn-cat$c))) (equal (nth 4 (fn-cat$c-apply-plan plan seq fn-cat$c)) (fn-cat-gputs plan (nth 4 fn-cat$c))) (equal (nth 5 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 5 fn-cat$c)))
```

- `(nth 0 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 0 fn-cat$c)`

- `(nth 1 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 1 fn-cat$c)`

- `(nth 2 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 2 fn-cat$c)`

- `(nth 3 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(fn-cat-nputs plan seq (nth 3 fn-cat$c))`

- `(nth 4 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(fn-cat-gputs plan (nth 4 fn-cat$c))`

- `(nth 5 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 5 fn-cat$c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:23002`, `(DEFTHM FN-CTG-COMMIT-FIELDS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-APPLY-PLAN-FIELDS-67

`books/catalog-logic.lisp:3277`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 12 occurrences across sampled logs.

```lisp
(and (equal (nth 6 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 6 fn-cat$c)) (equal (nth 7 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 7 fn-cat$c)))
```

- `(nth 6 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 6 fn-cat$c)`

- `(nth 7 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 7 fn-cat$c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:27145`, `(DEFTHM FN-CTG-BASE-FIELDS-67 ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-APPLY-PLAN-FIELDS-910

`books/catalog-logic.lisp:2810`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 12 occurrences across sampled logs.

```lisp
(equal (nth 9 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 9 fn-cat$c))
```

- `(nth 9 (fn-cat$c-apply-plan plan seq fn-cat$c))` → `(nth 9 fn-cat$c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:23002`, `(DEFTHM FN-CTG-COMMIT-FIELDS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-CAR-NTHCDR

`books/catalog-logic.lisp:2431`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (natp i) (equal (car (nthcdr i l)) (nth i l)))
```

- `(car (nthcdr i l))` → `(nth i l)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:18322`, `(DEFTHM FN-MPXT-SPEC-FROM-IS-CAT-SEQS-FOR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-COMMIT-GROUPS-COVER-ROW

`books/catalog-logic.lisp:2700`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (and (subsetp-equal groups (fn-record-groups h)) (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c) (fn-cat-groups-coverp c (nth 4 fn-cat$c))) (fn-cat-groups-cover-rowp (fn-cat-assign-numbers groups c) (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c))))
```

- `(fn-cat-groups-cover-rowp (fn-cat-assign-numbers groups c) (fn-cat-gputs (fn-cat$c-plan (fn-record-groups h) fn-cat$c) (nth 4 fn-cat$c)))` → `t`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:21320`, `(DEFTHM FN-CTG-COMMIT-GROUPS-COVERP ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-CONSP-NTHCDR

`books/catalog-logic.lisp:2434`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (natp i) (iff (consp (nthcdr i l)) (< i (len l))))
```

- `(consp (nthcdr i l))` → `(< i (len l))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:18322`, `(DEFTHM FN-MPXT-SPEC-FROM-IS-CAT-SEQS-FOR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-CP-COUNT-NTH

`books/catalog-logic.lisp:2951`; rule classes `(:rewrite :type-prescription)`. **4** distinct Rules-list events / **1** books; 48 occurrences across sampled logs.

```lisp
(implies (fn-cat$cp fn-cat$c) (natp (nth *fn-cat$c-count* fn-cat$c)))
```

- `(natp (nth *fn-cat$c-count* fn-cat$c))` → `t`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:23922`, `(DEFTHM FN-CTG-KEY-OF-COMMIT-BASE ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-CP-INDEX-FIELDS

`books/catalog-logic.lisp:601`; rule classes `:rewrite`. **7** distinct Rules-list events / **1** books; 84 occurrences across sampled logs.

```lisp
(implies (fn-cat$cp fn-cat$c) (and (fn-mlhp (nth *fn-cat$c-mpx* fn-cat$c)) (natp (nth *fn-cat$c-unplaced* fn-cat$c))))
```

- `(fn-mlhp (nth *fn-cat$c-mpx* fn-cat$c))` → `t`

- `(natp (nth *fn-cat$c-unplaced* fn-cat$c))` → `t`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:5598`, `(DEFTHM FN-CTG-CP-OF-APPLY-PLAN ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-GPUTS-LOOKUP

`books/catalog-logic.lisp:2279`; rule classes `:rewrite`. **3** distinct Rules-list events / **1** books; 36 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c) (fn-cat-groups-coverp c (nth 4 fn-cat$c))) (equal (hons-assoc-equal g (fn-cat-gputs (fn-cat$c-plan groups fn-cat$c) tab)) (if (member-equal g groups) (cons g (cons (+ 1 (fn-cat-group-rows g c)) (+ 2 (fn-cat-group-high g c)))) (hons-assoc-equal g tab))))
```

- `(hons-assoc-equal g (fn-cat-gputs (fn-cat$c-plan groups fn-cat$c) tab))` → `(if (member-equal g groups) (cons g (cons (+ 1 (fn-cat-group-rows g c)) (+ 2 (fn-cat-group-high g c)))) (hons-assoc-equal g tab))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:21251`, `(DEFTHM FN-CTG-COMMIT-GROUPS-COVER-ROW ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-GROUPS-COVER-ROWP-MONOTONE

`books/catalog-logic.lisp:2680`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (fn-cat-groups-cover-rowp ns tab) (fn-cat-groups-cover-rowp ns (fn-cat-gputs plan tab)))
```

- `(fn-cat-groups-cover-rowp ns (fn-cat-gputs plan tab))` → `t`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:21093`, `(DEFTHM FN-CTG-GROUPS-COVERP-MONOTONE ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-GROUPS-ENTRY-BOUND

`books/catalog-logic.lisp:2236`; rule classes `:rewrite`. **13** distinct Rules-list events / **1** books; 158 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-groups-okp tab tab c) (consp (cdr (hons-assoc-equal g tab)))) (equal (cdr (hons-assoc-equal g tab)) (cons (fn-cat-group-rows g c) (+ 1 (fn-cat-group-high g c)))))
```

- `(cdr (hons-assoc-equal g tab))` → `(cons (fn-cat-group-rows g c) (+ 1 (fn-cat-group-high g c)))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:16735`, `(DEFTHM FN-CTG-PLAN-NUMBERS-IS-ASSIGN ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-GROUPS-ENTRY-UNBOUND

`books/catalog-logic.lisp:2245`; rule classes `:rewrite`. **12** distinct Rules-list events / **1** books; 146 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-groups-okp tab tab c) (fn-cat-groups-coverp c tab) (not (consp (cdr (hons-assoc-equal g tab))))) (and (equal (fn-cat-group-high g c) 0) (equal (fn-cat-group-rows g c) 0)))
```

- `(fn-cat-group-high g c)` → `0`

- `(fn-cat-group-rows g c)` → `0`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:16735`, `(DEFTHM FN-CTG-PLAN-NUMBERS-IS-ASSIGN ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-HIGH-APPEND

`books/catalog-logic.lisp:1533`; rule classes `:rewrite`. **6** distinct Rules-list events / **1** books; 72 occurrences across sampled logs.

```lisp
(equal (fn-cat-group-high g (append c (list h))) (max (fn-cat-group-high g c) (nfix (fn-held-number-in g h))))
```

- `(fn-cat-group-high g (append c (list h)))` → `(max (fn-cat-group-high g c) (nfix (fn-held-number-in g h)))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:21457`, `(DEFTHM FN-CTG-COMMIT-GROUPS-OKP-KEYS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-INDEX-ADD-FIELDS

`books/catalog-logic.lisp:2752`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (fn-cat$cp fn-cat$c) (and (equal (nth 2 (fn-cat$c-index-add m seq fn-cat$c)) (if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c))) (mv-nth 1 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c))) seq (nth 2 fn-cat$c))) (nth 2 fn-cat$c))) (equal (nth 9 (fn-cat$c-index-add m seq fn-cat$c)) (if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c)) (equal (mv-nth 0 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c))) seq (nth 2 fn-cat$c))) :placed)) (nth 9 fn-cat$c) (+ 1 (nth 9 fn-cat$c)))) (implies (and (natp k) (not (equal k 2)) (not (equal k 9))) (equal (nth k (fn-cat$c-index-add m seq fn-cat$c)) (nth k fn-cat$c)))))
```

- `(nth 2 (fn-cat$c-index-add m seq fn-cat$c))` → `(if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c))) (mv-nth 1 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c))) seq (nth 2 fn-cat$c))) (nth 2 fn-cat$c))`

- `(nth 9 (fn-cat$c-index-add m seq fn-cat$c))` → `(if (and (< (+ 2 seq) *fn-mlh-tag-limit*) (fn-mlh-wfp (nth 2 fn-cat$c)) (equal (mv-nth 0 (fn-mlh-add (fn-mlh-tag m (fn-mlh-key-octets (nth 2 fn-cat$c))) seq (nth 2 fn-cat$c))) :placed)) (nth 9 fn-cat$c) (+ 1 (nth 9 fn-cat$c)))`

- `(nth k (fn-cat$c-index-add m seq fn-cat$c))` → `(nth k fn-cat$c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:23002`, `(DEFTHM FN-CTG-COMMIT-FIELDS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-INDEX-CLEAR-FIELDS-U

`books/catalog-logic.lisp:3165`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 12 occurrences across sampled logs.

```lisp
(and (equal (nth 2 (fn-cat$c-index-clear fn-cat$c)) (fn-mlh-clear (nth 2 fn-cat$c))) (equal (nth 9 (fn-cat$c-index-clear fn-cat$c)) 0))
```

- `(nth 2 (fn-cat$c-index-clear fn-cat$c))` → `(fn-mlh-clear (nth 2 fn-cat$c))`

- `(nth 9 (fn-cat$c-index-clear fn-cat$c))` → `0`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:25887`, `(DEFTHM FN-CTG-CLEAR-FIELDS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-INDEX-CLEAR-FRAME

`books/catalog-logic.lisp:3156`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 12 occurrences across sampled logs.

```lisp
(implies (and (natp k) (not (equal k 2)) (not (equal k 9))) (equal (nth k (fn-cat$c-index-clear fn-cat$c)) (nth k fn-cat$c)))
```

- `(nth k (fn-cat$c-index-clear fn-cat$c))` → `(nth k fn-cat$c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:25887`, `(DEFTHM FN-CTG-CLEAR-FIELDS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-LIVE-ENTRY-APPEND-MEMBER

`books/catalog-logic.lisp:3427`; rule classes `:rewrite`. **3** distinct Rules-list events / **1** books; 36 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-rowsp c) (member-equal g (fn-record-groups h))) (equal (fn-cat-live-entry g (append c (list (fn-cat-assign h c)))) (fn-ctg-commit-entry g (fn-cat-live-candidatep h) c)))
```

- `(fn-cat-live-entry g (append c (list (fn-cat-assign h c))))` → `(fn-ctg-commit-entry g (fn-cat-live-candidatep h) c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:28757`, `(DEFTHM FN-CTG-COMMIT-LIVE-OKP-OLD ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-LIVE-LOOKUP

`books/catalog-logic.lisp:3352`; rule classes `:rewrite`. **4** distinct Rules-list events / **1** books; 48 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-live-okp tab tab c) (fn-cat-groups-coverp c tab)) (equal (cdr (hons-assoc-equal g tab)) (if (consp (hons-assoc-equal g tab)) (fn-cat-live-entry g c) nil)))
```

- `(cdr (hons-assoc-equal g tab))` → `(if (consp (hons-assoc-equal g tab)) (fn-cat-live-entry g c) nil)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:28009`, `(DEFTHM FN-CTG-LIVE-READERS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-LIVE-READERS

`books/catalog-logic.lisp:3369`; rule classes `:rewrite`. **5** distinct Rules-list events / **1** books; 60 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-live-okp (nth 6 x) (nth 6 x) c) (fn-cat-groups-coverp c (nth 6 x))) (and (equal (fn-cat$c-group-live-count g x) (fn-cat-live-count-from g 1 (fn-cat-group-high g c) c)) (equal (fn-cat$c-group-live-low g x) (fn-cat-live-first g 1 (fn-cat-group-high g c) c)) (equal (fn-cat$c-group-live-high g x) (fn-cat-live-last g (fn-cat-group-high g c) c))))
```

- `(fn-cat$c-group-live-count g x)` → `(fn-cat-live-count-from g 1 (fn-cat-group-high g c) c)`

- `(fn-cat$c-group-live-low g x)` → `(fn-cat-live-first g 1 (fn-cat-group-high g c) c)`

- `(fn-cat$c-group-live-high g x)` → `(fn-cat-live-last g (fn-cat-group-high g c) c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:28455`, `(DEFTHM FN-CTG-LPLAN-LOOKUP ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-LPLAN-LOOKUP

`books/catalog-logic.lisp:3410`; rule classes `:rewrite`. **3** distinct Rules-list events / **1** books; 36 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c) (fn-cat-groups-coverp c (nth 4 fn-cat$c)) (fn-cat-live-okp (nth 6 fn-cat$c) (nth 6 fn-cat$c) c) (fn-cat-groups-coverp c (nth 6 fn-cat$c))) (equal (hons-assoc-equal g (fn-ctg-lputs (fn-cat$c-live-plan groups livep fn-cat$c) tab)) (if (member-equal g groups) (cons g (fn-ctg-commit-entry g livep c)) (hons-assoc-equal g tab))))
```

- `(hons-assoc-equal g (fn-ctg-lputs (fn-cat$c-live-plan groups livep fn-cat$c) tab))` → `(if (member-equal g groups) (cons g (fn-ctg-commit-entry g livep c)) (hons-assoc-equal g tab))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:28757`, `(DEFTHM FN-CTG-COMMIT-LIVE-OKP-OLD ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-NPUTS-LOOKUP

`books/catalog-logic.lisp:2227`; rule classes `:rewrite`. **3** distinct Rules-list events / **1** books; 37 occurrences across sampled logs.

```lisp
(equal (hons-assoc-equal k (fn-cat-nputs plan seq tab)) (if (member-equal k (fn-cat-plan-numbers plan)) (cons k seq) (hons-assoc-equal k tab)))
```

- `(hons-assoc-equal k (fn-cat-nputs plan seq tab))` → `(if (member-equal k (fn-cat-plan-numbers plan)) (cons k seq) (hons-assoc-equal k tab))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:17785`, `(DEFTHM FN-CTG-NUMBERS-OKP-OLD-KEYS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-NTHCDR-CDR

`books/catalog-logic.lisp:2428`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(implies (natp i) (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))
```

- `(nthcdr (+ 1 i) l)` → `(cdr (nthcdr i l))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:18322`, `(DEFTHM FN-MPXT-SPEC-FROM-IS-CAT-SEQS-FOR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-PLAN-NUMBERS-IS-ASSIGN

`books/catalog-logic.lisp:2257`; rule classes `:rewrite`. **4** distinct Rules-list events / **1** books; 48 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-groups-okp (nth 4 fn-cat$c) (nth 4 fn-cat$c) c) (fn-cat-groups-coverp c (nth 4 fn-cat$c))) (equal (fn-cat-plan-numbers (fn-cat$c-plan groups fn-cat$c)) (fn-cat-assign-numbers groups c)))
```

- `(fn-cat-plan-numbers (fn-cat$c-plan groups fn-cat$c))` → `(fn-cat-assign-numbers groups c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:17785`, `(DEFTHM FN-CTG-NUMBERS-OKP-OLD-KEYS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-ROWS-APPEND

`books/catalog-logic.lisp:1538`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 24 occurrences across sampled logs.

```lisp
(equal (fn-cat-group-rows g (append c (list h))) (+ (fn-cat-group-rows g c) (if (fn-held-number-in g h) 1 0)))
```

- `(fn-cat-group-rows g (append c (list h)))` → `(+ (fn-cat-group-rows g c) (if (fn-held-number-in g h) 1 0))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:21457`, `(DEFTHM FN-CTG-COMMIT-GROUPS-OKP-KEYS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-CTG-ROWS-CORR-NTH

`books/catalog-logic.lisp:2130`; rule classes `:rewrite`. **15** distinct Rules-list events / **1** books; 185 occurrences across sampled logs.

```lisp
(implies (and (fn-cat-rows-corr n c rows) (natp i) (< i (nfix n))) (equal (nth i rows) (nth i c)))
```

- `(nth i rows)` → `(nth i c)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:15576`, `(DEFTHM FN-CTG-ROWS-CORR-OF-RESIZE ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MIQ-CHUNK-SEQ-IS-PAGE-SEQ

`books/msgid-query-chunk.lisp:53`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 2 occurrences across sampled logs.

```lisp
(implies (and (fn-ibp-table-pagep fn-ibp-table-page) (natp slot) (< slot 1024)) (equal (fn-ibp-table-word (+ 1024 slot) fn-ibp-table-page) (fn-mpl-seq-at 0 slot (nth 0 fn-ibp-table-page))))
```

- `(fn-ibp-table-word (+ 1024 slot) fn-ibp-table-page)` → `(fn-mpl-seq-at 0 slot (nth 0 fn-ibp-table-page))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T145638Z-3791359/books--msgid-query-chunk.certify.log:1513`, `(DEFTHM FN-MIQ-CHUNK-NEXT-IS-PAGE-LAYOUT-STEP ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MIQ-CHUNK-TAG-IS-PAGE-TAG

`books/msgid-query-chunk.lisp:45`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 2 occurrences across sampled logs.

```lisp
(implies (and (fn-ibp-table-pagep fn-ibp-table-page) (natp slot) (< slot 1024)) (equal (fn-ibp-table-word slot fn-ibp-table-page) (fn-mpl-tag-at 0 slot (nth 0 fn-ibp-table-page))))
```

- `(fn-ibp-table-word slot fn-ibp-table-page)` → `(fn-mpl-tag-at 0 slot (nth 0 fn-ibp-table-page))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T232739Z-4123336/books--msgid-query-chunk.certify.log:709`, `(DEFTHM FN-MIQ-CHUNK-NEXT-IS-PAGE-LAYOUT-STEP ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MLH-NTHCDR-UNFOLD

`books/msgid-linear-exec.lisp:2730`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 4 occurrences across sampled logs.

```lisp
(implies (and (natp i) (< i (len l))) (equal (cons (nth i l) (nthcdr (+ 1 i) l)) (nthcdr i l)))
```

- `(cons (nth i l) (nthcdr (+ 1 i) l))` → `(nthcdr i l)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T145638Z-3791359/books--msgid-linear-exec.certify.log:29985`, `(DEFTHM FN-MLH-KEY-FROM-IS-NTHCDR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MLH-RECOGNIZER-FACTS

`books/msgid-linear-exec.lisp:2694`; rule classes `:rewrite`. **3** distinct Rules-list events / **1** books; 6 occurrences across sampled logs.

```lisp
(implies (fn-mlhp x) (and (true-listp x) (equal (len x) 7) (fn-mlh-keyp (nth 5 x)) (true-listp (nth 5 x)) (equal (len (nth 5 x)) 32)))
```

- `(true-listp x)` → `t`

- `(len x)` → `7`

- `(fn-mlh-keyp (nth 5 x))` → `t`

- `(true-listp (nth 5 x))` → `t`

- `(len (nth 5 x))` → `32`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T145638Z-3791359/books--msgid-linear-exec.certify.log:29985`, `(DEFTHM FN-MLH-KEY-FROM-IS-NTHCDR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MLH-SET-KEY-FROM-OVER-A-LIST

`books/msgid-linear-exec.lisp:2773`; rule classes `:rewrite`. **0** distinct Rules-list events / **0** books; 0 occurrences across sampled logs.

```lisp
(implies (and (true-listp l) (equal (len l) *fn-mpxt-key-octets*) (natp i) (<= i *fn-mpxt-key-octets*)) (equal (fn-mlh-set-key-from i key (list nil 0 0 0 0 l 0)) (list nil 0 0 0 0 (append (take i l) (fn-mlh-keytail i key)) 0)))
```

- `(fn-mlh-set-key-from i key (list nil 0 0 0 0 l 0))` → `(list nil 0 0 0 0 (append (take i l) (fn-mlh-keytail i key)) 0)`

Zero Rules-list uses does not mean unused: FN-MLH-SET-KEY-IS-A-LIST explicitly :USEs this theorem; Hint-events/source references are outside the requested Rules-list measure.

### FN-MLH-SET-KEY-IS-A-LIST

`books/msgid-linear-exec.lisp:2783`; rule classes `:rewrite`. **6** distinct Rules-list events / **4** books; 40 occurrences across sampled logs.

```lisp
(implies (fn-mlhp fn-mlh) (equal (fn-mlh-set-key key fn-mlh) (list nil 0 0 0 0 (fn-mlh-keytail 0 key) 0)))
```

- `(fn-mlh-set-key key fn-mlh)` → `(list nil 0 0 0 0 (fn-mlh-keytail 0 key) 0)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/log-ckpt-verdict/build/acl2/certify-20261012T204003Z-77964/books--catalog-logic.certify.log:33460`, `(DEFTHM FN-CTG-CORR-BASE-NIL-OF-RESIZE-ROWS ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MPL-CURSOR-FIELD-BOUNDS

`books/msgid-probe-layout.lisp:162`; rule classes `(:forward-chaining)`. **7** distinct Rules-list events / **3** books; 13 occurrences across sampled logs.

```lisp
(implies (fn-mpr-cursorp cursor pages) (and (consp cursor) (natp (car cursor)) (< (car cursor) pages) (natp (nth 0 cursor)) (< (nth 0 cursor) pages) (natp (nth 1 cursor)) (natp (nth 2 cursor)) (< (nth 2 cursor) *fn-mpxt-page-slots*)))
```

Forward-chaining: trigger `(fn-mpr-cursorp cursor pages)`; consequent is the exact AND of cursor facts above. There is no local rewrite LHS → RHS to oppose A0/A1.

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T145638Z-3791359/books--msgid-probe-layout.certify.log:2081`, `(DEFTHM FN-MPL-PLACE-PRESERVES-EXISTING-REACHABLE ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MPX-NTHCDR-CDR

`books/msgid-pages.lisp:85`; rule classes `:rewrite`. **1** distinct Rules-list events / **1** books; 2 occurrences across sampled logs.

```lisp
(implies (natp i) (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))
```

- `(nthcdr (+ 1 i) l)` → `(cdr (nthcdr i l))`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T093031Z-3015805/books--msgid-pages.certify.log:435`, `(DEFTHM FN-MPX-SPEC-FROM-IS-RECORDS-FOR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MPXT-NTHCDR-UNFOLD

`books/msgid-pages-exec.lisp:2626`; rule classes `:rewrite`. **2** distinct Rules-list events / **1** books; 4 occurrences across sampled logs.

```lisp
(implies (and (natp i) (< i (len l))) (equal (cons (nth i l) (nthcdr (+ 1 i) l)) (nthcdr i l)))
```

- `(cons (nth i l) (nthcdr (+ 1 i) l))` → `(nthcdr i l)`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T114611Z-3250289/books--msgid-pages-exec.certify.log:26022`, `(DEFTHM FN-MPXT-KEY-FROM-IS-NTHCDR ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### FN-MPXT-RECOGNIZER-FACTS

`books/msgid-pages-exec.lisp:2594`; rule classes `:rewrite`. **4** distinct Rules-list events / **1** books; 9 occurrences across sampled logs.

```lisp
(implies (fn-mpxtp x) (and (true-listp x) (equal (len x) 5) (fn-mpxt-keyp (nth 3 x)) (true-listp (nth 3 x)) (equal (len (nth 3 x)) 32)))
```

- `(true-listp x)` → `t`

- `(len x)` → `5`

- `(fn-mpxt-keyp (nth 3 x))` → `t`

- `(true-listp (nth 3 x))` → `t`

- `(len (nth 3 x))` → `32`

Example Rules-list provenance: `/Users/ember/dev/fn/build/lanes/vertical-one-world/build/acl2/certify-20261013T093031Z-3015805/books--msgid-pages-exec.certify.log:25391`, `(DEFTHM FN-MPXT-CLEAR-IS-A-LIST ...)`. Complete event list: [pairs-usage.json](pairs-usage.json).

### NTH-UPDATE-NTH (builtin supporting rule)

ACL2 builtin event -654, not a local lemma with a books/ source line. Exact rule: `(nth m (update-nth n val l)) → (if (equal (nfix m) (nfix n)) val (nth m l))`, no hypotheses. **587** distinct events in **100** books; **3826** Rules-list occurrences. [pairs-nth-update-pr.log](pairs-nth-update-pr.log). At m=0, the equivalent CAR/update specialization is `(car (update-nth n val l)) = (if (equal 0 (nfix n)) val (car l))`; do not change the global builtin on the basis of a consumer’s field proof.

### FN-MPXT-WI (generated definition)

Generator: `defstobj fn-mpxt`, `books/msgid-pages-exec.lisp:159`, array field at :160. Logical map: `(fn-mpxt-wi i fn-mpxt) → (nth i (nth 0 fn-mpxt))`. The exact translated RHS and I=1024 substitution are printed in frames 27–30 of [a27-probe-stack-gstack.log](a27-probe-stack-gstack.log). **6** distinct Rules-list events in **2** books, **17** occurrences. This supplies A1’s redex; it does not rewrite the peeled term back. Calling that trace a two-rule loop would be incorrect.

## Certificate-log measurement and limits

**21157** `.certify.log` paths were searched; **1077** contained a relevant name. Scope: this worktree’s `build/acl2/certify-*/*.certify.log` (including the local October 14 #5 run) and read-only `/Users/ember/dev/fn/build/lanes/*/build/acl2/certify-2026101[23]*/*.certify.log`. [pairs-log-manifest.txt](pairs-log-manifest.txt) records the exact scope. Only ACL2 `Form:` / `Rules:` summary blocks count; source echoes, theory lists and failure-stack mentions do not. Whitespace-normalized `(book log basename, event Form)` keys deduplicate repeated runs/copies. Occurrence counts deliberately include repeats. Same-named event variants across revisions collapse to one event; no source-closure identity is inferred from those use counts.

These are **observed lower bounds on proof dependencies**, not a claim that all historical certificates or all :USE dependencies were available. Failure summaries can omit rewrites active at an abort; zero Rules-list use cannot exonerate a rule. `FN-MLH-SET-KEY-FROM-OVER-A-LIST` has zero such uses despite an explicit :USE in source. Counts therefore support blast-radius planning, not automatic proof of an unaffected closure.

Recertify #5 evidence: [triage-96f0.txt](triage-96f0.txt), `build/acl2/certify-20261014T005030Z-306718/books--msgid-pages.certify.log:431` (the aborted event summary and unchanged top-level theorem). That run reports call-depth 1000; its abbreviated abort Rules list does not expose the looping rewrites. The L1 attribution combines the **same current source inverse pair**, the measured enabled AC in the certified include world, and R1’s recorded diagnosis; this report did not reproduce the abort or claim a new #5 gstack trace. Book-local FN-MPX-NTHCDR-CDR is enabled by its default local defthm. If exact #5-world dynamic stack evidence is required, it remains a separate proof-debug task, outside this read-statements-only brief.

Baseline reports: [REPAIRS-before-exporter.md](REPAIRS-before-exporter.md) (R1 pages and R2 pages-exec), [EXPORTER-FIX.md](EXPORTER-FIX.md) (A27 linear/probe), [ROUND4.md](ROUND4.md) (six-book dispositions, sixteen catalog scopes, chunk scopes, #404), and [ROUNDX4.md](ROUNDX4.md) (X5 candidate scope). The earlier statements that all ADT-NTH pairs should simply be disabled are not used as normal-form evidence.

Reproduce locally (read-only inputs; outputs restricted to this report directory):
```sh
timeout 180 python3 build/vertical-runs/one-world/pairs_measure.py > build/vertical-runs/one-world/pairs-measure.log 2>&1
timeout 20 python3 build/vertical-runs/one-world/pairs_families.py > build/vertical-runs/one-world/pairs-families-summary.txt
timeout 20 python3 build/vertical-runs/one-world/pairs_report.py
```

Read-only sessions `pairs-read-20261013` and `pairs-std-read-20261013` loaded certified include worlds (0 prover steps), queried statements/rules, and were stopped by the named proof_repl wrapper: [pairs-repl-stop.log](pairs-repl-stop.log), [pairs-std-stop.log](pairs-std-stop.log). The tool’s SSH multiplexing path initially failed sandbox binding; the retry changed only in-memory SSH options to disable multiplexing. No unrelated session/process was stopped.
