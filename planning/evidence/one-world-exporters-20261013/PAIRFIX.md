# A28 pair fixes and positive-opener measurement

The approved edits are implemented: **two local inverse rules now default disabled**, **three event-local theory hints retain their recorded uses without the opposing rule**, and **six literal NTH-0 terms in four lemmas become CAR**. The audit found no other source changes. The quoted-index hypothesis is confirmed: ACL2 matches quoted 4 against `(+ 1 j)` with J=`'3`. The completed sample covers **45 admitted ADT-NTH-1+ user events in 15 books**. **Neither quoted-only nor symbolic-only preserves the observed uses while removing the recorded collisions**; the recommendation remains default-disable with justified event-local enables. `books/proto/adt-key-lib.lisp` is unchanged. No commits.

## Approved source edits

`FN-MPX-NTHCDR-CDR` and `FN-CTG-NTHCDR-CDR` change from local `defthm` to local `defthmd`. Their complete formulas, hypotheses, locality and rule classes are unchanged. Prior certificate Rules lists name one pages consumer and two catalog consumers; those three existing hints explicitly enable their local inverse rule and disable `ADT-CDR-NTHCDR` **in that same hint only**. Enabling both directions there would reinstate the cycle. Outside those proofs the imported direction remains available and the inverse stays disabled. The checks below verify the resulting default membership.

| Event-local enable | Enabled inverse | Opposing rule excluded from that hint |
| --- | --- | --- |
| FN-MPX-SPEC-FROM-IS-RECORDS-FOR | FN-MPX-NTHCDR-CDR | ADT-CDR-NTHCDR |
| FN-MPXT-SPEC-FROM-IS-CAT-SEQS-FOR | FN-CTG-NTHCDR-CDR | ADT-CDR-NTHCDR |
| FN-CTG-SCAN-IS-SEQS-FOR | FN-CTG-NTHCDR-CDR | ADT-CDR-NTHCDR |

| F-Z lemma | Literal substitutions | One-line whole-statement equivalence |
| --- | ---: | --- |
| FN-CTG-APPLY-PLAN-FIELDS | 2 | ADT-NTH-0 holds for every object, so replacing both zero-frame selectors by CAR preserves the equality and the whole six-clause AND; all other fields remain unchanged. |
| FN-MPL-CURSOR-FIELD-BOUNDS | 2 | ADT-NTH-0 holds for every cursor object, so NATP/NTH-0 and the NTH-0 upper bound are equivalent to their CAR forms; all eight conjuncts, including duplicate CAR facts, and the forward-chaining class remain. |
| FN-MIQ-CHUNK-TAG-IS-PAGE-TAG | 1 | ADT-NTH-0 holds for every page object, so congruence of FN-MPL-TAG-AT preserves the complete conditional equality when its zero-field argument becomes CAR. |
| FN-MIQ-CHUNK-SEQ-IS-PAGE-SEQ | 1 | ADT-NTH-0 holds for every page object, so congruence of FN-MPL-SEQ-AT preserves the complete conditional equality when its zero-field argument becomes CAR. |

F-Z candidates `FN-MPXT-NTHCDR-UNFOLD`, `FN-MLH-NTHCDR-UNFOLD`, `FN-CTG-INDEX-ADD-FIELDS` and `FN-CTG-INDEX-CLEAR-FRAME` contain **no literal `(nth 0 ...)` in their statements**, so they remain byte-identical. In particular, `(nth i ...)` / `(nth k ...)` are not changed to CAR or to a conditional, and no zero specialization is added. `msgid-pages-exec.lisp` and `msgid-linear-exec.lisp` therefore have no diff. This applies the approved literal substitution exactly, retaining every quantified/general-index case.

Every edit, including all three theory hints, is shown below; [pairfix.diff](pairfix.diff) is the same diff as a standalone artifact.

```diff
--- a/books/msgid-pages.lisp
+++ b/books/msgid-pages.lisp
@@ -82,7 +82,7 @@
         rest))))
 
 (local
- (defthm fn-mpx-nthcdr-cdr
+ (defthmd fn-mpx-nthcdr-cdr
    (implies (natp i)
             (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))))
 
@@ -103,7 +103,8 @@
            (equal (fn-mpx-spec-from i msgid rows)
                   (fn-cei-article-records-for msgid (nthcdr i rows))))
   :hints (("Goal" :induct (fn-mpx-spec-from i msgid rows)
-           :in-theory (enable fn-cei-article-records-for))))
+           :in-theory (e/d (fn-cei-article-records-for fn-mpx-nthcdr-cdr)
+                            (adt-cdr-nthcdr)))))
 
 ; Candidates: strictly ascending naturals, every one at least FROM and
 ; below N.
--- a/books/catalog-logic.lisp
+++ b/books/catalog-logic.lisp
@@ -2212,7 +2212,7 @@
 
 (local
  (defthm fn-ctg-apply-plan-fields
-   (and (equal (nth 0 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 0 fn-cat$c))
+   (and (equal (car (fn-cat$c-apply-plan plan seq fn-cat$c)) (car fn-cat$c))
         (equal (nth 1 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 1 fn-cat$c))
         (equal (nth 2 (fn-cat$c-apply-plan plan seq fn-cat$c)) (nth 2 fn-cat$c))
         (equal (nth 3 (fn-cat$c-apply-plan plan seq fn-cat$c))
@@ -2425,7 +2425,7 @@
 ; the confirmation over the rows array is the confirmation over the list;
 ; the degraded scan is the walk.
 (local
- (defthm fn-ctg-nthcdr-cdr
+ (defthmd fn-ctg-nthcdr-cdr
    (implies (natp i) (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))))
 (local
  (defthm fn-ctg-car-nthcdr
@@ -2440,7 +2440,8 @@
            (equal (fn-mpxt-spec-from i msgid rows)
                   (fn-cat-seqs-for msgid (nthcdr i rows) i)))
   :hints (("Goal" :induct (fn-mpxt-spec-from i msgid rows)
-           :in-theory (enable fn-mpxt-spec-from fn-mpxt-hitp fn-cat-seqs-for))))
+           :in-theory (e/d (fn-mpxt-spec-from fn-mpxt-hitp fn-cat-seqs-for fn-ctg-nthcdr-cdr)
+                            (adt-cdr-nthcdr)))))
 
 ; KEYSTONE (PRF-970): the paged reader is the catalog's Message-ID column
 ; under the faithful relation.
@@ -2478,8 +2479,8 @@
                    (revappend acc (fn-cat-seqs-for msgid (nthcdr i c) i))))
    :hints (("Goal" :induct (fn-cat$c-scan-msgid msgid i acc fn-cat$c)
             :in-theory (e/d (fn-cat$c-scan-msgid fn-cat-seqs-for fn-cat$c-count fn-cat$c-rows-length
-                             fn-cat$c-rowsi)
-                            (nthcdr))
+                             fn-cat$c-rowsi fn-ctg-nthcdr-cdr)
+                            (nthcdr adt-cdr-nthcdr))
             :expand ((fn-cat-seqs-for msgid (nthcdr i c) i))))))
 
 ; The table that IS the fold with no unplaced row: well formed, its
--- a/books/msgid-query-chunk.lisp
+++ b/books/msgid-query-chunk.lisp
@@ -46,7 +46,7 @@
   (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                 (natp slot) (< slot 1024))
            (equal (fn-ibp-table-word slot fn-ibp-table-page)
-                  (fn-mpl-tag-at 0 slot (nth 0 fn-ibp-table-page))))
+                  (fn-mpl-tag-at 0 slot (car fn-ibp-table-page))))
   :hints (("Goal" :in-theory (e/d (fn-mpl-tag-at fn-mpxt-slot)
                             (fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))))
 
@@ -54,7 +54,7 @@
   (implies (and (fn-ibp-table-pagep fn-ibp-table-page)
                 (natp slot) (< slot 1024))
            (equal (fn-ibp-table-word (+ 1024 slot) fn-ibp-table-page)
-                  (fn-mpl-seq-at 0 slot (nth 0 fn-ibp-table-page))))
+                  (fn-mpl-seq-at 0 slot (car fn-ibp-table-page))))
   :hints (("Goal" :in-theory (e/d (fn-mpl-seq-at fn-mpxt-slot)
                             (fn-ibp-table-word fn-ibp-table-wordsi fn-ibp-table-pagep)))))
 
--- a/books/msgid-probe-layout.lisp
+++ b/books/msgid-probe-layout.lisp
@@ -162,7 +162,7 @@
 (defthm fn-mpl-cursor-field-bounds
   (implies (fn-mpr-cursorp cursor pages)
            (and (consp cursor) (natp (car cursor)) (< (car cursor) pages)
-                (natp (nth 0 cursor)) (< (nth 0 cursor) pages)
+                (natp (car cursor)) (< (car cursor) pages)
                 (natp (nth 1 cursor))
                 (natp (nth 2 cursor)) (< (nth 2 cursor) *fn-mpxt-page-slots*)))
   :rule-classes (:forward-chaining)
```

## Audit and narrow proof checks

[pairfix_edits.py](pairfix_edits.py) uses `tools/lisp_rewrite.py` for position-preserving splices. Its six before-source fixtures are in `pairfix-before/books/`. The audit independently compares source ASTs after removing `:in-theory` pairs: the only accepted non-theory differences are the two DEFTHMD heads and the six listed recursive literal NTH-0 substitutions. It also requires **the entire current file to be byte-identical to the planned transformation of the fixture**, preserving all untouched event/hint bytes, comments, locality, guards and rule classes. No broad reformatting or generated source edits occurred. [pairfix-audit.json](pairfix-audit.json) / [pairfix-edits.json](pairfix-edits.json) list each site. All six allow-listed books pass; only four have source diffs.

| Book | Top-level forms compared | Unexpected bytes / non-theory changes |
| --- | ---: | ---: |
| books/msgid-pages.lisp | 68 | 0 |
| books/catalog-logic.lisp | 647 | 0 |
| books/msgid-pages-exec.lisp | 401 | 0 |
| books/msgid-linear-exec.lisp | 398 | 0 |
| books/msgid-query-chunk.lisp | 19 | 0 |
| books/msgid-probe-layout.lisp | 25 | 0 |

Proof controls: pages uses this worktree’s certified history-columns dependencies and its edited source prefix. The catalog and remaining F-Z checks use cached dependencies from the existing `dev-reference` tree, with the **current edited source events** replayed. For catalog/cursor/chunk, a certified `proto/adt-key-lib` include supplies the imported rules; zero normalization and the imported CDR direction are available, while the positive opener is disabled in the **measurement world**, not edited in any book. These are admission checks, not certification of the current closure.

| Current edited event | Result | Prover steps | Evidence |
| --- | --- | ---: | --- |
| FN-MPX-SPEC-FROM-IS-RECORDS-FOR | admitted | 4178 | [a28-pages-start.log](a28-pages-start.log) |
| FN-CTG-APPLY-PLAN-FIELDS | admitted (0.81 s ACL2) | 444,173 | [a28-catalog-replay3.log](a28-catalog-replay3.log) |
| FN-MPXT-SPEC-FROM-IS-CAT-SEQS-FOR | admitted (0.02 s ACL2) | 2,412 | [a28-catalog-replay3.log](a28-catalog-replay3.log) |
| FN-CTG-SCAN-IS-SEQS-FOR | admitted (0.06 s ACL2) | 17,270 | [a28-catalog-replay3.log](a28-catalog-replay3.log) |
| FN-MPL-CURSOR-FIELD-BOUNDS | admitted | 167 | [a28-zero-cursor-replay.log](a28-zero-cursor-replay.log) |
| FN-MIQ-CHUNK-TAG-IS-PAGE-TAG | admitted | 359 | [a28-zero-chunk-replay.log](a28-zero-chunk-replay.log) |
| FN-MIQ-CHUNK-SEQ-IS-PAGE-SEQ | admitted | 383 | [a28-zero-chunk-replay.log](a28-zero-chunk-replay.log) |

Catalog replays **31 current source forms** from APPLY-PLAN-FIELDS through SCAN-IS-SEQS-FOR, plus the theory control: 32 forms, zero refused, 1.30 s ACL2 / 570900 steps. Source intermediate proofs admit as well as the three changed events. `:pr` after the proof hints reports each local inverse **Enabled: NIL** and ADT-CDR-NTHCDR **Enabled: T**: [a28-pages-pr.log](a28-pages-pr.log), [a28-catalog-pr.log](a28-catalog-pr.log). The two first catalog setup attempts used an old dependency world where the imported rune was absent; the relative certified include corrected that setup before the successful replay. No theorem counterexample or source proof failure is claimed from those setup refusals.

## Quoted-index constant matching: confirmed

The `a28-constant` hbox world loaded two source prefix forms, including certified history-columns, with zero prover steps before measurement. A non-interactive BRR monitor printed the unification substitution and translated target. The theorem enabled **only ADT-NTH-1+ as a rewrite rule**, plus the executable counterpart of NATP to relieve the quoted natural hypothesis:

```lisp
(thm (equal (nth 4 x) (nth 3 (cdr x)))
 :hints (("Goal"
          :in-theory '(adt-nth-1+ (:executable-counterpart natp)))))

; Exact first monitor record:
A28-INDEX '3 TARGET (NTH '4 X)
; Subsequent constant peeling includes:
A28-INDEX '2 TARGET (NTH '3 (CDR X))
A28-INDEX '1 TARGET (NTH '2 (CDR (CDR X)))
A28-INDEX '0 TARGET (NTH '1 (CDR (CDR (CDR X))))
```

The theorem succeeds in **58 steps / 0.01 s ACL2**. Its Rules list contains ADT-NTH-1+ and NATP’s executable counterpart, with no other rewrite rule. An independent symbolic control, `(implies (natp j) (equal (nth (+ 1 j) x) (nth j (cdr x))))`, succeeds in **48 steps**, recording J=`J` and target `(NTH (BINARY-+ '1 J) X)`. [a28-constant-forms.lisp](a28-constant-forms.lisp), [a28-constant-test2.log](a28-constant-test2.log). Thus A1’s LHS is not protected from constant field indices by its `(+ 1 j)` shape.

## Forty-five event replays in fifteen books

All **45** selected events were recorded users in the original certificate Rules-list census and admitted again with ADT-NTH-1+ in their replay Rules lists. The fifteen books emphasize byte-store, BP, store-log and owner users. **All 45 target event source forms are byte-identical between dev-reference and the current worktree**, checked in [a28-sample-source-audit.json](a28-sample-source-audit.json). Dependency closures are the cache-installed record-toolchain sets named in each start log; this does not equate their older exported theories to a freshly certified current closure.

The certified reference exports suppress the ADT field openers in some worlds. Each replay therefore explicitly enables the unchanged A0/A1 runes after the prefix, reproducing the recorded active-opener use context; no theorem statement or event hint is changed. An initial disabled-opener control in the first book admitted the same three selected events without ADT-NTH-1+, demonstrating that a Rules-list use is not itself proof of necessity. The monitored active replay is the sample used below.

The monitor in [a28-monitor.lisp](a28-monitor.lisp) returns NIL after printing `brr@ :unify-subst`’s J and the target NTH index, so there are no interactive stops. It classifies exactly the proposed guard’s argument: `quotep J` versus non-quoted J. Accumulated persistence is enabled. The per-event successful Rules list establishes that the rule was used; monitor records are **matched attempts, not a per-attempt success trace**. For mixed events the sample establishes both trigger classes, but does not attribute each successful application to its class.

Observed totals: **43 quoted-only matched events**, **2 mixed matched events**, **0 symbolic-only events**; **25090 quoted** and **65 symbolic** monitor matches. The two mixed events are in byte-store-k0: `FN-BS-K0C-CUT-PAIR-IS-PREVIOUS-PAIR` and `FN-BS-K0C-NTH-SUCC`; both record symbolic J=`K`, instantiated index `(BINARY-+ '1 K)`, as well as quoted J=`'0`, index `'1`. This is a targeted sample, not a classification of all 1274 historical event users.

Runtime remained practical. For the fourteen automatically timed later books, start wall time totals **242.406 s** (range 10.778–27.512 s), and monitored range wall time totals **75.802 s** (range 0.945–33.140 s). The manually prepared first prefix reports 1.36 s ACL2. The slowest selected event, FN-OLR-TAKE-AGREES-WITH-THE-OWNER, reports **31.21 s ACL2** with 16342 monitor matches, in a 33.140 s range. An initial conservative ten-second monitor threshold paused after that completed range; the remaining workload was still practical, so sampling resumed and reached the requested coverage. No timeout or proof refusal ended the completed sample.

Each row gives all distinct **instantiated NTH indices** found by the monitor for that selected event. Exact J/index pairs, attempt counts, original certify-log provenance, and run timings are retained in [a28-sample-results.json](a28-sample-results.json). [a28-sample-plan.json](a28-sample-plan.json) and [pairfix_sample.py](pairfix_sample.py) retain selection and replay code.

| Book / event | Quoted / symbolic matches | Instantiated NTH indices | Full replay |
| --- | ---: | --- | --- |
| byte-store-record-provenance-bytes<br>FN-BS-K6-WRITE-THEN-FENCE-KEEPS-EXACT-OCTETS | 19 / 0 | `'1`; `'2`; `'3` | [a28-sample-01-active-full.log](a28-sample-01-active-full.log) |
| byte-store-record-provenance-bytes<br>FN-BS-K6-UNKNOWN-INODE-HAS-NO-PENDING-WRITE | 22 / 0 | `'1` | [a28-sample-01-active-full.log](a28-sample-01-active-full.log) |
| byte-store-record-provenance-bytes<br>FN-BS-K6-ENTRY-AFTER-LAST-SET | 24 / 0 | `'1`; `'2`; `'3` | [a28-sample-01-active-full.log](a28-sample-01-active-full.log) |
| byte-store-record-provenance-node<br>FN-BS-K0-FRONTIER-FILE-CUT-IS-WRITE-FENCE | 26 / 0 | `'1`; `'2`; `'3`; `'4`; `'5` | [a28-sample-02-range.log](a28-sample-02-range.log) |
| byte-store-record-provenance-node<br>FN-BS-K0-FRONTIER-FILE-CUT-HAS-EXACT-FRAME | 10 / 0 | `'1`; `'2`; `'3`; `'4`; `'5` | [a28-sample-02-range.log](a28-sample-02-range.log) |
| byte-store-record-provenance-node<br>FN-BS-K0-FRONTIER-FILE-CUT-SOURCE-IS-NEW-INODE | 10 / 0 | `'1`; `'2`; `'3`; `'4`; `'5` | [a28-sample-02-range.log](a28-sample-02-range.log) |
| byte-store-scan<br>FN-BS-APPLY-ENTRIES-NAMES-IS-NAMES-AFTER | 842 / 0 | `'1`; `'2`; `'3` | [a28-sample-03-range.log](a28-sample-03-range.log) |
| byte-store-scan<br>FN-BS-NAMES-AFTER-OF-TEAR-WRITE | 802 / 0 | `'1`; `'2`; `'3` | [a28-sample-03-range.log](a28-sample-03-range.log) |
| byte-store-scan<br>FN-BS-NAMES-AFTER-OF-APPEND | 536 / 0 | `'1`; `'2` | [a28-sample-03-range.log](a28-sample-03-range.log) |
| byte-store-k0-staging<br>FN-BS-K0T-PENDING-ENTRY-TARGETS-OF-APPEND | 223 / 0 | `'1`; `'2`; `'3` | [a28-sample-04-range.log](a28-sample-04-range.log) |
| byte-store-k0-staging<br>FN-BS-K0T-WRITES-KNOWNP-OF-APPEND | 12 / 0 | `'1` | [a28-sample-04-range.log](a28-sample-04-range.log) |
| byte-store-k0-staging<br>FN-BS-K0T-WRITES-NONEMPTYP-OF-APPEND | 45 / 0 | `'1`; `'2`; `'3` | [a28-sample-04-range.log](a28-sample-04-range.log) |
| store-log-kernel-concrete<br>FN-LGC-OBSERVERS-OF-ABSTRACTION | 360 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8` | [a28-sample-05-range.log](a28-sample-05-range.log) |
| store-log-kernel-concrete<br>FN-LGC-APPEND-OCTETS-OF-ABSTRACTION | 232 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8` | [a28-sample-05-range.log](a28-sample-05-range.log) |
| store-log-kernel-concrete<br>FN-LGC-FITSP-OF-ABSTRACTION | 1185 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8` | [a28-sample-05-range.log](a28-sample-05-range.log) |
| byte-store-k0<br>FN-BS-K0C-CUT-PAIR-IS-PREVIOUS-PAIR | 4 / 34 | `'1`; `(BINARY-+ '1 K)` | [a28-sample-06-range.log](a28-sample-06-range.log) |
| byte-store-k0<br>FN-BS-K0C-OK-KINDS-RETURN-OK | 5 / 0 | `'1`; `'2` | [a28-sample-06-range.log](a28-sample-06-range.log) |
| byte-store-k0<br>FN-BS-K0C-NTH-SUCC | 13 / 31 | `'1`; `(BINARY-+ '1 K)` | [a28-sample-06-range.log](a28-sample-06-range.log) |
| bp-node-rotation-recovery<br>FN-BPRPF-ADMITTED-RECOVERY-IS-THE-EVENT-BY-DEFINITION | 4 / 0 | `'1`; `'2` | [a28-sample-07-range.log](a28-sample-07-range.log) |
| bp-node-rotation-recovery<br>FN-BPNR-PROOF-ANSWER-FIELDS | 3 / 0 | `'1`; `'2` | [a28-sample-07-range.log](a28-sample-07-range.log) |
| bp-node-rotation-recovery<br>FN-BPNR-RUNTIME-WRITERS-KEEP-BASE | 8 / 0 | `'1` | [a28-sample-07-range.log](a28-sample-07-range.log) |
| byte-store-record-provenance-owner<br>FN-BS-K0-FRONTIER-ROOT-EIO-APPLY-IS-SUCCESSFUL-BYTE-FENCE | 4 / 0 | `'1` | [a28-sample-08-range.log](a28-sample-08-range.log) |
| byte-store-record-provenance-owner<br>FN-BS-K0-FRONTIER-ROOT-EIO-APPLY-REACHES-DURABLE-CUT | 185 / 0 | `'1`; `'10`; `'11`; `'12`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8`; `'9` | [a28-sample-08-range.log](a28-sample-08-range.log) |
| byte-store-record-provenance-owner<br>FN-BS-K0-FRONTIER-NODE-ROOT-EIO-APPLIED-FENCES-RELATED-STATE | 458 / 0 | `'1`; `'10`; `'11`; `'12`; `'13`; `'14`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8`; `'9` | [a28-sample-08-range.log](a28-sample-08-range.log) |
| byte-store-record-fence<br>FN-BS-K8-OTHER-DIRECTORY-OPS-SURVIVE-FILTER | 86 / 0 | `'1` | [a28-sample-09-range.log](a28-sample-09-range.log) |
| byte-store-record-fence<br>FN-BS-K8-ENTRY-AFTER-THROUGH-DIRECTORY-OPS | 607 / 0 | `'1`; `'2`; `'3` | [a28-sample-09-range.log](a28-sample-09-range.log) |
| byte-store-record-fence<br>FN-BS-K8-DIRECTORY-FILTER-KEEPS-INODE-WRITES | 300 / 0 | `'1`; `'2`; `'3` | [a28-sample-09-range.log](a28-sample-09-range.log) |
| store-log-route<br>FN-OLR-LOG-NEED-IS-THE-APPEND-END | 71 / 0 | `'1`; `'2`; `'3`; `'4`; `'5` | [a28-sample-10-range.log](a28-sample-10-range.log) |
| store-log-route<br>FN-OLR-TAKE-IS-THE-PREPARE-AT-THE-OWNERS-TXID | 228 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8` | [a28-sample-10-range.log](a28-sample-10-range.log) |
| store-log-route<br>FN-OLR-TAKE-AGREES-WITH-THE-OWNER | 16342 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7`; `'8` | [a28-sample-10-range.log](a28-sample-10-range.log) |
| owner-publication-lifecycle<br>FN-OPL-ATTEMPTS-BEFORE-NATP | 33 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7` | [a28-sample-11-range.log](a28-sample-11-range.log) |
| owner-publication-lifecycle<br>FN-OPL-RECORD-IS-A-RECORD | 1779 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7` | [a28-sample-11-range.log](a28-sample-11-range.log) |
| owner-publication-lifecycle<br>FN-OPL-RECORD-CLASS | 37 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6`; `'7` | [a28-sample-11-range.log](a28-sample-11-range.log) |
| store-log-open-scan<br>FN-LGO-LZR-EXPAND-SHAPE | 110 / 0 | `'1`; `'2`; `'3`; `'4` | [a28-sample-12-range.log](a28-sample-12-range.log) |
| store-log-open-scan<br>FN-LGO-CHAIN-IS-THE-OPEN-CHAIN-FOLD | 24 / 0 | `'1`; `'2` | [a28-sample-12-range.log](a28-sample-12-range.log) |
| store-log-open-scan<br>FN-LGO-ARENA-OF-MAKE | 1 / 0 | `'1` | [a28-sample-12-range.log](a28-sample-12-range.log) |
| owner-obligation-state<br>FN-OWNER-OBLIGATION-VIEW-OF-OTHER-GLOBAL-PUT | 10 / 0 | `'1`; `'2` | [a28-sample-13-range.log](a28-sample-13-range.log) |
| owner-obligation-state<br>FN-OWNER-INSTALLED-OCFG-EFFECT | 4 / 0 | `'1`; `'2` | [a28-sample-13-range.log](a28-sample-13-range.log) |
| owner-obligation-state<br>FN-OWNER-INSTALLED-OWNER-BOUND | 4 / 0 | `'1`; `'2` | [a28-sample-13-range.log](a28-sample-13-range.log) |
| byte-store-k0-recovery<br>K0R-TARGETS-APPEND | 133 / 0 | `'1`; `'2`; `'3` | [a28-sample-14-range.log](a28-sample-14-range.log) |
| byte-store-k0-recovery<br>K0R-APPLY-WRITES-KEEPS-KEYS | 84 / 0 | `'1`; `'2`; `'3` | [a28-sample-14-range.log](a28-sample-14-range.log) |
| byte-store-k0-recovery<br>K0R-TARGETS-OF-TEAR-WRITE | 101 / 0 | `'1`; `'2`; `'3` | [a28-sample-14-range.log](a28-sample-14-range.log) |
| store-log-open-barriers<br>FN-LGOB-RELP-IDLE-HAS-NOTHING-PENDING | 35 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6` | [a28-sample-15-range.log](a28-sample-15-range.log) |
| store-log-open-barriers<br>FN-LGOB-DUPLICATE-SEGMENT-FENCE-IS-IDENTITY | 63 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6` | [a28-sample-15-range.log](a28-sample-15-range.log) |
| store-log-open-barriers<br>FN-LGOB-RECOVERED-KERNEL-HAS-NOTHING-IN-FLIGHT | 6 / 0 | `'1`; `'2`; `'3`; `'4`; `'5`; `'6` | [a28-sample-15-range.log](a28-sample-15-range.log) |

## Restriction decision and predicted recertify impact

| Candidate | Keeps measured uses? | Removes recorded collisions? | Decision |
| --- | --- | --- | --- |
| SYMBOLIC-only: `(syntaxp (not (quotep j)))` | Rejects every quoted match in the 45 events; removes all observed matches in the 43 quoted-only events. Could retain K matches in the two mixed events. | Removes the quoted fixed-field and 1024 expansion matches, but leaves symbolic successor-pattern displacement and the inverse with NTH-OF-CDR. | Does not keep the real quoted uses. |
| QUOTED-only: `(syntaxp (quotep j))` | Keeps every quoted match in the sample, but rejects the symbolic K matches. | Keeps exactly the quoted matches causing opaque field opening and NTH-1024 expansion. | Does not remove the collisions. |
| Neither; default-disable plus derived event-local enables | Keeps the theorem; intentional uses can be enabled only in proofs needing that opener. | Removes uncontrolled exported expansion. Local enables must be chosen against canonical field/slice facts. | Recommended; not implemented in adt-key-lib here. |

A proposed global A1 restriction/default change must be recertified with the ADT library’s affected closure. The existing census finds **1274 distinct Rules-list user events in 198 books** (1803 repeated summary uses). Those are observed dependency lower bounds, not the full cert-cache invalidation closure and not predicted failures. The sample shows that symbolic-only would change the proof path for at least 43 quoted-only sampled users; it does **not** show they all fail—three first-book controls succeeded with the opener disabled. Quoted-only preserves the dangerous constant matches, so it is insufficient even if it reduces some symbolic use. Default-disable will require rechecking the observed users and deriving local enables from proof failures or necessary matches, not blindly enabling every census entry. The exact red count and wall cost require that recertify, which was not launched.

The implemented A28 changes themselves require recertification of the four edited books and their affected closures. Static gates and cached-dependency admissions do not supply new closure-key certificates. The two untouched exec books require no F-Z source change. The positive opener remains unchanged and enabled wherever the existing exporters enable it; the separate F-P decision is the next source-policy action for main.

## Five static gates and shutdown

| Command | Exit | Result | Evidence |
| --- | ---: | --- | --- |
| `python3 tools/one_world_check.py` | 0 | 29 / 29 sites; 0 findings | [a28-one-world-gate.log](a28-one-world-gate.log) |
| `python3 tools/book_roots_check.py` | 0 | 1934 / 1989 books covered; 55 excluded; 0 unlisted / unanalyzable | [a28-book-roots-gate.log](a28-book-roots-gate.log) |
| `python3 tools/host_check.py --attach-order` | 0 | 3 pairs; 56 files; 0 findings | [a28-attach-order-gate.log](a28-attach-order-gate.log) |
| `python3 tools/extract/world.py --check` | 0 | no output | [a28-world-gate.log](a28-world-gate.log) |
| `python3 tools/interface_emit.py --check` | 0 | 1915 declared; 1862 / 1862 dispatched; 0 findings | [a28-interface-gate.log](a28-interface-gate.log) |

The interface checker retains its pre-existing source-undecidable categories, including one unresolved keystone; they are non-failing and were not changed or rebaselined. The five gates ran after the completed measurement. No gate regenerated source files.

Every owned session was stopped by the named proof_repl wrapper: `a28-constant`, `a28-pages`, `a28-catalog`, `a28-zero-cursor`, `a28-zero-chunk`, and `a28-sample-01` through `a28-sample-15`. The five individual stop logs and each sampled run’s stop result are retained beside this report / in the sample JSON. No unrelated process/session was stopped. No commits, pushes, box certification jobs, publication, or adt-key-lib edits.

Recheck the edit audit:
```sh
timeout 20 python3 build/vertical-runs/one-world/pairfix_edits.py
```
The initial apply command is intentionally single-use because it refuses to overwrite the before fixtures.
