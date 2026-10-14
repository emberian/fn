# P1D — guard repairs and two direct-book RED mechanisms

The four proto guard refusals are confirmed ADT-NTH-1+ dependencies: each fails with the rule disabled and passes when **only that rune is added to its guard hint**. All four resulting complete Rules sets match dev evidence. Eleven subjects receive the authorized single LOCAL enable line: the four named proto books and seven additional historical census users. P1 now records 53 enable subjects, including its 42 committed enables. All five static gates pass. **Catalog and probe remain RED and are diagnosis only**: both are category **(iii), enabled ADT-NTH-0 interacting with the builtin NTH definition**, not a missing ADT-NTH-1+ enable and not the pair fixes. No commits or changes to any of the seven excluded books.

Baseline: `2a4c8a203`, publishing run `run-20261014T023805Z-c10b`, `build/acl2/certify-20261014T024024Z-828604`; [triage-c10b.txt](triage-c10b.txt) reports six REAL refusals and 375 cascades. The diagnosis reproduces both direct-book refusals in current certified-dependency hbox worlds; it does not supply a new certificate at any changed closure key.

## A. Four guard controls

Each current-world session loads the certified dependency prefix before the `defadt-keyed` declaration. The actual generator is expanded with TRANS1; its preceding events are admitted through the generated pool recognizer. The failing/generated DEFUN is then sent unchanged. The passing control changes **only its existing :GUARD-HINTS enable list**, adding ADT-NTH-1+; the function, stobj, guard formula, recursion and all other hints stay unchanged. No generator or generated implementation is edited. The expanded diagnostic files are output from the existing generator, not handwritten twins.

| Subject / generated guard event | Rule off | Rule locally on | Dev Rules comparison |
| --- | --- | --- | --- |
| books/proto/adt-config-groups; CFGROUP$C-POOLW | refusal; 931,579 steps / 2.34 s | admitted; 37,655 steps / 0.21 s | all **82** runes identical to certified dev-reference guard replay |
| books/proto/adt-config-policy; CFPOLICY$C-POOLW | refusal; 199,921 steps / 0.43 s | admitted; 19,873 steps / 0.06 s | all **73** runes identical to certified dev-reference guard replay |
| books/proto/adt-consumer-position; CPENT$C-POOLW | refusal; 460,249 steps / 0.95 s | admitted; 27,085 steps / 0.10 s | all **77** runes identical to archived successful dev certificate |
| books/proto/adt-topic-accepted-type; STXA$C-POOLW | refusal; 1,102,845 steps / 2.52 s | admitted; 41,534 steps / 0.27 s | all **82** runes identical to archived successful dev certificate |

Evidence: [p1d-guards.json](p1d-guards.json), [p1d-guard-rule-comparison.json](p1d-guard-rule-comparison.json), and each `p1d-<name>-off.log` / `p1d-<name>-on.log`. CPENT/STXA archival evidence is named by exact file and summary line in the comparison JSON. CFGROUP/CFPOLICY have no archived certificate logs in the named P1 corpus; their comparison uses the unchanged generated guard and a certified dev-reference dependency world, whose default opener behavior reproduces the full 82/73-rule sets without the added guard hint. Those two reference replays are [p1d-dev-cfgroup-guard.log](p1d-dev-cfgroup-guard.log) and [p1d-dev-cfpolicy-guard.log](p1d-dev-cfpolicy-guard.log), with their install-set scopes in the corresponding start logs. They are **not** presented as historical certificates.

## Census root cause, regeneration, and exact edit boundary

The original SUMMARY parser was already generic and captured DEFUN and explicit VERIFY-GUARDS Form/Rules summaries. It was **not a DEFTHM-only parser**; a claim to that effect would be false. The concrete coverage defect was `certify-2026101*`, which excludes October 1–9. That omitted, for example, CPENT$C-POOLW in the successful October 7 `integrate-20261006n` certificate (summary at line 545), and STXA$C-POOLW in its October 7 certificate (line 636). The extended script explicitly tests and tags function/guard summaries and scans all October dates. It also names a disjoint September guard-only scope; that scope adds no qualifying dev users in this corpus. Failed/incomplete certificates, source echoes and own/one-world-descendant lane logs still do not qualify.

`p1_enables.py` now has fixtures for DEFTHM, DEFUN, VERIFY-GUARDS, a macro wrapper whose outer Rules list is NIL, and a decoy rune outside a Rules block. Its log prefilter batches rg calls before reading full logs. Its idempotent apply accepts each committed enable exactly once at its original anchor; the 42 committed subjects are left byte-identical. A stale other-lane HEAD detected before apply caused a refused apply; a fresh provenance scan and apply succeeded. No ancestry/staleness check was bypassed.

The historical selection still uses `U = (U_dev union U_lane_other) minus the seven exclusions`: **49 dev users**, **43 qualifying other-lane users**, **51 selected historical subjects**. The expanded historical corpus adds nine subjects over the original 42. CFGROUP/CFPOLICY are additional **explicitly authorized named guard repairs** after the four off/on controls; their absent archival logs are not replaced with fabricated dev provenance or own-lane certificates. This distinction is recorded in `authorized_guard_repairs`, `guard_repairs_without_historical_logs`, and the `A28-authorized-guard-repair` evidence entries. The original success/provenance predicate is unchanged.

The final list and evidence were regenerated through the script: [p1-enables.txt](p1-enables.txt), [p1-enables.json](p1-enables.json), [p1-census.json](p1-census.json), [P1.md](P1.md). Total enable subjects: **53 = 42 committed + 11 new**. Missing original CFGROUP/CFPOLICY certificate-log paths were requested for additional archival corroboration; the authorized source repairs and full dev-reference rule comparisons do not depend on that reply.

Newly inserted subjects:

- `books/history-image-census.lisp`
- `books/history-pool-columns.lisp`
- `books/history-root-status.lisp`
- `books/proto/adt-compact-lib.lisp`
- `books/proto/adt-config-groups.lisp`
- `books/proto/adt-config-policy.lisp`
- `books/proto/adt-consumer-position.lisp`
- `books/proto/adt-nest-lib.lisp`
- `books/proto/adt-topic-accepted-type.lisp`
- `tests/acl2/history-image-binding-tests.lisp`
- `tests/acl2/history-image-canonical-tests.lisp`

Each receives exactly `(local (in-theory (enable adt-nth-1+)))` after its last raw top-level include. [p1d-one-line-audit.json](p1d-one-line-audit.json) verifies **HEAD plus that one line only** for all eleven files. All seven exclusions and `adt-key-lib` are byte-identical to HEAD. Here is every source diff:

```diff
diff --git a/books/history-image-census.lisp b/books/history-image-census.lisp
index be8bec49d..8fcdd7a28 100644
--- a/books/history-image-census.lisp
+++ b/books/history-image-census.lisp
@@ -3,6 +3,7 @@
 ; retained, traversed or materialized by these scalar operations.
 (in-package "ACL2")
 (include-book "history-pages-row")
+(local (in-theory (enable adt-nth-1+)))
 
 (defun fn-hcc-begin ()
   (declare (xargs :guard t))
diff --git a/books/history-pool-columns.lisp b/books/history-pool-columns.lisp
index f13a58d6c..8da12bdcf 100644
--- a/books/history-pool-columns.lisp
+++ b/books/history-pool-columns.lisp
@@ -4,6 +4,7 @@
 (include-book "history-page-buffers")
 (include-book "history-image-columns")
 (include-book "snapshot-source-token")
+(local (in-theory (enable adt-nth-1+)))
 
 ; phase,count,ordinal,offset,pool-limit,child,token,key,encoded,column,capture,lease.
 (defun fn-hpcx-shapep (c)
diff --git a/books/history-root-status.lisp b/books/history-root-status.lisp
index 512be2556..6280d2646 100644
--- a/books/history-root-status.lisp
+++ b/books/history-root-status.lisp
@@ -14,6 +14,7 @@
 (include-book "history-root-credit")
 (include-book "native-live-status")
 (include-book "history-capture-state")
+(local (in-theory (enable adt-nth-1+)))
 
 (defun fn-hrs-line (status)
   (declare (xargs :guard t))
diff --git a/books/proto/adt-compact-lib.lisp b/books/proto/adt-compact-lib.lisp
index dd83a7d60..b6c8b9300 100644
--- a/books/proto/adt-compact-lib.lisp
+++ b/books/proto/adt-compact-lib.lisp
@@ -18,6 +18,7 @@
 
 (in-package "ACL2")
 (include-book "adt-key-lib")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (local (in-theory (disable nth update-nth)))
diff --git a/books/proto/adt-config-groups.lisp b/books/proto/adt-config-groups.lisp
index 8725bec66..b60bbb002 100644
--- a/books/proto/adt-config-groups.lisp
+++ b/books/proto/adt-config-groups.lisp
@@ -20,6 +20,7 @@
 (in-package "ACL2")
 (include-book "adt-keyed")
 (include-book "../config-invariants")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (defadt-keyed cfgroup :order :append :key name
diff --git a/books/proto/adt-config-policy.lisp b/books/proto/adt-config-policy.lisp
index 735626c1b..c40b12cb3 100644
--- a/books/proto/adt-config-policy.lisp
+++ b/books/proto/adt-config-policy.lisp
@@ -20,6 +20,7 @@
 (in-package "ACL2")
 (include-book "adt-keyed")
 (include-book "../config-invariants")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (defadt-keyed cfpolicy :order :append :key slot
diff --git a/books/proto/adt-consumer-position.lisp b/books/proto/adt-consumer-position.lisp
index 150909779..004fa84de 100644
--- a/books/proto/adt-consumer-position.lisp
+++ b/books/proto/adt-consumer-position.lisp
@@ -21,6 +21,7 @@
 (in-package "ACL2")
 (include-book "adt-keyed")
 (include-book "../consumer-position")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (defadt-keyed cpent :order :stack :key consumer
diff --git a/books/proto/adt-nest-lib.lisp b/books/proto/adt-nest-lib.lisp
index 2f6dd7532..52343b3e0 100644
--- a/books/proto/adt-nest-lib.lisp
+++ b/books/proto/adt-nest-lib.lisp
@@ -20,6 +20,7 @@
 
 (in-package "ACL2")
 (include-book "adt-key-lib")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (local (in-theory (disable nth update-nth)))
diff --git a/books/proto/adt-topic-accepted-type.lisp b/books/proto/adt-topic-accepted-type.lisp
index c36f59450..c0cf0c977 100644
--- a/books/proto/adt-topic-accepted-type.lisp
+++ b/books/proto/adt-topic-accepted-type.lisp
@@ -7,6 +7,7 @@
 
 (in-package "ACL2")
 (include-book "adt-keyed")
+(local (in-theory (enable adt-nth-1+)))
 
 (defadt-keyed stxa :order :stack :key sequence
   (sequence :u32) (txid :u32) (generation :u32) (keyring-generation :u32)
diff --git a/tests/acl2/history-image-binding-tests.lisp b/tests/acl2/history-image-binding-tests.lisp
index dc680ca3d..4f92328f7 100644
--- a/tests/acl2/history-image-binding-tests.lisp
+++ b/tests/acl2/history-image-binding-tests.lisp
@@ -24,6 +24,7 @@
 ; tables being the history's is witnessed instead (root-is-image removed).
 (in-package "ACL2")
 (include-book "../../books/history-image-fold")
+(local (in-theory (enable adt-nth-1+)))
 
 ; -----------------------------------------------------------------------------
 ; The host runs compiled code: every executable the host will call is
diff --git a/tests/acl2/history-image-canonical-tests.lisp b/tests/acl2/history-image-canonical-tests.lisp
index b1ce3f545..cfbe5ace3 100644
--- a/tests/acl2/history-image-canonical-tests.lisp
+++ b/tests/acl2/history-image-canonical-tests.lisp
@@ -2,6 +2,7 @@
 (in-package "ACL2")
 (include-book "../../books/history-image-concrete-proof")
 (include-book "../../books/history-image-size")
+(local (in-theory (enable adt-nth-1+)))
 (local (include-book "arithmetic/top" :dir :system))
 
 (defconst *m13-fresh* '(nil nil nil nil nil nil))   ; the empty pgs-mem
```

## B. Catalog: FN-CTG-KEY-OF-COMMIT-BASE — RED, category (iii)

Dev summary: `/Users/ember/dev/fn/build/integrate-20261006n/build/acl2/certify-20261007T091847Z-3873414/books--catalog-logic.certify.log:21558`; [p1d-catalog-dev-summary.txt](p1d-catalog-dev-summary.txt), **289 steps**. The publishing refusal is at summary line **23894**, **951 steps**. Dev uses the enabled type-prescription FN-CTG-CP-COUNT-NTH; the refusal does not. The count lemma is still enabled in the failing world, as [p1d-catalog-runes.log](p1d-catalog-runes.log) shows; this is a failed match, not a disable of that lemma.

The relevant pair of terms is:

```lisp
; Guard fact from local FN-CTG-CP-COUNT-NTH (count slot = 1):
(fn-cat$cp fn-cat$c) => (natp (nth 1 fn-cat$c))
; Bottom-up rewriting in the refusal, with NTH and A0 enabled:
(nth 1 fn-cat$c)
  -> (if (consp fn-cat$c) (nth 0 (cdr fn-cat$c)) nil)
  -> (if (consp fn-cat$c) (cadr fn-cat$c) nil)
; The reported branch has CONSP FN-CAT$C and NOT INTEGERP(CADR FN-CAT$C).
; The saved type rule is about NTH 1, not CADR.
```

A1 is **disabled** in the refusal, so this is not its constant matcher. Its temporary enable also fails. Removing A0 alone keeps A1 disabled and restores the **exact dev Rules set and 289-step proof**. Closing NTH alone with A0 retained admits in **200 steps**. The unchanged :USE instance of FN-CTG-KEY-OF-INDEX-ADD needs the count’s naturalness; expansion has removed the matching count term before that type rule can discharge it.

Exact dev-only / publishing-only runes:

```text
DEV ONLY
(:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
(:TYPE-PRESCRIPTION FN-CTG-CP-COUNT-NTH)
PUBLISHING ONLY
(:DEFINITION HIDE)
(:DEFINITION NATP)
(:DEFINITION NTH)
(:ELIM CAR-CDR-ELIM)
(:EXECUTABLE-COUNTERPART BINARY-+)
(:EXECUTABLE-COUNTERPART INTEGERP)
(:EXECUTABLE-COUNTERPART ZP)
(:REWRITE ADT-NTH-0)
(:REWRITE DEFAULT-CAR)
(:REWRITE NTH-ADD1)
```

Evidence: [p1d-catalog-baseline.log](p1d-catalog-baseline.log), [p1d-catalog-enable-a1.log](p1d-catalog-enable-a1.log), [p1d-catalog-disable-a0.log](p1d-catalog-disable-a0.log), [p1d-catalog-disable-nth.log](p1d-catalog-disable-nth.log). No catalog statement or hint is repaired in source.

## B. Probe: FN-MPL-PLACED-ENTRY-IS-REACHABLE — RED, category (iii)

Dev summary: `/Users/ember/dev/fn/build/integrate-20261006n/build/acl2/certify-20261008T234410Z-396321/books--msgid-probe-layout.certify.log:2303`; [p1d-probe-dev-summary.txt](p1d-probe-dev-summary.txt), **2480 steps**. Publishing summary line **2446** refuses after **18913 steps**. A0 is enabled and used in that certificate Rules list. A1 is disabled. The changed forward-chaining cursor-bounds rune is enabled and fires; the refusal is not caused by an absent A0 or disabled bounds theorem.

The remaining field-1 fact is still `(natp (nth 1 cursor))`, and the new rewriting produces CADR cursor. In the replay with the original, pre-9983b4b7c cursor-bounds statement reinstated, the failure again asks for `(integerp (cadr cursor))` under `fn-mpr-cursorp cursor pages`. The positive field-1 clause is unchanged by the literal NTH-0 substitution. The induction template’s printed `(nth 0 cursor)` is an unreduced source/induction term; it is not evidence that A0 is disabled during rewriting.

| Diagnostic control, source untouched | Catalog | Probe |
| --- | --- | --- |
| Current rule membership / current bounds | refuses, 951 steps | refuses, 18913 steps |
| Enable only A1 additionally | refuses | refuses |
| Disable only A0; A1 remains disabled | admits, 289 steps; exact dev Rules | admits, 2438 steps |
| Disable NTH; A0 stays enabled | admits, 200 steps | admits, 1946 steps |
| Restore original NTH-0 cursor bounds in REPL; A0 remains enabled | not applicable | refuses, same 18913-step attempt |

The original-bounds control undoes only that theorem and its two following lemmas in the session, re-admits the byte-preserved pre-pairfix statement, reloads the two unchanged helpers, and retries the unchanged event as THM. [p1d-probe-original-bounds.lisp](p1d-probe-original-bounds.lisp) / [p1d-probe-original-bounds.log](p1d-probe-original-bounds.log). This directly refutes the proposed F-Z-causation hypothesis in this world. All control changes are session-only; the source remains diagnosis-only.

Exact dev-only / publishing-only runes:

```text
DEV ONLY
(:DEFINITION NFIX)
(:REWRITE CAR-CONS)
(:REWRITE CDR-CONS)
PUBLISHING ONLY
(:DEFINITION SYNP)
(:ELIM CAR-CDR-ELIM)
(:EXECUTABLE-COUNTERPART <)
(:EXECUTABLE-COUNTERPART INTEGERP)
(:EXECUTABLE-COUNTERPART NOT)
(:EXECUTABLE-COUNTERPART SYMBOLP)
(:REWRITE ADT-NTH-0)
(:REWRITE DEFAULT-CAR)
(:REWRITE FN-HP-MV-NTH-CONS)
(:REWRITE NTH-ADD1)
(:REWRITE PGS-X-NFIX-WHEN-NATP)
(:REWRITE ZP-OPEN)
(:TYPE-PRESCRIPTION FN-MPR-ADVANCE)
```

The PGS-X-NFIX-WHEN-NATP and FN-HP-MV-NTH-CONS differences are retained in the full delta; removing A0 alone while retaining the remaining current theory admits. They are therefore not sufficient causes of this refusal. NFIX normalizes the changed branch in dev, while CAR-CONS/CDR-CONS no longer appear in the failed publishing path. Evidence: [p1d-probe-runes.log](p1d-probe-runes.log), [p1d-probe-baseline.log](p1d-probe-baseline.log), [p1d-probe-enable-a1.log](p1d-probe-enable-a1.log), [p1d-probe-disable-a0.log](p1d-probe-disable-a0.log), [p1d-probe-disable-nth.log](p1d-probe-disable-nth.log).

## Rune-setting events and shared mechanism

For every other rune in the two Rules-list deltas, the setting event is listed below. Initial-world entries are ACL2 boot events, inherited here without a new book-local admission or theory change. A Rules-list delta measures use during these attempts, not a change in the admission or enablement of each listed rune. The three remaining project events are enabled by their ordinary admission and retained through the imported theory.

| Remaining delta runes | Admission / setting event |
| --- | --- |
| `(:DEFINITION HIDE)`, `(:DEFINITION NATP)`, `(:DEFINITION NFIX)`, `(:DEFINITION SYNP)` | ACL2 initial-world function events HIDE, NATP, NFIX and SYNP, respectively. |
| `(:EXECUTABLE-COUNTERPART BINARY-+)`, `INTEGERP`, `ZP`, `<`, `NOT`, `SYMBOLP` | ACL2 initial-world primitive function events of the corresponding names; each supplies its executable-counterpart rune. |
| `(:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)` | ACL2 initial-world NATP-COMPOUND-RECOGNIZER event. |
| `(:ELIM CAR-CDR-ELIM)` | ACL2 initial-world CAR-CDR-ELIM event. |
| `(:REWRITE DEFAULT-CAR)`, `NTH-ADD1`, `CAR-CONS`, `CDR-CONS`, `ZP-OPEN` | ACL2 initial-world theorem events of the corresponding names. |
| `(:REWRITE PGS-X-NFIX-WHEN-NATP)` | DEFTHM at `books/pagestore-exec.lisp:1010`; default enabled. |
| `(:REWRITE FN-HP-MV-NTH-CONS)` | DEFTHM at `books/history-pages-step.lisp:253`; default enabled. |
| `(:TYPE-PRESCRIPTION FN-MPR-ADVANCE)` | DEFUN at `books/msgid-probe-cursor.lisp:23`; ACL2 derives this type-prescription at function admission. |

| Rune / fact | Event setting it | Effect at the two refusals |
| --- | --- | --- |
| ADT-NTH-0 | public DEFTHM in `books/proto/adt-key-lib.lisp:561`; imported through the concrete history include chain | Enabled T; unconditional NTH-0 → CAR permits the NTH definition to reduce positive opaque fields to selectors. |
| ADT-NTH-1+ | DEFTHMD at `books/proto/adt-key-lib.lisp:556`; the enable at :559 is LOCAL to that book | Exported default NIL. The seven direct subjects have no P1 book enable. Temporarily enabling it does not repair either RED. |
| NTH definition | ACL2 boot definition, inherited enabled; neither direct event hint excludes it | Enabled T; its translated RHS is `(and (consp l) (if (zp n) (car l) (nth (+ -1 n) (cdr l))))`. With A0, the positive field-1 term changes shape. |
| FN-CTG-CP-COUNT-NTH | local DEFTHM at `books/catalog-logic.lisp:2952`, classes `(:rewrite :type-prescription)` | Both runes enabled. Publishing does not use the type fact after NTH 1 becomes CADR. |
| FN-MPL-CURSOR-FIELD-BOUNDS | forward-chaining DEFTHM at `books/msgid-probe-layout.lisp:162`; 9983b4b7c changes only literal zero fields | Enabled T and fires in publishing. It still gives NATP(NTH 1 CURSOR); the original-bounds control fails too. |

The current import route is catalog:64 → msgid-linear-exec → msgid-linear → msgid-pages:46 → history-columns; probe:4 → msgid-probe-cursor → msgid-pages-exec → msgid-pages:46 → history-columns. `history-columns:10` introduces history-records and the history page implementation dependencies before the named `fn-hist-theory-before-paged` snapshot at :12; the concrete paged include is :13. The final NON-LOCAL `in-theory` at :187 unions foundation and enabled before-paged snapshots with the implementation-subtracted current theory. It preserves shared enabled rules, including the newly available A0. A0’s defining event is enabled by default; no direct-book event disables it before these proofs. This is the new imported-theory context relative to the old dev proof paths, not a theorem-statement regression from 9983b4b7c. The full deltas and provenance are [p1d-red-rule-delta.json](p1d-red-rule-delta.json). No claim is made that a rune absent from a dev Rules list was necessarily disabled; the controlled replays establish A0’s causal role.

## Five gates, audit and shutdown

| Command | Exit | Result / log |
| --- | ---: | --- |
| `python3 tools/one_world_check.py` | 0 | 29 / 29 sites; 0 findings; [p1d-gate-one-world.log](p1d-gate-one-world.log) |
| `python3 tools/book_roots_check.py` | 0 | 1934 / 1989 covered; 55 excluded; 0 findings; [p1d-gate-book-roots.log](p1d-gate-book-roots.log) |
| `python3 tools/host_check.py --attach-order` | 0 | 3 pairs; 56 files; 0 findings; [p1d-gate-host-attach-order.log](p1d-gate-host-attach-order.log) |
| `python3 tools/extract/world.py --check` | 0 | no output; [p1d-gate-extract-world.log](p1d-gate-extract-world.log) |
| `python3 tools/interface_emit.py --check` | 0 | 1915 declared; 1862 / 1862 dispatched; 0 findings; [p1d-gate-interface.log](p1d-gate-interface.log) |

The interface checker’s existing source-undecidable categories remain non-failing. The source diff is eleven insertions in eleven subjects; no direct-book, interface, generated register or library edit is hidden in that audit. New local guard enables are verified admission controls, not certificates of the revised books or their affected closures. Catalog/probe remain unrepaired REDs for main.

Stopped by the named wrapper: p1d-catalog, p1d-probe, p1d-cfgroup, p1d-cfpolicy, p1d-cpent, p1d-stxa, p1d-dev-cfgroup and p1d-dev-cfpolicy. Their stop logs are retained beside this report. No other session/process was stopped. No commits, pushes, deployments, publication, or certify jobs; census SSH work only read the named existing log trees.
