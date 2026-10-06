# LANEDUMP extract-b (2026-10-05/06; successor of extract and extract-b²; card D, D40)

## Mission (5 lines)
Card D of the extraction family: make raw host dispatch a JUDGED, CARRIED thing —
the ACL2 world itself judges every raw-declared fn-interfaces row (verdicts as
table data, digested), the image AND the extracted core admit raw only through
one gate (fn-rdv-admit over the world's own judgment), and export refuses a
world whose table is not its own judgment. Fixes the core dying at load since
633e3cdec ("Selected ACL2 table metadata is unavailable for FN-CARRIED").

## Landed (both commits pushed; origin/lane/extract-b == 1e99adbf0, verified)
- 913113600 — D40 raw-dispatch verdicts: books/raw-dispatch-verdict.lisp
  (fn-rdv-judge, table fn-raw-dispatch-verdicts, fn-rdv-admit, keystones
  fn-rdv-admits-only-a-clean-judged-row / fn-rdv-admit-returns-the-judged-
  target), host/raw-dispatch-verdicts.lisp (make-event), fnn-install-raw-dispatch
  one path for image+core (refused/unjudged/changed row stops the build BY NAME),
  xt-core-verdicts re-judges at export, tests + driver test. Laptop
  certify-20261006T012051Z-51253 GREEN.
- 1e99adbf0 — defteeth for both keystones via an mv-list bridge in
  books/defkeystone.lisp (fn-dt-bridge-events): defteeth's assert-event could
  not evaluate (mv-nth k (mv-fn ...)) claims (ACL2 forbids a multiply valued
  call as an argument outside a theorem context, :DOC mv-nth); the bridge
  re-translates each assert-event's value (stobjs-out T) and wraps every >1-
  output call in (mv-list k ...), definitionally the identity; unused lambda
  formals with variable/constant actuals are dropped. Identity for mv-free
  claims (three pinned expansions unchanged; fn-dt-two-first-is-x pins the
  bridge). tools/teeth_check.py marks generated assert-events exempt; the 21
  remaining findings are other books' pre-existing hand debt. Laptop
  certify-20261006T015538Z-86958 GREEN, manifest indexed.

## What the defteeth cover (tests/acl2/raw-dispatch-verdict-tests.lisp)
- fn-rdv-admits-only-a-clean-judged-row: mutations unjudged-row, unread-row,
  digest-unchecked, problem-ignored (an admit that skips digest comparison
  dispatches a row changed since its verdict; one that ignores the judged
  problem dispatches a refused row) — each with positive witness, clean-
  hypothesis removal, :must-fail.
- fn-rdv-admit-returns-the-judged-target: mutations judged-target-ignored
  (returns the row's own name → applies the wrong raw function), judged-role-
  ignored (grants creator role to every row → traps the wrong dispatch).
- Tail note (verbatim intent): NO defteeth-check in this book — it declares
  teeth for its own plain defthms, and its closure (state-digest →
  def-keyset-check) carries other books' fn-teeth-owed rows, dev-wide gate
  debt, not this book's to discharge.

## Certify verdict (hbox, --lane)
- Run run-20261006T020943Z-57ad (certify-20261006T021147Z-2903647, extract-b²'s
  submit): 36 books — 28 PASSED / 8 FAILED. This lane's own books GREEN
  (books/raw-dispatch-verdict, tests/acl2/raw-dispatch-verdict-tests,
  books/defkeystone, tests/acl2/defkeystone-tests; none in the failed set).
- Run run-20261006T021824Z-e0d5 (certify-20261006T022159Z-2918125, extract-b³'s
  submit, same --lane closure): installed the 28 green from cache, re-certified
  the 8 — SAME 8 RED. Reproduced twice.
- The 8: tests/acl2/{def-carried-view,feed-connection-teeth,newnews-cursor,
  peer-carriage,resource-vector-relations,resource-vector,resource-vector-tree,
  withdrawal-index-carried}-tests. Signature everywhere: `ACL2 Error
  [Translate] in ASSERT-EVENT: The variable EVENTS/ARTS/BUDGET/OP is not
  [used]` — defkeystone-expansion assert-events (mv-claim teeth class).
  NOT this lane's books; plausibly the dev-wide class teeth-gate documented
  (TEETH-OWED-MV-CLAIM: "defkeystone.lisp change, every closure" — the change
  this lane landed; residual shapes: unused formals whose actuals are not
  variables/constants). Repair items GEN-CARRIED-VIEW, FILL-KEYSTONE-EMIT-151,
  X18 reference these books as pre-existing loci.
- OPEN for the coordinator: base-vs-head attribution of the 8 was NOT
  established (no run at base 319aee828). Triage: certify one of the 8 at
  base, or check teeth-gate-owed.md classes. If pre-existing, they join the
  dev-wide teeth debt; if 1e99adbf0 broke them, the bridge's identity claim
  for mv-free claims is falsified and the fix is the bridge, not the books.

## NEXT PHASE — the recorded question (verbatim, extract-b²'s dying insight)
"The chain closes only if fn-rdv-admit and friends are in the extracted
closure — raw host code isn't walked, so the tokens must carry them. Read
host_tokens.py."

Lane PAUSED after two context deaths; resume with the closure question.

## Mission remainder (from extract-b², unstarted)
(a) core LOAD-side digest check (fnn-install-raw-dispatch in the extracted
core; the snapshot carries fn-interfaces + fn-raw-dispatch-verdicts);
(b) wire xt-core-verdicts into the export the release runs (tools/extract/
core.sh, release FN_RELEASE_SERVED=extracted); (c) qualification smoke/core/
peer; (d) close planning/decisions.md item 8 (the D40 row).

## Traps (kept from extract-b²)
- keystone_emit --check: 165 pre-existing dev-wide findings, none fn-rdv-*;
  the manifest is stale dev-wide, not this lane's to rewrite.
- teeth_obligations gate scans defkeystone forms only; plain defthm+defteeth
  adds no gate rows.
- (stobjs-out 'if w) HARD-ERRORS — the bridge reads (getpropc fn 'stobjs-out
  nil w); translated let-lambdas carry ignorable formals.
- NEVER explore tools/extract/* or host_tokens.py casually — two agents died
  of context there. Names only, then plan the read.
