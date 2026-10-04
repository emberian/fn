# Lane tariff2: lanedump (Opus successor of tariff; exited on ramp-down 2026-10-04)

Worktree: build/lanes/tariff2 (this lane's own; the Fable dir build/lanes/tariff is not used).
Branches:
- lane/tariff2: the slice, at native-config bytes of next.
- lane/tariff2-optin: lane/tariff2 plus the native-config opt-in, for batch R.
Both are on origin. Base: origin/next, merged at 30e5133b4.

## Coordinate table

| sha | world receipt | manifest | image | native run |
|---|---|---|---|---|
| (this lanedump's commit on lane/tariff2) | persvati narrow certify (rule 3): run-20261004T043912Z-0a6f: 8 passed (output-tariff-article{,-row} + tests, output-admission-line at its earlier bytes), 1 failed (tests/acl2/output-reservation-tests: its expected (:heap 528 ...) is stale at next's bytes; not this lane's, and the book is back at next's bytes); run-20261004T050951Z-77d3: 11 passed, 0 failed (output-admission-line + tests at current bytes) | certify-20261004T044137Z-1141752, certify-20261004T051020Z-1493764 (indexed in planning/evidence-index.tsv) | none | none: raw harness tests/native_output_preflight_raw-mock.lisp, green at lane HEAD, red at 00ee1ec57 (old producer arity / refuses instead of answering) |

## What landed on lane/tariff2 (in order)
1. d216ab498: tests/acl2/output-tariff-article-tests.lisp, defteeth over the three keystones of
   books/output-tariff-article.lisp (removal per hypothesis; mutations: off-by-one, always-hold,
   wrong family, saturation). Makefile roots. Laptop REPL: 14 forms through defteeth-check.
2. c4fb292f2: the producer and the wire.
   - books/output-tariff-article-row.lisp: the version-free row charge. Keystones:
     - fn-tariff-article-prices-the-served-row (number/current form: exact at every view, or 0);
     - fn-tariff-article-prices-the-served-msgid (≤ at every view);
     - fn-tariff-article-served-payload-within-xref;
     - fn-tariff-article-octets-of-two-renders (the Xref form's two renders folded).
   - books/output-admission-line.lisp: :unpriced-output-family → 403 with the connection kept;
     :output-tariff-unaffordable → 400 and close. Keystone fn-oadl-refusal-is-one-line.
   - host/owner-host.lisp fn-owner-output-tariff-preview(id preview fn-arena fn-cat state):
     ARTICLE from the row, every other family (:unpriced F). New fn-owner-output-refusal-line-at.
   - host/native/owner.lisp: fnn-owner-output-prefix-locked returns the refusal word and logs it
     (ACL2 line fn-oadl-log-line). The step answers it via fnn-owner-output-refusal-locked.
     The pass-through arm is KEPT.
   - books/output-admission-line.lisp fn-oadl-accounting-line; host/native/operator.lisp prints it in
     status and health ("output accounting: on ..." / "output accounting: off (no [resources])").
   - host/cost-host.lisp: def-cost for fn-ocap-at, fn-ocap-admit-preview, fn-tariff-article-octets,
     fn-tariff-article-descriptor (:visits 0, nothing unaccounted; laptop REPL).
   - interfaces rows; specs/resource-vector.md: the dated open precondition.
   - Ledger: PGO-TARIFF-ARTICLE-REPLY-WITHIN-TARIFF (PRF-1316), proof-owed.
3. ffb5a8543 / 5a9173d17: the native-config opt-in moved to lane/tariff2-optin (assembler: native-config
   is a root-closure book held for batch R with apps and caps).
4. 6b5f13fa2: Makefile roots for the row and admission-line books; tests/acl2/output-admission-line-tests.lisp.
5. df7b43268: fn-ocap-at's interface row declares :kinds ((n natp)), the last class disagreement on next.
6. 075343bea: the status line moved into books/output-admission-line.lisp (fn-oadl-accounting-line);
   books/output-reservation.lisp is back at next's bytes.
7. 1efcad5fa: tools/cost_obligations.py records "families" (priced of served) in the generated
   cost-obligations.json. At this tree: priced 1 of 25 (article). Tests in tests/test_cost_obligations.py.

## Counts
- cost-obligations none (computed at the lane tree; interfaces.json not regenerated, the integrator's):
  1,655 at next's committed json → 1,653 (fn-ocap-at and fn-ocap-admit-preview none → proved).
  The 1,442 of the packet was measured at an older base.
- Families priced on the served path: 0 → 1 of 25 (ARTICLE).
- Proof-owed: 1 filed (PRF-1316, the exec-arm cons bound).

## Rulings recorded (root, 2026-10-04)
- (a) as first written would have answered 403 to every command but ARTICLE on every default node.
  Ruling: the pass-through at owner.lisp fnn-owner-output-prefix-locked is deleted, with a profile
  default (quantum = the maximum of the families' tariffs at the profile's article bound), in the
  commit that prices the LAST family a stock node serves, i.e. when "unpriced_families" in
  cost-obligations.json is empty. Until then a node without [resources] behaves as before.
- (b) unpriced family in accounted mode: 403, connection kept (done). Over quantum: 400 and close.
- An explicit [resources] output policy is the operator's opt-in (lane/tariff2-optin, batch R).
- Status and health show the accounting mode (done).

## What remains (exact continuation, in order)
1. The integrator merges lane/tariff2 into the pending-native batch: regenerate interfaces.json and
   cost-obligations.json (--write); image native: [resources] set, ARTICLE n → 220 and NEWNEWS → 403
   on the batch-R image (needs lane/tariff2-optin). Red at base: run refused "output_resources".
   Suggested test: tests/test_native_output_tariff.py (not written; it needs the opt-in image).
2. tests/owner_output_preview_fixture.lisp still calls the old 3-argument producer. It is an orphan
   (no runner names it). Either delete it, or rewrite it over the row book's catalog fixture
   (tests/acl2/output-tariff-article-row-tests.lisp) with a connection whose session selects fn.test.
3. PRF-1316: def-cost :conses rows for fn-nntp-article-idp, fn-rcl-tombstonep, fn-nntp-crlf,
   fn-nntp-single, fn-nntp-retrieval-initial, fn-nntp-block-rev / fn-nntp-section-rev; then
   fn-tariff-article-reply-within-tariff over fn-nntp-article-response-of-bytes.
4. Next family (packet order): HEAD/BODY/STAT. Same row, smaller sections.
   - Generalize fn-tariff-article-descriptor to take the family; the HEAD/BODY replies are within
     ARTICLE's, and STAT is the initial line.
   - Add :head :body :stat to the producer's quoted list in fn-owner-output-tariff-preview.
     The ratchet then reads 4 of 25.
5. Q2 amendment (i), which unblocks apps' FNCR row (sent to apps; recorded verbatim in
   TARIFF-OWED-FNCR-CONNECTION, lane/apps@23d02fe96):
   - books/definterface.lisp fn-di-operation-formp: accept :slot :dynamic only with :principal :connection;
   - books/def-cost.lisp fn-cost-operation-drawp: with :dynamic, match the draw over any
     non-constant slot term whose tariff argument calls the declared tariff.
   Then apps declares :operation on fn-crf-open.
6. definterface :operation as the generator (packet Q2 items 1-7). Not started.

## Box log
- hbox: run-20261004T035150Z-1621, cancelled on the assembler's rule (one at a time, --jobs 8).
- persvati REPL slot (granted by the assembler): tarp, from about 04:15Z to about 04:38Z, stopped.
  The row book was admitted in it, with the closure source-loaded. The admission-line book could
  not load its closure from source (served-tls-prefix encapsulate; served per-form limit) and was
  stopped. The certify above is its check.
- persvati certify: run-20261004T043912Z-0a6f (8 passed / 1 failed, see table) and
  run-20261004T050951Z-77d3 (11 passed). Nothing on hbox.
- Laptop REPLs (tat2, tcost, tresp): all stopped. books/statement-codec failing from source on the
  laptop was a theory leak from records-invariants (root's diagnosis), not a toolchain difference.
