# LANEDUMP: lane/proof-cost-regressions

Branch `lane/proof-cost-regressions` (from dev `46f2660d`) has two commits: `ad0bbfb5` (the fix) and a follow-up commit (evidence, ledger and manifests). Nothing was pushed.

## Cause
- **Rule:** the definition `(:DEFINITION FN-TH-TOPIC-EVENTP)`. With it open, the prover also opened `FN-TH-LOCAL-ADMIN-EVENTP`, `FN-TH-AUTH-REF-P`, `FN-TH-SOURCE-ID-P`, `FN-TH-AT` and `FN-TH-EXACT-OCTETS-P` as splitters.
- **Where it came from:** `books/topic-history-store-events` defines the recognizer and leaves it enabled. Commit `15f4fb19` (Store envelope) made `books/store-events` include that book and put the recognizer inside `fn-store-event-p`, the event accessors, the encoder and the decoder. Commit `702d6ef1` and its successors made `books/replay` and `books/store-node` dispatch on it.
- **Why it leaked:** `books/consumer-store-events` withdraws its sibling `fn-cpe-eventp`, and the replay and Store proofs close `fn-cpe-eventp` by name. Nothing withdrew or closed the new topic recognizer, so every proof that dispatches on event kind unfolded the whole topic shape. The ledger's include-hygiene check had already flagged "no theory withdrawal" for this include.
- **Not the cause:** `frame.lisp`, `frame-journal.lisp` (the ION commit `9c47f526`) and the v6 export interface. The changes to the frame books only append constants.
- **Events that blew up** (before run; each lists FN-TH-TOPIC-EVENTP among its rules):

| Event | Book | Before | After |
| --- | --- | ---: | ---: |
| `fn-replay-apply-record-non-nil-is-node-state` | replay | 51.5 s, 27.2M steps | 0.12 s (REPL) |
| `fn-sn-finish-identity-arm-keeps-the-store-and-index` | store-node-invariants | 28.6 s | 0.02 s |
| `fn-sn-finish-acknowledges-exact-pair` | store-node-invariants | 15.5 s | 0.05 s |
| `fn-sis-finish-enabled-files` | store-identity-sequence-invariants | 19.5 s | 0.03 s |
| `fn-sis-finish-enabled-next` | store-identity-sequence-invariants | 16.7 s | 0.04 s |
| `fn-csi-finish-advances-projection-by-definition` | consumer-store-invariants | 19.0 s | 0.02 s |
| `fn-sti-current-records-topic-ok` and `...-including-completed` | topic-history-store-invariants | 16.0 s and 17.2 s | no longer slow |
| guard of `fn-sn-completion-core-enabledp` | store-node | 20.6 s | 0.02 s |

## Files changed
No theorem statement, hypothesis or definition changed. The book diff adds only hint entries, one local-free shape lemma and one `in-theory`.
- **`books/topic-history-store-events.lisp`:**
  - adds the forward-chaining `fn-th-topic-event-shape-by-definition`: a topic event is a true list with natural fields 1, 2 and 3.
  - then `(in-theory (disable (:d fn-th-topic-eventp)))`, following `consumer-store-events`.
- **`books/topic-history-identity-disjoint.lisp`:** three `-is-not-stx*` proofs enable `fn-th-topic-eventp` in their hints (0.02 s each).
- **`books/replay.lisp`:** the `fn-replay-record-is-a-true-list` hint enables `fn-th-topic-eventp`. Without it, 7221 subgoals took 11.9 s; with it, 0.29 s.
- **`books/store-node.lisp`:** the guard hint of `fn-sn-completion-core-enabledp` also closes the record, retention, stx, cpe and topic recognizers.
- **`books/consumer-event-index-store-invariants.lisp`:** `fn-ceis-prepare-identity-preserves-related` also closes `fn-stxe-p`, `fn-stxk-p` and `fn-stxa-p` (45.5 s before, 0.07 s after).
- **Evidence and ledger:**
  - evidence note: `planning/evidence/topic-recognizer-proof-cost-2026-09-24.md`
  - regenerated `planning/ledger.{json,md}`: +1 theorem; include-hygiene warnings 640 → 638
  - three manifests force-added
  - `make check` passes.

## Timings (same host, persvati; w25 toolchain `1b4169e9…`; 2 jobs; 300 s cap)
- **Before:** `run-20260924T084451Z-58c8` at 46f2660d → `planning/evidence/manifests/certify-20260924T084459Z-2414753.json`
- **After:** `run-20260924T090348Z-92f1` at ad0bbfb5 → `planning/evidence/manifests/certify-20260924T090352Z-2580961.json`

| Book | 6bfab467 (hbox, ref) | Before (s) | After (s) |
| --- | ---: | ---: | ---: |
| store-node-invariants | 19.6 | 85.00 | **17.59** |
| consumer-store-invariants | 7.7 | 41.98 | **8.33** (within 2x) |
| store-identity-sequence-invariants | 3.3 | 46.64 | **2.97** |
| store-node-traces | 15.2 | 50.49 | **20.25** (within 2x) |
| replay | 3.2 | 58.11 | **2.52** |
| consumer-event-index-store-invariants (bonus) | — | 74.53 | 28.06 |
| topic-history-store-invariants (bonus) | — | 48.32 | 13.04 |
| store-node | — | 23.16 | 2.57 |

The same leak explains most of `topic-history-store-invariants`. It explains only part of `consumer-event-index-store-invariants`; see below.

## Dependents re-certified
- **Run:** `run-20260924T090548Z-876b` (`--affected-by books/topic-history-store-events`, every Makefile root that includes it) → `planning/evidence/manifests/certify-20260924T090604Z-2599989.json`.
- **Result:** 332 certified, 329 passed. Summed book wall time was 1678 s on persvati. The same books took 2242 s on hbox at 46f2660d.
- **The three failures are the handoff's known reds:**
  - `books/bp-node-progress-guards` hit the 300 s cap in `VERIFY-GUARDS FN-BPNP-ISSUED-DEBT-DELTA`, the known missing premise.
  - `books/bp-node-progress-selection-invariants` failed at `fn-bpnp-step-progress-preserves-held-and-issued`.
  - `tests/acl2/bp-node-machine-teeth-tests` could not load its uncertified include.
  - The first two logs contain no `FN-TH-TOPIC`.

## Still over 10 s (from the after and dependent manifests)
- **Store books:**
  - consumer-event-index-store-invariants: 28.1
  - store-node-traces: 20.2
  - store-node-invariants: 17.6
  - topic-history-store-invariants: 13.0
- **Unrelated to this lane:**
  - checkpoint-compaction: 26.2
  - owner-invariants: 25.1
  - bp-fnbs-codec-invariants: 22.9
  - bp-fnbs-byte-invariants: 18.8
  - bp-channel-ingress: 13.6
  - nntp-auth-fold: 13.3
  - byte-store-record-provenance: 13.1
  - consumer-local-control: 11.6
  - owner-config: 11.0
  - checkpoint-codec: 11.0
  - bp-node-fragment-guards: 10.5
  - config-owner-live: 10.2

## Next concrete experiment
- **Remaining splitters:** the three stx recognizers `fn-stxe-p`, `fn-stxk-p` and `fn-stxa-p` are still globally enabled and are the next splitter in several Store proofs. That is why the store-node guard and CEIS proofs needed them closed by hand.
- **Proposed withdrawal:** withdraw them at export from their stx record books, following `consumer-store-events`. Give each an exported shape fact (true list, natural counters, leading tag) like `fn-th-topic-event-shape-by-definition`.
- **How to check it:** measure with the same REPL simulation first: send the disable after the includes, then `ld` the rest of each chain book. The script is `/tmp/fnpc-sim2.py` on persvati. Then run one `--affected-by` farm run.
- **Separate item:** CEIS `fn-ceis-finish-keeps-index` (14.2 s) and `fn-ceis-finish-keeps-records` (11.1 s) split on `fn-sn-finish` and `fn-sn-finish-identity`. A finish-arm projection lemma should fix them, in the style of the `store-node-traces` projection repair.
