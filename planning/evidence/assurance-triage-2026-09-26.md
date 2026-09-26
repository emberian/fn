# assurance-triage, 2026-09-26

Lane `lane/assurance-triage` from dev 0d211647. Brief:
`build/coordinator/queue/w3-assurance-triage.txt`. Ids: PKT-412 to PKT-416
(all five taken, below); no PRF, requirement or SCN id was taken.

| count | before | after |
|---|---|---|
| `proofs.json` status | typed: 9 certified, 109 in-progress, 11 planned | generated: 116 certified, 0 uncertified-at-current-digest, 13 planned |
| model-only theorems (`reach_check`) | 49 baselined, 25 with the placeholder reason | 41, every one SPEC (36) or HOST (5) |
| books over 10 s at 2 jobs (the brief's four) | 4 (worst under load: 11.6, 11.2, 10.4, 13.9 s) | 0 (r1 on hbox: 3.02, 3.12, 2.12, 2.97 s) |
| implemented or validated scenarios naming a test and a log | 0 of 32 (no field) | 28 of 28 (4 returned to specified; 23 on a native image, 5 not) |

## 1. The status field is generated

Chosen: generate, not delete. Four tools read it (`check_scaffold`,
`certified_claims` selects the rows it audits by it, `current_view` prints it
into current.md, `teeth_check` prints it), and "which targets have every cited
event certified at today's bytes" is the question a reader asks of the
registry. Deleting it would move that question into each reader.

- `tools/ledger.py`: `derived_status` and `event_books`; `apply_events` now
  writes `status` with `events`. `planned`: no events. `certified`: a manifest
  the row cites under `planning/evidence/manifests/` recorded every event's
  defining book `passed` at its current source digest and include closure
  (`certified_claims.certifies`, the rule make check already applies).
  Otherwise `uncertified-at-current-digest`. A hand-edited value makes
  `ledger.py --check` report `planning/proofs.json: stale` (tried: flipping
  PRF-001 by hand fails the check).
- Scope stated in docs/proofs.md "Registry states" and the registry's
  description: the status covers the cited events, not everything a target's
  statement says. Editing a book turns its targets uncertified until the lane
  cites the run that certified the new bytes; that is the point.
- `deferred` and `in-progress` are gone from `check_scaffold`'s set (no row
  used `deferred`).
- 53 rows cited a manifest at an older digest (or none) while an archived
  manifest certified their books at the current digest; each now cites the
  newest such manifest (48 at the first pass, five more after r1 certified the
  six BP books no archived manifest had at current bytes:
  bp-node-progress-bridge, -receipt-send, -contact-driver, -job-offer-progress,
  -job-offer, -run-class).
- Tests: tests/test_ledger.py `GeneratedStatusTests` (planned; uncertified
  without a cited manifest; certified at the current digest; not at an older
  one). `certified_claims`: 116 certified targets, 288 event books, 0 warnings,
  0 citation failures.

## 2. The model-only theorems

`reach_check` before: 49 baselined, 0 unbaselined. After: 41, 0 unbaselined.
Removed from the registry because a hosted theorem states the property of the
function the host calls (each theorem stays in its book; four are lemmas other
books `:use`):

| PRF | theorem | why no host line reaches it | hosted theorem that carries it |
|---|---|---|---|
| PRF-001 | `fn-node-trace-preserves-state` | the host steps `fn-sn-prepare`/`fn-sn-finish` one event at a time through `fn-own-store-step`; `fn-node-trace` is an event-list model | `fn-sn-prepare-preserves-state`, `fn-sn-finish-preserves-state`, `fn-snrt-mixed-trace-preserves-live-history-relation` |
| PRF-001 | `fn-node-trace-preserves-old-bindings` | same | `fn-snrt-acknowledged-history-retained-through-mixed-trace` (PRF-007) |
| PRF-001 | `fn-recover-preserves-state` | recovery is a reopen and replay (`fn-store-sn-recover`, host/store-node-host.lisp) | `fn-sn-recover-preserves-state` |
| PRF-002 | `fn-state-has-fresh-local-numbers` | an invariant consequence the host never evaluates | `fn-own-raw-local-number-is-never-reassigned`, `fn-own-served-local-number-is-never-reassigned` (proved from it) |
| PRF-010 | `fn-index-rebuild-correspondence` | nothing calls `fn-index-rebuild`; the served index is `fn-gidx-build` -> `fn-index-build` | replaced by `fn-index-build-correspondence` (the same property of `fn-index-build`) |
| PRF-016 | `fn-wm-pattern-match-work-cost` | a counting copy of a per-pattern helper; an intermediate lemma of the whole-match bound | replaced by `fn-wm-match-codepoints-work-value`, which equates the counted matcher with the served `fn-wildmat-match-codepoints` |
| PRF-076 | `fn-hm-run-keeps-every-open-admitted` | the host calls `fn-hm-after-commit`/`fn-hmr-open-verdict` (host/native/io.lisp `fnn-check-history-marker`) | `fn-bs-marker-crash-open-stays-admitted` (same conclusion over the host's marker program) |

Hosted after a checker fix: PRF-044 `fn-bs-txn-name-impl-injective`. The host
names files through `fn-store-txn-name` -> `fn-sbud-txn-name` -> the constrained
`fn-bs-txn-name`, which books/byte-store-txn-name.lisp `defattach`es to
`fn-bs-txn-name-impl`. `reach_check` now follows `defattach` (both forms), with
a test.

The 41 that remain, each with its disposition in planning/reach-baseline.json
(`reach_check --strict` now refuses the placeholder reason or one that is not
SPEC or HOST):

| PRF | theorem | disposition | reason (as recorded in the baseline) |
|---|---|---|---|
| PRF-001 | `fn-bprv-actual-finite-replay-preserves-invariant` | SPEC | the receiver-only journal semantics fn-bpr-live-state-is-replay-of-journal is stated against; the host replays with fn-bpaj-replay / fn-bpaj-apply-record-fast (host/bp-receipt-journal-host.lisp fn-bprj-install), whose per-record step is the hosted fn-bprv-actual-record-preserves-invariant. Hosting it needs a bridge fn-bpaj-replay = fn-bprr-replay off the transit arm (PKT-413). |
| PRF-001 | `fn-bprv-successful-replay-has-invariant` | SPEC | the receiver-only journal semantics fn-bpr-live-state-is-replay-of-journal is stated against; the host replays with fn-bpaj-replay / fn-bpaj-apply-record-fast (host/bp-receipt-journal-host.lisp fn-bprj-install), whose per-record step is the hosted fn-bprv-actual-record-preserves-invariant. Hosting it needs a bridge fn-bpaj-replay = fn-bprr-replay off the transit arm (PKT-413). |
| PRF-001 | `fn-bprv-system-run-preserves-invariant` | SPEC | the process-lifetime interleaving the two hosted step theorems (fn-bprv-store-step-preserves-evolving-invariant via fn-own-store-step, fn-bprv-apply-record-preserves-evolving-invariant via fn-bpaj-apply-record-fast) compose into; the host has no lifetime loop to call. |
| PRF-007 | `fn-bprv-successful-replay-has-invariant` | SPEC | the receiver-only journal semantics fn-bpr-live-state-is-replay-of-journal is stated against; the host replays with fn-bpaj-replay / fn-bpaj-apply-record-fast (host/bp-receipt-journal-host.lisp fn-bprj-install), whose per-record step is the hosted fn-bprv-actual-record-preserves-invariant. Hosting it needs a bridge fn-bpaj-replay = fn-bprr-replay off the transit arm (PKT-413). |
| PRF-011 | `fn-exchange-admitted-ingest-retains-conflicting-evidence` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-exchange-admitted-order-member` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-exchange-merge-commutative-member` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-exchange-merge-idempotent` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-exchange-policy-ingest-trace-preserves-facts` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-exchange-policy-ingest-trace-preserves-statep` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-transfer-add-chunk-preserves-statep` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-transfer-complete-entry-candidate-byte-agreement` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-transfer-complete-entry-candidate-correct` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-transfer-exact-duplicate-no-overwrite` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-011 | `fn-transfer-reserve-preserves-statep` | SPEC | M4 exchange/transfer staging model (specs/transfer-experiment.md: no wire format, queue or protocol chosen); nothing in host/ or tools/ names fn-exchange-* or fn-transfer-*. The host's article exchange is NNTP peering (fn-peer-decide-transfer, PRF-042), a different property. Kept as the model a future exchange adapter must refine. |
| PRF-012 | `fn-bprv-actual-finite-replay-preserves-invariant` | SPEC | the receiver-only journal semantics fn-bpr-live-state-is-replay-of-journal is stated against; the host replays with fn-bpaj-replay / fn-bpaj-apply-record-fast (host/bp-receipt-journal-host.lisp fn-bprj-install), whose per-record step is the hosted fn-bprv-actual-record-preserves-invariant. Hosting it needs a bridge fn-bpaj-replay = fn-bprr-replay off the transit arm (PKT-413). |
| PRF-012 | `fn-bprv-successful-replay-has-invariant` | SPEC | the receiver-only journal semantics fn-bpr-live-state-is-replay-of-journal is stated against; the host replays with fn-bpaj-replay / fn-bpaj-apply-record-fast (host/bp-receipt-journal-host.lisp fn-bprj-install), whose per-record step is the hosted fn-bprv-actual-record-preserves-invariant. Hosting it needs a bridge fn-bpaj-replay = fn-bprr-replay off the transit arm (PKT-413). |
| PRF-016 | `fn-article-parse-work-profile-bound` | SPEC | the cost bound of the counting copy fn-aw-parse; the hosted fn-article-parse-work-value equates its value with fn-article-parse, which host/bp-ingress-host.lisp and tools/stx.py call. The number is the model's until admission consults a parse budget (unimplemented, not wrong). |
| PRF-016 | `fn-transfer-entry-candidate-work-cost-bound` | SPEC | transfer-model lemma or budget for the unimplemented M4 chunked transfer (as PRF-011); no host transfer exists to call it. Belongs with PRF-011's family. |
| PRF-016 | `fn-transfer-entry-candidate-work-value` | SPEC | transfer-model lemma or budget for the unimplemented M4 chunked transfer (as PRF-011); no host transfer exists to call it. Belongs with PRF-011's family. |
| PRF-016 | `fn-transfer-initial-statep` | SPEC | transfer-model lemma or budget for the unimplemented M4 chunked transfer (as PRF-011); no host transfer exists to call it. Belongs with PRF-011's family. |
| PRF-016 | `fn-transfer-invalid-chunk-no-overwrite` | SPEC | transfer-model lemma or budget for the unimplemented M4 chunked transfer (as PRF-011); no host transfer exists to call it. Belongs with PRF-011's family. |
| PRF-016 | `fn-wm-match-codepoints-work-cost-bound` | SPEC | the cost bound of the counting copy fn-wm-match-codepoints-work; PRF-016 now also cites fn-wm-match-codepoints-work-value, which equates it with the served fn-wildmat-match-codepoints (fn-nntp-filter-groups-by-wildmat). The bound is the model's until LIST ACTIVE consults a budget. |
| PRF-041 | `fn-bs-crash-image-frontier-decodes-to-a-natural` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-crash-image-namespace-is-contiguous` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-crash-image-reads-the-config` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-k0-covered-crash-image-is-a-related-image` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-k0c-cut-pair-is-previous-pair` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-stable-prefix-retained-by-byte-crash` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-step-preserves-k0-coverage` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-041 | `fn-bs-store-crash-image-is-kernel-admissible` | SPEC | a byte-store model lemma (K0 coverage, K1/K2 scan and crash image, K5 stable prefix) that the hosted results are built from: the fn-bs-k0-*-cut-relation-by-step family, fn-bs-recover-program-keeps-relation-at-every-cut and fn-bs-crash-image-reopens are over the host storage programs (native_program_check maps them to fnn-finish/fnn-recover). The host open scans natively, so no ACL2 caller of the scan exists. The earlier reason (host programs not proved to keep fn-bs-store-relation) is out of date. |
| PRF-043 | `fn-feed-journal-uncertainty-survives-all-later-observations` | SPEC | the model of the host's sequence of fnn-owner-feed-phase calls (host/native/owner.lisp), each one fn-feed-journal-phase-step; the host never folds a list. A one-step restatement over fn-feed-journal-phase-step would be hosted. |
| PRF-045 | `fn-bpn-sf-step-preserves-nonreuse` | SPEC | the crash-trace model of the native sequence-file protocol (fnn-bp-reserve-sequence); fn-bpn-sf-host-{reserve,recover}-is-core-* tie it to the hosted core fn-bpn-sequence-reserve/-recover. |
| PRF-045 | `fn-bpn-sf-trace-preserves-safety` | SPEC | the crash-trace model of the native sequence-file protocol (fnn-bp-reserve-sequence); fn-bpn-sf-host-{reserve,recover}-is-core-* tie it to the hosted core fn-bpn-sequence-reserve/-recover. |
| PRF-083 | `fn-bs-read-ranges-concatenate` | SPEC | models the native back-to-back read loop of fnn-state-checkpoint-plan (host/native/io.lisp) under A-HOST-EXCLUSIVE-READ; no ACL2 function can be its caller. Decoding after the reads join is hosted (fn-sccr-decode-plan-is-decode-segments). |
| PRF-088 | `fn-rcl-reclaim-keeps-the-numbering` | SPEC | the in-memory reclaim transition no host verb drives; the host reclaims offline (fn-store-reclaim-decide -> fn-rclp-decide), whose record-level numbering is the hosted fn-rclp-event-decodes-to-the-tombstoned-record (PRF-119). No theorem yet equates replaying the rewritten pack with fn-rcl-reclaim-state (PKT-416). |
| PRF-118 | `fn-arena-seal-keeps-sealed` | HOST | not implemented; nothing includes payload-arena. The finish (fnn-owner-attempt -> fn-owner-finish-submission) must seal with fn-arena-seal-buffer and the reopen (fn-store-sn-recover) seal one handle per retained record, after the records-shape freeze: PKT-029/PKT-303 (rep-wave-d). Preparatory work, not a running capability (review-2026-09-26-gpt6-answers). |
| PRF-118 | `fn-arena-seal-new-handle` | HOST | not implemented; nothing includes payload-arena. The finish (fnn-owner-attempt -> fn-owner-finish-submission) must seal with fn-arena-seal-buffer and the reopen (fn-store-sn-recover) seal one handle per retained record, after the records-shape freeze: PKT-029/PKT-303 (rep-wave-d). Preparatory work, not a running capability (review-2026-09-26-gpt6-answers). |
| PRF-118 | `fn-arena-seals-keep-sealed` | HOST | not implemented; nothing includes payload-arena. The finish (fnn-owner-attempt -> fn-owner-finish-submission) must seal with fn-arena-seal-buffer and the reopen (fn-store-sn-recover) seal one handle per retained record, after the records-shape freeze: PKT-029/PKT-303 (rep-wave-d). Preparatory work, not a running capability (review-2026-09-26-gpt6-answers). |
| PRF-118 | `fn-arn-store-corr-of-commit` | HOST | not implemented; nothing includes payload-arena. The finish (fnn-owner-attempt -> fn-owner-finish-submission) must seal with fn-arena-seal-buffer and the reopen (fn-store-sn-recover) seal one handle per retained record, after the records-shape freeze: PKT-029/PKT-303 (rep-wave-d). Preparatory work, not a running capability (review-2026-09-26-gpt6-answers). |
| PRF-118 | `fn-arn-store-corr-of-open` | HOST | not implemented; nothing includes payload-arena. The finish (fnn-owner-attempt -> fn-owner-finish-submission) must seal with fn-arena-seal-buffer and the reopen (fn-store-sn-recover) seal one handle per retained record, after the records-shape freeze: PKT-029/PKT-303 (rep-wave-d). Preparatory work, not a running capability (review-2026-09-26-gpt6-answers). |

The checker is still generous in ways this triage measured and did not fix
(PKT-412): subjects include `:hints` and hypothesis symbols
(`fn-article-parse-work-input-bound` is "hosted" through `fn-cbor-at-mostp` in
a hint; PRF-088's `fn-rcl-reclaim-state` theorems through a reachable
hypothesis), and `host/index-host.lisp`, which nothing loads, still seeds the
graph. The 41 is a floor.

## 3. The four books over ten seconds

Read in the REPL on hbox (w28 toolchain, `tools/proof_repl.py`, each form
timed as sent; `accumulated-persistence` was not informative because none of
the four spends its time in the prover).

| book | worst at 2 jobs, current digest, before | where the time goes | change | r1, hbox, 2 jobs |
|---|---|---|---|---|
| tests/acl2/bp-node-forwarding-teeth-tests | 13.9 s (hbox; 8.5 to 10.8 s typical) | evaluation: `fn-bpb-encode` of the 49,254-octet fixture bundle is 0.31 s; each `:session` `fn-bpnp-step` is 1.3 s (three forward scans, each encoding every candidate); about 5 s of the book | the fixture keeps its shape at one eighth of the sizes (payloads 6,144 and 1,024 octets against MRUs 4,096 and 8,192; the held-image bound 131,072 is untouched); every assertion and the must-fail hold unchanged; guards were already verified (`fn-bpnp-step` is `:common-lisp-compliant`), so including bp-node-progress-guards changed nothing | 2.97 s |
| books/bp-node-progress | 11.1 s once under load; 4.8 to 6.5 s otherwise | about 100 definitions, no expensive proof event (each form under 0.1 s) | none: its time is compilation and include, not proof | 3.12 s (recertified) |
| books/bp-node-job-offer | 11.6 s under load at an earlier digest | at the current digest it measured 3.27 s | none | 3.02 s (recertified) |
| tests/acl2/relay-source-routes-tests | 10.4 s once under load; 1.7 to 4.9 s otherwise | 52 forms, none over 0.11 s | none | 2.12 s (recertified) |

Run `run-20260926T072413Z-c8fc` = `certify-20260926T072432Z-773372` (hbox,
jobs_effective 2, 10 certified, 209 installed, verdict passed, "no book over
10 s"), manifest planning/evidence/manifests/certify-20260926T072432Z-773372.json.
No baseline edit and no split. The finding behind the fixture change is a
served-path cost, filed as PKT-414 (quadratic-shaped encode work per session
event; D27). Three of the four were over ten seconds only under concurrent
load, which answers §7 already called measurement evidence.

Still over ten seconds in `proof_cost.py` (not the brief's four, not worked
here): books/owner-invariants 10.29 s (the baseline's one book; was 25 to 41 s
before the last merge) and books/owner-control-read 10.34 s (5.3 to 5.8 s in
its other measurements), both from the loaded run certify-20260926T064807Z-632722.
Per-event times for owner-invariants in the REPL: no event over 0.81 s; 31
events over 0.15 s total about 9 s; the cost is spread across the relation
preservation theorems, so bringing it down is a per-theorem hint pass, not one
fix.

## 4. fn-bpn-limits-compose and PKT-265

`fn-bpn-limits-compose` (introduced ed05e1ab) is already gone: bp-lifecycle-4
(9ebf5f0e) replaced it with `fn-bpn-limits-compose-at-the-codec-widths`
(books/bp-limits.lisp, cited by PRF-134), whose statement is a set of true
codec-width relations at 2^24 and keeps the sender job image at 131,072
(PKT-294). Who cited the old theorem: no book, test book or registry row (git
grep at 9ebf5f0e^ finds only its own defthm); the citations were four prose
lines in specs/bp-node-machine.md, which bp-lifecycle-5 already points at the
replacement. The limitation stays visible, as the answers asked: the new
theorem is not a proof that the whole sender-to-receiver path accepts every
profile-admitted ADU (books/bp-limits.lisp header; PKT-294).

PKT-265 (the fragment/job-table relation, cold start only): what the
warm-start theorem needs is written into PKT-415 for the BP lane: (1) recovery
replay establishes `fn-bpnf-family-jobs-agreep` for every journal whose replay
is `:ready`, which needs the lemma that every replayed fragment row is
job-only and every replayed issued record names a non-fragment row; (2) every
`fn-bpnp-host-eventp` arm of `fn-bpnp-step` preserves it, the statement in the
packet; teeth a warm witness and a must-fail without the non-fragment premise.
Until then the hot path keeps the checks that rely on the relation.

## Packets filed (planning/backlog-2026-09-25.md, "assurance-triage")

- PKT-412 reach_check generosity: conclusion-only subjects, loaded-host seeds.
- PKT-413 the bpaj/bprr replay bridge that hosts five baselined bprv entries.
- PKT-414 BP encode cost per session event (served path, D27).
- PKT-415 PKT-265's warm-start relation.
- PKT-416 the reclaim bridge (reopening the rewritten pack is `fn-rcl-reclaim-state`).

## 5. The scenario catalog

Every `implemented` or `validated` scenario now carries `implementation`:
`test` (a dotted test module, or a harness script's path), `cases` (the
classes or methods; each must occur in the module), `native` (whether a native
image ran it), `log` (a committed log of a passing run) and `record` (the
evidence record reporting it). `tools/check_scaffold.py`
`scenario_implementation` refuses a scenario without them, a case the module
lacks, an uncommitted log, and a log that neither names the test nor is named
by the record (tests/test_scenario_implementation.py, six cases, added to
`make tooling-test`). `validated` stays the qualification lane's mapping.

Logs harvested so the check can hold (each record gained one line naming the
file and its SHA-256, which matches the digest or prefix the record already
quoted): bp-routing-2 test_bp_node_native.log (5038214f...), peer-carriage
tests2.log (12f02fc4...), visibility-join's log (f5cbf08a...), bp-lifecycle-3
test_bp_fragment_node_native.log (fc37d711..., from its tgz), mission-four-node
unsigned.out (from its tgz), mission-signed-2 signed-r2.out (ff9cf70c...) and
report.json (55580c3b...), width-producers-2 gate-served.log (4de4b106...),
the hbox files copied from the lanes' own scratch trees.

Returned to `specified` (the catalog's `note` says why; conflicting evidence
kept, not overwritten):

- SCN-027: no recorded run of the SBCL witness or any native run.
- SCN-047: the one recorded native run refused the 2^40 charge and wrote no
  schema-2 record, the opposite of the expected result.
- SCN-055: the served-node steps are recorded as NOT RUN; only fake-node
  tests ran.
- SCN-056: no committed harness or log, and the recorded numbers show a
  checkpoint start slower than full replay.

Not native (`native: false`, the scenario's own scope says so): SCN-002
(validated; tests.test_store on the Python host), SCN-026 (tests.test_owner),
SCN-036 and SCN-068 (tests.test_fn_web against a fake NNTP peer; SCN-068's
native half is a scripted browser walk). Harness scripts rather than unittest
modules: SCN-049, 050, 051, 066, 070, 072, 074 (and SCN-076's walk).

| scenario | status | test | native | log (under planning/evidence/) |
|---|---|---|---|---|
| SCN-002 | validated | `tests.test_store` | no | `harness-repair-2026-09-25/laptop-after.txt` |
| SCN-026 | implemented | `tests.test_owner` | no | `harness-repair-2026-09-25/laptop-after.txt` |
| SCN-036 | implemented | `tests.test_fn_web` | no | `harness-repair-2026-09-25/laptop-after.txt` |
| SCN-040 | implemented | `tests.test_native_history_marker` | yes | `m5-history-lifetimes/native-marker.log` |
| SCN-041 | implemented | `tests.test_native_control_filing` | yes | `control-c3e-2026-09-25/native-control-filing-9ad31f6c.log` |
| SCN-042 | implemented | `tests.test_bp_node_native` | yes | `bp-routing-2-2026-09-25/test_bp_node_native.log` |
| SCN-043 | implemented | `tests.test_native_state_checkpoint` | yes | `qual-bbf52159/chainC.out` |
| SCN-045 | implemented | `tests.test_native_history_required` | yes | `marker-required/native-required.log` |
| SCN-049 | implemented | `planning/evidence/live-status-2026-09-25/native.sh` | yes | `live-status-2026-09-25/summary.txt` |
| SCN-050 | implemented | `planning/evidence/path-and-login-2026-09-25/pl_probe.py` | yes | `path-and-login-2026-09-25/tin-wire.log` |
| SCN-051 | implemented | `planning/evidence/path-and-login-2026-09-25/pl_probe.py` | yes | `path-and-login-2026-09-25/probe-bound.log` |
| SCN-052 | implemented | `tests.test_native_profile_namespace` | yes | `bounds-profile/native-namespace.log` |
| SCN-054 | implemented | `tests.test_native_hybrid_author` | yes | `peer-carriage-2026-09-25/tests2.log` |
| SCN-058 | implemented | `tests.test_native_peer_pull` | yes | `peer-pull-2026-09-25/native-peer-pull.log` |
| SCN-059 | implemented | `tests.test_bp_node_native` | yes | `bp-n16-prod-2026-09-25/test_bp_node_native-r4.log` |
| SCN-060 | implemented | `tests.test_native_visibility_join` | yes | `visibility-join-2026-09-25/tests.test_native_visibility_join.log` |
| SCN-062 | implemented | `tests.test_native_source_corpus` | yes | `source-corpus-2026-09-25/native-15.log` |
| SCN-068 | implemented | `tests.test_fn_web` | no | `harness-repair-2026-09-25/laptop-after.txt` |
| SCN-061 | implemented | `tests.test_native_consumer_exchange` | yes | `consumer-e2/test_native_consumer_exchange.gate-eca72d1c.log` |
| SCN-066 | implemented | `tests/bp-dtn7/run_mission_four_node.py` | yes | `mission-four-node/unsigned.out` |
| SCN-071 | implemented | `tests.test_native_peer_pull` | yes | `peering-tls-pull-2026-09-26/native-peer-pull.log` |
| SCN-067 | implemented | `tests.test_bp_fragment_node_native` | yes | `bp-lifecycle-3-2026-09-26/test_bp_fragment_node_native.log` |
| SCN-070 | implemented | `planning/evidence/operator-health-2026-09-25/native.sh` | yes | `operator-health-2026-09-25/native-out/summary.txt` |
| SCN-072 | implemented | `planning/evidence/width-producers-2-gate-served.sh` | yes | `width-producers-2-2026-09-26/gate-served.log` |
| SCN-076 | implemented | `tests.test_native_rollback_history` | yes | `rollback-history-2026-09-26/green2-test.log` |
| SCN-074 | implemented | `tests/bp-dtn7/run_mission_four_node.py` | yes | `mission-signed-2-2026-09-26/signed-r2.out` |
| SCN-073 | implemented | `tests.test_native_source_corpus_bp` | yes | `source-corpus-2-2026-09-26/native-7.log` |
| SCN-080 | implemented | `tests.test_native_consumer_exchange` | yes | `consumer-e2-2/test_native_consumer_exchange.gate-9900a68f.log` |

## Assurance chain for this slice

This lane changed checkers and registries, not a served path. The one book
change is a test book: tests/acl2/bp-node-forwarding-teeth-tests exercises the
host-called `fn-bpnp-step` (host/native/bp-service.lisp
`fnn-bps-foundation-step`) on reachable states built by the host-called
receive path; the change shrinks its fixture and keeps every assertion and the
must-fail. Native entry, refinement and behavioural theorem are those of
PRF-120/PRF-121, unchanged.

## What ran

- `make check-lane` green after steps 1 to 4 and again after step 5 (exit 0,
  at b70c619a's tree).
- Farm r1 on hbox, 2 jobs, 300 s: run-20260926T072413Z-c8fc, passed 10,
  failed 0, "no book over 10 s"; manifest committed. One farm run (the budget
  was three).
- REPL sessions on hbox (w28): forwarding-teeth-tests (before and after),
  relay-source-routes-tests, bp-node-progress, owner-invariants; all stopped.
- Unit tests: tests.test_ledger GeneratedStatusTests, tests.test_reach_check,
  tests.test_certified_claims, tests.test_scenario_implementation.

## Not done

- books/owner-invariants (10.29 s) and books/owner-control-read (10.34 s),
  both from one loaded run: not the brief's four; owner-invariants needs a
  per-theorem hint pass (no event over 0.81 s).
- The checker generosity (PKT-412), the bprv bridge (PKT-413), the encode cost
  (PKT-414), the warm-start relation (PKT-415) and the reclaim bridge
  (PKT-416) are filed, not started.
- The arena (PRF-118) stays HOST under PKT-029/PKT-303.
