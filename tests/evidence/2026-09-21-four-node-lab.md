# Four-node carried-media lab, 2026-09-21

A complete run, and the first one since `4ec3541` in which the lab could
start at all. `tests/evidence/2026-09-21-four-node-lab.json` is the machine
record the lab wrote; this file says what it means. It replaces
`tests/evidence/2026-09-20-four-node-lab.md`, whose run was made on a tree
that predated the `bundle` argument (see "What was broken" below).

## Invocation and versions

- Command: `python3 tests/bp-dtn7/run_four_node_lab.py`, run from the lane
  worktree `build/lanes/w11-workflow-replay`, which is where its evidence
  directory and this file are anchored.
- Revision `90818958c69f33097daeb5c90979d57aabb0e9e4` (the `dev` merge of this
  lane) with the lane's uncommitted sources in the tree; the commit that
  follows adds only this file, the JSON and the registry rows. The lab's own
  `sources_unchanged` digest over `books/`, `host/`, `tools/` and
  `tests/bp-dtn7/` is **true**, so nothing under it moved during the run.
- Transport `mock_bpa` (no `DTN7_REPO`); the pinned-dtn7-rs run is separate
  and was not made.
- Python 3.14.7 (Clang 21.0.0), macOS 26.6.1 arm64.
- ACL2 8.7 on SBCL 2.6.8, `/opt/homebrew/bin/acl2`, sha256
  `36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`, reached
  through `tools/run_store.py`, `tools/run_bp_receive.py`,
  `tools/workflow_bridge.py` and `tools/bundle_bridge.py` against the
  certificates installed in that worktree.
- 67.1 s, against the 300 s budget `tests/test_four_node_lab.py` enforces.

## Result

**Passed. Twenty-two of twenty-two named assertions were checked and every one
held**, including the eleven the 2026-09-20 00:20 run never reached and which
the run this file replaces reached on a tree that could no longer start.

| assertion | outcome |
| --- | --- |
| `window_1_delivers_both_letters` | held |
| `relay_a_accepts_both_letters` | held |
| `relay_a_archival_receipts_survive_kill` | held |
| `relay_a_journal_is_usable_after_recovery` | held |
| `relay_a_onward_obligation_recoverable_after_kill` | held |
| `relay_a_archival_receipts_unchanged_by_recovery` | held |
| `media_hop_accepts_both_letters` | held |
| `carried_media_is_not_modified_by_import` | held |
| `media_reimport_is_duplicate_not_a_second_acceptance` | held |
| `lost_receipt_regenerates_byte_identically` | held |
| `reimport_adds_no_receipt_record` | held |
| `attempt_expires_while_no_contact_is_open` | held |
| `expired_attempt_leaves_the_work_outstanding` | held |
| `retry_uses_a_distinct_transport_identity` | held |
| `window_2_delivers_a_reordered_pair_and_a_duplicate` | held |
| `the_pair_reaches_the_destination_in_the_reverse_of_its_submission_order` | held |
| `destination_accepts_each_letter_once_and_calls_the_rest_duplicates` | held |
| `destination_holds_exactly_one_acceptance_per_article` | held |
| `destination_holds_exactly_one_archive_pin_per_article` | held |
| `every_node_holds_the_exact_article_bytes` | held |
| `each_node_advanced_only_by_its_own_acceptances` | held |
| `the_same_letter_carries_a_different_local_number_at_home_and_destination` | held |

Each of the four nodes ends with 2 articles, 2 pins, 2 records and a local
number frontier of 3, and every node's stored bytes equal the posted bytes.

## The assertion this lane was sent for

`relay_a_onward_obligation_recoverable_after_kill` **asserts something it did
not assert before.** It read `work_status_a1 not in ("", "absent",
"unknown")`, and the lab's own recovery branch reaches that by re-enqueuing
`a1` — so the assertion held whether the obligation came back from the journal
or was created fresh, which is the one distinction it exists to make.

The cut reached `relay-a-killed-mid-forward` with `SIGKILL` and resolved as
`durable-intent-recovered-committed`, and the lab now reads three values
around it, all of them ACL2's:

    work_status_a1              outstanding
    work_origin_a1_at_recovery  enqueued
    work_origin_a1_after_reopen recovered
    work_status_a1_after_reopen outstanding
    work_origin_a2_after_reopen recovered

In the session that resolved the cut, the obligation is that session's: the
replay that opened it installed no work, and the recovery outcome was applied
live, so ACL2 answers `enqueued`. The session then ends, and a **new process**
finds the work in the journal: `recovered`, which is an answer only replay can
produce, with `outstanding` beside it saying the work carries no attempt yet.
`fn-bp-work-origin-at-open-is-recovered-or-absent` and
`fn-bp-durable-enqueue-after-open-reads-enqueued`
(`books/bp-workflow-replay-status.lisp`, PRF-034) are the theorems behind
those two words.

## What was broken, and what the repair means for this record

At `dev` `38460cf` the lab died at `run_four_node_lab.py:439` with
`TypeError: receive_bpa_request() missing 1 required keyword-only argument:
'bundle'`. `4ec3541` (2026-09-19) made `bundle` required and moved
`tools/media.py` to `(identity, adu, bundle)` triples; `w6/workflow-restart`
branched from a dev that predated it, so the merge of the two produced a lab
that could not start. Nothing in `make check` runs a lab, so it stayed red.

The repair is not cosmetic and it changes what this record shows. fn stages an
inbound bundle under the identity **ACL2 derives from the bundle's own primary
block**, so the mock BPA now carries a real primary block per bundle, encoded
by ACL2 through the new `tools/bundle_bridge.py:encode_primary`
(`fn-bpi-host-bundle-prefix`); a forwarded copy carries the same octets under
a fresh BID. The duplicate at the destination and the media re-import are
therefore duplicates **by fn's identity derivation**, not by the stand-in's
bookkeeping, which is stronger than what the 2026-09-20 record showed. The run
cost rose from 40.5 s to 67.1 s.

## Limits (the machine record carries these verbatim)

- The mock BPA is a laboratory contact scheduler, not BPv7: no convergence
  layer, routing or status reports, and every bundle carries a primary block
  and nothing else. The primary block is real and the staging identity is
  ACL2's, so the duplicate and redelivery behaviour here is fn's; the
  scheduling around it is not an interoperability result.
- Bundle expiry in this lab is the **scheduler's**: the primary block's
  lifetime is long enough that no admissible true time falls outside it, so a
  bundle that reaches a receiver is `:live` and
  `attempt_expires_while_no_contact_is_open` tests the queue drop it means to,
  not a receiver clock decision. A receiver-side expiry refusal is NOT
  exercised here; `tests/test_bp_receive.py` covers it.
- A relay is receiver-then-sender through two host paths. No relay receipt
  kind is emitted, so no accepted forwarding responsibility (SCN-001) is
  demonstrated; `books/relay.lisp`'s forwarding undertaking is recorded as a
  **proposal** and never as a passed assertion.
- `run_bp_receive` carries one destination EID, policy and issuer, so all four
  nodes present the same application endpoint identity.
- Trusted local A-POLICY: unsigned receipts, no authenticated peer.
- Real local process death (SIGKILL of a created process group) and real
  filesystem recovery. No power-loss and no media-hardware claim.
- Contact windows are explicit and never overlap by construction. This is not
  a scheduler, liveness or fairness result.
- One kill point, at one durable publication boundary. The cut table is not
  enumerated here.

## Assertions that still cannot run

None in this lab: all twenty-two ran. Two things next door still cannot.

- `tests/ltp/run_fn_ltp_lab.py:96` calls `receive_bpa_request` without
  `bundle` and fails the same way this lab did. It was not repaired here.
- The pinned-BPA run (`DTN7_REPO`) raises `NotImplementedError` by design;
  `tests/test_four_node_lab.py` asserts that it declares itself rather than
  skipping silently.
