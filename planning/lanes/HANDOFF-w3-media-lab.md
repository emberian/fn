# w3-media-lab handoff (C2-08)

HEAD: branch `w3/media-lab`, merged with `dev` at `72279c8`.

Carried-media export/import through the same bounded staging and acceptance
path as network receipt, and a four-node non-overlapping-contact lab with one
carried-media hop.

## Status of the run (rewritten 2026-09-20, after the merge with dev)

HEAD is `w3/media-lab` merged with `dev` at `72279c8`. The merge was clean; the
lane owns no ACL2 book, so nothing here needed the proof-style rewrite and
nothing was sent to the farm.

**There is now a real run, and it is an incomplete one.**
`tests/evidence/2026-09-20-four-node-lab.{json,md}` replace the two
placeholders. Ten of the twenty-one named assertions were checked and every
one held, including the whole carried-media group; the run then failed at
`tests/bp-dtn7/run_four_node_lab.py:541`. The eleven unreached assertions are
evidence for nothing.

### The one thing that blocks a complete run

`fn-workflow-preflight-history` refuses an `attempt` record --
`JournalError('ACL2 rejected workflow durable history before publication')` --
at two distinct points: for work relay-b enqueued in the same session, and for
work whose enqueue reached ACL2 only through recovery replay (relay-a, after
the mid-forward kill). The sharper reading from the same tree: **after a
journal reopen, `fn-workflow-work-status` answers `absent` for every work id
in the replayed history, although `fn-workflow-install-replay` answered
`ready`.** If that is the model rather than the bridge, no fn node can submit
outbound work across a restart, which is a v0.3 DTN blocker and not this
lane's to close. Owner: the workflow cluster.

`tests/test_four_node_lab.py` names that refusal text in
`WORKFLOW_HISTORY_REFUSAL` and skips the six cases that need a completed run
**only** for that exact text; any other failure still fails. Nothing in this
lane asserts the blocked behaviour in either direction.

### Removed rather than weakened

`relay_a_onward_obligation_recoverable_after_kill` is **gone**, not softened.
It read `work_status("a1") not in ("", "absent", "unknown")`, and
`fn-workflow-work-status` answers `absent` both for work recovered from the
cut and for work enqueued ordinarily after a reopen, so the status the lab can
read does not distinguish the two. The two values are still recorded in the
cut record; nothing is asserted of them.

### What the merge fixed

- `tools/media.py` gained the command line it never had: `export`, `verify`,
  `import`, on `run_store`'s exit codes, with the three outcomes distinct out
  to them and **uncertain dominating refused** in a multi-item volume. Six new
  cases in `tests/test_media.py`.
- `run_store.Store._safe_directory` creates the store leaf and no parent it did
  not check; `tests/test_media.py` now owns the node directory. That was seven
  errors. `tests.test_media` is 19 of 19 green against real ACL2.
- The lab allocated transaction ids from an in-memory counter on `Node`, so a
  process-death cut reissued a txid the journal already held and the history
  preflight refused it. `Outbound.next_txid` allocates above the durable
  history.

### Still to do

Close the workflow refusal above, then re-run

```sh
python3 tests/bp-dtn7/run_four_node_lab.py
python3 -m unittest tests.test_media tests.test_four_node_lab tests.test_bp_receive -v
```

replace the evidence pair with the complete run, and add a row to
`planning/evidence-index.md`.

## What was added

| File | Lines | What it owns |
| --- | --- | --- |
| `tools/media.py` | 406 | Export/import of a carried-media directory |
| `tests/bp-dtn7/mock_bpa.py` | 237 | File-backed store-and-forward BPA stand-in |
| `tests/bp-dtn7/run_four_node_lab.py` | 644 | The four-node lab (22 named assertions) |
| `tests/test_media.py` | 276 | 13 cases |
| `tests/test_four_node_lab.py` | 141 | 9 cases, one optional class |

`specs/bp-path.md` gains a **carried-media path** section.

## Outcomes table (carried media)

Each row is a case in `tests/test_media.py`. The outcome is the receiver's, the
journal's or the copy check's; `tools/media.py` reports it and adds no
semantics.

| Case | Outcome | Reason reported | What must also hold |
| --- | --- | --- | --- |
| Whole volume, new content | `accepted` | `accepted` | one record, one article, one pin per item; media bytes unchanged; consumption recorded beside the journals, not on the media |
| Re-import of the same volume | `duplicate` | `duplicate` | receipt digest identical to the first import; no new receipt record; no new store record |
| Partial copy (item truncated) | `refused` | `media-incomplete` | the truncated item is absent from the inventory rather than short; the whole item still accepts; nothing charged for the truncated one |
| Corrupted file (same length) | `refused` | `media-digest` | refused by the copy digest *before* staging; exactly one inbound frame staged, for the good item only |
| Quota exhausted (store bound) | `refused` | `refused-capacity` | no frontier advance, charge or receipt; media unchanged |
| Uncertain staging cut (`inbound-linked`) | `uncertain` | `JournalUncertain` | reported uncertain, never refused; zero records/articles/pins; nothing consumed; the volume still carries the item |

There is no partial acceptance to observe: an item is accepted whole through
`receive_bpa_request` or it changes no acceptance, receipt or pin at all.

## Lab events

`home -> relay-a -> relay-b -> destination`, one contact window open at a time
(`MockNetwork.contact` refuses to open a second), the relay-a to relay-b hop
carried on media with no window at all.

| Event | How it is produced | Asserted |
| --- | --- | --- |
| Restart relay-a mid-forward | a child process group is SIGKILLed at the workflow journal's `postlink` cut while publishing the onward enqueue intent | archival receipts byte-identical across the kill and across recovery; the journal is either fenced with a durable intent (resolved through `recover_intent`) or the intent never landed and the obligation is re-established; never half-published |
| Lose a receipt and regenerate it | the first media import's receipt bytes are dropped and the same read-only volume is re-imported | `duplicate`, byte-identical receipt digest, no new receipt record |
| Expire an attempt, retry under the next window | a short-lifetime submission ages past its lifetime in the mock BPA while no contact is open | the work stays outstanding; the retry carries a distinct transport identity |
| Duplicate delivery | the contact re-forwards the same application bytes under a fresh transport identity | recognised as `duplicate` |
| Reordered pair | the contact delivers the queue in reverse | the destination still holds exactly one acceptance and one pin per article |
| Local numbers stay local | each node's `fn.letters` frontier is read from ACL2 after the run, plus the destination's frontier right after its first acceptance | each node's frontier is one plus *its own* acceptances; the destination accepted the pair in the reverse order, so the letter that is home's number 1 is the destination's number 2 |

## Relay kinds

The host emits no relay receipt *kind*. A relay in this lab is
receiver-then-sender through two separate host paths: `receive_bpa_request`
accepts and archives, then an onward sender work is enqueued for the same
committed article. So the lab asserts the **archival** behaviour and records
the **forwarding undertaking as a proposal**, in `evidence.json` under
`relay_kinds.forwarding.status = "proposal"`, with a test that fails if it is
ever relabelled. No accepted forwarding responsibility (the `SCN-001` part) is
demonstrated.

## Proposals

- **Wire `books/relay.lisp`'s kinds into the host.** The missing pieces named
  in `specs/relay.md` are a byte grammar for the proposed FNWF
  `(:relay-undertaking upstream-work-id onward-work-id)` record and a host path
  that records the undertaking before preparing a `:forwarding` receipt. Until
  then every relay receipt this host can emit is archival.
- **Per-node receiver configuration.** `tools/run_bp_receive.py` carries one
  module-level `DESTINATION`, `POLICY_ID` and `ISSUER`, so all four lab nodes
  present the same application endpoint identity while only their transport
  identities differ. A relay chain wants these per node.
- **A msgid-to-local-number accessor.** `host/store-node-host.lisp` exposes
  `fn-store-sn-group-next` (the frontier) but nothing that answers "what number
  did this node give this Message-ID". The lab therefore states local-number
  independence through frontiers plus acceptance order. An accessor would let
  it be stated directly, and belongs in ACL2, not in Python.
- **Parameterise `tests/bp-dtn7/fn_sender_lab.py`.** Its `Sender` hard-codes
  one config, work id, Message-ID and article, so the four-node lab carries its
  own `Outbound` session class. One parameterised sender session would serve
  both labs.
- **A media hop is a submission.** The lab records the durable attempt intent
  (`persist_attempt_then_call`) before writing a byte to the volume, with the
  carrier substituted for the BPA. That discipline should be the documented
  contract for any carrier, not a property of this lab.
