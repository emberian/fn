# Two-Store join on 1a9dd747: signed peering into Mini consumption, with crash cuts

The first complete end-to-end exchange between two independently configured
native fn Stores and the Mini client, on the qualified image pair of
[`1a9dd747`](native-cut-1a9dd747-2026-09-24.md) (production launcher
`60e14e2a…`, developer `5d42db2d…`), run by
[`tools/runbooks/two_store_join.py`](../../tools/runbooks/two_store_join.py)
(the harness record is
[two-store-join-harness-2026-09-24.md](two-store-join-harness-2026-09-24.md);
its dry run on `863c2141` had stopped at B's receiver verdict). Mini binary
`0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286` from
`implement/fn-evidence` `183cd37`. Two fresh Stores A and B on hbox with fresh
TLS, generated passwords kept only in the scratch directory, and signed
reciprocal peering; the live node was not involved. Scratch and full logs:
`/tank/fn/scratch/two-store-20260924/qual-1a9dd747-<cut>/` on hbox; each
run's `summary.json` (every step with its outcome, seconds and log SHA-256) is
in [`two-store-join-1a9dd747/`](two-store-join-1a9dd747/).

The exchange: report R accepted durably at A → A peers R to B under signature
→ B's receiver verdict is durable and survives a B restart → Mini consumes R
at B and ACKs → Mini's signed reply Q is posted at B → Q verified at B and
peered to A, exactly once → A and B restart → Q is at A after restart with
stable bytes, A's verdict for Q holds → Mini reads Q at A and ACKs → both
Stores hold exactly two articles.

| run | cut | cut reached | steps | outcome | non-accepted steps | summary SHA-256 |
| --- | --- | --- | --- | --- | --- | --- |
| none | none | n/a | 77 | EXCHANGE COMPLETE | none | `81d4a6c6…` |
| a-accepted | A killed after its durable feed-sent record, before R reached B; restarted | yes | 81 | EXCHANGE COMPLETE | none | `5df43da6…` |
| b-verdict | B killed after its receiver verdict, before Mini's ACK; restarted; repoll cursor, event and position unchanged | yes | 83 | EXCHANGE COMPLETE | none | `ec7e2700…` |
| ack-response | the ACK response to Mini lost in transport | yes | 79 | EXCHANGE COMPLETE | `cut-ack-response-lost` reported **UNCERTAIN** (`fnAck transport-fault`), then `cut-ack-settle-position` settled it | `0d8f149a…` |
| reply-at-b | B (developer image) killed after Q's feed-sent record, before Q reached A; restarted | yes | 83 | EXCHANGE COMPLETE | none | `786bf2df…` |

Full hashes are in the directory listing beside this file. Step 23,
`b-verdict-gen1`, was ACCEPTED in every run (keyring 1, projected source equal
to R); it was the step the 863c2141 dry run refused, and the peer-authored
ingress fix is what changed. The `ack-response` cut is the one place a step is
not ACCEPTED, and that is the required answer: a lost ACK response is
uncertain, not refused and not accepted, and the position settles on the next
poll without a duplicate.

## What this does not establish

- R is the retained Mini E1 source signed with fresh harness keys, not a new
  Mini submission; Mini's A-side deployment reuses the E2 genesis and custody
  key, so it is not the separate identity Mini's handoff asks for.
- The `b-verdict` cut kills an idle B between commands; the harness cannot
  show its feed worker was mid-write, so it is a process-death cut at a
  command boundary, not a byte-level cut ("every process-death cut is a model
  crash point": the cut families here are the ones the harness can express).
- The `a-accepted` and `reply-at-b` cuts use the developer image's
  `FN_NATIVE_FEED_TEST_STOP_AFTER_SENT` selector, not a fault injected into
  the production image.
- One exchange per cut family, one host, one clock. No power-loss, no
  storage-platform variation, no contact-loss BP forwarding (that join is
  separate).
- Mini's branch is not merged to Mini main; its own two-Store handoff remains
  its record.
