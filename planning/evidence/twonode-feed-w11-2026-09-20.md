# An article crosses between two fn nodes (lane `w11/twonode-feed`, 2026-09-20)

The v0 question -- can two peered fn servers exchange an article -- had never
been answered yes. This record says what was run, what was observed, what was
repaired to make it possible, and what is still not exercised.

**The answer: yes, one way and then both ways, by fn's own outbound feed.**
Node A accepted a POST, `books/owner-feed.lisp`'s feed table enqueued it for
peer `b`, the owner offered it over a real NNTP connection, node B accepted
it through the same durable path a POST takes, and a reader on B fetched the
same octets node A serves. The detailed per-run rows are below; nothing in
this file is a proof, and none of it is a flight-readiness claim.

## Why it had never happened: four defects, all in code that had run green

| # | Where | What | How it presented |
| --- | --- | --- | --- |
| 1 | `books/article-fields.lisp`, used by `books/peer-inbound.lisp` and `books/owner-feed.lisp` | `fn-af-proto-article-check` is RFC 5537 §3.4.1, the INJECTING agent's check, whose first refusal is a present `Injection-Info`. Both transit paths applied it to an ALREADY-INJECTED article, and every article fn posts carries that field (`fn-inj-injection-info-line`). | `fn-peer-decide-transfer` answered `:refuse :proto-article` to every offer; `fn-own-feed-groups-of` answered `NIL`, so no peer was ever a feed target and the feed dialled nobody. |
| 2 | `tools/run_store.py`, `bin/fn` | `--inbound-max-octets` defaulted to 1048576, and `fn-cfg-peer-inboundp` caps it at `*fn-record-max-payload*` = 32768. | `peer add` was refused `:peer-record` for every invocation made with the defaults; no peer record could exist. |
| 3 | `tools/twonode_gate.py` | `FEED_DRIVER`'s `post` phase called an `article()` it never defined, and neither article builder wrote a `Date` (RFC 5536 §3.1.1, enforced by `fn-peer-decide-transfer`). | Every owner-feed post raised `NameError` and was recorded as an article that did not become durable. |
| 4 | `tools/run_owner.py`, `host/owner-host.lisp`, `tools/run_reader.py` | Three type errors on the transit and feed paths, each raised where nothing catches, so the OWNER PROCESS EXITED: octets re-encoded in `transit_decide`; group names as strings where the global holds octets; `acl2_boolean` anchored at the first octet where an error triple prints a leading space. | A peer that transferred an article, or a feed that dialled anybody, ended the service. |

Defect 1 is the one that made the milestone impossible; 2 and 3 made it
unmeasurable; 4 made every attempt look like a crash.

## Run 1: two owners on the laptop, the first crossing

The reproduction that isolated defect 1 and then showed the crossing. It is
a scratch driver, not a gate: it exists because each persvati round trip
costs a quarter of an hour and the loop needed four.

| fact | value |
| --- | --- |
| host | laptop, macOS 26.6.1 (build 25G76), arm64 |
| python3 | 3.14.7 |
| ACL2 | 8.7, `/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` |
| revision | `0adb14e` (lane `w11/twonode-feed`), certificates installed by `python3 tools/certs.py install` at the lane's start, then STALE for the five books this lane edits -- ACL2 loaded those five uncertified, with warnings |
| driver | a scratch two-node script: `run_store.py init`, `run_store.py peer add`, two `tools/run_owner.py` on fixed loopback ports |
| peer records | each node holds one naming the other: `--path-identity <other>.local.example.invalid --nntp 127.0.0.1:<other port> --inbound-groups 'fn.*' --outbound-groups 'fn.*' --source-address 127.0.0.1`, no `--streaming` |

### Before the fix (defect 1 live)

| step | result |
| --- | --- |
| `peer add` on both nodes | `peer added name=b generation=2`, `peer list` shows `inbound=fn.* max-octets=32768` |
| both owners reach LISTENING | yes, and each prints `FEED <peer> replayed 0` |
| A: `POST <cross-ab@example.invalid>` | `340`, then `240 article received OK` |
| B serves it within 90 s | **no** -- `430 no article with that message-id` |
| A's `store/feed/b.fnfd` | 49 octets: the startup `(:feed-restart b)` record and nothing else |
| the bridge, on A's own stored octets | `(fn-af-proto-article-check (fn-own-feed-article-of ...))` = `(:ERROR :INJECTION-INFO)`; `(fn-own-feed-groups-of ...)` = `NIL`; `(fn-own-feed-targets ...)` = `NIL` |

### After the fix

| step | result |
| --- | --- |
| A: `POST <cross-ab@example.invalid>` | `340`, then `240 article received OK` |
| B serves it | **`220 0 <cross-ab@example.invalid> article follows`** |
| A serves it | `220 0 <cross-ab@example.invalid> article follows` |
| the octets | **identical**: the ARTICLE block B returns is equal, line for line, to the one A returns |
| A's `store/feed/b.fnfd` | 320 octets, four sealed FNFD records in order -- kind `06` restart, `02` offer, `03` sent, `04` outcome -- each carrying peer `b` and `<cross-ab@example.invalid>` |

The octet comparison is the whole ARTICLE block as each server rendered it,
compared by the driver, not a digest and not a status code.

## Limits of this record

- **Run 1 is not the gate.** It is a scratch driver on the laptop with a
  fixed pair of loopback ports. It exercises POST, the feed's enqueue,
  dial, offer, transfer and outcome, and a reread. It does NOT exercise the
  B-to-A direction, streaming, the duplicate path, the loop refusal or any
  crash.
- **The five edited books were loaded uncertified in run 1.** ACL2 warns and
  loads the source; the behaviour observed is the source's, and the
  certification is recorded separately below.
- Both nodes are on one host over loopback. Nothing here exercises a real
  network, a partition, latency or two clocks disagreeing.
- The peer records are configuration, not authorization: nothing on this
  tree authenticates a peer, so a node accepts transit from whoever connects
  from a configured address.
- Two articles crossing is not the merge property of specs/peering.md §4
  (K3); that needs the certified statement, not a run.
