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

## Certification of the change

`python3 tools/farm.py submit persvati --jobs 6 --timeout-seconds 3600
--remote-root /home/ember/fn-lanes/w11-twonode-feed --affected-by
books/article-fields.lisp --closure`, run `run-20260920T235641Z-3179`, then
`wait`. Evidence
`build/acl2/certify-20260920T235649Z-727455/manifest.json`.

| fact | value |
| --- | --- |
| host | persvati, Linux 6.17.0-40-generic x86_64, Python 3.13.7, SBCL 2.6.8 |
| ACL2 | 8.7, `/home/ember/fn-tools/acl2-8.7/saved_acl2`, sha256 `c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163` |
| environment | `ACL2_BOOK_HASH_ALISTP=NIL`, `ACL2_CUSTOMIZATION=NONE` |
| roots | **123 requested, 122 certified, 1 failed**, 282.8 s wall at `--jobs 6` |
| the one failure | `books/owner-config` at `( DEFUN FN-OCFG-STATEP ...)`, `books--owner-config.certify.log:969`. **Pre-existing and not this lane's**: `w10/owner-relation` recorded it on the board ("`books/owner-config` has never been admitted") with both its defects, and it is open in `HANDOFF-w10-owner-relation.md` §3. Nothing in this lane touches that book or `fn-own-relation`. |
| published | 122 pairs to persvati's `/home/ember/fn-certcache` |

The roots this lane's change is about, each certified, with its wall time:

| root | s |
| --- | --- |
| `books/article-fields` | 0.88 |
| `tests/acl2/article-fields-tests` | 0.59 |
| `books/peer-inbound` | 82.47 |
| `books/peer-inbound-invariants` | 1.15 |
| `tests/acl2/peer-inbound-tests` | 1.13 |
| `books/owner-feed` | 2.31 |
| `tests/acl2/owner-feed-tests` | 0.98 |
| `books/owner` | 2.08 |
| `books/owner-invariants` | 10.25 |
| `tests/acl2/owner-tests` | 1.50 |
| `books/served` | 1.88 |
| `tests/acl2/served-tests` | 1.23 |
| `books/nntp-post` | 6.77 |
| `books/bp-ingress` | 1.06 |
| `books/injection-invariants` | 1.19 |

`books/nntp-post` and `books/bp-ingress` are the injecting agents and are in
the table on purpose: they keep `fn-af-proto-article-check` and keep
refusing a proto-article that carries `Injection-Info`. That they certify
unchanged is what says the split was additive.

**What this certification does and does not establish.** It establishes that
every root in the closure of `books/article-fields` admits, verifies its
guards and proves its theorems with the new function present, and that the
five assertions separating the two checks evaluate as stated. It does NOT
establish that the relaying check is the right reading of RFC 5537 §3.6
step 1 -- that is a reading of a document, argued in
`specs/peering.md`'s wave-11 status section, and no theorem in this tree
says it.

## Run 2 and run 3: the two-node gate on persvati

`python3 tools/twonode_gate.py HEAD --host persvati`, invoked from this lane's
worktree (`build/lanes/w11-twonode-feed`), which is where the evidence lands.
Both runs are committed whole: `twonode-bbd1f47-2026-09-21.md` (99 steps, 2
failed, 4 not exercised) and `twonode-ea76826-2026-09-21.md` (101 steps).

### What run 2 (`bbd1f47`) established, and what it hid

`transit | IHAVE -> '335 send it'`, where every gate before this lane
recorded `502 transit is not permitted on this connection`. The hand-driven
relay crossed with `identical=True`.

Its owner-feed rows all read "not exercised", and they were wrong: the
crossings had happened. `FEED_DRIVER`'s `post` read its reply with
`conn.read_line()`, which `Conn` does not have, and the AttributeError fires
AFTER the article is on the wire. The wire tap is what caught it, and is the
reason this gate has one. Recorded here because it is a shape to watch for:
**a harness can report a feature as absent when the only thing missing is
its own reply read.**

### What run 3 (`ea76826`) shows

| row | value |
| --- | --- |
| `owner feed` | **A->B True** |
| `owner feed streaming` | **True** |
| `owner feed wire` | `IHAVE <fed-ab@example.invalid>` |
| `owner feed streaming wire` | `MODE STREAM; CHECK <fed-streaming@example.invalid>; TAKETHIS <fed-streaming@example.invalid>` |
| `feed` (hand relay) | `offer=335 transfer=235 ... loop=437 transfer rejected; path loop reread=220 identical=True` |
| `owner feed cut` | `CUT-TAKEN ; served=220 ... accepted-transfers-observed=0` |
| `transit` | `IHAVE -> '335 send it'` |

Three readings.

**The feed carried it, and by which command is on record.** The tap in front
of node B recorded, from node A's own feed and nothing else,
`IHAVE <fed-ab@example.invalid>` / `335` / the article / `235`, and then
`MODE STREAM` / `203` / `CHECK <fed-streaming@...>` / `238` /
`TAKETHIS` / `239`. Same node pair, same deploy, two offer commands, because
streaming is the peer record's outbound flag and the records were rewritten
and both nodes restarted between them.

**Loop suppression fired for the first time on this tree.** `loop=437
transfer rejected; path loop`. Every earlier run recorded `235 article
transferred OK` for the same probe, and that was correct behaviour for a node
with no name: `fn-peer-local-identity` reads a policy slot nothing could
write, an unset slot reads as the empty string, and `fn-path-names-p` never
matches it.

**The lost-reply crash point was reached and resolved.** The tap cut the
transfer after the article block and before the status line (`CUT-TAKEN`);
node B served the article afterwards and node A observed ZERO accepted
transfers. Whether B committed before the cut is genuinely indeterminate and
neither is asserted.

### What run 3 did not show, with the blocker named

| step | why |
| --- | --- |
| B to A by node B's own feed | Node B reached its connection bound. `tools/run_owner.py` defaults to `--max-connections 8`; a two-node run holds a persistent feed connection each way, a tap backend session per dial, and the harness's own probes. `accept_nntp` closes the socket at accept when the bound is reached, which the driver reports as `RuntimeError: server closed the connection`. Four steps were lost to it: the B-to-A post, the second-offer probe, the K5 restart arrival and the cut scenario's first group count. The gate's nodes now run with `--max-connections 32`; **that the default of 8 is reachable in a two-node run is a finding and is not fixed here.** |
| K5 restart by re-offer (`kill -9` node A) | the same bound, at the arrival step |
| `identical` for the two feed-delivered articles | reported `False` with nothing to say which lines differ. RFC 5537 3.6 lets a relaying agent alter Path and Xref and nothing else, so which lines differ is the whole question; `wait` now reports both line counts and the lines present on one side only. The hand relay's `identical=True` in the same run says the octets survive an IHAVE that copies them verbatim. |
| the TCPCLv4 scenario | `build/fn-host` did not build on this commit; the layer was not exercised at all |
| `CAPABILITIES` naming the transit commands | the book renders the reader block on a peer session (`transit | ... CAPABILITIES lists IHAVE: False`), which is an open defect, not a gap in this run |

### One limitation worked around, named as the coordinator asked

A connection can never POST twice today: one clock observation is pinned at
accept and the decision is built from it, so a second POST on the same
connection is refused `441` whatever the article is. A separate lane owns
that seam. This harness was already immune -- `FEED_DRIVER`'s `post` opens a
fresh connection per article and closes it -- so nothing here works around
it, and nothing here exercises two posts on one connection either.

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
