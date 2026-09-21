# Handoff: w11/transit-correct (the decision the wire carries)

Branch `w11/transit-correct`, worktree `build/lanes/w11-transit-correct`,
from `dev` `0eedafc`, merged with `dev` `fd2eb2d` and then `9e4b7ee`.
Head `9a4f6f4`. The certification of record is of `3f68944`; the two
commits since it change only `planning/`, no book, host file or tool.

## Three defects, three different places, and none of them was the model

The lane was sent for three disagreements between a certified decision and
the reply on the wire. They have three separate causes, and the model is
right in all three.

### 1. The offer decision read the node the connection opened with

`fn-peer-decide-offer` answers from the node its session carries, and only
`fn-peer-open-session` ever wrote that field. So every offer on a connection
was decided against the node as it stood at `:open`, for the whole life of
the connection. A peer that transferred an article and then offered the same
Message-ID again on the same connection drew `335`/`238` and then paid for
the whole article a second time. K3's duplicate suppression, which is proved
of `fn-peer-decide-offer`, was being handed a node that did not hold the
article yet.

Measured as two values from one `ld` against the certified closure, on a
connection opened before the post and read after it:

| | value |
| --- | --- |
| `fn-peer-decide-offer` over the node the session pinned at `:open` | `(:WANT NIL)` -- 335 |
| `fn-own-read` over the same connection, same octets | `"435 duplicate"` |

**The fix is `fn-own-conn-live-session` (`books/owner.lisp`), which
`fn-own-read` calls.** It re-pins the node from the owner's own store once
per socket read. That is the finest granularity that can differ -- nothing
becomes durable inside one read, because the submission a read produces is
drained after it -- and it is one field assignment with no recognizer over
the store, so it is not the whole-state revalidation D3 forbids. A reader
connection is returned unchanged; the PEER RECORD stays pinned, because the
owner holds no store configuration to re-read.

The coordinator's observation that the owner feed's own re-offer already
drew 435/438 is the same fact from the other side: the feed dials a NEW
connection each time, so its pinned node is current.

### 2. The v0 matrix never gave either node a name of its own

`fn-peer-local-identity` reads the `path-identity` POLICY slot; an unset
slot is the empty string and `fn-path-names-p` never matches it, so
`fn-peer-decide-transfer`'s loop arm cannot fire. `tools/v0_matrix.py` wrote
both peer records -- each naming the OTHER node's path-identity -- and never
set either node's own slot.

Measured by the difference between two harnesses on the same commit and the
same code, differing in one command:

| harness at `6fb30ca` / `ea76826` | `loop_result` | `loop_absent` |
| --- | --- | --- |
| `v0_matrix.py`, no `policy set path-identity` | `235 article transferred OK` | `220 ... article follows` |
| `twonode_gate.py`, steps 13 and 17 set it | `437 transfer rejected; path loop` | `430 no article with that message-id` |

Configuration, not a model defect. `peer_records` sets the slot on both
nodes before the listeners start and emits `V0-TRANSIT-IDENTITY`, which is
the row the two loop rows rest on.

### 3. The octets a receiver serves differed by one trailing CRLF

This one arrived mid-lane from `w11/gate-verdicts` and is the larger finding
of the three. `tools/feed_wire.py` `send_block` ended the block with
`stuffed.rstrip(b"\r\n") + b"\r\n.\r\n"`. `rstrip` removes EVERY trailing
CRLF, not the one terminator the article's last line carries, so an article
whose last line is BLANK reaches the peer one line shorter -- and two blank
lines, two lines shorter. Every other octet, a dot-stuffed body line
included, is exact.

The measurement, on the four shapes that separate it:

| article | current | fixed |
| --- | --- | --- |
| `...Body.\r\n` | round-trips | round-trips |
| `...Body.\r\n\r\n` | **5 lines in, 4 out** | round-trips |
| `...Body.\r\n\r\n\r\n` | **6 lines in, 4 out** | round-trips |
| body line `.` | round-trips (stuffed `..`) | round-trips |

That is exactly the gate's signature at `f49a844`: `source_lines: 11,
target_lines: 10, only_on_target: [], only_on_source: []` -- one line fewer
and **not one line different in content** -- on `<fed-ab@...>`,
`<fed-ba@...>` and `<fed-streaming@...>`, the three the OWNER feed carries,
while the hand-driven relay's `<alpha@a...>` was `identical=True` in the
same run. The relay frames with `tools/twonode_gate.py`'s own `send_block`,
which never had it. The two article shapes differ because an article POSTed
through the server stores the blank last line its dot block carried.

**So the gate's assertion is not too strict: nothing but the trailing CRLF
differs and Path and Xref are not involved at all.**

It is a regression with a named commit. `w11/twonode-feed` removed the same
`rstrip` from `tools/run_feed.py` and measured the same three numbers then;
`c3aacd2` moved `Session.send_block` into `tools/feed_wire.py` **from the
copy that still had it**, and said in its own message that the method "had
no test of any kind while it lived in the retired driver".

## The subject rule, closed in two halves

K2 (`fn-peer-loop-is-refused`) and K3 (`fn-peer-history-is-have-at-offer`,
`fn-peer-history-is-refused-at-transfer`) were already about the functions
the host calls. What was missing was the bridge from those functions to the
octets, and the statement of which node the served path supplies.

| the host line | what it calls | the theorem |
| --- | --- | --- |
| `host/owner-host.lisp` `fn-owner-chunk` -> `books/owner.lisp` `fn-own-read` | `fn-served-step` -> `fn-served-dispatch` -> `fn-auth-step` -> `fn-peer-step` -> `fn-peer-command`, whose IHAVE and CHECK arms are the only callers of `fn-peer-decide-offer` on this tree | `fn-peer-ihave-of-a-held-message-id-is-435-and-no-article`, `fn-peer-check-of-a-held-message-id-is-438-and-no-offer-outstanding` (`books/peer-inbound-invariants.lisp`): the reply octets ARE the decision and the connection does not enter article mode |
| the same line | `fn-own-conn-live-session` | `fn-own-read-offers-against-the-live-node` (`books/owner-invariants.lisp`): the node handed to `fn-peer-decide-offer` is `fn-sn-node` of the owner's own store |
| `host/owner-host.lisp:413` `fn-owner-transit-decide` | `fn-peer-decide-transfer` over `(fn-sn-node (fn-own-store owner))` and the live `fn-store-cfg` | K2 and `fn-peer-history-is-refused-at-transfer` are already about that function; `fn-own-transit-outcome` passes `completion` `nil` unless the decision is `:want`, so the store's word cannot turn a refusal into a `2xx` |

`fn-own-live-session-boundedp` says the re-pin cannot drop a connection: it
leaves the reader session identical, so `fn-own-conn-boundedp` -- the test
that made ADVANCE a silent no-op for a wave when a rebuild lost a wrapper --
answers exactly as before. The two K1 served-port statements
(`fn-own-read-is-served-step-on-pinned-prefix` and its `-after-any-trace`)
now name the re-pinned session, which is what `fn-own-read` passes.

**PRF-042** is the target these belong to (claimed as PRF-040; `w11/k1-scan` and `w11/owner-survival` had both taken that number by their own merges, exactly as the brief predicted). PRF-029 is the outbound half and
PRF-024 is the substrate policy gate (`fn-pol-admitp`, SUB-003), a different
subject; the inbound half had no target and no curated events at all.

## Teeth

`tests/acl2/peer-inbound-tests.lisp`: one session before and after, with a
violating value for each hypothesis -- a Message-ID the live node does not
hold (`335`/`238`), a reader connection (`502 transit is not permitted on
this connection`), a name in no peer table (`435 not wanted; not a peer`), a
feed-only peer record (`435 not wanted; no inbound feed configured`), and a
token that is not a Message-ID (`501 syntax error`).

`tests/acl2/owner-tests.lisp`: a peer connection opened BEFORE the post, the
post run through the real kernel events, and then `fn-own-read` of `IHAVE
<one@example>` answering `435 duplicate` where `fn-served-step` over the
session as it was pinned answers `335`. Both nodes are real and the stale
one is the value a real open produced.

`tests/test_feed.py`: one blank line, two blank lines, and a round trip that
unstuffs the block back to the article it was given over four shapes.
14 tests, OK, 5.0 s.

## Certification

Farm, persvati, `--affected-by books/peer-inbound.lisp --affected-by
books/owner.lisp --closure --jobs 8`, remote root
`/home/ember/fn-lanes/w11-transit-correct`.

| run | verdict |
| --- | --- |
| `run-20260921T033252Z-6ba2` | 86 of 87 passed; the one failure was `tests/acl2/owner-tests` and it was the TEST's own accessor -- `fn-served-step` returns a result record and the assertion read `(car ...)` of it, which is the connection |
| `run-20260921T034738Z-5276` | passed, 0 failures, 87 books, 215.5 s, on `873e109`, `source_digests_sha256` unchanged |
| `run-20260921T043029Z-6012` | **passed, 0 failures, 88 books, 198.3 s**, on the MERGED head `3f68944`, `source_digests_sha256` unchanged. **This is the certification of record**, and it is of the head: the second `dev` merge brought `books/owner-fault.lisp` (which sits above `books/owner`) and 72 lines of `host/owner-host.lisp` from other lanes, and that book is in the set and passed. It covers `books/peer-inbound` (58.0 s), `books/peer-inbound-invariants`, `books/owner`, `books/owner-invariants` (8.2 s), `books/served`, `books/owner-feed`, `books/peer-feed-invariants`, `tests/acl2/peer-inbound-tests`, `tests/acl2/owner-tests`, `tests/acl2/served-tests`, `tests/acl2/owner-config-tests`, `tests/acl2/nntp-auth-tests` |

## The two-node gate, before and after

`tools/twonode_gate.py HEAD --host persvati --jobs 8`, run from this
worktree. `planning/evidence/twonode-873e109-2026-09-21.md`, 371.0 s, 132
steps, and again on the MERGED head as
`planning/evidence/twonode-3f68944-2026-09-21.md` with the same five verdicts
and the same two violations, so the numbers below are of the head.

| | `f49a844` (w11/gate-verdicts) | `873e109` (this lane) |
| --- | --- | --- |
| held | 40 | **48** |
| violated | **7** | **2** |
| inconclusive | 4 | 4 |
| not-exercised | 10 | 7 |
| limitation | 4 | 4 |

The five that moved are exactly the five this lane owned:

| assertion | before | after |
| --- | --- | --- |
| `duplicate-435` | `335 send it; end with <CR-LF>.<CR-LF>` | `435 duplicate` |
| `check-438` | `238 <alpha@a.example.invalid>` | `438 <alpha@a.example.invalid>` |
| `feed-identical[ab]` | `identical=False` (11 -> 10 lines) | `identical=True` |
| `feed-identical[ba]` | `identical=False` | `identical=True` |
| `feed-identical[stream-ab]` | `identical=False` | `identical=True` |

`loop-refused` and `loop-absent` held in the gate before and still hold: the
gate always set `path-identity`. It was the matrix that did not.

The two violations left are **not this lane's**: `k5-arrival` (w11/feed-k5 --
node B never served `<fed-restart@...>` within 90 s, `server closed the
connection`, the same ninety-second refusal) and `tcpcl-image` (the BP
cluster -- `build/fn-host` did not build, `build_native_host` reports an
uncertified-book marker for `books/frame-journal` and `books/frame`).

**One limit on that run, stated because it is real:** `certificates-match`
is `inconclusive`, `matched=220 mismatched=52`. The gate installs
certificates from the best NEIGHBOUR GATE TREE
(`/home/ember/fn-gates/dev-e4fb8bc`), not from the box's own
`/home/ember/fn-certcache`, which is where `farm.py` had just published this
revision's pairs. So the wire observations above are exact and the sentence
"this certified commit serves" does not follow from the gate; it follows
from the farm run, separately, over the same sources. One line in
`tools/deploy_gate.py` `certificates()` would join them; it is on the board.

## The v0 matrix

`python3 tools/v0_matrix.py HEAD --host persvati --jobs 8`, written by the
tool into `planning/v0-matrix.json` and
`planning/evidence/v0-matrix-2026-09-21.md`; `make check` validates the rows
against their sha256.

Run twice: on the lane head before the second `dev` merge (`873e109`,
1370.5 s) and on the merged head (`3f68944`, 1354.3 s, which is the record in
`planning/v0-matrix.json`).

| | `6fb30ca` (before) | `873e109` | `3f68944` (head) |
| --- | --- | --- | --- |
| rows | 190 | 192 | 192 (`V0-TRANSIT-IDENTITY-A/B` are new) |
| accepted | 145 | 142 | 141 |
| refused | 29 | 34 | 34 |
| uncertain | 2 | 2 | 3 |
| not exercised | 13 | 13 | 13 |
| not built | 1 | 1 | 1 |
| **disagreed** | **17** | **6** | **7** |

The seventh on the head is `V0-CRASH-CHECKPOINT`, `uncertain`, `anchor rc=3
(anchor uncertain: unmodelled-tree)`. It is **not this lane's**: it arrived
with the second `dev` merge and it did not appear at `873e109`, which is the
same tree without those 31 commits. Whoever owns the anchor should read it.

Eleven rows moved and every one is this lane's:

| row | before | after |
| --- | --- | --- |
| `V0-TRANSIT-DUPLICATE-AB/BA` | `335 send it` | `435 duplicate` |
| `V0-TRANSIT-CHECK-DUP-AB/BA` | `238 <msgid>` | `438 <msgid>` |
| `V0-TRANSIT-LOOP-AB/BA` | `235 article transferred OK` | `437 transfer rejected; path loop` |
| `V0-TRANSIT-LOOP-ABSENT-AB/BA` | `220 ... article follows` | `430 no article with that message-id` |
| `V0-TRANSIT-INDEPENDENT-A/B` | `refused` (the feed had crossed) | `accepted` (the control measures the seeds) |
| `V0-CRASH-RESTART` | `rc=1` -- node B still served `<loop-ab@...>`, which it should never have taken | `rc=0` |

**F-TRANSIT is now 26 rows, 16 accepted and 10 refused, and NOT ONE
disagrees, in both runs.** The owner feed's own facts in the same run:
`owner feed ab duplicate: ihave=435 duplicate check=438 takethis=439`, and
`octets identical to the source=True` in both directions.

The six that remain, none of them the transit path's:

| row | what it is |
| --- | --- |
| `V0-AUTH-GATED-A/B` | the policy question, answered on the board: a peer record's `auth-source-address` is not an RFC 4643 authentication, and what unblocks the row is taking the three transit keywords out of `fn-auth-restricted-keywordp`. The auth cluster's packet |
| `V0-PIN-ADVERTISED-A/B` | the node dispatches `IHAVE`, `STREAMING` and `CHECK` on a peer connection and `CAPABILITIES` renders the reader block. Disagreeing since before this lane; the open item `w11/twonode-feed` recorded (`books/served`'s capability list has to read the session, RFC 3977 §5.2.2) |
| `V0-FEED-JOURNAL` | `(no feed journal found)`. Not touched here |
| `V0-BP-IMAGE` | the native image did not build; `books/nntp-auth` and others read uncertified in the deploy tree. The BP cluster's |

## Open, named, not weakened

- **The peer record is still pinned at `:open` while the node is not.** A
  `(:set-peer ...)` delta reaches an open peer connection's TRANSFER
  decision, because the host passes the live configuration
  (`fn-owner-transit-decide`), and not its OFFER decision, because the owner
  holds no store configuration to re-read. specs/peering.md §1.2.1 says a
  peer delta changes future transit decisions; that is true of one of the
  two. Closing it means the owner carrying the store configuration, which is
  `books/owner-config`'s pin table and not this lane's.
- **`fn-own-read-step` does not re-pin.** It is the per-event law and the
  host drives it only with `(:tls-established)`, which consults no node.
  Left alone deliberately; if it ever carries a command it must re-pin too.
- **The block rendering belongs in ACL2 and is in three Python copies.** See
  the ASK on the board: `tools/feed_wire.py`, `tools/twonode_gate.py` and
  `tools/inn_lab.py` each render an RFC 3977 §3.1.1 block and they do not
  agree, which is how the same octet defect shipped twice in two days.
  `fn-wire-stuff-line` and `fn-wire-unstuff-stuff-line` exist; the
  whole-block renderer and the theorem that `fn-wire-drive` of it recovers
  the article do not.
- **The auth ASK is answered on the board and the packet is the auth
  cluster's.** A peer record's `auth-source-address` is not an RFC 4643
  authentication and should not be written into `books/assumptions.lisp` as
  one. The question that unblocks `V0-AUTH-GATED` is whether
  `IHAVE`/`CHECK`/`TAKETHIS` are load-bearing in
  `fn-auth-restricted-keywordp`, and this lane answers the cheap half by an
  assertion that certifies: a session with no peer is already refused
  `502 transit is not permitted on this connection` BELOW the auth layer.
  So taking them out of the restricted set costs a reader nothing.
- **`V0-TRANSIT-INDEPENDENT` measures the seeds now.** Its absent set is the
  other node's articles as of before either listener started, not everything
  it has accepted: both nodes carry an outbound feed record and the feed is
  running by the time the control does. At `6fb30ca` the only two
  Message-IDs present in the absent map were `<auth-*>` and `<socket-*>`,
  the two the AUTHINFO and POST phases had just posted through the server,
  and the feed delivering them is the feature working.
