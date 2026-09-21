# Handoff: `w11/harness-health`

Lane worktree `build/lanes/w11-harness-health` on `w11/harness-health` from
`dev` at `ad9a794`. Four items of unowned harness debt. No ACL2 process was
started by this lane and no book was touched; one host comment and four
specification rows changed, and no certificate is invalidated by anything
here.

| item | outcome |
| --- | --- |
| 1. `tests/test_inn_lab.py` errors in `setUpClass` | fixed; 18/18, the thirteen `LabTests` had never run |
| 2. retire `tools/run_feed.py` | deleted; `tools/feed_wire.py` is the transport half, one line of `run_owner.py` |
| 3. the second-driver sweep | 7 real twins, 2 fixed here, 5 with owners below; 6 needing an ACL2 function that does not exist |
| 4. gate hygiene | `tools/gate_reap.py`; 12 gates and 475 M off persvati; hbox listed, one stale row, not reaped |

## 1. The lab's `setUpClass` error, named three times and owned zero

Two defects on opposite sides of the seam, and each hid the other.

`tools/inn_lab.py` read a started server's pid as
`output.split("pid=")[-1].strip().splitlines()[0]`. An empty pid file makes
that list empty and the expression an `IndexError` out of `inn_start`, which
reaches the caller as a harness crash. A lab that raises inside setup reports
*nothing whatever* about the box; a lab that records a gap reports exactly
what is missing. New `inn_lab.reported_pid(output)` is total — no `pid=`, an
empty one, and a non-numeric tail (`cat: no such file`) all answer `""` — and
each of the three call sites appends a gap naming the pid file it wanted. A
pid the lab does not know means the lab kills nothing, which is the safe
direction.

`tests/inn_lab_fake` wrote `run/nnrpd.pid` on every port. Real `nnrpd -D`
writes `run/nnrpd-<port>.pid` on any port but 119, which is what the lab reads
and what the box did: step 38 of
`planning/evidence/inn-lab-f4e8272-2026-09-20.md` is `NNRPD-UP pid=629447`
out of `cat $P/run/nnrpd-11120.pid`. **The fake was the side that diverged**,
so the lab's behaviour against real INN is unchanged by this lane.

One more of the same class, found while looking: `inn_stop` spelled an unknown
innd pid `0`, and `kill -0 0` asks about the whole process group and succeeds,
so `INND-GONE` could not have been reported honestly. It reads the pid file
now, else `-1`.

`PidParseTests` pins both halves. Evidence: `python3 -m unittest
tests.test_inn_lab -v` — 18 tests, OK, 40.9 s, `steps=80 failed=0
not-exercised=3`. Before: 5 ran, `setUpClass (LabTests)` ERROR.

## 2. `tools/run_feed.py` is deleted

The driver's reason to exist went with `w10/owner-feed`: the live feed is the
owner's, and the Python three-digit reply split was already deleted for
`fn-own-feed-response-code`. What was left was a second copy of owner
decisions that drifted invisibly three times.

Every caller, from `grep -rn run_feed`:

- `tools/run_owner.py:36` imported `Journal`, `Session`, `TRAILER_BYTES`.
  Those are transport and file layout, not feed decisions, so they moved
  verbatim into **`tools/feed_wire.py`** and the import was repointed. That is
  the only line of `run_owner.py` this lane touched; `w11/twonode-feed` is
  driving the owner's feed, and the board CHANGE naming these files went up
  before the edit.
- `tests/test_feed.py` drove the CLI. Its feed cases have not passed since
  they stopped skipping (BOARD 739) and the cause is a bug in their own
  fixture (BOARD 781). They are **not ported**, because the same scenarios
  exist stronger against a real fn node: a crash between `sent` and the
  outcome resolved by a CHECK with exactly one copy at the far end is
  `tools/twonode_gate.py::scenario_feed_restart` (K5), and offer-once-each is
  `scenario_owner_feed`.
- `specs/peering.md`: four rows re-pointed, including the
  `fn-feed-parse-response` open item, which prose still called open after
  `w10/owner-feed` closed it.
- `host/owner-host.lisp:644`: a comment claiming the host seals a frame
  "exactly as tools/run_feed.py does". Comment only.
- `books/owner-feed.lisp`'s two mentions are past tense and still true, so no
  book was touched.

`tests/test_feed.py` is now a unit test of the two host mechanisms the owner
imports and the two-node gate does not isolate: the FNFD journal layout (round
trip, the record bound, a torn tail ending the stream, a length claiming more
than the bound) and RFC 3977 §3.1.1 dot stuffing. **`Session.send_block` had
no test of any kind** while it lived in the retired driver.

One defect found by writing them: `Session.__init__` read the greeting outside
a `try`, so a peer whose first line exceeds `MAX_LINE` raised out of the
constructor and **leaked the socket** — no caller ever held the object whose
`close` would have run. Fixed in `tools/feed_wire.py`; the test is clean under
`-W error::ResourceWarning`, which is how it was seen.

Evidence: `tests.test_feed` 11 OK; `tests.test_twonode_gate` 19 OK;
`tests.test_deploy_gate` 17 OK; `compileall tools tests` clean.

## 3. A second driver is the pattern: every Python-side decision twin

Swept `tools/*.py`, `tests/*.py`, the two fakes and `bin/fn` against the
categories AGENTS.md names. Two findings before the table. **The store path is
already right and is the pattern to copy**: `tools/frame_bridge.py:124-146`
cross-checks nine host constants against `(fn-store-frame-constants)` at
session open, so a divergence fails at start-up rather than in a record. And
**there is no wildmat twin at all** — no Python in this tree matches a group
name against a pattern, and `fnmatch` is not imported anywhere.

### Fixed in this lane

| file:line | what Python computed | disposition |
| --- | --- | --- |
| `tests/deploy_gate_fake/tools/run_store.py:88` | `charge={len(payload)}` — a second charge formula that **disagrees** with `fn-charge-for-payload` (`books/identity.lisp:271`), which charges in 4096-octet pages | **deleted.** Nothing parsed it (`grep -rn charge` over `deploy_gate.py`, `twonode_gate.py`, `inn_lab.py`, `scale_gate.py`, `test_deploy_gate.py` is empty), so nothing broke — and the day something read it, it would have validated the wrong number |
| `tools/live_service.py:210` | `(("fn.*") 1048576 4)` as the inbound half of a peer record "the two boxes are meant to hold" | **corrected to 32768**, which is `*fn-record-max-payload*` (`books/records.lisp:43`), the ceiling `fn-cfg-peer-inboundp` (`books/peer-config.lisp:150`) holds an inbound record to. The stub as written is refused `:peer-record`, so that configuration could never have been held |

### Real twins with an owner, not taken here

| file:line | Python's value | ACL2 owner | owner of the fix |
| --- | --- | --- | --- |
| `tools/run_store.py:51,1829` | `max_payload_bytes` 32768 | `*fn-record-max-payload*` `books/records.lisp:43`, `*fn-article-max-octets*` `books/article.lisp:15` | store. `run_store.py:1503` checks only `<= max_store`, never equality with the article bound |
| `tools/run_store.py:81` | `CONFIG_RECORD_BYTES` 65538 | `*fn-cfg-max-octets*` `books/config.lisp:54` | store |
| `tools/run_store.py:36,70` | `65538` inside `MAX_RECOVERY_RECORD_BYTES` | `*fn-record-max-octets*` `books/records.lisp:47` (the multiplier is legitimately the host's) | store |
| `tools/run_store.py:90` | `ANCHOR_RECORD_BYTES = 1024 + 42` | `*fn-anchor-max-payload*` `books/anchor-record.lisp:45` + `*fn-frame-overhead-octets*` `books/frame-octets.lisp:24` | store / time-anchor |
| `tools/scheduler.py:41,42` | `MAX_TEXT = 512`, `MAX_DECISION_RECORD = 4096 + 42` | `*fn-frame-max-text*` `books/frame-octets.lisp:31`, `*fn-sched-max-payload*` `books/scheduler.lisp:420` | scheduler. The identical `MAX_TEXT` in `workflow_journal`/`receipt_journal` **is** checked; this one never consults the vector |
| `tools/feed_wire.py:36` (was `run_feed.py`) | `TRAILER_BYTES = 32`, re-exported into `tools/run_owner.py:337,348` | `*fn-frame-trailer-octets*` `books/frame-octets.lisp:21` | owner/feed. Named in a comment in `feed_wire.py` by this lane; the fix belongs where the session is, and `run_owner.py` is live |
| `tools/run_bp_receive.py:22,23,162,235`, `tools/run_bp_ingress.py:26`, `tools/media.py:54` | `512`, `256`, a bare `65538`, the payload refusal, `512`, `65538` | `*fn-frame-max-text*`, `*fn-bpa-max-metadata*` and `*fn-bpa-max-octets*` `books/bp-adu.lisp:23,24`, `*fn-article-max-octets*` | bp. `run_bp_receive.py:162` is the worst spelling: a bare literal with no name and no comment. `run_bp_receive.py:235` **refuses an article before ACL2 sees it** |
| `tools/auth_secret.py:37,38,39` | `16`, `32`, `64` | `*fn-authsec-salt-octets*` `books/auth-secret.lisp:55`, `*fn-digest-octets*` `books/crypto-seam.lisp:40`, `*fn-auth-max-name-octets*` `books/nntp-auth.lisp:94` | substrate. The docstring names the defconst and the number is still typed beside it |
| `tools/crypto_host.py:17,18` | `32`, `64` | `*fn-anchor-key-octets*`, `*fn-anchor-sig-octets*` `books/anchor.lisp:63,65` | time-anchor |
| `tools/roughtime.py:48-51` | `NONCE_OCTETS`, `ROOT_OCTETS`, `SIGNATURE_OCTETS`, `PUBLIC_KEY_OCTETS` | `books/anchor.lisp:63-66` — and these **gate refusals** at `roughtime.py:228,244,262,266` | time-anchor |
| `tools/roughtime.py:45,46` | the two Roughtime context strings | `*fn-anchor-response-context*` `books/anchor.lisp:74`, `*fn-anchor-delegation-context*` `books/anchor.lisp:81` | time-anchor. A **checked** twin: `tests/test_anchor.py:147,149` pins each against the octets ACL2 built, so a divergence is a test failure. Still two owners |
| `tools/roughtime.py:66-79` | the Roughtime tag-count/offset header, encode half | the same layout arithmetic in `fn-anchor-srep-from-root` `books/anchor.lisp:264` and `fn-anchor-dele-octets` `books/anchor.lisp:329` | time-anchor. The decode half (`82-116`) is legitimately the host's |

### Twins that need an ACL2 function that does not exist

1. **The Roughtime Merkle fold** — `tools/roughtime.py:124,128,132,264`.
   `books/anchor.lisp:171-179` constrains `fn-anchor-leaf-digest` for the
   one-nonce case only; there is no node digest, no path fold and no
   `fn-anchor-in-treep`, so **Python alone decides whether a response covers
   this client's nonce.** Needs a constrained `fn-anchor-node-digest`, an
   executable fold, and `fn-anchor-verifiedp` (`books/anchor.lisp:426`)
   extended to require it. Owner: time-anchor.
2. **Signature preimages inside `parse_response`** — `tools/roughtime.py:237,247`.
   ACL2 *does* own these octets (`fn-anchor-delegation-signed-octets`
   `books/anchor.lisp:343`, `fn-anchor-signed-octets` `books/anchor.lisp:316`),
   but they are reachable only through a live store bridge at
   `tools/run_store.py:1911,1914`, which runs **after** `parse_response` has
   already accepted or refused. Needs an anchor-only entry point, or
   `parse_response` restructured to return unchecked fields with
   `anchor_verdict` the sole gate. Owner: time-anchor.
3. **The delegation validity window** — `tools/roughtime.py:258`
   (`mint <= midpoint <= maxt`) is a literal copy of `books/anchor.lisp:435-436`
   inside `fn-anchor-verifiedp`. The function exists; only the ordering of (2)
   blocks it, and deleting the Python copy before (2) lands removes the only
   check on that path.
4. **9P2000 framing** — `tools/fn9p.py:134-404` owns the whole message layout
   and no book encodes it. By the letter of the rule that is an open registry
   item; in practice it is an adapter for a foreign protocol, so the honest
   move is a registry entry accepting it as an unowned wire format.
5. **`tools/checkpoint.py:46`** `SELECTION_BOUND = 4096`, described as "a
   header, one CBOR uint and a trailer". `books/checkpoint-codec.lisp` has
   `*fn-cpc-tag-octets*` and no selection-frame maximum: the number is
   invented host-side. Owner: checkpoint.
6. **The media manifest** — `tools/media.py:54,122,194,266,353` owns a schema,
   a naming rule and an integrity comparison with no book anywhere. Either
   `books/media.lisp` or a registry entry saying media staging is outside the
   model. Owner: media-lab.

### The two crypto twins the digest lane left open: still two, now three sites

`planning/lanes/HANDOFF-w9-digest.md` findings 2 and 5 are both still open,
and finding 2 has **one site more than it records**:

- the frame integrity trailer, `host/native/io.lisp:757,762` and
  `tools/frame_bridge.py:153,160` as recorded — **plus
  `tools/run_owner.py:337,348`**, the FNFD feed trailer, which arrived with
  `w10/owner-feed` after that handoff was written. All three are the same
  shape, and one `fn-store-frame-trailer` wrapper over the attached
  `fn-frame-digest` closes all three.
- `fn-anchor-leaf-digest` is still constrained (`books/anchor.lisp:171-179`,
  `defattach` only in `tests/acl2/anchor-teeth-tests.lisp:47`), which is why
  the Merkle fold above has no owner at all.

Everything else that hashes in `tools/` is A-CRYPTO-legitimate: the host is
handed an opaque prefix ACL2 built with a zero trailer and appends a digest,
building no preimage. `tools/frame_bridge.py:313` (`subject_id`) is the
exemplary case, and `tools/auth_secret.py` hashes nothing at all.

## 4. Gate hygiene, and how to read a box's memory

`tools/gate_reap.py --host <box>` lists every gate with revision, age,
on-disk size, `.cert` count, whether the revision is still an ancestor of dev
— asked of the **repository**, because a gate is a `git archive` export with
no `.git` — and whether any process has it or anything under it as its cwd.
`--remove` deletes only the rows the listing called `stale`, one `rm -rf` per
row, by a name that came back from that listing and is re-checked for a
separator, `..`, emptiness and a leading dash, with the path rebuilt from the
root so nothing the box said can widen the target.

Never removed, in this order of authority: a gate with a process in it;
anything at all while the box's `flock` is held; the newest `--keep-recent`
(2) gates of each tree, which is what a deploy scavenges pairs from; anything
under `--min-age-hours` (24); and a revision git does not know, because that
export may be the only copy of that tree. A box with no `/proc` keeps
everything — "I could not check" must not read the same as "nothing is
running".

**What the one run of the flag removed** (`--host persvati --remove`): twelve
gates, 475 M — `dev-60c5322`, `8ce64eb`, `e72660a`, `03f15fa`, `b4dadf2`,
`0a16592`, `056b29b`, `ca66782`, `df80e0b`, `8cec594`, `498b766`, `d83dea5`.
All ancestors of dev, all 24.7–41.5 h old, none with a process in it.
persvati went 25 gates / 1.1 G to 13 / 599 M. They held 1075 `.cert` files
between them; the box's content-keyed cache holds 7197 entries in 215 M
(`~/fn-certcache`), so the worst case of a wrong call is a re-certification.
**hbox was listed and not reaped**: 9 gates, 135 M, exactly one stale row
(`dev-9321344`, 16 M).

**Do not judge a box by `free`.** hbox is a ZFS box: the ARC is counted in
`used` and in unreclaimable slab and never in `buff/cache`. Measured
2026-09-21 by this tool: `AnonPages` 2.4 G, RSS summed over every process
3.5 G, ARC 44.7 G on a 123 G box. persvati, not a ZFS box: `AnonPages` 12.8 G,
RSS sum 17.6 G of 84 G. The tool prints those three separately and says why.
One correction to the coordinator's hypothesis, measured: the ARC's metadata
is **not** fn's stale trees — all of `/tank/fn` is 2.1 G, of which gates are
135 M and lanes 404 M.

## Open, and not this lane's

- `tests/twonode_gate_fake/tools/run_peer.py:72-77` implements the RFC 5537
  §3.5 Path loop rule and the duplicate rule to choose a 437. Its subject is a
  *peer* and not fn, so it is not a twin — but it is a relay decision
  `books/relay.lisp` also models, in a file that is cited in gate evidence.
- `tests/deploy_gate_fake/tools/run_reader.py:59,86,96-101` computes what a
  group contains and its high-water numbers, and `:86-152` maps commands to
  replies. It declares itself non-evidence at `run_reader.py:6-9`. That
  declaration is the only thing standing between it and a twin of
  `books/nntp-projection.lisp`; if a gate's output is ever cited as fn
  evidence, it becomes one.
- `bin/fn:804` and `tools/run_store.py:2054`: `--inbound-max-octets` defaults
  to 1048576, which `fn-cfg-peer-inboundp` refuses (the ceiling is 32768).
  Not a twin — the value is operator configuration carried into the record —
  but a live defect `w10/v0-matrix` measured, and its own lane declined it.
  The one-owner fix is a default of `None` resolved from the model at
  `peer_arguments`/`set_peer`, not a second typed number. Two live files, so
  it is reported and not taken.
- `tests/identity_differential.py:68,79` is the last caller keeping
  `host/store-host.lisp:214` alive.
