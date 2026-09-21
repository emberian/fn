# Handoff: w10/v0-matrix

Branch `w10/v0-matrix` from dev `92e4a40`, worktree `build/lanes/w10-v0-matrix`.

## What this lane is

v0 is **every feature of fn usable between two peered fn nodes**. Before this
lane nobody could say, per feature, whether that was true: the evidence was
spread over `tools/deploy_gate.py`, `tools/twonode_gate.py`, `tools/inn_lab.py`,
`tools/tcpcl_lab.py`, `tools/scale_gate.py` and a set of hand-written records,
and "green" was a step count.

`tools/v0_matrix.py` is that question asked feature by feature, executably.

```sh
python3 tools/v0_matrix.py dev --host persvati          # the gate
python3 tools/v0_matrix.py --list                       # the inventory, nothing run
python3 tools/v0_matrix.py --check                      # validate the committed JSON
```

It stands up two fn nodes A and B on one box, peers them, drives the whole
surface between them and writes two files: `planning/v0-matrix.json` (machine
readable, indexed by requirement id and scenario id) and
`planning/evidence/v0-matrix-<date>.md`.

Everything below the rows is `DeployGate`'s and `TwoNodeGate`'s, reused by
subclassing: shipping the commit, installing the host's certificates pair by
pair, starting a server on a port, the step accounting, the evidence renderer,
the `presence`/`relay`/`cut` driver. This file owns three things: the row
inventory, the probes that decide which rows can run, and the two outputs.

## The verdict vocabulary

Five words, and they are never collapsed into pass/fail.

| verdict | what it means |
| --- | --- |
| `accepted` | the node did the thing (D13's accepted outcome) |
| `refused` | the node decided not to, and that decision is the observation |
| `uncertain` | the node could not tell, or did not say (a reset, a 4xx fault code, an exit code outside the vocabulary) |
| `not-exercised` | the row could not run; `blocker` says exactly why |
| `not-built` | the feature is not on the tree; `blocker` says why and `owner` names the lane |

A row whose feature **is** a refusal -- a duplicate offer drawing 435, a
capacity overflow, a wrong password -- and which draws its refusal reads
`refused`, and that is the feature working. Whether a row did what it was
designed to do is the separate `agrees` bit: `verdict == expected`, null when
the row did not run or is a pure probe.

**Do not read `verdict == "accepted"` as the green test.** Read

```
verdict in ("accepted", "refused", "uncertain") and agrees is not False
```

## The JSON shape

Agreed with the release lane (`w9/release`) before it was written.

```json
{
  "schema_version": 1,
  "generated_by": "tools/v0_matrix.py",
  "generated_at": "2026-09-20T...Z", "wall_seconds": 0.0,
  "commit": "<40 hex>", "revision": "<7 hex>", "tree": "dev", "host": "persvati",
  "evidence": "planning/evidence/v0-matrix-<date>.md",
  "verdicts": ["accepted","refused","uncertain","not-exercised","not-built"],
  "outcomes": ["accepted","refused","uncertain"],
  "summary": {"accepted":0,"refused":0,"uncertain":0,"not-exercised":0,
              "not-built":0,"total":0,"disagreed":0},
  "features": [{"id":"F-READ","title":"...","rows":["..."],
                "counts":{...},"disagreed":0}],
  "rows": [{
    "id": "V0-TRANSIT-DUPLICATE-AB",
    "feature": "F-TRANSIT", "feature_title": "...",
    "title": "a second IHAVE of the same Message-ID is refused with 435",
    "node": null, "direction": "ab",
    "requirements": ["REP-002"], "scenarios": ["SCN-022"],
    "verdict": "refused", "expected": "refused", "agrees": true,
    "invocation": "python3 <deploy>/feed.py relay --from-port ... --to-port ...",
    "observed": "435 not wanted", "exit_code": null,
    "revision": "<7 hex>", "log": "planning/evidence/v0-matrix-<date>.md",
    "limit": "one host, loopback; the peer is not authenticated",
    "blocker": null, "owner": null
  }],
  "by_requirement": {"REP-002": ["V0-TRANSIT-DUPLICATE-AB"]},
  "by_scenario": {"SCN-022": ["V0-TRANSIT-DUPLICATE-AB"]},
  "rows_digest": "<sha256 over the canonical rows>"
}
```

`tools/verdict.py` composes harnesses by running them and parsing two lines, so
the matrix prints the same contract:

```
matrix: <path to the json>
evidence: <path to the md>
steps=<total rows> failed=<disagreed> not-exercised=<not-exercised + not-built>
```

and exits 0 (every row that ran agrees), 1 (one did not, or the document it
wrote is inconsistent) or 2 (the gate stopped early). `not-exercised` in that
line is the two non-outcome classes **summed**, so the fiber table and the
matrix cannot disagree.

## The inventory is declared, not accumulated

`PLAN` in `tools/v0_matrix.py` is every row the matrix can emit. A `Spec`'s
`scope` is `single`, `node` (one row per node, id suffixed `-A`/`-B`) or
`direction` (`-AB`/`-BA`). A phase that never reaches a planned row does not
drop it: `backfill` emits it as `not-exercised` saying the run reached its end
without it, so a silently skipped feature is impossible. `emit` refuses a
verdict outside the vocabulary, refuses a second emission of the same id, and
refuses a `not-exercised` or `not-built` row with no blocker.

`validate` checks a document against all of that plus a sha256 over the
canonical rows, and `tools/check_scaffold.py` runs it, so `make check` refuses a
verdict a person typed into the file. `tests/test_v0_matrix.py` has the six
ways that can be attempted, including a forged digest (which then fails on the
summary).

## Adding a row

1. Add a `Spec` to `PLAN` with its requirement and scenario ids from the
   registries. `expected` is one of the three outcomes, or `None` for a probe
   -- and a probe must carry a `limit` saying what it records instead (the test
   enforces that).
2. Emit it from a phase with `self.emit`, `self.from_step` (an exit code) or
   `self.from_reply` (an NNTP status line). Nothing else creates a row.
3. When the feature may be missing, probe for it and call `self.blocked(...)`
   with `verdict=NOT_BUILT` and the owning lane, quoting the reply or the
   uncertified book in the blocker.

## What the matrix must never do

It computes no decision ACL2 owns: no identity derivation, no group table, no
charge, no framing, no bound. Where it needed one it asked the node. The
charge in the capacity row is the one ACL2 returned; the ports are the
kernel's; the peer record's admissibility is `fn-cfg-peerp`'s.

## What the runs found

Eleven runs on persvati between `d469e99` and the head of this lane. Each one
fixed what the disagreements showed was wrong with the matrix and then found
the next thing wrong with the tree; the fixes are one commit each and the
commit messages carry the measurement. The tree moved under the lane twice
(`w10/auth-served` landed AUTHINFO and a certificate for `books/served`;
`w10/owner-feed` and `w9/dtn-2` landed `books/owner-feed` and
`books/bp-node`), so the runs are not a single sequence of one variable.

Findings about the tree, in the order they stopped being hidden:

1. **No fn server of any kind started** at first. `host/reader-host.lisp:4`
   includes `../books/served`, so the read-only entry point is behind the same
   certificate as the owner, and `books/peer-inbound` had no certificate on
   any gate persvati has ever held.
2. **`fn peer add` cannot succeed with the CLI's own default.**
   `--inbound-max-octets` defaults to 1048576 in both `tools/run_store.py` and
   `bin/fn`; `fn-cfg-peer-inboundp` (`books/peer-config.lisp:144`) requires at
   most `*fn-record-max-payload*` (`books/records.lisp:43`), which is 32768.
   No harness had ever written a peer record, so every "peering: not available
   on this tree" line in `tools/twonode_gate.py` and `tools/inn_lab.py` was
   measuring an unconfigured connection.
3. **A peer record written before the listener names port 0**, which
   `fn-store-cfg-peer-record` reads as a BP endpoint.
4. **The owner died on the first `IHAVE`** --
   `tools/run_owner.py:270` encoded octets that were already octets. Fixed on
   this branch; the fix is one line and the evidence is the run that found it.
5. **The owner dies again, further in**: with that fixed, a transfer reaches
   `drain` and raises `RuntimeError: unexpected ACL2 octet-list result` at
   `(fn-inj-nth <i> (@ fn-owner-submit-groups))`. Not this lane's seam; it is
   an ASK on the board. Both crashes are the same shape -- an exception inside
   `Owner.drain` is not caught there, so **a peer that offers an article can
   end the service**.
6. **An article with no `Date` is refused in transit** (`437`, RFC 5536
   section 3.1.1) and `tools/twonode_gate.py`'s builder writes none. The local
   store CLI accepts such an article, so the omission is invisible until one
   crosses -- and it made the duplicate and CHECK rows read as ACCEPTANCES,
   because nothing had crossed for them to be duplicates of.
7. **A plaintext command after a `382` wedges the connection** and every later
   phase with it.
8. **A POST through the served path committed the article and never answered
   the poster.** 340, the article, the dot, then no byte for 300 s, while the
   group's count rose by one and the owner answered fresh connections
   immediately -- D13's three outcomes not reaching the wire at all. **CLOSED
   by the clock work (D10-a) that landed while this lane ran**: at `c3b99f8`
   all ten POST rows are outcomes, 340/240/read-back/fresh-read all accepted
   and the duplicate refused with 441, and `V0-POST-CLOCK` confirms the
   duplicate cost the node nothing (`DATE` still answers 111). Recorded here
   because the matrix is what found it and the two states are in the same
   evidence file's history.
8b. **The credential `fn principal set-password` writes is rejected by the
   server.** `AUTHINFO USER matrix` answers 381 and `AUTHINFO PASS` answers
   `481 authentication failed`, on both nodes, with the secret the CLI had
   just written to `<store>/auth.toml` in the same run. `AUTHINFO` is also
   not advertised in CAPABILITIES at all, before or after, and `POST` before
   any login answers 340 -- so nothing on the served path is gated on the
   login that does not work. Four of the ten disagreements in the recorded
   run are these.
9. **`fn principal list` does not show what `fn principal set-password`
   wrote**: `<store>/auth.toml` and `<store>/principals/*.principal` are two
   registries.
10. **The reverse half of NNT-001 is live**: the node dispatches `IHAVE` and
    `MODE STREAM` on a connection it resolved as a peer and advertises
    neither. The forward half passes -- everything advertised is dispatched.

## The next global step

**The recorded run** is `c3b99f8` on persvati, 1149 s, 190 rows: 111 accepted,
25 refused, 2 uncertain, 29 not exercised, 23 not built, 10 disagreements, 2
rows observed by something that is not fn. Reading it: F-NODE, F-OUT, F-GROUP,
F-READ and F-POST are whole features that work between two peered nodes;
F-AUTH runs and disagrees; F-TRANSIT is 22 rows of `not-built` behind one
`IHAVE` that got no answer because node B had already died; F-FEED, F-CRASH
and F-BP are behind that same death and the image build.

One theorem, then one harness. **`books/peer-inbound` is the frontier**: every
book it includes has a certificate, and above it sit `books/served` (now
certified by `w10/auth-served`), `books/owner`, `books/owner-feed` and
`host/reader-host.lisp`. Below that, the two owner crashes and the POST hang
are what stand between this matrix and a run in which the transit, feed, POST
and crash rows are outcomes rather than blockers: roughly 60 of the 188 rows
move on those three alone, and none of them is a proof problem.

Nothing in the matrix needs to change for that to happen. The rows are already
written, the probes already flip, and the blockers already name the lane.
