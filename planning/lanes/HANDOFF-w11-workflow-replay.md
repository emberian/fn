# w11-workflow-replay handoff

Branch `w11/workflow-replay`, worktree `build/lanes/w11-workflow-replay`, from
`dev` `38460cf`, with `dev` merged again at `e67b6cb`.

## What the brief asked and what was actually open

The brief carried the defect w3/media-lab recorded in the body of `212dffa`:
after a journal reopen, `fn-workflow-work-status` answers `absent` for every
work id in the replayed history. **It was already cured nine minutes later**,
in `cdf4ae1`, by moving the projection into ACL2 as `fn-bp-work-status`; and
`6b83aa3` restored `relay_a_onward_obligation_recoverable_after_kill` and
fixed the `bp-lifetime` mismatch that was the lab's real stop. Both are on
`dev`. The brief was written from the commit body, which outlived its repair.

Three things were genuinely open, and this lane closed them.

**1. `fn-bp-work-status` had no theorem of any kind, and the host calls it.**
An `absent` that had just been wrong by construction was now right by
inspection only. `books/bp-workflow-replay-status.lisp` is the evidence.

**2. The assertion that had been removed was restored in a form that could
not fail.** `relay_a_onward_obligation_recoverable_after_kill` read
`work_status_a1 not in ("", "absent", "unknown")` — and the lab's own `else`
branch reaches that by RE-ENQUEUING `a1`. So the assertion held whether the
obligation came back from the journal or was created fresh, which is the one
distinction it exists to make.

**3. The four-node lab did not run at all on `dev`.** See below.

## The book: `books/bp-workflow-replay-status.lisp`

A new root rather than a twelfth section of `books/bp-workflow-records-invariants`,
which is at 856 lines. It opens by closing the workflow vocabulary its
dependency leaves enabled — that book's own disables are all `local`, so an
includer inherits `fn-bp-statep` and every accessor open, which is the fan
this project has measured four times. Every form in it proves in under 0.02 s.

Four keystones.

- `fn-bp-work-status-of-restart`. Under `fn-bp-statep`, the `:restart`
  transition a reopen runs changes the boundary answer by
  `fn-bp-work-status-after-restart` and by nothing else: an attempt that was
  in flight is marked `:restart-observed`, and `:absent`, `:outstanding`,
  `:receipted`, a retryable status and `:delivered` are fixed points. So a
  reopen can neither lose a work, nor invent one, nor reopen a receipted one.
  The hypothesis does two jobs: `fn-bp-restart` is the identity off it, and an
  attempt of a well-formed work carries a `fn-bp-transport-statusp`, which is
  what keeps the three non-attempt answers from being attempt answers.
- `fn-bp-replay-work-status-is-the-pre-crash-status-restarted`. Lifts that to
  `fn-bp-replay-journal`, which `host/workflow-host.lisp:8` calls on open. New
  `fn-bp-durable-events` names the pre-crash machine: the journal's denotation
  without the trailing restart, so "what the machine that never died would
  have answered" is a term and not a phrase.
- `fn-bp-work-origin-at-open-is-recovered-or-absent`. Against the id list
  `fn-bp-work-ids` records at open, every work the image holds reads
  `:recovered` and every other id reads `:absent`. Unconditional.
- `fn-bp-durable-enqueue-after-open-reads-enqueued`. This session's durable
  enqueue of an id that list does not name reads `:enqueued`.

Registered as `PRF-034`, milestone M3, requirements STO-005 and FLR-002,
with its events curated in `planning/proof-events.json`.

## Why provenance is a second answer and not a fourth status word

Two works can both read `:outstanding` and have reached the image by
materially different routes: one recovered from a cut, one enqueued after the
reopen. Folding that into `fn-bp-work-status` would have changed what every
existing caller and every existing witness means. So the image's id list is
carried separately: `fn-workflow-install-replay` records `fn-bp-work-ids` of
what it installed, the host holds that list unread, and
`fn-workflow-work-origin` hands it back to `fn-bp-work-origin`. The host
computes nothing; ACL2 answers `:recovered`, `:enqueued` or `:absent`.

One consequence worth stating plainly: in the session that RESOLVES a cut, the
obligation reads `:enqueued`, not `:recovered` — a recovery outcome applied
live is this session's act, and the replay that installed the image held no
such work. `:recovered` is what the NEXT process sees. That is the right
answer and it is what makes the lab's assertion bite.

## Teeth (`tests/acl2/bp-workflow-records-tests.lisp`)

`tools/teeth_check.py --evaluate` on that book: 321 probes, prefix ok, exit 0,
321 values, nothing flagged. The static pass and `make check` are clean.

The witness for the two status keystones is a journal on which the two sides
read **different** words — `:intent` before the cut, `:restart-observed`
after — because an equality witness that reads the same word on both sides
separates nothing. Beside it, `:receipted` and `:expired` as fixed points.

One tooth per hypothesis:

- `fn-bp-statep`: a value that is not a state, holding the same in-flight
  work. `fn-bp-restart` is the identity on it, so the attempt is not marked
  and the two sides part (`:intent` against `:restart-observed`).
- the replay's success: `(config, attempt, enqueue, outcome)` — an attempt
  before any enqueue. Replay refuses at the attempt and leaves the image at
  the prefix it reached, `:absent`, while the same records denote
  `:outstanding`.
- `fn-bp-pending-matchesp`: the wrong transaction pair, `:absent`.
- not fenced: the fenced pending, `:absent`.
- the id not already recovered: the same works with that id in the list,
  `:recovered`.
- the `:enqueue` kind: **a constructed state, and the book says so**. An
  `:attempt` pending over an image that holds no work gives `:absent`, and
  `fn-bp-prepare-attempt` only prepares an attempt for a work the image
  holds, so the composed machine does not reach it. The theorem quantifies
  over states, so the hypothesis is required; the tooth is honest about being
  a legal value rather than a reachable one.

## The lab was red on dev, for a reason nothing tested

`python3 tests/bp-dtn7/run_four_node_lab.py` at `38460cf` dies at line 439:

    TypeError: receive_bpa_request() missing 1 required keyword-only argument: 'bundle'

`4ec3541` (2026-09-19, "Key inbound staging by ACL2 bundle identity") made
`bundle` required and moved `tools/media.py` to `(identity, adu, bundle)`
triples. `w6/workflow-restart` branched from a dev that predated it and
recorded its 22-of-22 run at `9443fec`; the merge of the two produced a lab
that cannot start. `tests/test_four_node_lab.py` does fail on it — its skip
gate matches only the workflow refusal text — but nothing in `make check`
runs that file.

**`tests/ltp/run_fn_ltp_lab.py:96` is broken the same way and is not mine.**

The repair is in the mock BPA, and it is not cosmetic. fn stages an inbound
bundle under the identity ACL2 derives from the bundle's own primary block, so
a transport that hands the receiver invented octets hands it an invented
identity, and the duplicate and redelivery assertions become the mock's rather
than fn's. Each `submit` now encodes a real primary block through the new
`bundle_bridge.encode_primary` (ACL2's `fn-bpi-host-bundle-prefix`; nothing in
Python spells a BPv7 field), `deliver_into` carries the same octets under a
fresh BID, and the spool keeps them with a digest. Carried-media items are
triples with their own bundles. The run costs 67.1 s where it cost 40.5 s,
inside the 300 s budget.

Expiry in the lab stays the scheduler's: the primary block's lifetime is long
enough that no admissible true time falls outside it, so a bundle that reaches
a receiver is `:live` and `attempt_expires_while_no_contact_is_open` still
tests the thing it means to. That is written into the lab's limitations.

## Evidence

- `tests/evidence/2026-09-21-four-node-lab.md` and `.json`: 22 of 22.
- Certification, on the merged tree: hbox `run-20260921T010656Z-5f0e`,
  `build/acl2/certify-20260921T010700Z-1373865`, **37 books attempted, 37
  passed, 0 failed**, 398.4 s at `--jobs 8`, ACL2 8.7
  `/tank/fn/acl2-8.7/saved_acl2` sha256 `64030dda0b03bbb6…`, Python 3.12.7 on
  Linux 6.11. `books/bp-workflow-replay-status` 0.33 s,
  `books/bp-workflow-records` 0.65 s, `books/bp-workflow-records-invariants`
  0.64 s, `tests/acl2/bp-workflow-records-tests` 0.60 s,
  `tests/acl2/bp-workflow-records-guards-tests` 0.23 s. An earlier run on the
  pre-merge tree (`run-20260921T005523Z-05dc`) passed the same 37.
- A third run covers the commit after it, which changes three COMMENT lines
  in `books/bp-workflow-replay-status.lisp` (host line numbers that moved when
  `fn-workflow-work-origin` was added) plus `docs/prefixes.md` and registry
  prose. Content hashing means a comment invalidates a certificate, so the
  pairs are regenerated; nothing in it is a proof change. See the board.

## Open, and named

1. **Re-certify on the merged tree.** The certification above is for the
   pre-merge revision. Same command, same box.
2. **`tests/ltp/run_fn_ltp_lab.py` does not run** — the same missing `bundle`.
   Whoever owns the LTP lab: `bundle_bridge.encode_primary` is there now, and
   `IonStagingInbox` needs a `bundle` alongside its `download`.
3. **Nothing in `make check` runs a lab.** Both labs were broken for a day by
   a signature change with no complaint from any gate. A cheap first step is a
   caller-signature lint over the host entry points, or a `make labs` that CI
   runs.
4. **`fn-workflow-work-origin` has no caller outside the lab.** The real
   server does not read provenance yet. When it does — a reopened node
   deciding what to re-offer a peer is the obvious case — the answer is there
   and proved.
