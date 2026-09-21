# Handoff: w11/owner-survival

Branch `w11/owner-survival` from dev `4732ace`, worktree
`build/lanes/w11-owner-survival`. Evidence:
[`planning/evidence/owner-survival-2026-09-21.md`](../evidence/owner-survival-2026-09-21.md).

## What this lane is

**A peer could end the owner.** Both instances were an uncaught exception
inside `Owner.drain` (`tools/run_owner.py`). One was fixed on dev before this
lane (line 270 encoded octets that were already octets). This lane fixes the
second, and then fixes the class: a single exception anywhere in the serve
loop took the whole server down, for every connection, because of one peer's
input.

The cost was measured, not asserted: node B's death in `drain` is the single
blocker behind 22 transit rows, 4 feed rows, 6 crash rows and 1 concurrency
row of the 190-row v0 matrix recorded at `c3b99f8`.

## 1. The open crash: one global, two contracts

`(@ fn-owner-submit-groups)` is read by `Acl2Owner.submit_groups` with
`acl2_octet_list`, one element at a time. The POST path stages octet lists
(`fn-inj-decision-groups`; `fn-inj-group-namesp` requires
`fn-cbor-octet-listp` of each). The transit path staged
`fn-peer-scope-groups`, whose own comment at `books/peer-inbound.lisp:139`
says it answers **strings**. So the first transit transfer met
`"fn.letters"` where the bridge required decimal naturals,
`RuntimeError: unexpected ACL2 octet-list result`, and the owner exited.

Fixed in `host/owner-host.lisp` by rendering the transit half into the
global's contract with `fn-owner-group-octets` — the function that file
already defines for exactly this, one line above the one that already
renders the evidence string the same way. ACL2 still decides which groups
(`fn-peer-scope-groups`) and whether (`fn-peer-decide-transfer`); nothing
moved into Python or into host Lisp but a representation change of ACL2's own
answer.

## 2. The class: `books/owner-fault.lisp`

`fn-own-fault` is the owner's host-fault transition: the RFC 3977 §3.2.1
`403` line, the close, and the connection, in-flight submission and pending
transaction the owner forgets. It answers `(effects . owner)`, the shape
`fn-own-outcome` answers, so the host installs and projects it exactly as it
does a served read.

It is a **fourth outcome**, following the precedent
`fn-post-outcome-separates-a-malformed-session` set for a malformed session:
`fn-own-fault-reply-is-not-a-post-outcome` says the octets are not
`fn-nntp-post-outcome`'s for any session and any completion, including that
function's own 403.

Why its own book rather than a form in `books/owner.lisp`: `books/owner` is
1,424 lines and is included by `owner-invariants`, `owner-config` and two
test books, so a form there costs five recertifications for a seam that is
about the HOST's failure rather than the service's. `books/owner-invariants`
is included LOCALLY here, so the connection-list algebra is cited rather than
copied and the host does not load two thousand proof rules into a served
node's world. The prefix stays `fn-own-` and `docs/prefixes.md` records the
book on that row.

The keystones are listed in the evidence, section 2.
`fn-own-fault-clears-the-faulted-submission` is the one that reaches past the
faulted peer: `fn-own-take-submission` takes nothing while a submission is in
flight, so a boundary that abandoned the connection and kept its submission
would have cost **every** connection the post path.

## 3. Where the boundary is

**Per event, in `Owner.run`'s dispatch, with a second boundary per submission
inside `Owner.drain`.**

* Per event, not per connection: an accept, a feed read and a feed poll have
  no connection at all and a fault in one of them ended the process just as
  surely. Between events the owner is quiescent, and each transition it just
  ran is proved to touch one connection.
* Per submission inside `drain`: the submission `drain` carries belongs to a
  different connection than the reader whose read called it. `drain` reads
  the submission's connection id first, on its own, so the boundary can name
  the right one, and continues with the next submission after a fault.

Accounting: an attributable fault costs one connection or one peer's feed
session and is **not** counted, because the number of those is already
bounded by `--max-connections` and counting them would hand a peer a way to
stop the service by faulting that many times. Only unattributable faults are
counted, 16 of them in a row before the owner stops with the fault exit code.
A poisoned ACL2 bridge stops it at once: the image is where every decision is
made.

## 4. The test

`tests/test_owner.py` `OwnerSurvivesAFaultTests`, two cases over the new
documented hook `--inject-fault served-read|drain` (`OWNER_FAULTS` in
`tools/run_owner.py`; one-shot, and a `RuntimeError` on purpose — the class
of defect is the exception nobody expected). One connection faults and gets
the 403 and EOF and nothing else; the connection open across the fault is
served at the pin it already had; a connection opened afterwards is served;
the control channel answers, so it is the same process; stderr carries
`FAULT`, distinct from `refused` and `uncertain`. The drain case then posts
from another connection to `240` and shows the faulted article is absent.

`SCN-026` is that scenario; `HST-005` (`specs/host.md`) is the requirement;
`PRF-035` is the proof target.

## 5. The matrix re-run

See section 5 of the evidence and `planning/v0-matrix.json`. Before: 190
rows at `c3b99f8`, 111 accepted / 25 refused / 2 uncertain / 29
not-exercised / 23 not-built, 10 disagreements.

## What is open after this lane

* `tools/run_reader.py` has no fault boundary at all.
* No theorem says the host calls `fn-own-fault` at every point where it can
  fault; the boundary's coverage is a code property.
* `fn-own-find-conn-of-remove-conn-same` is proved `local` in
  `books/owner-fault.lisp` because its sibling
  `fn-own-find-conn-of-remove-conn-other` lives in `books/owner-invariants`
  and that book did not need this half before. It moves there the next time
  that book is opened, rather than becoming a second exported copy.
* `fn-peer-transit-outcome` still never tests `fn-peer-sessionp`, so a
  wrong-level session gets a correct-looking transit reply — the offer
  `w10/session-depth` left on the board. The 403 vocabulary this lane adds is
  what that fix would use.
