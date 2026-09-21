# Owner survival, 2026-09-21: the second crash, and the boundary that was missing

Tree `build/lanes/w11-owner-survival`, branch `w11/owner-survival` from dev
`4732ace`. ACL2 8.7 (`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2`, sha256
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`), Python
3.14 on darwin 25.6.0; the matrix re-run is on persvati and says so in its own
record.

Everything the lane claims, with the command that produces it.

## 1. The open crash: two shapes in one global

`planning/deputies/BOARD.md:840` asked whether `(@ fn-owner-submit-groups)`
is supposed to hold octets per group, and what `fn-inj-nth` saw instead. It
is, and it saw ACL2 strings.

* The POST path stages `fn-inj-decision-groups`
  (`host/owner-host.lisp:260`), whose elements are octet lists:
  `fn-inj-group-namesp` (`books/injection.lisp:412`) requires
  `fn-cbor-octet-listp` of each.
* The transit path staged `(nth 3 args)` of
  `fn-peer-injection-arguments` (`host/owner-host.lisp:344`), which is
  `fn-peer-scope-groups` (`books/peer-inbound.lisp:140`). Its own comment
  says what it answers: "**Strings**, as `fn-node-prepare` takes."
* `Acl2Owner.submit_groups` (`tools/run_owner.py`) reads every element with
  `acl2_octet_list`, so on the first transit transfer it met `"fn.letters"`
  where it required a list of decimal naturals and raised
  `RuntimeError: unexpected ACL2 octet-list result`. Nothing caught it, so
  the owner process exited.

So it is neither "a shape the host handed the model" nor "a model answer
indexed wrongly": **the global had two contracts and the bridge implemented
one**. The fix is to render the transit half into the global's contract, with
the function the file already uses for exactly this (`fn-owner-group-octets`,
`host/owner-host.lisp:41`) and on the line above the one that already renders
the evidence string the same way. No decision moved into Python and no
decision moved into host Lisp: `fn-peer-scope-groups` still decides which
groups, and `fn-peer-decide-transfer` still decides whether.

## 2. The class: a host fault is a fourth outcome, and it costs one connection

The two crashes differ in their cause and agree in their consequence: an
exception under `Owner.serve` unwound through `run` and out of `main`. That
is a remote denial of service in a server whose whole purpose is to face
untrusted peers.

`books/owner-fault.lisp` is the transition, certified:

    FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py \
        books/owner-fault tests/acl2/owner-tests
    # build/acl2/certify-20260921T014925Z-66779
    # books/owner-fault 7.558 s, tests/acl2/owner-tests 8.916 s, both passed

`fn-own-fault` answers `(effects . owner)`, the shape `fn-own-outcome` and
`fn-own-read` answer, so the host installs and projects it exactly as it does
a served read. Its keystones, all in that book:

| name | what it says |
| --- | --- |
| `fn-own-fault-closes-the-faulted-connection` | the faulted connection is not found afterwards |
| `fn-own-fault-keeps-every-other-connection` | every other id finds an EQUAL connection, so every later step has the input it would have had |
| `fn-own-fault-clears-the-faulted-submission` | that connection's in-flight submission is gone, with no hypothesis that its socket was still open |
| `fn-own-fault-keeps-another-connections-submission` | a different connection's in-flight submission is untouched |
| `fn-own-fault-releases-the-faulted-transaction` | the pending transaction it held is released |
| `fn-own-fault-is-not-a-store-event` | store, committed view and completion ledger are unchanged |
| `fn-own-fault-reply-is-not-a-post-outcome` | the reply octets are not `fn-nntp-post-outcome`'s for ANY session and ANY completion, including its own malformed-session 403 |
| `fn-own-fault-effects-close-the-connection`, `-are-typed`, `-ask-for-nothing-else` | the host is told to close; the effects are `fn-served-effectsp`; no handshake and no submission are asked for |

`fn-own-fault-clears-the-faulted-submission` is the one that matters beyond
the faulted peer: `fn-own-take-submission` moves a submission into the
durable path only when NOTHING is in flight, so a boundary that abandoned the
connection and left its submission would have cost **every** connection the
post path — a denial of service outliving its cause.

Teeth are evaluated in `tests/acl2/owner-tests.lisp`, on the witness that
book already builds for the served POST path (`*own-taken*`: connection 4's
submission in flight and owning the pending transaction, reader 3 open at its
own pin — the exact state the process died in). One violating value per
hypothesis, the fault reply against all four posting lines, and
`fn-own-relation` holding after the fault.

## 3. Where the boundary is, and why

**Per event, in `Owner.run`'s dispatch, with a second boundary per submission
inside `Owner.drain`.** Not per connection.

* Per event, because an accept, a feed read and a feed poll have no
  connection at all, and a fault in one of them ended the process just as
  surely as a fault in a served read. One selector event is also the
  granularity at which resuming is sound: between events the owner is
  quiescent, and each transition it has just run is proved to touch one
  connection (`fn-own-read-touches-only-its-connection`; `fn-own-outcome`'s
  "no other connection is touched at all").
* Per submission inside `drain`, because the submission `drain` is carrying
  belongs to a **different** connection than the one whose read called it.
  A per-connection boundary would close the reader for the poster's failure
  and leave the poster's submission in flight. `drain` therefore reads the
  submission's connection id first, on its own, and continues with the next
  submission after a fault.

What each fault costs: a served-read fault costs one connection, a feed fault
costs one peer's session (its journal and queue are untouched, so the next
dial replays them), and a fault the host cannot attribute costs nothing —
which is why only that kind is counted, with `MAX_UNATTRIBUTED_FAULTS` = 16
before the owner stops with the fault exit code. Counting the attributable
ones would have handed a peer a way to stop the service by faulting that many
times, which is the defect this exists to remove. A lost ACL2 bridge
(`Acl2Store.poisoned`) stops the owner at once: the image is where every
decision is made, and there is nothing to keep serving with.

The host decides one thing here — whether it still trusts the socket. The
reply code, the fourth-outcome status and everything the owner forgets are
`fn-own-fault`, reached through `fn-owner-fault` (`host/owner-host.lisp`).

## 4. The test that had never existed

    python3 -m unittest tests.test_owner.OwnerSurvivesAFaultTests -v
    # test_a_fault_carrying_a_submission_leaves_the_post_path_open ... ok
    # test_a_fault_in_a_served_read_costs_that_connection_and_nothing_else ... ok
    # Ran 2 tests in 56.236s  OK

Each starts one owner with the documented test-only injector armed
(`--inject-fault served-read|drain`, `OWNER_FAULTS` in `tools/run_owner.py`),
which raises a `RuntimeError` — deliberately not a `StoreError`, because the
class of defect is the exception nobody expected, and the one that killed the
owner twice was a `RuntimeError` out of the ACL2 result parser. It fires
once, so the surviving connection cannot pass by faulting too.

The served-read case asserts: the faulting connection receives
`403 internal fault; this connection is closed and the server continues\r\n`
and then EOF, and **nothing else**; the connection open across the fault is
served `DATE` and `GROUP` at the pin it already had; a connection opened
after the fault is served; the control channel still answers `VERSION`, so it
is the same process; and stderr carries `FAULT served-read cid=… RuntimeError`,
which is the fault recorded distinctly — never `refused`, never `uncertain`.

The drain case asserts the same for a fault while carrying a submission, and
then the thing the model theorem is about: a second connection POSTs and
reaches `240`, so the faulted submission did not wedge the writer, and the
group holds the seed and the second article only, so the faulted article was
not committed.

Limitations of this test: the fault is injected, not provoked from the wire.
The two real crashes are fixed, so provoking one needs a defect; a regression
that drives the transit path from a peer is `tools/v0_matrix.py`'s transit
rows, in section 5.

## 5. Three defects the re-run found before it could measure anything

The first attempt at the re-run (`abbb2ff` on persvati, 273 s) measured
nothing, and what stopped it is worth more than the run would have been.

**(a) `bin/fn`'s logging wrapper mirrored a signature, and the server died at
start-up.** `install_logging_owner.LoggedOwner.__init__(self, *arguments)`
took positional arguments only, so the moment `Owner.__init__` gained
`faults=` the node raised `TypeError` — *after* printing `LISTENING`, which
is why `V0-NODE-START-A` and `-B` both read **accepted** while every socket
row behind them read not-exercised. Fixed by `*arguments, **keywords`: a
logging wrapper has no business knowing what its base takes. This is the
lane's own regression, caught by its own re-run, and it is the reason the
first attempt is reported here rather than quietly repeated.

**(b) `tools/v0_matrix.py` could abort the whole gate over a missing
blocker.** The paired-phase `else` branch built its blocker only from nodes
with no port, so a node that STARTED and then DIED gave an empty string,
`emit` refused the row (rightly — a not-exercised row must say why), and the
`GateError` ended the run. A gate that had forty outcomes in hand wrote 148
not-exercised rows instead. Now both reasons are named and the fallback is
never empty.

**(c) `tests/test_fn_cli.py` had been losing the `CONTROL` line for so long
that a stale assertion behind it had stopped being checked.** `Service.start`
read the service's stdout with `BufferedReader.readline()` after `select`;
`run_owner.main` prints `LISTENING` and `CONTROL` on adjacent lines, so one
`os.read` returns both, `readline()` buffers the second, and the next
`select` on the empty pipe never fires — the service is up and the harness
waits 300 s for a line it is holding. Measured: one raw read returned
`b"LISTENING 61627\nCONTROL /tmp/.../control.sock\n"`. Fixed with the
raw-descriptor pattern `tests/test_owner.py` already documents. Behind it,
`tests/interop_fn_cli_nntplib.py` asserted the greeting was `201` (posting
prohibited) against `fn run`, which is the OWNER and answers `200`; that
expectation dates from when `fn run` started the read-only reader.
`python3 -m unittest tests.test_fn_cli` now runs 5 tests in 156 s, OK,
against 337 s and one error before.

## 6. The matrix re-run: 36 rows moved, measured

    python3 tools/v0_matrix.py 941731a --host persvati
    # matrix: planning/v0-matrix.json
    # evidence: planning/evidence/v0-matrix-2026-09-21.md
    # steps=190 failed=22 not-exercised=16     (1449 s)

| | `c3b99f8` (recorded) | `941731a` (this lane) |
| --- | --- | --- |
| accepted | 111 | **138** |
| refused | 25 | **34** |
| uncertain | 2 | 2 |
| not-exercised | 29 | **15** |
| not-built | 23 | **1** |
| disagreements | 10 | **22** |
| rows an fn client saw | 136 | **172** |

**36 rows moved out of `not-built`/`not-exercised` into one of the three
outcomes**, and none moved the other way. The lane's note predicted about 33;
the number is measured, not predicted, and the extra three are
`V0-CFG-LIVE`, `V0-CFG-LIVE-REFUSE` and `V0-STX-CROSS`, paired-node rows that
were blocked by the same death without naming it.

Whole features that ran for the first time: **F-TRANSIT** is 24 rows of
outcomes where it was 22 `not-built` and 2 blocked -- an article crosses A to
B and B to A through `IHAVE`, `TAKETHIS`, `CHECK` and `MODE STREAM`, and
`V0-TRANSIT-IDENTICAL-AB/BA` say the octets that arrive are the octets that
left. **F-CRASH** is 9 rows where it was 6 blocked. **F-PIN**, **`V0-POST-CONCURRENT`**
and the two live-reconfiguration rows ran.

The 12 new disagreements are all fresh observations of behaviour nothing had
ever exercised, not regressions -- every one of them is a row that could not
run before:

* `V0-TRANSIT-DUPLICATE-AB/BA`: a second `IHAVE` of a Message-ID the node
  holds draws `335 send it`, where RFC 4644 and
  `fn-peer-history-is-refused-at-offer` say `435`.
* `V0-TRANSIT-CHECK-DUP-AB/BA`: `CHECK` of a duplicate draws `238`, not `438`.
* `V0-TRANSIT-LOOP-AB/BA` and `-ABSENT-AB/BA`: an article whose `Path`
  already names the receiving node is accepted (`235`) and then served, so
  the RFC 5537 section 3.2.1 loop refusal is not reaching the wire.
* `V0-FEED-QUEUE`/`V0-FEED-JOURNAL`: the matrix's own feed driver raises
  `NameError: name 'article' is not defined` -- a defect in
  `tools/v0_matrix.py`'s driver, not in the node.
* `V0-CRASH-RESTART`, `V0-PIN-ADVERTISED-B`: one recovery row and the
  capability-truthfulness row for node B, both first observations.

An independent lane, `w11/auth-live`, ran the matrix at `6fb30ca` with dev's
own copy of the transit fix and reported the same shape from a different
tree: `not-built` 23 to 1, twelve new transit disagreements. Two independent
measurements of the same move is the best evidence this lane has that the
number is the tree's and not the harness's.

## 7. What is still open after this lane

* `tools/run_reader.py` has no fault boundary at all. The reader host serves
  no writer and holds no store, so a fault there costs less, but the process
  still ends for every connection.
* Nothing states that the host calls `fn-own-fault` at every point where it
  can fault. The boundary's coverage is a property of the code, checked by
  reading `Owner.run` and `Owner.drain`, not a theorem.
* The fault reply is proved distinct from every POSTING outcome
  (`fn-nntp-post-outcome`, which is what the served path renders for a POST
  and what the fourth-outcome precedent is about). It is NOT proved distinct
  from the TRANSIT reply table (`fn-peer-transit-outcome-effects`), whose
  lines carry a free reason string and a free Message-ID, so the separation
  there needs a prefix lemma about `fn-nntp-string-octets` of a
  `string-append` rather than ground evaluation. Every code in that table
  has `3` as its middle digit and the fault has `0`, so the statement is
  available; the lemma is not written.
* `Owner.accept_control` catches `StoreError` and `OSError` around one
  command; the outer per-event boundary now covers the rest, but a control
  command that faults leaves its caller with no reply line for the fault.
