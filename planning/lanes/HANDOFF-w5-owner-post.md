# w5/owner-post — the owner serves POST end to end

Branch `w5/owner-post` from `dev` at `b7f106b`. Worktree `build/lanes/w5-owner-post`.
One process holds the store, pins a committed version per connection,
serializes durable posts and serves readers and POST on one listener; the
interim `run_reader.py --post` path is gone.

## What landed

| File | What it is |
| --- | --- |
| `books/owner.lisp` | Connection record `(id version frontier wire session archive config observation)`; owner record gains `config`, `queue`, `inflight`; submission record `(id version mark decision)`. `fn-own-read` records the `:submit` effect of a served read as a submission against the connection and its pinned version; `fn-own-take-submission` is the writer step; `fn-own-outcome` renders the reply through `fn-served-post-outcome`; `fn-own-configure` sets the posting configuration new connections pin; `fn-own-close` drops a connection's submissions; `fn-own-conn-boundedp` and `fn-own-advance` read the POST session's base; `fn-own-read-step` is one `fn-served-dispatch`. |
| `books/owner-invariants.lisp` | Every earlier keystone under its name; the three POST events preserve the relation and K3/K4/K5/K6 cover them (`fn-own-connection-events-keep-store-bound-and-ledger` is what the trace lemmas now read instead of opening the served step inside each event). New: `fn-own-outcome-completion-is-one-of-three`, `fn-own-durable-reply-names-a-durable-record`, `fn-own-read-touches-only-its-connection`, `fn-own-outcome-touches-only-its-connection`, `fn-own-conn-boundedp-is-post-session`. |
| `tests/acl2/owner-tests.lisp` | The served POST transcript on the owner witness: 440 unconfigured; 340, the article, one queued submission (connection 5, version 2), the take (mark 2, pending 5), a second take refused while one is in flight, the uncertain 441 for a host word of `:durable` before any completion, the store events, 240 from the book, the three lines distinct, the reply reaching connection 5 alone; reader 4 pinned at 2 across the post while connection 6 opens at 3; a From-less 441 that queues nothing; close dropping a queued submission. One violating value per hypothesis of each new keystone. |
| `host/owner-host.lisp` | `fn-owner-take`, `fn-owner-outcome` (renders through `fn-own-outcome`), `fn-owner-post-config` from the store groups, `fn-owner-submittedp`. |
| `tools/run_owner.py` | One clock observation per connection at accept; `drain` takes one submission at a time through `durable_post` and feeds the observed word back; every reply octet is the book's. `post_via_owner` is unchanged as the CLI client. |
| `tools/run_reader.py` | Read-only: `--post`, `PostOwner`, `submission`/`reselect`/`outcome` removed; POST is the book's 440. |
| `tests/test_post.py` | Against the owner: 340/240 and read-back through a second connection, the From-less 441, the uncarried-group 441, the duplicate-Message-ID refusal 441, the read-only reader's 440, the nntplib probe, and a pinned-reader concurrency case (a reader open before the post keeps its view and its `423`; a reader opened after sees the article; `ADVANCE ALL` moves it). |
| `specs/nntp.md`, `specs/node-functionality.md` | POST section rewritten around the owner; sections 2.1, 3.6, 5.2 updated. |

## The shape of the decision

A served read that injects an article leaves a `:submit` effect; the owner
queues it (`fn-own-read`) and returns the served step's effects unchanged,
so K1 holds as before. `fn-own-take-submission` moves the oldest queued
submission into the durable path only when nothing is in flight, no
transaction is pending and the store is `:ready`, and records the ledger
length as the submission's mark. The host runs the same `:store`/`:complete`
events the CLI post reports. `fn-own-outcome` turns the host's word into the
completion `fn-served-post-outcome` renders: `:durable` only when the ledger
grew past the mark (a completion consumed by `fn-own-complete`, which
consumes the actual `fn-sn-finish`); `:refused` for the host's typed
refusal; `:uncertain` for everything else, including a host that claims
`:durable` without a consumed completion. The reply is produced for the
connection whose submission is in flight and no other; the connection
record is unchanged by it.

Serialization is structural: `inflight` is one record, the take is refused
while it is filled (`fn-own-take-submission` is the identity then; witnessed
in the test book, not cited as a theorem), and the Python `drain` loop is the
same discipline in the host.

## Statements changed, and why

Forced by the w4-post-compose byte fold, not chosen here: the served
connection is five fields, so `fn-own-read-is-served-step-on-pinned-prefix`
and its `-after-any-trace` form thread the connection's pinned `config` and
`observation` into `fn-served-make-conn`; the per-event law
`fn-own-reader-sees-pinned-prefix-replay` (and `-after-any-trace`) is stated
over `fn-served-dispatch`, the step the fold now applies, where it was
stated over `fn-nntp-step` before POST existed. `fn-own-open-session-boundedp`
opens the five-argument `fn-served-open`. Everything else keeps its
statement.

`fn-own-durable-reply-names-a-durable-record` is `:rule-classes nil` (its
`(equal word :durable)` conjunct would rewrite a variable); it is cited, not
rewritten with.

## Open, recorded rather than weakened

1. The completion a 240 names is proved to be a ledger pair consumed after
   the take with a record in the durable history, not to be the
   submission's own article: a control-channel post consumed in the same
   window would satisfy the theorem. The host serializes; the book records
   only the ledger mark. Closing it needs the record's Message-ID compared
   with the decision's.
2. No theorem states serialization beyond the shape of `inflight`; the
   refused take is witnessed in the test book.
3. RFC 3977 section 3.5 pipelining after POST's article (w4 open item 6)
   stands; the session has no awaiting-outcome state.
4. The greeting is still a fixed 201; POST is not advertised in
   CAPABILITIES (w4 open item 4).
5. `fn-own-pinned-prefix-survives-any-trace`'s connection-exists hypothesis
   is still unnecessary (w2 note), kept as stated.
6. A duplicate supplied Message-ID through the served path is a refusal
   (441), not 240: this submission made nothing durable. The CLI's
   `duplicate` exit stays as it was.

## Evidence

ACL2 (this worktree, `ACL2_BOOK_HASH_ALISTP=NIL`, `FN_ACL2_TIMEOUT_SECONDS=1800`),
on the tree merged with dev 7a9e89a (config-groups, reader profile): the
dev-changed books in the owner closure recertified in place
(`build/acl2/certify-20260920T025533Z-22858`: nntp-responses, nntp,
nntp-overview, nntp-invariants, nntp-effects, nntp-post), then one invocation
`build/acl2/certify-20260920T030724Z-59801` certifies `books/served`,
`tests/acl2/served-tests`, `books/owner`, `books/owner-invariants` and
`tests/acl2/owner-tests`, every `assert-event` of the owner test book
passing under real ACL2. Before the merge the three owner roots certified on
b7f106b in `certify-20260920T014456Z-95448`, `-014458Z-95661` and
`-015014Z-10448`.

Python: see the farm gate of dev after 40b75e4. The last local run
(`python3 -m unittest tests.test_post tests.test_owner tests.test_reader
tests.test_served_differential -v`, 31 tests, 102 s): 25 pass, including the
served 440, both 441s (From-less, uncarried group), the duplicate-Message-ID
refusal, every reader and differential case; 6 fail, and all six are the one
defect this lane's last commit addresses: on the merged tree
`Store.recover` asks the bridge for the allocation domain and the inherited
`fn-store-cfg-domain` reads `fn-store-sn`, a global the owner image never
sets, so `group_codes` saw an empty domain and every durable post (served
240 and control-channel `committed`) was refused. `fn-owner-domain` answers
from the owner's own node; that fix is committed untested locally (the
laptop's slot pool starves further suite runs) and the farm gate is its
verdict. Two harness defects fixed on the way: `OwnerProcess.start` read the
two banner lines through a `BufferedReader` after `select`, which slurped
both on one read and then never saw the second (every owner "did not start"
with an empty stderr); and the failure path read a stopped process's stderr.
A hand-driven transcript against the merged owner before that fix (fresh
store, one CLI seed post) showed the served path itself working end to end:
201, 340, the duplicate refusal `441 posting failed; the article was
refused`, `version 1`, QUIT.

