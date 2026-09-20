# Handoff: w2/mutable-owner (C1-05, the mutable service owner)

Worktree `/Users/ember/dev/fn/build/lanes/w2-mutable-owner`, branch
`w2/mutable-owner`, merged with `dev` c1c8ab1 (b431b94). HEAD: the commit
carrying this file (the fourth of the lane after the merge).

## What the owner is

One process holds the store (exclusive writer lock), reopens it through
`fn-sn-open-observed` and drives `fn-own-step` (`books/owner.lisp`). A
committed version (the length of the durable record history) is pinned per
connection at open; writers are serialized through the one pending
transaction; readers are served concurrently, each through the served port
`fn-own-read`: one `fn-served-step` (`books/served.lisp`) per socket read
over the connection's own wire state, session and pinned archive, never over
the live node. `specs/owner.md` is the specification.

## Books (this wave: realigned to `docs/proof-style.md`)

| Book | Status | Evidence |
| --- | --- | --- |
| `books/owner.lisp` | CERTIFIED (ACL2 8.7, this laptop, `tools/certify_books.py`) | `build/acl2/certify-20260919T235441Z-24670` |
| `books/owner-invariants.lisp` | CERTIFIED | `build/acl2/certify-20260920T000958Z-62232` |
| `tests/acl2/owner-tests.lisp` | CERTIFIED (95 `assert-event`s) | `build/acl2/certify-20260920T000958Z-62232` |

Ledger regenerated (`python3 tools/ledger.py --write`); `make check` green
(0 owner lints, 0 owner suspects). Nothing in the cluster is open except
what the last section lists.

Makefile roots sit after `tests/acl2/served-tests` (the owner includes
`served`, `store-observed` and `clock`).

Realignment, in proof-style order: (1) the connection
`(id version frontier wire session archive)`, view, owner and group-fact
records are opaque, with `fn-<field>-of-fn-own-<make>` record lemmas and the
three forward-chaining shape facts each; (2) `books/owner` ends with
`fn-own-vocabulary` (recognizer, glue, transitions, machine withdrawn) and
`books/owner-invariants` with `fn-own-invariants-vocabulary` (keystones stay
enabled); (3) `fn-own-open-kind-ok-is-okp` is `:rule-classes nil`; (4) the
served port and every connection event are guard `t` verified, the store
events carry `(fn-sn-statep (fn-own-store o))`, and no recognizer of any
kind runs on a served read; (5) every tooth is an `assert-event` on a
concrete violating value. Local vocabulary opened in `owner-invariants`
(named on the board): store's `fn-snt-relation`, `fn-snrt-step`,
`fn-snt-step`, the `fn-sn-*` transitions, `fn-sn-completion-enabledp`,
`fn-sf-crash-imagep`, `fn-sn-open-okp`/`-errorp`; nntp's session record;
served's `fn-served-open`.

## Keystones (statements unchanged from the first cut; two new)

- `fn-own-read-is-served-step-on-pinned-prefix` (new; the host's subject):
  hyps `(fn-own-relation o)`, `(fn-own-find-conn id (fn-own-conns o))`;
  concl `(car (fn-own-read o id octets))` equals
  `(fn-served-result-effects (fn-served-step (fn-served-make-conn wire session (fn-node-acceptance (fn-sf-replay-node groups capacity (fn-own-take version records) frontier))) octets))`
  with the connection's own wire, session, version and frontier.
  `-after-any-trace` (new): the same over `(fn-own-run o events)`.
- `fn-own-reader-sees-pinned-prefix-replay` and `-after-any-trace`: the
  per-event law (`fn-nntp-step` on one framed event), statements unchanged.
- `fn-own-completion-consumed-once`, `fn-own-pinned-prefix-survives-any-trace`,
  `fn-own-reclaim-floor-below-every-pin`,
  `fn-own-connections-bounded-after-any-trace`,
  `fn-own-completed-post-survives-close-and-any-trace`,
  `fn-own-run-preserves-relation`, `fn-own-run-preserves-store-relation`,
  `fn-own-open-observed-start-relation`, the three fact theorems: unchanged.
- Recorded open (test book): the connection-exists hypothesis of
  `fn-own-pinned-prefix-survives-any-trace` has no violating value.

## Host and Python

`host/owner-host.lisp`: one `fn-own-read` per `fn-owner-chunk` (no wire
globals, no suffix), `fn-owner-open` returns the greeting from the book,
`fn-owner-recover` dispatches on `fn-sn-open-kind`
(`fn-own-open-kind-ok-is-okp`), `fn-owner-outcome` feeds a submission's
outcome back through `(:outcome id outcome)`. `tools/run_owner.py`: one
`bridge.chunk` per `recv`, `Owner.submit` is the served POST seam.
`run_store.py post --owner` and `post_article` unchanged. Tests:
`tests/test_owner.py` (4).

Python evidence (`python3 -m unittest tests.test_owner tests.test_reader
tests.test_reader_partitions tests.test_served_differential`, this laptop,
dev c1c8ab1 merged): 22 of 28 pass (`test_reader` seed cases 8/8,
`test_reader_partitions` 7/7, `test_served_differential` 7/7). The six
`--store` cases (four owner, two reader) FAIL before reaching what they
test, in two layers, both outside the owner: (1) `run_store.py init`
crashed on dev, `Store.config_record_path` (`tools/run_store.py:719`, from
w4/config-records) lacked `@property` while its five call sites use it as
one; fixed in this tree and posted on the board; (2) with that fixed, the
store bridge's own startup does not reach a prompt: `(ld
"host/anchor-host.lisp")` stalls past 900 s after `books/replay`,
`host/store-host.lisp` and `host/store-node-host.lisp` load, under a 6 to
8 load average with four foreign certifications holding every ACL2 slot,
and `books/config{,-invariants,-records}` (loaded by `host/config-host.lisp`)
have no certificates in this worktree (`make certs-install` lists them
uncached). Logs: the scratchpad `pytests.log`, `pytests2.log`. Rerun the
six on a quiet box after `make certs-install` publishes the config books.

## What the server wave still needs from this lane

- Groups from configuration records: `fn-own-declare-group` keeps the fact
  log in the owner process; `books/config-records` (w4) is the durable
  record kind it should replay from, so `(:reopen ...)` and
  `fn-owner-recover` restore the groups and `fn-sn-groups` stops being a
  process constant (`*fn-store-groups*` in the host).
- POST folded in: when w4/post's submit effect lands in `fn-nntp-effectp`,
  `Acl2Owner.chunk` returns it as the third value, `Owner.submit` runs the
  durable path with the connection as transaction owner, and
  `(:outcome id outcome)` gets its meaning in `fn-own-step` (the 240/441
  reply is then the book's, not the host's).
- Legacy RFC 2980 commands (`XOVER`, `XHDR`, `LIST NEWSGROUPS`) belong in
  `books/nntp-responses.lisp` per the nntp NOTE; the owner needs nothing for
  them beyond the archive they read.
- The `fn` CLI and service unit: `tools/run_owner.py` is the process; a
  `fn serve <store>` entry and a unit file that runs it with `--control`
  under the store directory are host work, plus `run_reader.py --store`
  becoming a thin client of the owner.
- Guard closure: store gives `fn-snrt-step`/`fn-snt-step` the guard
  `(fn-sn-statep s)` and verifies them; the owner then verifies
  `fn-own-store-step`, `fn-own-step`, `fn-own-run`.
- Carry `fn-served-connp` per connection in `fn-own-relation` so the owner
  inherits `fn-served-step-effects-are-typed` (needs the served port to
  refuse a non-octet read).
- Python evidence for the `--store` paths: the two host defects above
  (`config_record_path`, fixed here; the bridge startup stall and the
  uncertified config books, tooling) have to clear before the owner's four
  socket tests and the two store-reader tests can run to a verdict.
