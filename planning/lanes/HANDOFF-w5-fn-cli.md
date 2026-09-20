# Handoff: w5/fn-cli (the operator surface)

Lane `w5/fn-cli`, worktree `/Users/ember/dev/fn/build/lanes/w5-fn-cli`,
branched at `7a9e89a` (dev). Deliverable: an operator can install and run fn
as one command, one configuration file and a service unit. No book was
touched, so nothing here needed certification.

## What landed

| File | What it is |
| --- | --- |
| [`bin/fn`](../../bin/fn) | the CLI: `init run post group status recover anchor` |
| [`packaging/fn.service`](../../packaging/fn.service) | systemd unit |
| [`packaging/net.fn.plist`](../../packaging/net.fn.plist) | launchd daemon |
| [`packaging/fn.toml.example`](../../packaging/fn.toml.example) | the annotated configuration |
| [`docs/operator.md`](../../docs/operator.md) | the two-page operator guide (linked from `docs/README.md`) |
| [`tests/test_fn_cli.py`](../../tests/test_fn_cli.py) | five cases: the store-side sequence, the live-service sequence, the three outcome codes |
| [`tests/interop_fn_cli_nntplib.py`](../../tests/interop_fn_cli_nntplib.py) | the independent read-back probe |

`bin/fn` adds no semantics. It reads one TOML file with `tomllib`
(`[store] path`, `[listener] host port`, `[posting] enabled agent`,
`[anchor] server`, `[acl2] path slots`, plus `[log] path` and
`[control] path`), turns it into the arguments `tools/run_store.py` and
`tools/run_owner.py` already take, and writes exactly **one** line on stderr
per invocation whose first word is the outcome. `accepted` 0, `refused` 1,
`uncertain` 3, `fault` 4, `usage` 5 -- `run_store`'s own codes, unchanged;
the delegated command's stderr is captured and folded into that one line so
two processes never write two outcome lines for one invocation.

The served groups are deliberately **not** in the configuration file. They
are durable configuration records that ACL2 replays (w5/config-groups);
`fn init --group` seeds them once, `fn group create|retire` changes them.

## How `run` wraps the owner without editing it

`tools/run_owner.py`, `host/owner-host.lisp` and `books/owner*.lisp` belong
to the sibling `w5/owner-post` lane and were not edited. `fn run` rebinds
the two classes `run_owner.main` looks up by name --

- `run_owner.Acl2Owner` -> a subclass whose `outcome(cid, word)` logs the
  book's own outcome word for the served POST seam, then defers;
- `run_owner.Owner` -> a subclass whose `accept_nntp`, `drop`, `read_line`
  and `control` log and then defer

-- and then calls `run_owner.main(argv)` unchanged. **The entry points this
lane depends on** (also posted on the board as a NOTE, so the owner lane
keeps them stable):

1. `run_owner.main(argv)` accepting `--store --port --control
   --max-connections --clock-error-ms`, printing `LISTENING <port>` and
   `CONTROL <path>` on stdout, and releasing the writer lock and unlinking
   the control socket in its `finally`.
2. `run_owner.Owner` and `run_owner.Acl2Owner` as **module-level names** that
   `main` looks up at call time (not local imports, not closures).
3. `Owner.accept_nntp(listener)` installing the new connection in
   `self.connections`, `Owner.drop(conn)` with `conn.cid`,
   `Owner.control(sock)` returning the reply bytes or raising,
   `Owner.read_line(sock)` called as `self.read_line(...)`,
   `Owner.outcome_word(error)`, and `Acl2Owner.outcome(cid, word)` with the
   words `committed`/`duplicate`/`refused`/`uncertain`.
4. `run_store.post_via_owner`'s `POST <message-id> <groups> <charge> <length>`
   control line, and the `VERSION` and `CONNECTIONS` lines `fn status` probes.
5. SIGTERM raising `SystemExit(128 + SIGTERM)` out of the loop and through
   that `finally`.

Logging: one line per accepted, refused and uncertain post (control path and
served seam) and per reader connection, outcome word first, to `[log] path`
or stderr.

## Two limits refused rather than papered over

- **A non-loopback `[listener] host`.** `run_owner.main` binds `127.0.0.1`
  and nothing else, and `docs/architecture.md` says this scaffold does not
  authorize a public listener. `fn run` refuses (exit 1) instead of quietly
  serving loopback. The fix is the owner's: a `--host` argument.
- **`fn group create|retire` while the service is live.** A configuration
  record needs the exclusive writer lock the owner holds, so `fn` refuses
  with that reason rather than letting the operator read
  `store is already locked`. `docs/operator.md` documents stop/change/start.
  The real fix is the reconfiguration event in the owner: w5/config-groups
  already put its exact form on the board as a PROPOSAL to `w5/owner-post`.

## Open, recorded rather than hidden

- **`fn status` while an owner is live.** The control channel answers
  `VERSION` and `CONNECTIONS`; there is no control line for the
  configuration generation, the article count or the anchor, and this lane
  will not recompute any of the three in Python (the store's own ACL2 owns
  them). Those fields print `owner-held` while the service runs and are
  exact when it is stopped. **Ask to the owner lane:** one `STATUS` control
  line returning `generation=<g> articles=<n> anchor=<incarnation|none>`
  from the values the bridge already holds closes this in one line here.
- **`[posting] agent`.** The injecting-agent identity reaches the operator
  log and nothing else. `run_store.post_article` has no parameter for it and
  the durable injection record is built inside ACL2, so wiring it through is
  an interface change in the store cluster, not a Python addition.
- **`[posting] enabled = false`** gates the `fn post` subcommand only. The
  owner's control socket still accepts `POST`; gating it there is the
  owner's configuration, not this file's.
- `fn recover` reports the freshness verdict's exit code, so a store with no
  recorded anchor recovers `accepted` (`anchor=none`) and one that cannot
  reach a server recovers `uncertain`. That is `run_store`'s existing
  contract, unchanged.

## The one blocker, and it is not in this lane

`fn run` cannot start on this base. `books/owner.lisp` fails to include:

```
ACL2 Error [Failure] in ( DEFUN FN-OWN-OPEN ...)
  ... is (ARCHIVE LINE-LIMIT BODY-LIMIT CONFIG OBSERVATION).
ACL2 Error [Failure] in ( INCLUDE-BOOK "books/owner" ...)
```

`fn-served-open` and `fn-served-make-conn` grew two fields with w4/post
(board CHANGE `w4-post-compose`) and the owner cluster has not caught up;
the board NOTE from w3/reader-profile to the owner names the same two call
sites. That repair belongs to `w5/owner-post`. `bin/fn` needs no change for
it: the moment `books/owner` includes, the wrapped classes and the service
test run as written.

`tests/test_fn_cli.py::test_init_run_post_read_group_status_sigterm_recover`
therefore skips with that exact ACL2 text in the skip reason, and only on
that text -- any other failure to start fails the test. The store-side
sequence it does not cover is covered for real by
`test_init_post_group_status_and_recover_without_a_live_owner`.

## Evidence

`python3 tools/check_scaffold.py` (this worktree): `Scaffold OK: 161 Markdown
files, 50 requirements, 18 proof targets, 18 scenario specifications`,
`Ledger OK`, 156 pre-existing ledger lints, unchanged from dev.

`python3 -m unittest tests.test_fn_cli -v`, this laptop, ACL2 8.7 through
`tools/run_store.py`'s bridge: **5 tests, 4 OK, 1 skipped in 51.1 s**. The
skip is the live-service case on the `books/owner` include failure above;
the four that ran are the store-side sequence (init, post committing
sequence 0, `group create` reaching generation 2, `status` reporting
`owner=absent generation=2 transactions=1 articles=1 anchor=none`, `recover`
reporting `transactions=1 articles=1 anchor=none`), the refused post and
missing store on exit 1 and exit 4, the non-loopback listener refusal, and
the missing configuration refusal. Log:
`/tmp/claude-501/-Users-ember-dev-fn/990cbaad-8018-4168-a716-1ffe2d847cfb/scratchpad/fncli2.log`.

No book was touched, so no certification was run and none was needed.

The nntplib read-back probe runs under `/opt/homebrew/bin/python3.12` and is
skipped when it is absent, the pattern `tests/test_post.py` established
(nntplib was removed in Python 3.13). It has not yet run against a live
owner, for the reason above.
