# Handoff: `w24/process-containment`

This development-only packet addresses the 2026-09-21 escaped-test incident;
it changes no ACL2 book, protocol contract, requirement, or proof claim.

`tools/run_command.py` is the CLI:

```sh
python3 tools/run_command.py --timeout 120 -- python3 -m unittest tests.test_feed -v
```

Its shared `tools/process_supervisor.py` starts the command in a new POSIX
session.  A leader exit alone is not command completion: timeout, SIGTERM, and
SIGINT send SIGTERM to every live inherited-group member, wait for the selected
bounded grace, escalate to SIGKILL, then reap the direct child.  The command
transcript is an explicit bounded final tail (1 MiB default), so it does not
use `communicate()` to retain unbounded output. It does not claim to clean a
descendant that creates a new session/process group, or to run cleanup after
the supervisor itself is SIGKILLed.

`make tooling-test` uses this CLI around its focused Python suite, including
the new containment regressions. Those regressions retain a shell leader and a
Python grandchild, verify timeout, SIGTERM, and SIGINT cleanup, and cover the
critical case where the leader has already exited while its grandchild ignores
SIGTERM and retains stdout. A repeated SIGTERM during cleanup cannot interrupt
the escalation/reap sequence. `tests/test_feed.py` also covers the finite
ancestor walk: a stop directory outside the chain is refused before
`dirname('/')` can repeat.

Validation run from this lane, with an outer 45-second guard:

```sh
python3 -m py_compile tools/process_supervisor.py tools/run_command.py \
  tools/feed_wire.py tests/test_process_supervisor.py tests/test_feed.py
timeout 45s python3 tools/run_command.py --timeout 30 -- \
  python3 -m unittest tests.test_process_supervisor \
  tests.test_feed.JournalTests.test_non_ancestor_directory_walk_stops_at_root -v
```

ACL2, certification, broad test suite, or deployment action was run.
The contained process tests and finite-walk regression passed. No ACL2,
certification, broad test suite, or deployment action was run.
ACL2, certification, broad test suite, or deployment action was run.
